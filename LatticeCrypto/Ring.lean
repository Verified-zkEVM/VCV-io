/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Init.Data.Vector.Algebra
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Generic Negacyclic Lattice Arithmetic

This file defines the generic architectural layer for negacyclic lattice arithmetic.
The core is backend-neutral:

- `PolyBackend` describes a fixed-degree polynomial carrier.
- `NegacyclicQuotient` is the proof-facing semantic model `R[X]/(X^n + 1)`.
- `NegacyclicOps` packages executable coefficient-domain arithmetic.
- `TransformOps` packages an optional transform-domain acceleration layer.

The existing vector-backed carrier remains available as `Poly`, but is now just one
backend instance (`vectorBackend`) rather than the only representation.
-/


open scoped BigOperators

universe u v

namespace LatticeCrypto

/-- A degree-`n` polynomial represented by its coefficient vector. -/
abbrev Poly (Coeff : Type u) (n : Nat) := Vector Coeff n

/-- A length-`k` vector of degree-`n` polynomials. -/
abbrev PolyVec (Coeff : Type u) (n k : Nat) := Vector (Poly Coeff n) k

/-- A `rows × cols` row-major matrix of degree-`n` polynomials. -/
abbrev PolyMatrix (Coeff : Type u) (n rows cols : Nat) := Vector (PolyVec Coeff n cols) rows

/-- Backend-neutral storage for fixed-degree polynomials. -/
structure PolyBackend (Coeff : Type u) where
  Poly : Type v
  degree : Nat
  toCoeffFn : Poly → Fin degree → Coeff
  ofCoeffFn : (Fin degree → Coeff) → Poly
  /-- Optional eager array exposure for executable kernels. -/
  toArray : Poly → Array Coeff

namespace Poly

variable {Coeff : Type u} {n : Nat}

/-- View a vector-backed polynomial as a `Fin n → Coeff` function. -/
def toPi (p : Poly Coeff n) : Fin n → Coeff :=
  fun i => p.get i

/-- Build a vector-backed polynomial from a `Fin n → Coeff` function. -/
def ofPi (f : Fin n → Coeff) : Poly Coeff n :=
  Vector.ofFn f

@[simp] theorem toPi_ofPi (f : Fin n → Coeff) :
    toPi (ofPi f) = f := by
  funext i
  simp [Vector.get, toPi, ofPi]

@[simp] theorem ofPi_toPi (p : Poly Coeff n) :
    ofPi (toPi p) = p := by
  apply Vector.ext
  intro i hi
  simp [Vector.get, toPi, ofPi]

end Poly

namespace PolyVec

variable {Coeff : Type u} {n k : Nat}

/-- View a vector-backed polynomial vector as a `Fin k → Poly Coeff n` function. -/
def toPi (v : PolyVec Coeff n k) : Fin k → Poly Coeff n :=
  fun i => v.get i

/-- Build a vector-backed polynomial vector from a `Fin k → Poly Coeff n` function. -/
def ofPi (f : Fin k → Poly Coeff n) : PolyVec Coeff n k :=
  Vector.ofFn f

@[simp] theorem toPi_ofPi (f : Fin k → Poly Coeff n) :
    toPi (ofPi f) = f := by
  funext i
  simp [Vector.get, toPi, ofPi]

@[simp] theorem ofPi_toPi (v : PolyVec Coeff n k) :
    ofPi (toPi v) = v := by
  apply Vector.ext
  intro i hi
  simp [Vector.get, toPi, ofPi]

end PolyVec

namespace PolyMatrix

variable {Coeff : Type u} {n rows cols : Nat}

/-- View a row-major polynomial matrix as a Mathlib `Matrix`. -/
def toMatrix (A : PolyMatrix Coeff n rows cols) :
    Matrix (Fin rows) (Fin cols) (Poly Coeff n) :=
  fun i j => (A.get i).get j

/-- Build a row-major polynomial matrix from a Mathlib `Matrix`. -/
def ofMatrix (A : Matrix (Fin rows) (Fin cols) (Poly Coeff n)) :
    PolyMatrix Coeff n rows cols :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] theorem toMatrix_ofMatrix (A : Matrix (Fin rows) (Fin cols) (Poly Coeff n)) :
    toMatrix (ofMatrix A) = A := by
  funext i j
  simp [Vector.get, toMatrix, ofMatrix]

@[simp] theorem ofMatrix_toMatrix (A : PolyMatrix Coeff n rows cols) :
    ofMatrix (toMatrix A) = A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [Vector.get, toMatrix, ofMatrix]

end PolyMatrix

namespace PolyBackend

variable {Coeff : Type u}

/-- The array obtained by reifying the coefficient function directly. -/
def coeffArray (backend : PolyBackend Coeff) (p : backend.Poly) : Array Coeff :=
  Array.ofFn fun i : Fin backend.degree => backend.toCoeffFn p i

/-- Bridge the backend carrier to a Mathlib polynomial by summing monomials. -/
noncomputable def toPolynomial [Semiring Coeff] (backend : PolyBackend Coeff) (p : backend.Poly) :
    Polynomial Coeff :=
  ∑ i : Fin backend.degree, Polynomial.monomial i.val (backend.toCoeffFn p i)

/-- Map coefficients between equal-degree backends. -/
  def mapCoeffs {Coeff' : Type v}
    (src : PolyBackend Coeff) (dst : PolyBackend Coeff')
    (hdeg : src.degree = dst.degree) (f : Coeff → Coeff') (p : src.Poly) : dst.Poly :=
  dst.ofCoeffFn fun i =>
    f (src.toCoeffFn p ⟨i.val, by
      have hi : i.val < dst.degree := i.isLt
      rwa [hdeg]⟩)

/-- Backend roundtrip laws. The proof-facing semantic bridges can rely on these while
executable kernels are free to use `toArray`. -/
structure Laws (backend : PolyBackend Coeff) : Prop where
  coeff_ofCoeffFn : ∀ f i, backend.toCoeffFn (backend.ofCoeffFn f) i = f i
  ofCoeffFn_coeff : ∀ p, backend.ofCoeffFn (backend.toCoeffFn p) = p

end PolyBackend

/-- The default vector-backed backend used by the current lattice developments. -/
def vectorBackend (Coeff : Type u) (n : Nat) : PolyBackend Coeff where
  Poly := Poly Coeff n
  degree := n
  toCoeffFn := fun p i => p.get i
  ofCoeffFn := Vector.ofFn
  toArray := Vector.toArray

/-- The vector-backed backend satisfies the backend roundtrip laws. -/
theorem vectorBackendLaws (Coeff : Type u) (n : Nat) :
    PolyBackend.Laws (vectorBackend Coeff n) where
  coeff_ofCoeffFn := by
    intro f i
    simp [vectorBackend, Vector.get]
  ofCoeffFn_coeff := by
    intro p
    apply Vector.ext
    intro i hi
    simp [vectorBackend, Vector.get]

/-- The semantic modulus polynomial `X^n + 1`. -/
noncomputable def negacyclicModulus (R : Type u) [Semiring R] (n : Nat) : Polynomial R :=
  Polynomial.X ^ n + 1

/-- The proof-facing semantic model `R[X]/(X^n + 1)`. -/
abbrev NegacyclicQuotient (R : Type u) [CommRing R] (n : Nat) :=
  Polynomial R ⧸ (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R)))

namespace NegacyclicQuotient

variable {R : Type u} [CommRing R] {n : Nat}

/-- Inject a polynomial into the negacyclic quotient. -/
noncomputable def ofPolynomial (n : Nat) (p : Polynomial R) : NegacyclicQuotient R n :=
  Ideal.Quotient.mk _ p

/-- Inject a backend carrier into the negacyclic quotient via its coefficient polynomial. -/
noncomputable def ofBackend (backend : PolyBackend R) (p : backend.Poly) :
    NegacyclicQuotient R backend.degree :=
  ofPolynomial backend.degree (backend.toPolynomial p)

end NegacyclicQuotient

/-- A length-`k` vector over a backend carrier. -/
abbrev CarrierVec {Coeff : Type u} (backend : PolyBackend Coeff) (k : Nat) :=
  Vector backend.Poly k

/-- A `rows × cols` row-major matrix over a backend carrier. -/
abbrev CarrierMatrix {Coeff : Type u} (backend : PolyBackend Coeff) (rows cols : Nat) :=
  Vector (CarrierVec backend cols) rows

/-- Executable coefficient-domain arithmetic for a negacyclic ring. -/
structure NegacyclicOps {Coeff : Type u} (backend : PolyBackend Coeff) where
  mul : backend.Poly → backend.Poly → backend.Poly

namespace NegacyclicOps

variable {Coeff : Type u} {backend : PolyBackend Coeff}

/-- Semantic soundness of an executable negacyclic multiplication against the quotient model. -/
structure Semantics [CommRing Coeff] (ops : NegacyclicOps backend) : Prop where
  mul_sound : ∀ f g,
    NegacyclicQuotient.ofPolynomial backend.degree (backend.toPolynomial (ops.mul f g)) =
      NegacyclicQuotient.ofPolynomial backend.degree (backend.toPolynomial f) *
        NegacyclicQuotient.ofPolynomial backend.degree (backend.toPolynomial g)

end NegacyclicOps

/-- Generic schoolbook negacyclic multiplication over a backend carrier. -/
def schoolbookNegacyclicMul {Coeff : Type u} [Ring Coeff]
    (backend : PolyBackend Coeff) (f g : backend.Poly) : backend.Poly := Id.run do
  let fa := backend.toArray f
  let ga := backend.toArray g
  let mut h : Array Coeff := Array.replicate backend.degree 0
  for i in [0:backend.degree] do
    for j in [0:backend.degree] do
      let fi := fa.getD i 0
      let gj := ga.getD j 0
      let k := (i + j) % backend.degree
      if i + j < backend.degree then
        h := h.set! k ((h.getD k 0) + fi * gj)
      else
        h := h.set! k ((h.getD k 0) - fi * gj)
  return backend.ofCoeffFn fun ⟨i, _⟩ => h.getD i 0

/-- A tagged transform-domain carrier over a coefficient-domain backend. -/
@[ext] structure TransformPoly {Coeff : Type u} (backend : PolyBackend Coeff) where
  coeffs : backend.Poly

namespace TransformPoly

variable {Coeff : Type u} {backend : PolyBackend Coeff}

instance [Repr backend.Poly] : Repr (TransformPoly backend) where
  reprPrec fHat prec := Repr.reprPrec fHat.coeffs prec

instance [DecidableEq backend.Poly] : DecidableEq (TransformPoly backend)
  | ⟨coeffs₁⟩, ⟨coeffs₂⟩ =>
      match decEq coeffs₁ coeffs₂ with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by
          intro hEq
          cases hEq
          exact h rfl)

/-- Rewrap a coefficient-domain polynomial as a tagged transform-domain value. -/
def ofPoly (f : backend.Poly) : TransformPoly backend := ⟨f⟩

/-- Forget the transform-domain tag. -/
def toPoly (fHat : TransformPoly backend) : backend.Poly := fHat.coeffs

/-- Expose a transform-domain value as a coefficient array through the backend coefficient view. -/
def toArray (fHat : TransformPoly backend) : Array Coeff :=
  backend.coeffArray fHat.coeffs

instance : Coe (TransformPoly backend) backend.Poly := ⟨TransformPoly.toPoly⟩

instance [Zero backend.Poly] : Zero (TransformPoly backend) := ⟨⟨0⟩⟩

instance [Add backend.Poly] : Add (TransformPoly backend) :=
  ⟨fun fHat gHat => ⟨fHat.coeffs + gHat.coeffs⟩⟩

instance [Sub backend.Poly] : Sub (TransformPoly backend) :=
  ⟨fun fHat gHat => ⟨fHat.coeffs - gHat.coeffs⟩⟩

instance [Neg backend.Poly] : Neg (TransformPoly backend) :=
  ⟨fun fHat => ⟨-fHat.coeffs⟩⟩

instance : GetElem (TransformPoly backend) Nat Coeff (fun _ i => i < backend.degree) where
  getElem fHat i hi := backend.toCoeffFn fHat.coeffs ⟨i, hi⟩

@[simp] theorem getElem_eq_coeffs_getElem
    (fHat : TransformPoly backend) {i : Nat} (hi : i < backend.degree) :
    fHat[i] = backend.toCoeffFn fHat.coeffs ⟨i, hi⟩ := rfl

@[simp] theorem toArray_getElem
    (fHat : TransformPoly backend) {i : Nat} (hi : i < backend.degree) :
    fHat.toArray[i]'(by simpa [toArray, PolyBackend.coeffArray] using hi) =
      backend.toCoeffFn fHat.coeffs ⟨i, hi⟩ := by
  simp [toArray, PolyBackend.coeffArray]

end TransformPoly

/-- Optional transform-domain acceleration for a coefficient-domain negacyclic ring. -/
structure TransformOps {Coeff : Type u} (backend : PolyBackend Coeff) (Hat : Type v) where
  coeffOps : NegacyclicOps backend
  toHat : backend.Poly → Hat
  fromHat : Hat → backend.Poly
  mulHat : Hat → Hat → Hat

namespace TransformOps

variable {Coeff : Type u} {backend : PolyBackend Coeff} {Hat α : Type v}

/-- Backwards-compatible projection name for transform conversion. -/
abbrev ntt (ops : TransformOps backend Hat) : backend.Poly → Hat := ops.toHat

/-- Backwards-compatible projection name for inverse transform conversion. -/
abbrev invNTT (ops : TransformOps backend Hat) : Hat → backend.Poly := ops.fromHat

/-- Backwards-compatible projection name for transform-domain multiplication. -/
abbrev multiplyNTTs (ops : TransformOps backend Hat) : Hat → Hat → Hat := ops.mulHat

/-- Transpose a row-major matrix. -/
def transpose {rows cols : Nat} (A : Vector (Vector α cols) rows) :
    Vector (Vector α rows) cols :=
  Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j

variable (ops : TransformOps backend Hat)

/-- Apply the transform coordinate-wise to a coefficient-domain vector. -/
def hatVec {k : Nat} (v : Vector backend.Poly k) : Vector Hat k :=
  v.map ops.toHat

/-- Apply the inverse transform coordinate-wise to a transform-domain vector. -/
def unhatVec {k : Nat} (v : Vector Hat k) : Vector backend.Poly k :=
  v.map ops.fromHat

/-- Backwards-compatible alias for `hatVec`. -/
abbrev nttVec {k : Nat} (v : Vector backend.Poly k) : Vector Hat k :=
  hatVec ops v

/-- Backwards-compatible alias for `unhatVec`. -/
abbrev invNTTVec {k : Nat} (v : Vector Hat k) : Vector backend.Poly k :=
  unhatVec ops v

/-- Multiply a transform-domain scalar by each component of a transform-domain vector. -/
def scalarVecMul {k : Nat} (cHat : Hat) (vHat : Vector Hat k) : Vector Hat k :=
  Vector.map (ops.mulHat cHat) vHat

/-- Multiply a coefficient-domain scalar by each component of a coefficient-domain vector
via the transform layer. -/
def coeffScalarVecMul {k : Nat} (c : backend.Poly) (v : Vector backend.Poly k) :
    Vector backend.Poly k :=
  ops.unhatVec (ops.scalarVecMul (ops.toHat c) (ops.hatVec v))

/-- Dot product in the transform domain. -/
def dot {k : Nat} [Zero Hat] [Add Hat] (u v : Vector Hat k) : Hat :=
  (Vector.zipWith ops.mulHat u v).foldl (· + ·) 0

/-- Matrix-vector multiplication in the transform domain. -/
def matVecMul {rows cols : Nat} [Zero Hat] [Add Hat]
    (A : Vector (Vector Hat cols) rows) (v : Vector Hat cols) :
    Vector Hat rows :=
  A.map fun row => ops.dot row v

/-- Transposed matrix-vector multiplication in the transform domain. -/
def matTransposeVecMul {rows cols : Nat} [Zero Hat] [Add Hat]
    (A : Vector (Vector Hat cols) rows) (v : Vector Hat rows) :
    Vector Hat cols :=
  (transpose A).map fun row => ops.dot row v

/-- Coefficient-domain matrix-vector multiplication via the transform layer. -/
def coeffMatVecMul {rows cols : Nat} [Zero Hat] [Add Hat]
    (A : Vector (Vector Hat cols) rows) (v : Vector backend.Poly cols) :
    Vector backend.Poly rows :=
  ops.unhatVec (ops.matVecMul A (ops.hatVec v))

/-- Coefficient-domain transposed matrix-vector multiplication via the transform layer. -/
def coeffMatTransposeVecMul {rows cols : Nat} [Zero Hat] [Add Hat]
    (A : Vector (Vector Hat cols) rows) (v : Vector backend.Poly rows) :
    Vector backend.Poly cols :=
  ops.unhatVec (ops.matTransposeVecMul A (ops.hatVec v))

/-- Generic transform laws, kept separate from scheme-specific primitive laws. -/
structure Laws [Add backend.Poly] [Sub backend.Poly] [Add Hat] [Sub Hat]
    (ops : TransformOps backend Hat) : Prop where
  fromHat_toHat : ∀ f : backend.Poly, ops.fromHat (ops.toHat f) = f
  toHat_fromHat : ∀ fHat : Hat, ops.toHat (ops.fromHat fHat) = fHat
  toHat_mul : ∀ f g : backend.Poly,
    ops.mulHat (ops.toHat f) (ops.toHat g) = ops.toHat (ops.coeffOps.mul f g)
  toHat_add : ∀ f g : backend.Poly,
    ops.toHat (f + g) = ops.toHat f + ops.toHat g
  toHat_sub : ∀ f g : backend.Poly,
    ops.toHat (f - g) = ops.toHat f - ops.toHat g

end TransformOps

/-- Integer-lift structure used by Falcon-style secret-key arithmetic. -/
structure IntegralLift (IntPoly Rq : Type*) where
  toRq : IntPoly → Rq
  mul : IntPoly → IntPoly → IntPoly
  const : ℤ → IntPoly

/-- The constant polynomial with value `c` at position 0 and 0 elsewhere. -/
def constPoly {Coeff : Type u} [Zero Coeff] (backend : PolyBackend Coeff) (c : Coeff) :
    backend.Poly :=
  backend.ofCoeffFn fun i => if i.val = 0 then c else 0

/-- The canonical integral lift from vector-backed integer polynomials to vector-backed
`ZMod q` polynomials. -/
def vectorIntegralLift (q n : Nat) :
    IntegralLift (Poly ℤ n) (Poly (ZMod q) n) where
  toRq := PolyBackend.mapCoeffs (vectorBackend ℤ n) (vectorBackend (ZMod q) n) rfl
    (fun z => (z : ZMod q))
  mul := schoolbookNegacyclicMul (vectorBackend ℤ n)
  const := constPoly (vectorBackend ℤ n)

end LatticeCrypto
