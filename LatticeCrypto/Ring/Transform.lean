/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import Batteries.Data.Vector.Lemmas
import LatticeCrypto.Ring.Kernel

/-!
# Generic Transform Layer For Negacyclic Rings

Optional transform-domain (NTT) acceleration layer on top of a bundled
coefficient-domain `NegacyclicRing`. Defines:

- `TransformPoly`: a newtype wrapper tagging a coefficient-domain polynomial as
  living in the transform domain. Provides its own `Zero`, `Add`, `Sub`, `Neg`,
  and `GetElem` instances via the underlying ring operations.
- `TransformOps`: the transform interface bundle (`toHat` / `fromHat` and
  pointwise arithmetic), plus lifted vector and matrix operations (`hatVec`,
  `dot`, `matVecMul`, etc.).
- `TransformOps.Laws`: a proposition asserting that the transform is a ring
  isomorphism compatible with the coefficient-domain operations.

Scheme-specific concrete NTTs (under `Concrete/NTT.lean`) provide executable
`TransformOps` instances. Proof-oriented uses consume `TransformOps.Laws`.
-/


universe u v

namespace LatticeCrypto

/-- A newtype tagging a coefficient-domain polynomial as a transform-domain value.

The wrapper exists so that transform-domain vectors and matrices carry a
distinct type from their coefficient-domain counterparts, preventing accidental
mixing. Arithmetic instances delegate to the underlying `NegacyclicRing`
operations. -/
@[ext] structure TransformPoly {Coeff : Type u} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) where
  coeffs : ring.Poly

namespace TransformPoly

variable {Coeff : Type u} [CommRing Coeff] {ring : NegacyclicRing Coeff}

instance [Repr ring.Poly] : Repr (TransformPoly ring) where
  reprPrec fHat prec := Repr.reprPrec fHat.coeffs prec

instance [DecidableEq ring.Poly] : DecidableEq (TransformPoly ring)
  | ⟨coeffs₁⟩, ⟨coeffs₂⟩ =>
      match decEq coeffs₁ coeffs₂ with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by
          intro hEq
          cases hEq
          exact h rfl)

/-- Rewrap a coefficient-domain polynomial as a tagged transform-domain value. -/
def ofPoly (f : ring.Poly) : TransformPoly ring :=
  ⟨f⟩

/-- Forget the transform-domain tag. -/
def toPoly (fHat : TransformPoly ring) : ring.Poly :=
  fHat.coeffs

/-- Expose a transform-domain value through the bundled executable kernel. -/
def toArray (fHat : TransformPoly ring) : Array Coeff :=
  ring.kernel.toArray fHat.coeffs

instance : Coe (TransformPoly ring) ring.Poly :=
  ⟨TransformPoly.toPoly⟩

instance : Zero (TransformPoly ring) :=
  ⟨⟨ring.zero⟩⟩

instance : Add (TransformPoly ring) :=
  ⟨fun fHat gHat => ⟨ring.add fHat.coeffs gHat.coeffs⟩⟩

instance : Sub (TransformPoly ring) :=
  ⟨fun fHat gHat => ⟨ring.sub fHat.coeffs gHat.coeffs⟩⟩

instance : Neg (TransformPoly ring) :=
  ⟨fun fHat => ⟨ring.neg fHat.coeffs⟩⟩

instance : GetElem (TransformPoly ring) Nat Coeff (fun _ i => i < ring.degree) where
  getElem fHat i hi := ring.backend.coeff fHat.coeffs ⟨i, hi⟩

@[simp] theorem getElem_eq_coeffs_getElem
    (fHat : TransformPoly ring) {i : Nat} (hi : i < ring.degree) :
    fHat[i] = ring.backend.coeff fHat.coeffs ⟨i, hi⟩ :=
  rfl

end TransformPoly

/-- Transform-domain acceleration interface for a bundled negacyclic ring.

Bundles the forward and inverse transforms (`toHat` / `fromHat`) together with
pointwise transform-domain arithmetic (`zeroHat`, `addHat`, `subHat`, `mulHat`).
Concrete NTT modules provide executable instances; `TransformOps.Laws` certifies
that the transform is a ring isomorphism. -/
structure TransformOps {Coeff : Type u} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) (Hat : Type v) where
  toHat : ring.Poly → Hat
  fromHat : Hat → ring.Poly
  zeroHat : Hat
  addHat : Hat → Hat → Hat
  subHat : Hat → Hat → Hat
  mulHat : Hat → Hat → Hat

namespace TransformOps

variable {Coeff : Type u} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat α : Type v}

/-- Backwards-compatible projection name for transform conversion. -/
abbrev ntt (ops : TransformOps ring Hat) : ring.Poly → Hat :=
  ops.toHat

/-- Backwards-compatible projection name for inverse transform conversion. -/
abbrev invNTT (ops : TransformOps ring Hat) : Hat → ring.Poly :=
  ops.fromHat

/-- Backwards-compatible projection name for transform-domain multiplication. -/
abbrev multiplyNTTs (ops : TransformOps ring Hat) : Hat → Hat → Hat :=
  ops.mulHat

/-- Transpose a row-major `PolyMatrix`, swapping rows and columns. -/
def transpose {rows cols : Nat} (A : PolyMatrix α rows cols) :
    PolyMatrix α cols rows :=
  Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j

variable (ops : TransformOps ring Hat)

/-- Apply the transform coordinate-wise to a coefficient-domain vector. -/
def hatVec {k : Nat} (v : PolyVec ring.Poly k) : PolyVec Hat k :=
  v.map ops.toHat

/-- Apply the inverse transform coordinate-wise to a transform-domain vector. -/
def unhatVec {k : Nat} (v : PolyVec Hat k) : PolyVec ring.Poly k :=
  v.map ops.fromHat

/-- Backwards-compatible alias for `hatVec`. -/
abbrev nttVec {k : Nat} (v : PolyVec ring.Poly k) : PolyVec Hat k :=
  hatVec ops v

/-- Backwards-compatible alias for `unhatVec`. -/
abbrev invNTTVec {k : Nat} (v : PolyVec Hat k) : PolyVec ring.Poly k :=
  unhatVec ops v

/-- Multiply a transform-domain scalar by each component of a transform-domain vector. -/
def scalarVecMul {k : Nat} (cHat : Hat) (vHat : PolyVec Hat k) : PolyVec Hat k :=
  Vector.map (ops.mulHat cHat) vHat

/-- Coefficient-domain scalar/vector multiplication via the transform layer. -/
def coeffScalarVecMul {k : Nat} (c : ring.Poly) (v : PolyVec ring.Poly k) :
    PolyVec ring.Poly k :=
  ops.unhatVec (ops.scalarVecMul (ops.toHat c) (ops.hatVec v))

/-- Dot product in the transform domain. -/
def dot {k : Nat} (u v : PolyVec Hat k) : Hat :=
  (Vector.zipWith ops.mulHat u v).foldl ops.addHat ops.zeroHat

/-- Matrix-vector multiplication in the transform domain. -/
def matVecMul {rows cols : Nat} (A : PolyMatrix Hat rows cols) (v : PolyVec Hat cols) :
    PolyVec Hat rows :=
  A.map fun row => ops.dot row v

/-- Transposed matrix-vector multiplication in the transform domain. -/
def matTransposeVecMul {rows cols : Nat}
    (A : PolyMatrix Hat rows cols) (v : PolyVec Hat rows) :
    PolyVec Hat cols :=
  (transpose A).map fun row => ops.dot row v

/-- Coefficient-domain matrix-vector multiplication via the transform layer. -/
def coeffMatVecMul {rows cols : Nat}
    (A : PolyMatrix Hat rows cols) (v : PolyVec ring.Poly cols) :
    PolyVec ring.Poly rows :=
  ops.unhatVec (ops.matVecMul A (ops.hatVec v))

/-- Coefficient-domain transposed matrix-vector multiplication via the transform layer. -/
def coeffMatTransposeVecMul {rows cols : Nat}
    (A : PolyMatrix Hat rows cols) (v : PolyVec ring.Poly rows) :
    PolyVec ring.Poly cols :=
  ops.unhatVec (ops.matTransposeVecMul A (ops.hatVec v))

@[simp] theorem hatVec_get {k : Nat} (v : PolyVec ring.Poly k) (i : Fin k) :
    (ops.hatVec v).get i = ops.toHat (v.get i) :=
  Vector.get_map v ops.toHat i

@[simp] theorem unhatVec_get {k : Nat} (v : PolyVec Hat k) (i : Fin k) :
    (ops.unhatVec v).get i = ops.fromHat (v.get i) :=
  Vector.get_map v ops.fromHat i

/-- Algebraic laws asserting that a `TransformOps` instance is a ring isomorphism.

States that `toHat` / `fromHat` are mutual inverses and that `toHat` preserves
zero, addition, subtraction, and multiplication. Scheme-specific concrete NTTs
discharge these obligations (typically via matrix certification). -/
structure Laws (ops : TransformOps ring Hat) : Prop where
  fromHat_toHat : ∀ f : ring.Poly, ops.fromHat (ops.toHat f) = f
  toHat_fromHat : ∀ fHat : Hat, ops.toHat (ops.fromHat fHat) = fHat
  toHat_zero : ops.toHat ring.zero = ops.zeroHat
  toHat_mul : ∀ f g : ring.Poly,
    ops.toHat (ring.mul f g) = ops.mulHat (ops.toHat f) (ops.toHat g)
  toHat_add : ∀ f g : ring.Poly,
    ops.toHat (ring.add f g) = ops.addHat (ops.toHat f) (ops.toHat g)
  toHat_sub : ∀ f g : ring.Poly,
    ops.toHat (ring.sub f g) = ops.subHat (ops.toHat f) (ops.toHat g)

end TransformOps

end LatticeCrypto
