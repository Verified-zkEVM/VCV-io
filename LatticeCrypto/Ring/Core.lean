/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Init.Data.Vector.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Generic Negacyclic Ring Core

Semantic foundations for the generic lattice ring layer. Defines:

- `PolyBackend`: a backend-neutral, coefficient-indexed carrier for fixed-degree polynomials.
- `PolyVec` / `PolyMatrix`: length-indexed module containers over an arbitrary carrier.
- `NegacyclicQuotient`: the proof-facing quotient ring `R[X] / (X^n + 1)`.

All definitions here are purely semantic — no executable array operations or mutable
state. Executable array exposure is layered on top in `LatticeCrypto.Ring.Kernel`, and
the canonical vector-backed instantiation lives in `LatticeCrypto.Ring.VectorBackend`.
-/


open scoped BigOperators

universe u v

namespace LatticeCrypto

/-- A length-`k` vector over an arbitrary carrier. -/
abbrev PolyVec (P : Type u) (k : Nat) := Vector P k

/-- A `rows × cols` row-major matrix over an arbitrary carrier. -/
abbrev PolyMatrix (P : Type u) (rows cols : Nat) := Vector (PolyVec P cols) rows

namespace PolyVec

variable {P : Type u} {k : Nat}

/-- View a vector as a `Fin k → P` function. -/
def toPi (v : PolyVec P k) : Fin k → P :=
  fun i => v.get i

/-- Build a vector from a `Fin k → P` function. -/
def ofPi (f : Fin k → P) : PolyVec P k :=
  Vector.ofFn f

@[simp] theorem toPi_ofPi (f : Fin k → P) :
    toPi (ofPi f) = f := by
  funext i
  simp [toPi, ofPi, Vector.get]

@[simp] theorem ofPi_toPi (v : PolyVec P k) :
    ofPi (toPi v) = v := by
  apply Vector.ext
  intro i hi
  simp [toPi, ofPi, Vector.get]

end PolyVec

namespace PolyMatrix

variable {P : Type u} {rows cols : Nat}

/-- View a row-major matrix as a Mathlib `Matrix`. -/
def toMatrix (A : PolyMatrix P rows cols) : Matrix (Fin rows) (Fin cols) P :=
  fun i j => (A.get i).get j

/-- Build a row-major matrix from a Mathlib `Matrix`. -/
def ofMatrix (A : Matrix (Fin rows) (Fin cols) P) : PolyMatrix P rows cols :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] theorem toMatrix_ofMatrix (A : Matrix (Fin rows) (Fin cols) P) :
    toMatrix (ofMatrix A) = A := by
  funext i j
  simp [toMatrix, ofMatrix, Vector.get]

@[simp] theorem ofMatrix_toMatrix (A : PolyMatrix P rows cols) :
    ofMatrix (toMatrix A) = A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [toMatrix, ofMatrix, Vector.get]

end PolyMatrix

/-- Backend-neutral storage for fixed-degree polynomials.

A `PolyBackend` bundles a carrier type `Poly`, a fixed `degree`, and a bijective
coefficient-indexing interface (`coeff` / `build`). Concrete instantiations include
vector-backed storage (`vectorBackend`) and function-backed storage (`piBackend`).

The backend carries no arithmetic — ring operations are added by `NegacyclicRing`
in `LatticeCrypto.Ring.Kernel`. -/
structure PolyBackend (Coeff : Type u) where
  Poly : Type v
  degree : Nat
  coeff : Poly → Fin degree → Coeff
  build : (Fin degree → Coeff) → Poly
  coeff_build : ∀ f i, coeff (build f) i = f i
  build_coeff : ∀ p, build (coeff p) = p

namespace PolyBackend

variable {Coeff : Type u}

/-- Materialize coefficients as an eager array. -/
def coeffArray (backend : PolyBackend Coeff) (p : backend.Poly) : Array Coeff :=
  Array.ofFn fun i : Fin backend.degree => backend.coeff p i

@[simp] theorem coeff_build_apply (backend : PolyBackend Coeff)
    (f : Fin backend.degree → Coeff) (i : Fin backend.degree) :
    backend.coeff (backend.build f) i = f i :=
  backend.coeff_build f i

@[simp] theorem build_coeff_apply (backend : PolyBackend Coeff) (p : backend.Poly) :
    backend.build (backend.coeff p) = p :=
  backend.build_coeff p

/-- Bridge the backend carrier to a Mathlib polynomial by summing monomials. -/
noncomputable def toPolynomial [Semiring Coeff]
    (backend : PolyBackend Coeff) (p : backend.Poly) : Polynomial Coeff :=
  ∑ i : Fin backend.degree, Polynomial.monomial i.val (backend.coeff p i)

/-- Map coefficients between equal-degree backends. -/
def mapCoeffs {Coeff' : Type v}
    (src : PolyBackend Coeff) (dst : PolyBackend Coeff')
    (hdeg : src.degree = dst.degree) (f : Coeff → Coeff') (p : src.Poly) : dst.Poly :=
  dst.build fun i =>
    f (src.coeff p ⟨i.val, by
      exact Nat.lt_of_lt_of_eq i.isLt hdeg.symm⟩)

end PolyBackend

/-- The semantic modulus polynomial `X^n + 1`. -/
noncomputable def negacyclicModulus (R : Type u) [Semiring R] (n : Nat) : Polynomial R :=
  Polynomial.X ^ n + 1

/-- The proof-facing semantic model `R[X] / (X^n + 1)`.

This is the mathematical ring that executable `NegacyclicRing` operations are
sound with respect to. The soundness bridge is provided by
`NegacyclicRingSemantics` in `LatticeCrypto.Ring.Kernel`. -/
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

end LatticeCrypto
