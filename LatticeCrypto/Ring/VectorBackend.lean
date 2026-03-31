/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Init.Data.Vector.Algebra
import LatticeCrypto.Ring.Kernel

/-!
# Vector Backend For Negacyclic Rings

Canonical instantiation of the generic ring layer using `Vector Coeff n` as the
polynomial carrier. Provides:

- `Poly`: a type alias for `Vector Coeff n`.
- `vectorBackend`: a `PolyBackend` backed by `Vector`.
- `vectorKernel`: a `PolyKernel` that bridges `Vector` to `Array`.
- `vectorNegacyclicRing`: the bundled `NegacyclicRing` with pointwise
  add/sub/neg and `schoolbookNegacyclicMul`.
- `vectorNegacyclicSemantics`: the `noncomputable` proof bridge to the
  quotient ring `R[X] / (X^n + 1)`.

All three scheme `Arithmetic.lean` modules (`MLDSA`, `MLKEM`, `Falcon`)
instantiate their coefficient-domain rings through `vectorNegacyclicRing`.
-/


universe u

namespace LatticeCrypto

/-- A degree-`n` polynomial represented by a coefficient vector. -/
abbrev Poly (Coeff : Type u) (n : Nat) := Vector Coeff n

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
  simp [toPi, ofPi, Vector.get]

@[simp] theorem ofPi_toPi (p : Poly Coeff n) :
    ofPi (toPi p) = p := by
  apply Vector.ext
  intro i hi
  simp [toPi, ofPi, Vector.get]

end Poly

/-- The canonical vector-backed semantic backend. -/
def vectorBackend (Coeff : Type u) (n : Nat) : PolyBackend Coeff where
  Poly := Poly Coeff n
  degree := n
  coeff := fun p i => p.get i
  build := Vector.ofFn
  coeff_build := by
    intro f i
    simp [Vector.get]
  build_coeff := by
    intro p
    apply Vector.ext
    intro i hi
    simp [Vector.get]

/-- The canonical vector/array executable kernel. -/
def vectorKernel (Coeff : Type u) [Zero Coeff] (n : Nat) :
    PolyKernel Coeff (vectorBackend Coeff n) where
  toArray := Vector.toArray
  ofArray := fun a => Vector.ofFn fun i => a.getD i.val 0
  toArray_size := by
    intro p
    exact p.size_toArray
  coeff_ofArray := by
    intro a h i
    have hi : i.val < a.size := by
      exact Nat.lt_of_lt_of_eq i.isLt h.symm
    simp [vectorBackend, hi, Vector.get]
  ofArray_toArray := by
    intro p
    apply Vector.ext
    intro i hi
    simp

/-- The canonical bundled negacyclic ring over the vector backend. -/
def vectorNegacyclicRing (Coeff : Type u) [CommRing Coeff] (n : Nat) :
    NegacyclicRing Coeff where
  backend := vectorBackend Coeff n
  kernel := vectorKernel Coeff n
  zero := (0 : Poly Coeff n)
  add := fun f g => Vector.ofFn fun i => f.get i + g.get i
  sub := fun f g => Vector.ofFn fun i => f.get i - g.get i
  neg := fun f => Vector.ofFn fun i => -f.get i
  mul := schoolbookNegacyclicMul (vectorKernel Coeff n)

section VectorRingSimp

variable {Coeff : Type u} [CommRing Coeff] {n : Nat}

private abbrev vRing (Coeff : Type u) [CommRing Coeff] (n : Nat) :=
  vectorNegacyclicRing Coeff n

@[simp] theorem vectorBackend_coeff (p : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff p i = p.get i := rfl

@[simp] theorem vectorRing_zero :
    (vectorNegacyclicRing Coeff n).zero = (0 : Poly Coeff n) := rfl

@[simp] theorem vectorRing_zero_get (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).zero).get i = (0 : Coeff) := by
  show (0 : Vector Coeff n).get i = 0
  simp [Vector.get, Zero.zero, Vector.instZero]

@[simp] theorem vectorRing_add_get (f g : Poly Coeff n) (i : Fin n) :
    ((vRing Coeff n).add f g).get i = f.get i + g.get i := by
  simp [vRing, vectorNegacyclicRing, Vector.get]

@[simp] theorem vectorRing_sub_get (f g : Poly Coeff n) (i : Fin n) :
    ((vRing Coeff n).sub f g).get i = f.get i - g.get i := by
  simp [vRing, vectorNegacyclicRing, Vector.get]

@[simp] theorem vectorRing_neg_get (f : Poly Coeff n) (i : Fin n) :
    ((vRing Coeff n).neg f).get i = -f.get i := by
  simp [vRing, vectorNegacyclicRing, Vector.get]

end VectorRingSimp

/-- Proof-facing quotient interpretation for the canonical vector backend.

Maps each executable operation to its counterpart in the quotient ring
`R[X] / (X^n + 1)` and asserts soundness of the mapping. -/
noncomputable def vectorNegacyclicSemantics (Coeff : Type u) [CommRing Coeff] (n : Nat) :
    NegacyclicRingSemantics (vectorNegacyclicRing Coeff n) where
  quotientOf := NegacyclicQuotient.ofBackend (vectorBackend Coeff n)
  zero_sound := by sorry
  add_sound := by intro f g; sorry
  sub_sound := by intro f g; sorry
  neg_sound := by intro f; sorry
  mul_sound := by intro f g; sorry

end LatticeCrypto
