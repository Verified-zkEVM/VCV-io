/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all Init.Data.Vector.Algebra

public import Init.Data.Vector.Algebra
public import LatticeCrypto.Ring.Kernel

/-!
# Vector Backend For Negacyclic Rings

Canonical instantiation of the generic ring layer using `Vector Coeff n` as the
polynomial carrier. Provides:

- `Poly`: a non-reducible `def` wrapping `Vector Coeff n`.
- `vectorBackend`: a `PolyBackend` backed by `Vector`.
- `vectorKernel`: a `PolyKernel` that bridges `Vector` to `Array`.
- `vectorNegacyclicRing`: the bundled `NegacyclicRing` with pointwise
  add/sub/neg and `schoolbookNegacyclicMul`.
- `vectorNegacyclicSemantics`: the `noncomputable` proof bridge to the
  quotient ring `R[X] / (X^n + 1)`.

All three scheme `Arithmetic.lean` modules (`MLDSA`, `MLKEM`, `Falcon`)
instantiate their coefficient-domain rings through `vectorNegacyclicRing`.
-/

@[expose] public section


universe u

namespace LatticeCrypto

/-- A degree-`n` polynomial represented by a coefficient vector.
Defined as a `def` (not `abbrev`) so that `CommRing (Poly Coeff n)` remains a
separate instance from any elementwise `CommRing (Vector Coeff n)`, preventing
simp loops that would arise from the `CommRing` instance referencing back through
`vectorNegacyclicSemantics`. -/
def Poly (Coeff : Type u) (n : Nat) := Vector Coeff n

namespace Poly

variable {Coeff : Type u} {n : Nat}

/-- View a vector-backed polynomial as a `Fin n → Coeff` function. -/
def toPi (p : Poly Coeff n) : Fin n → Coeff :=
  fun i => p.get i

/-- Build a vector-backed polynomial from a `Fin n → Coeff` function. -/
def ofPi (f : Fin n → Coeff) : Poly Coeff n :=
  Vector.ofFn f

@[simp] theorem get_ofPi (f : Fin n → Coeff) (i : Fin n) :
    (ofPi f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

/-- `Vector.get` after `Vector.ofFn`, stated at the concrete carrier boundary.
Lean's core `ofFn` API is phrased using `GetElem`; this bridge keeps proof casts
out of users of the polynomial representation. -/
theorem get_vectorOfFn (f : Fin n → Coeff) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

@[simp] theorem toPi_ofPi (f : Fin n → Coeff) :
    toPi (ofPi f) = f := by
  funext i
  exact get_ofPi f i

/-- Pointwise extensionality for `Poly`: two vector-backed polynomials with
equal `Fin`-indexed entries are equal. Bridges core `Vector.ext` (stated in
terms of `[i]`) into the `.get` style used throughout the lattice layer. -/
theorem ext_get_eq {p q : Poly Coeff n}
    (h : ∀ i : Fin n, p.get i = q.get i) : p = q :=
  Vector.ext fun i hi => h ⟨i, hi⟩

@[simp] theorem ofPi_toPi (p : Poly Coeff n) :
    ofPi (toPi p) = p :=
  ext_get_eq fun i => get_ofPi (toPi p) i

/-- Reading a pointwise combination reads the corresponding entries. This is the
`Fin`-indexed boundary lemma used by the concrete ring operations. -/
@[simp] theorem get_zipWith (f : Coeff → Coeff → Coeff) (p q : Poly Coeff n)
    (i : Fin n) : (Vector.zipWith f p q).get i = f (p.get i) (q.get i) := by
  exact Vector.getElem_zipWith (f := f) (as := (show Vector Coeff n from p))
    (bs := (show Vector Coeff n from q)) i.isLt

/-- Reading a mapped polynomial reads and maps the corresponding entry. -/
@[simp] theorem get_map (f : Coeff → Coeff) (p : Poly Coeff n) (i : Fin n) :
    (Vector.map f p).get i = f (p.get i) := by
  exact Vector.getElem_map (xs := (show Vector Coeff n from p)) f i.isLt

end Poly

/-! ### Forwarding instances for `Poly`

These bridge the gap between `def Poly = Vector Coeff n` and Lean's instance
synthesis, which cannot automatically inherit `Vector` instances when `Poly` is
a non-reducible `def`.  All arithmetic instances (Zero, Add, Sub, Neg,
AddCommGroup) are given priority 1100 so they beat `CommRing`-derived defaults
(priority 1000), ensuring that `(0 : Poly Coeff n)` unfolds to `(0 : Vector
Coeff n)` rather than going through `vectorNegacyclicSemantics` and creating
simp loops. -/

variable {Coeff : Type u} {n : Nat}

instance (priority := 1100) [Zero Coeff] : Zero (Poly Coeff n) :=
  inferInstanceAs (Zero (Vector Coeff n))
instance (priority := 1100) [Add Coeff] : Add (Poly Coeff n) :=
  inferInstanceAs (Add (Vector Coeff n))
instance (priority := 1100) [Sub Coeff] : Sub (Poly Coeff n) :=
  inferInstanceAs (Sub (Vector Coeff n))
instance (priority := 1100) [Neg Coeff] : Neg (Poly Coeff n) :=
  inferInstanceAs (Neg (Vector Coeff n))
instance : GetElem (Poly Coeff n) Nat Coeff (fun _ i => i < n) :=
  inferInstanceAs (GetElem (Vector Coeff n) Nat Coeff (fun _ i => i < n))
instance [DecidableEq Coeff] : DecidableEq (Poly Coeff n) :=
  inferInstanceAs (DecidableEq (Vector Coeff n))
instance [Inhabited Coeff] : Inhabited (Poly Coeff n) :=
  inferInstanceAs (Inhabited (Vector Coeff n))
instance [Repr Coeff] : Repr (Poly Coeff n) :=
  inferInstanceAs (Repr (Vector Coeff n))

@[simp] theorem Poly.get_add [Add Coeff] (f g : Poly Coeff n) (i : Fin n) :
    (f + g).get i = f.get i + g.get i := by
  exact Vector.getElem_add f g i.val i.isLt

@[simp] theorem Poly.get_sub [Sub Coeff] (f g : Poly Coeff n) (i : Fin n) :
    (f - g).get i = f.get i - g.get i := by
  exact Vector.getElem_sub f g i.val i.isLt

/-- The canonical vector-backed semantic backend. Its carrier projection is used in
dependent types throughout the lattice layer, so that projection remains available
to implicit elaboration while the backend operations stay behind named laws. -/
abbrev vectorBackend (Coeff : Type u) (n : Nat) : PolyBackend Coeff where
  Poly := Poly Coeff n
  degree := n
  coeff := fun p i => p.get i
  build := Vector.ofFn
  coeff_build := by
    intro f i
    exact Poly.get_ofPi f i
  build_coeff := by
    intro p
    exact Poly.ofPi_toPi p

/-- The canonical vector/array executable kernel. -/
def vectorKernel (Coeff : Type u) [Zero Coeff] (n : Nat) :
    PolyKernel Coeff (vectorBackend Coeff n) where
  toArray := Vector.toArray
  ofArray := fun a => Vector.ofFn fun i => a.getD i.val 0
  toArray_size := by
    intro p
    exact p.size_toArray
  coeff_ofArray := by
    simp only [vectorBackend]
    intro a h i
    have hi : i.val < a.size := Nat.lt_of_lt_of_eq i.isLt h.symm
    rw [Poly.get_vectorOfFn]
    simp [hi]
  ofArray_toArray := by
    simp only [vectorBackend]
    intro p
    exact Poly.ext_get_eq fun i => by
      rw [Poly.get_vectorOfFn]
      have hi : i.val < ((p : Vector Coeff n)).toArray.size := by
        exact Nat.lt_of_lt_of_eq i.isLt
          (Vector.size_toArray (show Vector Coeff n from p)).symm
      rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?]
      split
      · exact Vector.getElem_toArray (xs := (show Vector Coeff n from p))
          hi
      · rename_i h
        exact (h hi).elim

/-- The canonical bundled negacyclic ring over the vector backend. Its carrier and degree
projections occur in dependent client types, so they remain available to implicit elaboration. -/
@[implicit_reducible] def vectorNegacyclicRing (Coeff : Type u) [CommRing Coeff] (n : Nat) :
    NegacyclicRing Coeff where
  backend := vectorBackend Coeff n
  kernel := vectorKernel Coeff n
  zero := (0 : Poly Coeff n)
  one  := Vector.ofFn fun i : Fin n => if i.val = 0 then 1 else 0
  add := Vector.zipWith (· + ·)
  sub := Vector.zipWith (· - ·)
  neg := Vector.map Neg.neg
  mul := negacyclicMulPure (vectorKernel Coeff n)
  add_coeff f g i := Poly.get_zipWith (· + ·) f g i
  sub_coeff f g i := Poly.get_zipWith (· - ·) f g i
  neg_coeff f i   := Poly.get_map Neg.neg f i
  zero_coeff i    := by
    change (0 : Vector Coeff n)[i.val] = 0
    exact Vector.getElem_zero i.val i.isLt

section VectorRingSimp

variable {Coeff : Type u} [CommRing Coeff] {n : Nat}

abbrev vRing (Coeff : Type u) [CommRing Coeff] (n : Nat) :=
  vectorNegacyclicRing Coeff n

omit [CommRing Coeff] in
@[simp] theorem vectorBackend_coeff (p : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff p i = p.get i := rfl

omit [CommRing Coeff] in
@[simp] theorem Poly.get_zero [Zero Coeff] (i : Fin n) : (0 : Poly Coeff n).get i = 0 := by
  change (0 : Vector Coeff n)[i.val] = 0
  exact Vector.getElem_zero i.val i.isLt

@[simp] theorem vectorRing_zero :
    (vectorNegacyclicRing Coeff n).zero = (0 : Poly Coeff n) := rfl

theorem vectorRing_zero_get (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).zero).get i = (0 : Coeff) := by
  exact Poly.get_zero i

@[simp] theorem vectorRing_one_get (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).one).get i = if i.val = 0 then 1 else 0 := by
  exact Poly.get_vectorOfFn (fun i : Fin n => if i.val = 0 then 1 else 0) i

@[simp] theorem vectorNegacyclicRing_mul :
    (vectorNegacyclicRing Coeff n).mul = negacyclicMulPure (vectorKernel Coeff n) := rfl

@[simp] theorem vectorNegacyclicRing_backend :
    (vectorNegacyclicRing Coeff n).backend = vectorBackend Coeff n := rfl

@[simp] theorem vectorRing_mul_apply (f g : (vectorNegacyclicRing Coeff n).Poly) :
    f * g = negacyclicMulPure (vectorKernel Coeff n) f g := rfl

/-- Concrete `Vector.get` form of the pure negacyclic multiplication law. -/
@[simp] theorem vectorKernel_mul_get (f g : Poly Coeff n) (i : Fin n) :
    (negacyclicMulPure (vectorKernel Coeff n) f g).get i =
      negacyclicConvCoeff f.get g.get i := by
  exact negacyclicMulPure_coeff (vectorKernel Coeff n) f g i

/-- Coefficient of a sum through the concrete vector backend (`Vector.instAdd`).
Paired with `vectorNegacyclicRing_backend` so that both variants of `+` on
`Poly Coeff n` are handled after the backend is normalised. -/
theorem vectorBackend_add_coeff (f g : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff (f + g) i =
      (vectorBackend Coeff n).coeff f i + (vectorBackend Coeff n).coeff g i := by
  exact Poly.get_add f g i

/-- Coefficient of a ring-`+` sum through the vector backend, where `+` comes from
`NegacyclicRing.instAddPoly`. Fires in downstream files where the carrier is spelled
as `(vectorNegacyclicRing ...).Poly` rather than `Poly Coeff n`. -/
@[simp] theorem vectorBackend_ring_add_coeff (f g : (vectorNegacyclicRing Coeff n).Poly)
    (i : Fin n) :
    (vectorBackend Coeff n).coeff (f + g) i =
      (vectorBackend Coeff n).coeff f i + (vectorBackend Coeff n).coeff g i :=
  NegacyclicRing.coeff_add (vectorNegacyclicRing Coeff n) f g i

theorem vectorRing_mul_add_right (f g h : Poly Coeff n) :
    (vRing Coeff n).mul f (g + h) = (vRing Coeff n).mul f g + (vRing Coeff n).mul f h := by
  apply Poly.ext_get_eq
  intro k
  change (negacyclicMulPure (vectorKernel Coeff n) f (g + h)).get k =
    (negacyclicMulPure (vectorKernel Coeff n) f g +
      negacyclicMulPure (vectorKernel Coeff n) f h).get k
  simp only [vectorKernel_mul_get, Poly.get_add, negacyclicConvCoeff]
  rw [← Finset.sum_add_distrib]; congr 1; ext ij
  split_ifs <;> ring

theorem vectorBackend_sub_coeff (f g : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff (f - g) i =
      (vectorBackend Coeff n).coeff f i - (vectorBackend Coeff n).coeff g i := by
  exact Poly.get_sub f g i

theorem vectorRing_mul_sub_right (f g h : Poly Coeff n) :
    (vRing Coeff n).mul f (g - h) = (vRing Coeff n).mul f g - (vRing Coeff n).mul f h := by
  apply Poly.ext_get_eq
  intro k
  change (negacyclicMulPure (vectorKernel Coeff n) f (g - h)).get k =
    (negacyclicMulPure (vectorKernel Coeff n) f g -
      negacyclicMulPure (vectorKernel Coeff n) f h).get k
  simp only [vectorKernel_mul_get, Poly.get_sub, negacyclicConvCoeff]
  rw [← Finset.sum_sub_distrib]; congr 1; ext ij
  split_ifs <;> ring

theorem vectorRing_mul_comm (f g : Poly Coeff n) :
    (vRing Coeff n).mul f g = (vRing Coeff n).mul g f := by
  apply Poly.ext_get_eq
  intro k
  change (negacyclicMulPure (vectorKernel Coeff n) f g).get k =
    (negacyclicMulPure (vectorKernel Coeff n) g f).get k
  simp only [vectorKernel_mul_get, negacyclicConvCoeff]
  let bn := vectorBackend Coeff n
  let n' := bn.degree
  let ff := fun (a b : Fin n') (f g: Poly Coeff n) => if (a.val + b.val) % n = k.val then
      if a.val + b.val < n then bn.coeff f a * bn.coeff g b
      else -(bn.coeff f a * bn.coeff g b)
    else 0
  calc ∑ ⟨a, b⟩ : Fin n' × Fin n', ff a b f g
  _ =  ∑ ⟨a, b⟩ : Fin n' × Fin n', ff b a f g := by
    exact Finset.sum_equiv (Equiv.prodComm (Fin n') (Fin n')) (by simp) (fun ij _ => rfl)
  _ =  ∑ ⟨a, b⟩ : Fin n' × Fin n', ff a b g f := by
    unfold ff
    congr 1; ext ⟨a, b⟩
    simp only [Nat.add_comm b a]
    split_ifs  <;> ring

@[simp] theorem vectorRing_add_get (f g : Poly Coeff n) (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).add f g).get i = f.get i + g.get i := by
  exact Poly.get_zipWith (· + ·) f g i

@[simp] theorem vectorRing_sub_get (f g : Poly Coeff n) (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).sub f g).get i = f.get i - g.get i := by
  exact Poly.get_zipWith (· - ·) f g i

@[simp] theorem vectorRing_neg_get (f : Poly Coeff n) (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).neg f).get i = -f.get i := by
  exact Poly.get_map Neg.neg f i

omit [CommRing Coeff] in
/-- Coefficient-wise negation lemma for abstract `Poly` (not tied to a specific ring). -/
@[simp] theorem Poly.get_neg [Neg Coeff] (f : Poly Coeff n) (i : Fin n) :
    (-f).get i = -f.get i := by
  change (-(f : Vector Coeff n))[i.val] = -((f : Vector Coeff n))[i.val]
  exact Vector.getElem_neg f i.val i.isLt

end VectorRingSimp

end LatticeCrypto
