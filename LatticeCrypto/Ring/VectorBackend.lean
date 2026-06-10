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

@[simp] theorem toPi_ofPi (f : Fin n → Coeff) :
    toPi (ofPi f) = f := by
  funext i
  simp [toPi, ofPi, Vector.get]

/-- Pointwise extensionality for `Poly`: two vector-backed polynomials with
equal `Fin`-indexed entries are equal. Bridges core `Vector.ext` (stated in
terms of `[i]`) into the `.get` style used throughout the lattice layer. -/
theorem ext_get_eq {p q : Poly Coeff n}
    (h : ∀ i : Fin n, p.get i = q.get i) : p = q :=
  Vector.ext fun i hi => h ⟨i, hi⟩

@[simp] theorem ofPi_toPi (p : Poly Coeff n) :
    ofPi (toPi p) = p :=
  ext_get_eq fun i => by simp [toPi, ofPi, Vector.get]

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
    exact Poly.ext_get_eq fun _ => by simp [Vector.get]

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
    have hi : i.val < a.size := Nat.lt_of_lt_of_eq i.isLt h.symm
    simp [vectorBackend, hi, Vector.get]
  ofArray_toArray := by
    intro p
    exact Poly.ext_get_eq fun _ => by simp

/-- The canonical bundled negacyclic ring over the vector backend. -/
def vectorNegacyclicRing (Coeff : Type u) [CommRing Coeff] (n : Nat) :
    NegacyclicRing Coeff where
  backend := vectorBackend Coeff n
  kernel := vectorKernel Coeff n
  zero := (0 : Poly Coeff n)
  one  := Vector.ofFn fun i : Fin n => if i.val = 0 then 1 else 0
  add := Vector.zipWith (· + ·)
  sub := Vector.zipWith (· - ·)
  neg := Vector.map Neg.neg
  mul := negacyclicMulPure (vectorKernel Coeff n)
  add_coeff f g i := by simp [vectorBackend, Vector.get]
  sub_coeff f g i := by simp [vectorBackend, Vector.get]
  neg_coeff f i   := by simp [vectorBackend, Vector.get]
  zero_coeff i    := by
    change (0 : Vector Coeff n).get i = 0
    simp [Vector.get]

section VectorRingSimp

variable {Coeff : Type u} [CommRing Coeff] {n : Nat}

private abbrev vRing (Coeff : Type u) [CommRing Coeff] (n : Nat) :=
  vectorNegacyclicRing Coeff n

omit [CommRing Coeff] in
@[simp] theorem vectorBackend_coeff (p : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff p i = p.get i := rfl

omit [CommRing Coeff] in
@[simp] theorem Poly.get_zero [Zero Coeff] (i : Fin n) : (0 : Poly Coeff n).get i = 0 := by
  change (0 : Vector Coeff n).get i = 0
  simp [Vector.get]

@[simp] theorem vectorRing_zero :
    (vectorNegacyclicRing Coeff n).zero = (0 : Poly Coeff n) := rfl

@[simp] theorem vectorRing_zero_get (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).zero).get i = (0 : Coeff) := by
  change (0 : Vector Coeff n).get i = 0
  simp [Vector.get]

@[simp] theorem vectorNegacyclicRing_mul :
    (vectorNegacyclicRing Coeff n).mul = negacyclicMulPure (vectorKernel Coeff n) := rfl

@[simp] theorem vectorNegacyclicRing_backend :
    (vectorNegacyclicRing Coeff n).backend = vectorBackend Coeff n := rfl

/-- Coefficient of a sum through the concrete vector backend (`Vector.instAdd`).
Paired with `vectorNegacyclicRing_backend` so that both variants of `+` on
`Poly Coeff n` are handled after the backend is normalised. -/
@[simp] theorem vectorBackend_add_coeff (f g : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff (f + g) i =
      (vectorBackend Coeff n).coeff f i + (vectorBackend Coeff n).coeff g i := by
  simp only [vectorBackend_coeff]
  exact Vector.getElem_add f g i.val i.isLt

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
  apply PolyBackend.ext_coeff; intro k
  -- Split the outer ring addition first, before vectorNegacyclicRing_backend fires.
  simp only [NegacyclicRing.coeff_add]
  simp only [vectorNegacyclicRing_mul, vectorNegacyclicRing_backend,
             vectorBackend_add_coeff, negacyclicMulPure_coeff, negacyclicConvCoeff]
  rw [← Finset.sum_add_distrib]; congr 1; ext ij
  split_ifs <;> ring

@[simp] theorem vectorBackend_sub_coeff (f g : Poly Coeff n) (i : Fin n) :
    (vectorBackend Coeff n).coeff (f - g) i =
      (vectorBackend Coeff n).coeff f i - (vectorBackend Coeff n).coeff g i := by
  simp only [vectorBackend_coeff]
  exact Vector.getElem_sub f g i.val i.isLt

theorem vectorRing_mul_sub_right (f g h : Poly Coeff n) :
    (vRing Coeff n).mul f (g - h) = (vRing Coeff n).mul f g - (vRing Coeff n).mul f h := by
  apply PolyBackend.ext_coeff; intro k
  simp only [NegacyclicRing.coeff_sub]
  simp only [vectorNegacyclicRing_mul, vectorNegacyclicRing_backend,
             vectorBackend_sub_coeff, negacyclicMulPure_coeff, negacyclicConvCoeff]
  rw [← Finset.sum_sub_distrib]; congr 1; ext ij
  split_ifs <;> ring

theorem vectorRing_mul_comm (f g : Poly Coeff n) :
    (vRing Coeff n).mul f g = (vRing Coeff n).mul g f := by
  apply PolyBackend.ext_coeff; intro k
  simp only [vectorNegacyclicRing_mul, vectorNegacyclicRing_backend,
             negacyclicMulPure_coeff, negacyclicConvCoeff]
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
  change (Vector.zipWith (· + ·) f g)[i] = f[i] + g[i]
  simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  rfl

@[simp] theorem vectorRing_sub_get (f g : Poly Coeff n) (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).sub f g).get i = f.get i - g.get i := by
  change (Vector.zipWith (· - ·) f g)[i] = f[i] - g[i]
  simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  rfl

@[simp] theorem vectorRing_neg_get (f : Poly Coeff n) (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).neg f).get i = -f.get i := by
  change (Vector.map Neg.neg f)[i] = Neg.neg f[i]
  simp [Fin.getElem_fin, Vector.getElem_map]
  rfl

omit [CommRing Coeff] in
/-- Coefficient-wise negation lemma for abstract `Poly` (not tied to a specific ring). -/
@[simp] theorem Poly.get_neg [Neg Coeff] (f : Poly Coeff n) (i : Fin n) :
    (-f).get i = -f.get i :=
  Vector.getElem_map (xs := (f : Vector Coeff n)) (- ·) i.isLt

end VectorRingSimp

end LatticeCrypto
