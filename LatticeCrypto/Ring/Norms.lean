/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Ring.VectorBackend
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Norms For Negacyclic Ring Backends

Backend-generic norm infrastructure for the lattice ring layer. Defines:

- `CenteredCoeffView`: an integer-valued centered representative map for
  coefficients, used to define norms generically over any backend.
- `NormOps`: a norm bundle (`cInfNorm`, `l1Norm`, `l2NormSq`) parameterized
  by a `PolyBackend`, with a `pairL2NormSq` helper for Falcon-style signature
  norm bounds.
- `centeredRepr` and associated lemmas: the canonical centered representative
  for `ZMod q`, mapping each element to `[-(q-1)/2, (q-1)/2]`.
- Generic norm constructors (`cInfNormOf`, `l1NormOf`, `l2NormSqOf`) and their
  specialized vector-backend versions (`cInfNorm`, `l1Norm`, `l2NormSq`).
- `PolyVec` norm lifts and `zmodPolyNormOps`.

`MLDSA.Arithmetic` and `Falcon.Arithmetic` assemble scheme-local norm aliases
from `zmodPolyNormOps`.
-/

@[expose] public section



namespace LatticeCrypto

/-- A centered integer view of coefficients.

Maps each coefficient to a representative integer, enabling backend-generic
norm definitions. The canonical instance for `ZMod q` is `zmodCenteredCoeffView`,
which uses `centeredRepr`. -/
structure CenteredCoeffView (Coeff : Type*) where
  repr : Coeff → ℤ

/-- Norm bundle layered over a `PolyBackend`.

Bundles the three standard polynomial norms used across ML-DSA and Falcon:
centered `ℓ∞`, `ℓ₁`, and squared `ℓ₂`. Constructed generically via
`normOpsOfCenteredView`, or directly via `zmodPolyNormOps` for `ZMod q`
coefficients. -/
structure NormOps {Coeff : Type*} (backend : PolyBackend Coeff) where
  cInfNorm : backend.Poly → ℕ
  l1Norm : backend.Poly → ℕ
  l2NormSq : backend.Poly → ℕ

namespace NormOps

variable {Coeff : Type*} {backend : PolyBackend Coeff}

/-- The squared `ℓ₂` norm of a pair of polynomials. -/
def pairL2NormSq (ops : NormOps backend) (p₁ p₂ : backend.Poly) : ℕ :=
  ops.l2NormSq p₁ + ops.l2NormSq p₂

end NormOps

section CenteredRepr

variable {q : ℕ} [NeZero q]

/-- The centered representative of `x : ZMod q`, mapping to the unique integer in
`[-(q-1)/2, (q-1)/2]` congruent to `x` mod `q`. -/
def centeredRepr (x : ZMod q) : ℤ :=
  if (x.val : ℤ) ≤ (q : ℤ) / 2 then (x.val : ℤ) else (x.val : ℤ) - q

omit [NeZero q] in
@[simp] theorem centeredRepr_of_le {x : ZMod q} (h : (x.val : ℤ) ≤ (q : ℤ) / 2) :
    centeredRepr x = x.val := by
  unfold centeredRepr
  exact if_pos h

omit [NeZero q] in
@[simp] theorem centeredRepr_of_gt {x : ZMod q} (h : (q : ℤ) / 2 < (x.val : ℤ)) :
    centeredRepr x = (x.val : ℤ) - q := by
  unfold centeredRepr
  exact if_neg (not_le.mpr h)

/-- The centered representative is always at most `q / 2`. -/
theorem centeredRepr_upper_bound (x : ZMod q) : centeredRepr x ≤ (q : ℤ) / 2 := by
  simp only [centeredRepr]
  split_ifs with h
  · exact h
  · push Not at h
    have hval := ZMod.val_lt x
    omega

/-- The centered representative has absolute value at most `q / 2`. -/
theorem centeredRepr_abs_le (x : ZMod q) : (centeredRepr x).natAbs ≤ q / 2 := by
  simp only [centeredRepr]
  have hval := ZMod.val_lt x
  split_ifs with h <;> omega

/-- Negation preserves the absolute value of the centered representative. -/
theorem centeredRepr_natAbs_neg (x : ZMod q) :
    (centeredRepr (-x)).natAbs = (centeredRepr x).natAbs := by
  by_cases hx : x = 0
  · simp [hx]
  · have : NeZero x := ⟨hx⟩
    simp only [centeredRepr, ZMod.val_neg_of_ne_zero]
    have hval := ZMod.val_lt x
    have hpos : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx)
    split_ifs <;> omega

/-- Casting the centered representative back into `ZMod q` recovers the original element. -/
theorem centeredRepr_intCast (x : ZMod q) :
    (x : ZMod q) = ((centeredRepr x : ℤ) : ZMod q) := by
  by_cases h : (x.val : ℤ) ≤ (q : ℤ) / 2
  · rw [centeredRepr_of_le h, Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hgt : (q : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [centeredRepr_of_gt hgt, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self]
    simp

/-- Twice the centered representative lies in the interval used by `ZMod.valMinAbs`. -/
theorem centeredRepr_mem_Ioc (x : ZMod q) :
    centeredRepr x * 2 ∈ Set.Ioc (-(q : ℤ)) q := by
  by_cases h : (x.val : ℤ) ≤ (q : ℤ) / 2
  · rw [centeredRepr_of_le h]
    have hx : 0 ≤ (x.val : ℤ) := by positivity
    have hmod : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
    constructor <;> omega
  · have hgt : (q : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [centeredRepr_of_gt hgt]
    have hval := ZMod.val_lt x
    constructor <;> omega

/-- The centered representative agrees with `ZMod.valMinAbs`. -/
theorem centeredRepr_eq_valMinAbs (x : ZMod q) :
    centeredRepr x = x.valMinAbs := by
  simpa using ((ZMod.valMinAbs_spec x (centeredRepr x)).2
    ⟨centeredRepr_intCast x, centeredRepr_mem_Ioc x⟩).symm

/-- Casting an integer already in the centered interval preserves that integer. -/
theorem centeredRepr_intCast_eq (z : ℤ)
    (hzlo : -(q : ℤ) < z * 2) (hzhi : z * 2 ≤ q) :
    centeredRepr ((z : ZMod q)) = z := by
  rw [centeredRepr_eq_valMinAbs]
  exact (ZMod.valMinAbs_spec ((z : ZMod q)) z).2 ⟨rfl, ⟨hzlo, hzhi⟩⟩

/-- A small-enough integer is unchanged by casting into `ZMod q` and taking `centeredRepr`. -/
theorem centeredRepr_intCast_eq_of_natAbs_le (z : ℤ) {b : ℕ}
    (hbound : z.natAbs ≤ b) (hbq : 2 * b < q) :
    centeredRepr ((z : ZMod q)) = z := by
  apply centeredRepr_intCast_eq
  · have : -(b : ℤ) ≤ z := by omega
    omega
  · have : z ≤ b := by omega
    omega

/-- A `natAbs` bound yields both lower and upper integer bounds. -/
theorem neg_le_and_le_of_natAbs_le {z : ℤ} {b : ℕ}
    (hbound : z.natAbs ≤ b) : -(b : ℤ) ≤ z ∧ z ≤ b := by
  constructor <;> omega

/-- Lower and upper integer bounds yield a `natAbs` bound. Inverse of
`neg_le_and_le_of_natAbs_le`. -/
theorem natAbs_le_of_neg_le_and_le {z : ℤ} {b : ℕ}
    (hl : -(b : ℤ) ≤ z) (hu : z ≤ b) : z.natAbs ≤ b := by
  omega

/-- The canonical centered coefficient view for `ZMod q`. -/
def zmodCenteredCoeffView (q : ℕ) [NeZero q] : CenteredCoeffView (ZMod q) where
  repr := centeredRepr

end CenteredRepr

section GenericNorms

variable {Coeff : Type*} (backend : PolyBackend Coeff) (view : CenteredCoeffView Coeff)

/-- Backend-generic centered infinity norm. -/
def cInfNormOf (p : backend.Poly) : ℕ :=
  Finset.sup Finset.univ fun i : Fin backend.degree => (view.repr (backend.coeff p i)).natAbs

/-- Backend-generic `ℓ₁` norm. -/
def l1NormOf (p : backend.Poly) : ℕ :=
  ∑ i : Fin backend.degree, (view.repr (backend.coeff p i)).natAbs

/-- Backend-generic squared `ℓ₂` norm. -/
def l2NormSqOf (p : backend.Poly) : ℕ :=
  ∑ i : Fin backend.degree, (view.repr (backend.coeff p i)).natAbs ^ 2

/-- Construct a generic norm bundle from a centered coefficient view. -/
def normOpsOfCenteredView : NormOps backend where
  cInfNorm := cInfNormOf backend view
  l1Norm := l1NormOf backend view
  l2NormSq := l2NormSqOf backend view

end GenericNorms

section SpecializedVectorNorms

variable {q : ℕ} [NeZero q] {n : Nat}

/-- The centered infinity norm on the canonical vector backend. -/
def cInfNorm (p : Poly (ZMod q) n) : ℕ :=
  cInfNormOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The `ℓ₁` norm on the canonical vector backend. -/
def l1Norm (p : Poly (ZMod q) n) : ℕ :=
  l1NormOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The squared `ℓ₂` norm on the canonical vector backend. -/
def l2NormSq (p : Poly (ZMod q) n) : ℕ :=
  l2NormSqOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The squared `ℓ₂` norm of a pair of vector-backed polynomials. -/
def pairL2NormSq (p₁ p₂ : Poly (ZMod q) n) : ℕ :=
  l2NormSq p₁ + l2NormSq p₂

theorem cInfNorm_le_iff {p : Poly (ZMod q) n} {b : ℕ} :
    cInfNorm p ≤ b ↔ ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b := by
  simp [cInfNorm, cInfNormOf, vectorBackend, zmodCenteredCoeffView, Finset.sup_le_iff]

theorem cInfNorm_le_of_coeff_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b) : cInfNorm p ≤ b :=
  cInfNorm_le_iff.mpr h

theorem coeff_le_cInfNorm (p : Poly (ZMod q) n) (i : Fin n) :
    (centeredRepr (p.get i)).natAbs ≤ cInfNorm p :=
  Finset.le_sup (f := fun i => (centeredRepr (p.get i)).natAbs) (Finset.mem_univ i)

/-- Every polynomial has centered infinity norm at most `q / 2`. -/
theorem cInfNorm_le_halfq (p : Poly (ZMod q) n) : cInfNorm p ≤ q / 2 :=
  cInfNorm_le_iff.mpr (fun i => centeredRepr_abs_le (p.get i))

/-- Negation preserves the centered infinity norm. -/
@[simp] theorem cInfNorm_neg (f : Poly (ZMod q) n) : cInfNorm (-f) = cInfNorm f := by
  simp only [cInfNorm, cInfNormOf, vectorBackend, zmodCenteredCoeffView]
  congr 1
  ext i
  have hneg : (-f).get i = -(f.get i) := Poly.get_neg f i
  rw [hneg, centeredRepr_natAbs_neg]

/-- The `ℓ₁` norm expands as the sum of the centered absolute values of the coefficients. -/
theorem l1Norm_eq_sum (p : Poly (ZMod q) n) :
    l1Norm p = ∑ i : Fin n, (centeredRepr (p.get i)).natAbs := by
  unfold l1Norm l1NormOf
  rfl

theorem l1Norm_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l1Norm p ≤ n * b := by
  unfold l1Norm l1NormOf
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs
      ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => (cInfNorm_le_iff.mp h) i
    _ = n * b := by simp [Finset.sum_const]

theorem l2NormSq_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l2NormSq p ≤ n * b ^ 2 := by
  unfold l2NormSq l2NormSqOf
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2
      ≤ ∑ _i : Fin n, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (cInfNorm_le_iff.mp h i) 2
    _ = n * b ^ 2 := by simp [Finset.sum_const]

/-! ### Negacyclic-convolution infinity-norm bound

The centered `ℓ∞` norm of a negacyclic product is bounded by the `ℓ₁` norm of one
factor times the `ℓ∞` norm of the other. Each output coefficient is an integer
negacyclic-convolution sum of at most `l1Norm f` terms, each of absolute value at
most `cInfNorm g`; the bound is unconditional via a case split on whether the
right-hand side already exceeds `q / 2`. This is the algebraic heart of the
ML-DSA `‖c · s‖∞ ≤ τ · η` challenge-product bound. -/

/-- The integer-domain negacyclic convolution of the centered-representative lifts of
`f` and `g` at output index `k`. Casting this integer back into `ZMod q` recovers
`negacyclicConvCoeff f g k`, and its absolute value is bounded by `l1Norm f * cInfNorm g`. -/
private def intConvCoeff (f g : Fin n → ZMod q) (k : Fin n) : ℤ :=
  ∑ ij : Fin n × Fin n,
    if (ij.1.val + ij.2.val) % n = k.val then
      if ij.1.val + ij.2.val < n then centeredRepr (f ij.1) * centeredRepr (g ij.2)
      else -(centeredRepr (f ij.1) * centeredRepr (g ij.2))
    else 0

/-- `negacyclicConvCoeff` is the `ZMod q` reduction of the integer convolution `intConvCoeff`
of the centered lifts. -/
private theorem negacyclicConvCoeff_eq_intCast (f g : Fin n → ZMod q) (k : Fin n) :
    negacyclicConvCoeff f g k = ((intConvCoeff f g k : ℤ) : ZMod q) := by
  rw [intConvCoeff, negacyclicConvCoeff, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro ij _
  by_cases h1 : (ij.1.val + ij.2.val) % n = k.val
  · by_cases h2 : ij.1.val + ij.2.val < n
    · simp only [h1, h2, if_true, Int.cast_mul]
      rw [← centeredRepr_intCast (f ij.1), ← centeredRepr_intCast (g ij.2)]
    · simp only [h1, h2, if_true, if_false, Int.cast_neg, Int.cast_mul]
      rw [← centeredRepr_intCast (f ij.1), ← centeredRepr_intCast (g ij.2)]
  · simp [h1]

omit [NeZero q] in
/-- The integer negacyclic convolution at any output index is bounded in absolute value by
`(∑ |centeredRepr (f i)|) * bg`, where `bg` bounds every `|centeredRepr (g j)|`. The negacyclic
wrap index `(i + j) % n = k` matches at most one `j` per `i`, removing the spurious factor `n`. -/
private theorem intConvCoeff_natAbs_le (f g : Fin n → ZMod q) (k : Fin n) (bg : ℕ)
    (hg : ∀ j, (centeredRepr (g j)).natAbs ≤ bg) :
    (intConvCoeff f g k).natAbs ≤ (∑ i : Fin n, (centeredRepr (f i)).natAbs) * bg := by
  refine (Int.natAbs_sum_le _ _).trans ?_
  have hterm : ∀ ij : Fin n × Fin n,
      (if (ij.1.val + ij.2.val) % n = k.val then
        if ij.1.val + ij.2.val < n then centeredRepr (f ij.1) * centeredRepr (g ij.2)
        else -(centeredRepr (f ij.1) * centeredRepr (g ij.2))
      else 0).natAbs ≤
      (if (ij.1.val + ij.2.val) % n = k.val then (centeredRepr (f ij.1)).natAbs * bg else 0) := by
    intro ij
    split_ifs with h1 h2
    · rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (hg ij.2)
    · rw [Int.natAbs_neg, Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (hg ij.2)
    · simp
  refine (Finset.sum_le_sum (fun ij _ => hterm ij)).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only []
  rw [← Finset.sum_filter]
  have hcard : (Finset.univ.filter (fun j : Fin n => (i.val + j.val) % n = k.val)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hmod : (i.val + a.val) % n = (i.val + b.val) % n := by rw [ha, hb]
    have hab : a.val % n = b.val % n := by
      have := Nat.ModEq.add_left_cancel' i.val (show Nat.ModEq n _ _ from hmod)
      simpa [Nat.ModEq] using this
    exact Fin.ext (by rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hab)
  refine (Finset.sum_le_card_nsmul _ _ ((centeredRepr (f i)).natAbs * bg)
    (fun x _ => le_refl _)).trans ?_
  calc _ ≤ 1 • ((centeredRepr (f i)).natAbs * bg) := Nat.mul_le_mul_right _ hcard
    _ = (centeredRepr (f i)).natAbs * bg := one_smul _ _

omit [NeZero q] in
/-- The `k`-th coefficient of the negacyclic product equals the negacyclic convolution of the
component coefficient functions. -/
private theorem mul_get_eq_convCoeff (f g : (vectorNegacyclicRing (ZMod q) n).Poly) (i : Fin n) :
    (f * g).get i = negacyclicConvCoeff f.get g.get i := by
  rw [vectorRing_mul_apply]
  exact vectorKernel_mul_get f g i

/-- **Negacyclic-convolution infinity-norm bound.** For coefficient-domain polynomials in
`ℤ_q[X] / (X^n + 1)`, the centered `ℓ∞` norm of the product is bounded by the `ℓ₁` norm of the
first factor times the `ℓ∞` norm of the second. Unconditional: the no-wraparound argument applies
when `l1Norm f * cInfNorm g < q / 2`, and otherwise `cInfNorm_le_halfq` already gives the bound. -/
theorem cInfNorm_mul_le (f g : (vectorNegacyclicRing (ZMod q) n).Poly) :
    cInfNorm (f * g) ≤ l1Norm f * cInfNorm g := by
  set bound := l1Norm f * cInfNorm g with hbound
  rw [cInfNorm_le_iff]
  intro k
  have hZle : (intConvCoeff f.get g.get k).natAbs ≤ bound := by
    rw [hbound]
    refine (intConvCoeff_natAbs_le f.get g.get k (cInfNorm g) ?_).trans (le_refl _)
    intro j; exact coeff_le_cInfNorm g j
  rw [mul_get_eq_convCoeff, negacyclicConvCoeff_eq_intCast]
  by_cases hsmall : 2 * bound < q
  · rw [centeredRepr_intCast_eq_of_natAbs_le _ hZle hsmall]
    exact hZle
  · push Not at hsmall
    refine (centeredRepr_abs_le _).trans ?_
    omega

end SpecializedVectorNorms

namespace PolyVec

variable {Coeff : Type*} {backend : PolyBackend Coeff} (ops : NormOps backend) {k : Nat}

/-- The centered infinity norm of a polynomial vector. -/
def cInfNorm (v : PolyVec backend.Poly k) : ℕ :=
  Finset.sup Finset.univ fun j : Fin k => ops.cInfNorm (v.get j)

/-- A polynomial vector has centered infinity norm at most `b` exactly when each component
polynomial does. -/
theorem cInfNorm_le_iff {v : PolyVec backend.Poly k} {b : ℕ} :
    PolyVec.cInfNorm ops v ≤ b ↔ ∀ j : Fin k, ops.cInfNorm (v.get j) ≤ b := by
  simp [PolyVec.cInfNorm, Finset.sup_le_iff]

/-- Each component polynomial is bounded by the centered infinity norm of the whole vector. -/
theorem component_cInfNorm_le (v : PolyVec backend.Poly k) (j : Fin k) :
    ops.cInfNorm (v.get j) ≤ PolyVec.cInfNorm ops v :=
  Finset.le_sup (f := fun j => ops.cInfNorm (v.get j)) (Finset.mem_univ j)

/-- The `ℓ₁` norm of a polynomial vector. -/
def l1Norm (v : PolyVec backend.Poly k) : ℕ :=
  Finset.sup Finset.univ fun j : Fin k => ops.l1Norm (v.get j)

/-- The squared `ℓ₂` norm of a polynomial vector. -/
def l2NormSq (v : PolyVec backend.Poly k) : ℕ :=
  ∑ j : Fin k, ops.l2NormSq (v.get j)

end PolyVec

/-- The canonical backend-generic norm bundle for `ZMod q` coefficients. -/
def zmodPolyNormOps (q : ℕ) [NeZero q] (backend : PolyBackend (ZMod q)) : NormOps backend :=
  normOpsOfCenteredView backend (zmodCenteredCoeffView q)

/-- The canonical norm bundle specializes definitionally to the vector-backed centered
infinity norm. Keeping this bridge at the generic layer prevents clients from unfolding an
entire concrete ring bundle merely to expose the shared coefficient formula. -/
@[simp]
theorem zmodPolyNormOps_cInfNorm {q n : ℕ} [NeZero q] (p : Poly (ZMod q) n) :
    (zmodPolyNormOps q (vectorBackend (ZMod q) n)).cInfNorm p = cInfNorm p :=
  rfl

end LatticeCrypto
