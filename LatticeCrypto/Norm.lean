/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Polynomial Norms for Lattice Cryptography

This file defines the centered infinity norm (`cInfNorm`) and ℓ₁ norm (`l1Norm`) for polynomials
and polynomial vectors over `ZMod q`. These norms are central to the security analysis of
lattice-based schemes such as ML-DSA (FIPS 204) and ML-KEM (FIPS 203).

The centered representative maps `x : ZMod q` to the integer in `[-(q-1)/2, (q-1)/2]`
congruent to `x` mod `q`, and the norms are defined in terms of absolute values of these
centered coefficients.

## References

- NIST FIPS 204, Section 2.3 (norms and rounding)
- EasyCrypt `DRing.eca` (abstract `cnorm` and `l1_norm` axioms)
-/

set_option autoImplicit false

namespace LatticeCrypto

section CenteredRepr

variable {q : ℕ} [NeZero q]

/-- The centered representative of `x : ZMod q`, mapping to the unique integer in
`[-(q-1)/2, (q-1)/2]` (or `[-⌊q/2⌋ + 1, ⌈q/2⌉]` for even `q`) congruent to `x` mod `q`. -/
def centeredRepr (x : ZMod q) : ℤ :=
  if (x.val : ℤ) ≤ (q : ℤ) / 2 then (x.val : ℤ) else (x.val : ℤ) - q

omit [NeZero q] in
@[simp]
theorem centeredRepr_of_le {x : ZMod q} (h : (x.val : ℤ) ≤ (q : ℤ) / 2) :
    centeredRepr x = x.val := by
  unfold centeredRepr; exact if_pos h

omit [NeZero q] in
@[simp]
theorem centeredRepr_of_gt {x : ZMod q} (h : (q : ℤ) / 2 < (x.val : ℤ)) :
    centeredRepr x = (x.val : ℤ) - q := by
  unfold centeredRepr; exact if_neg (not_le.mpr h)

/-- The centered representative is always at most `q / 2`. -/
theorem centeredRepr_upper_bound (x : ZMod q) : centeredRepr x ≤ (q : ℤ) / 2 := by
  simp only [centeredRepr]
  split_ifs with h
  · exact h
  · push_neg at h; have hval := ZMod.val_lt x; omega

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
  · haveI : NeZero x := ⟨hx⟩
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

end CenteredRepr

section PolyNorm

variable {q : ℕ} [NeZero q] {n : ℕ}

/-- The centered infinity norm of a polynomial: the maximum absolute value of the centered
representatives of its coefficients. Returns `0` for the zero polynomial or when `n = 0`. -/
def cInfNorm (p : Poly (ZMod q) n) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin n => (centeredRepr (p.get i)).natAbs)

/-- The ℓ₁ norm of a polynomial: the sum of absolute values of the centered representatives
of its coefficients. -/
def l1Norm (p : Poly (ZMod q) n) : ℕ :=
  ∑ i : Fin n, (centeredRepr (p.get i)).natAbs

omit [NeZero q] in
theorem cInfNorm_le_iff {p : Poly (ZMod q) n} {b : ℕ} :
    cInfNorm p ≤ b ↔ ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b := by
  simp [cInfNorm, Finset.sup_le_iff]

omit [NeZero q] in
theorem cInfNorm_le_of_coeff_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b) : cInfNorm p ≤ b :=
  cInfNorm_le_iff.mpr h

omit [NeZero q] in
theorem coeff_le_cInfNorm (p : Poly (ZMod q) n) (i : Fin n) :
    (centeredRepr (p.get i)).natAbs ≤ cInfNorm p := by
  exact Finset.le_sup (f := fun i => (centeredRepr (p.get i)).natAbs) (Finset.mem_univ i)

/-- Every polynomial has centered infinity norm at most `q / 2`. -/
theorem cInfNorm_le_halfq (p : Poly (ZMod q) n) : cInfNorm p ≤ q / 2 :=
  cInfNorm_le_iff.mpr (fun i => centeredRepr_abs_le (p.get i))

/-- Negation preserves the centered infinity norm. -/
@[simp]
theorem cInfNorm_neg (f : Poly (ZMod q) n) : cInfNorm (-f) = cInfNorm f := by
  simp only [cInfNorm]
  congr 1; ext i
  have : (-f).get i = -(f.get i) := Vector.getElem_map (- ·) i.isLt
  rw [this, centeredRepr_natAbs_neg]

omit [NeZero q] in
theorem l1Norm_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l1Norm p ≤ n * b := by
  unfold l1Norm
  calc ∑ i : Fin n, (centeredRepr (p.get i)).natAbs
      ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => (cInfNorm_le_iff.mp h) i
    _ = n * b := by simp [Finset.sum_const]

end PolyNorm

section PolyVecNorm

variable {q : ℕ} [NeZero q] {n k : ℕ}

/-- The centered infinity norm of a polynomial vector: the maximum `cInfNorm` across
all component polynomials. -/
def PolyVec.cInfNorm (v : PolyVec (ZMod q) n k) : ℕ :=
  Finset.sup Finset.univ (fun j : Fin k => LatticeCrypto.cInfNorm (v.get j))

/-- The ℓ₁ norm of a polynomial vector: the maximum `l1Norm` across all component polynomials.
This follows the convention where the ℓ₁ norm of a module element is the max over its ring
components, as used in lattice-based cryptography. -/
def PolyVec.l1Norm (v : PolyVec (ZMod q) n k) : ℕ :=
  Finset.sup Finset.univ (fun j : Fin k => LatticeCrypto.l1Norm (v.get j))

omit [NeZero q] in
theorem PolyVec.cInfNorm_le_iff {v : PolyVec (ZMod q) n k} {b : ℕ} :
    PolyVec.cInfNorm v ≤ b ↔ ∀ j : Fin k, LatticeCrypto.cInfNorm (v.get j) ≤ b := by
  simp [PolyVec.cInfNorm, Finset.sup_le_iff]

omit [NeZero q] in
theorem PolyVec.component_cInfNorm_le (v : PolyVec (ZMod q) n k) (j : Fin k) :
    LatticeCrypto.cInfNorm (v.get j) ≤ PolyVec.cInfNorm v :=
  Finset.le_sup (f := fun j => LatticeCrypto.cInfNorm (v.get j)) (Finset.mem_univ j)

end PolyVecNorm

/-! ## Squared ℓ₂ Norm

The squared ℓ₂ norm is used by Falcon (FIPS 206 / FN-DSA) for signature verification:
a signature `(s₁, s₂)` is accepted iff `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`. We define the squared
norm to avoid square roots in the formalization. -/

section L2Norm

variable {q : ℕ} [NeZero q] {n : ℕ}

/-- The squared ℓ₂ norm of a polynomial: the sum of squares of the centered representatives
of its coefficients. -/
def l2NormSq (p : Poly (ZMod q) n) : ℕ :=
  ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2

/-- The squared ℓ₂ norm of a pair of polynomials: the sum of their individual squared norms.
Used by Falcon to check `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`. -/
def pairL2NormSq (p₁ p₂ : Poly (ZMod q) n) : ℕ :=
  l2NormSq p₁ + l2NormSq p₂

omit [NeZero q] in
theorem l2NormSq_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l2NormSq p ≤ n * b ^ 2 := by
  unfold l2NormSq
  calc ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2
      ≤ ∑ _i : Fin n, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (cInfNorm_le_iff.mp h i) 2
    _ = n * b ^ 2 := by simp [Finset.sum_const]

end L2Norm

section PolyVecL2Norm

variable {q : ℕ} [NeZero q] {n k : ℕ}

/-- The squared ℓ₂ norm of a polynomial vector: the sum of `l2NormSq` across all components. -/
def PolyVec.l2NormSq (v : PolyVec (ZMod q) n k) : ℕ :=
  ∑ j : Fin k, LatticeCrypto.l2NormSq (v.get j)

end PolyVecL2Norm

end LatticeCrypto
