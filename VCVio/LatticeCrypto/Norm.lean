/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.LatticeCrypto.Ring
import Mathlib.Data.ZMod.Basic

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
theorem centeredRepr_of_gt {x : ZMod q} (h : (q : ℤ) / 2 < (x.val : ℤ)) :
    centeredRepr x = (x.val : ℤ) - q := by
  unfold centeredRepr; exact if_neg (not_le.mpr h)

theorem centeredRepr_upper_bound (x : ZMod q) : centeredRepr x ≤ (q : ℤ) / 2 := by
  simp only [centeredRepr]
  split_ifs with h
  · exact h
  · push_neg at h; have hval := ZMod.val_lt x; omega

theorem centeredRepr_abs_le (x : ZMod q) : (centeredRepr x).natAbs ≤ q / 2 := by
  simp only [centeredRepr]
  have hval := ZMod.val_lt x
  split_ifs with h <;> omega

end CenteredRepr

section PolyNorm

variable {q : ℕ} [NeZero q] {n : ℕ}

/-- The centered infinity norm of a polynomial: the maximum absolute value of the centered
representatives of its coefficients. Returns `0` for the degree-0 polynomial. -/
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

theorem cInfNorm_le_halfq (p : Poly (ZMod q) n) : cInfNorm p ≤ q / 2 :=
  cInfNorm_le_iff.mpr (fun i => centeredRepr_abs_le (p.get i))

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

end LatticeCrypto
