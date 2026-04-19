/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Probability.Distributions.Uniform

/-!
# Heavy ENNReal Arithmetic Lemmas

Extended-nonnegative-real arithmetic identities whose proofs bridge through `ENNReal.toReal`
and invoke `push_cast`, `ring`, `nlinarith`, or `aesop`. These proofs are several times more
expensive to elaborate than the general-purpose helpers in `ToMathlib.General`, so they live
in a separate module that only the files that need them pull in.

## Contents

- `ENNReal.one_sub_one_sub_mul_one_sub` — the identity `1 - (1-x)(1-y) = x + y - xy`
  used when combining two bounded failure probabilities.
- `ENNReal.toReal_sub_le_abs_toReal_sub` — real-valued bridge for truncated subtraction.
- `ENNReal.gauss_sum_inv_le` and `ENNReal.gauss_sum_inv_eq` — the Gauss sum
  `∑_{k<n} k/N ≤ n²/(2N)` (and its equality variant), the arithmetic core of the
  birthday bound.
- `ENNReal.add_div_two_mul_nat` — a nat-cast identity pairing `a/(2N)` with `b/N` over
  the common denominator `2N`.
-/

@[expose] public section

namespace ENNReal

lemma one_sub_one_sub_mul_one_sub {x y : ℝ≥0∞} (hx : x ≤ 1) (hy : y ≤ 1) :
    1 - (1 - x) * (1 - y) = x + y - x * y := by
  have hxy : x * y ≤ x + y := by
    have hxy_le_x : x * y ≤ x := mul_le_of_le_one_right' hy
    have hxy_le_y : x * y ≤ y := by
      apply mul_le_of_le_one_left (by positivity) hx;
    exact le_trans hxy_le_x ( le_add_of_nonneg_right <| by positivity )
  have hxy' : (1 - x) * (1 - y) ≤ 1 := by
    calc (1 - x) * (1 - y) ≤ 1 * 1 :=
          mul_le_mul' (tsub_le_self) (tsub_le_self)
        _ = 1 := one_mul 1
  rw [← ENNReal.toReal_eq_toReal_iff' (by aesop) (by aesop),
    ENNReal.toReal_sub_of_le, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le,
    ENNReal.toReal_sub_of_le, ENNReal.toReal_sub_of_le, ENNReal.toReal_add, ENNReal.toReal_mul]
  · simp
    linarith
  all_goals try aesop

/-- Real bridge for truncated `ENNReal` subtraction:
`(a - b).toReal` is bounded by `|a.toReal - b.toReal|`. -/
lemma toReal_sub_le_abs_toReal_sub (a b : ℝ≥0∞) :
    (a - b).toReal ≤ |a.toReal - b.toReal| := by
  by_cases ha : a = ⊤
  · by_cases hb : b = ⊤
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases h : b ≤ a
    · rw [ENNReal.toReal_sub_of_le h ha]
      exact le_abs_self _
    · have h' : a ≤ b := le_of_not_ge h
      rw [tsub_eq_zero_of_le h']
      exact abs_nonneg _

open Finset in
/-- The Gauss sum `∑_{k=0}^{n-1} k/N ≤ n²/(2N)`, the arithmetic core of the birthday bound. -/
lemma gauss_sum_inv_le (n : ℕ) (N : ℝ≥0∞) (_hN : 0 < N) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ ≤
      (n ^ 2 : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  have hnat : 2 * (∑ k ∈ range n, k) ≤ n ^ 2 := by
    have := Finset.sum_range_id_mul_two n; nlinarith [Nat.sub_le n 1]
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num,
      show (n : ℝ≥0∞) ^ 2 = ((n ^ 2 : ℕ) : ℝ≥0∞) from by push_cast; ring,
      ← Nat.cast_mul]
    exact_mod_cast hnat
  have hle : (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
    rwa [mul_comm]
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      ≤ ((n : ℝ≥0∞) ^ 2 / 2) * N⁻¹ := mul_le_mul_left hle N⁻¹
    _ = (n : ℝ≥0∞) ^ 2 / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

open Finset in
/-- Tight Gauss sum: `∑_{k=0}^{n-1} k/N = n*(n-1)/(2N)`. -/
lemma gauss_sum_inv_eq (n : ℕ) (N : ℝ≥0∞) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ =
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  have hnat : (∑ k ∈ range n, k) * 2 = n * (n - 1) :=
    Finset.sum_range_id_mul_two n
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
    congr 1; omega
  have heq : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 := by
    rw [ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    exact henn
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 * N⁻¹ := by rw [heq]
    _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

/-- `a/(2N) + b/N = (a + 2b)/(2N)` for natural-number casts to `ℝ≥0∞`. -/
lemma add_div_two_mul_nat (a b N : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / (2 * N) +
      ((b : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ =
    ((a + 2 * b : ℕ) : ℝ≥0∞) / (2 * N) := by
  set D := (2 * (N : ℝ≥0∞))
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [mul_comm (((b : ℕ) : ℝ≥0∞)) ((N : ℝ≥0∞)⁻¹)]
  have hD_inv : (N : ℝ≥0∞)⁻¹ = D⁻¹ * 2 := by
    simp only [D]
    rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)),
      mul_comm (2 : ℝ≥0∞)⁻¹ _, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
  rw [hD_inv, mul_assoc, ← mul_add]
  congr 1
  push_cast
  ring

end ENNReal
