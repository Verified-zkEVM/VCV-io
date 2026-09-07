/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sum-of-squares inequalities for `ℝ≥0∞`

Cauchy-Schwarz-style inequalities relating sums, products, and squares over `ℝ≥0∞`.
These are used in the forking lemma and other game-hopping arguments.
-/

@[expose] public section

open Finset ENNReal

namespace ENNReal

/-- The `ℝ≥0∞` form of Mathlib's root `two_mul_le_add_sq` (which needs an ordered ring with
`ExistsAddOfLE` and `MulPosStrictMono`, so it does not apply to `ℝ≥0∞`); inside `open ENNReal` the
unqualified name resolves to this lemma. -/
lemma two_mul_le_add_sq (a b : ℝ≥0∞) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [top_pow, top_add, le_top]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [top_pow, add_top, le_top]
  rw [← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb]
  exact_mod_cast _root_.two_mul_le_add_sq a.toNNReal b.toNNReal

/-- The `ℝ≥0∞` form of Mathlib's root `sq_sum_le_card_mul_sum_sq`
(`Mathlib/Algebra/Order/Chebyshev`, stated for linearly ordered rings); inside `open ENNReal` the
unqualified name resolves to this lemma. -/
lemma sq_sum_le_card_mul_sum_sq {ι' : Type*}
    (s : Finset ι') (f : ι' → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  suffices h : 2 * ∑ i ∈ s, ∑ j ∈ s, f i * f j ≤ 2 * (↑s.card * ∑ i ∈ s, f i ^ 2) by
    have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    calc ∑ i ∈ s, ∑ j ∈ s, f i * f j
      _ = 2⁻¹ * (2 * ∑ i ∈ s, ∑ j ∈ s, f i * f j) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2 h2', one_mul]
      _ ≤ 2⁻¹ * (2 * (↑s.card * ∑ i ∈ s, f i ^ 2)) := by gcongr
      _ = ↑s.card * ∑ i ∈ s, f i ^ 2 := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2 h2', one_mul]
  calc 2 * ∑ i ∈ s, ∑ j ∈ s, f i * f j
    _ = ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * f j) := by
        rw [Finset.mul_sum]; congr 1; ext i; rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) := by
        gcongr with i _ j _
        calc 2 * (f i * f j) = 2 * f i * f j := (mul_assoc ..).symm
          _ ≤ f i ^ 2 + f j ^ 2 := ENNReal.two_mul_le_add_sq (f i) (f j)
    _ = ∑ i ∈ s, (↑s.card * f i ^ 2 + ∑ j ∈ s, f j ^ 2) := by
        congr 1; ext i
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ = ↑s.card * ∑ i ∈ s, f i ^ 2 + ↑s.card * ∑ i ∈ s, f i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
          Finset.mul_sum]
    _ = 2 * (↑s.card * ∑ i ∈ s, f i ^ 2) := by rw [← two_mul]

/-- Divided Cauchy-Schwarz: `(∑ i, f i)² / card ≤ ∑ i, (f i)²`. Derived from
`sq_sum_le_card_mul_sum_sq` by dividing both sides by `s.card`. Holds unconditionally in
`ℝ≥0∞`: when `s = ∅` the left-hand side reduces to `0 / 0 = 0`. -/
lemma sq_sum_div_card_le_sum_sq {ι' : Type*}
    (s : Finset ι') (f : ι' → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 / (s.card : ℝ≥0∞) ≤ ∑ i ∈ s, f i ^ 2 := by
  rcases Nat.eq_zero_or_pos s.card with hcard | hcard
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    simp [hs]
  · set N : ℝ≥0∞ := (s.card : ℝ≥0∞)
    have hN_ne_zero : N ≠ 0 := by
      simp only [N, Nat.cast_ne_zero]
      exact Nat.pos_iff_ne_zero.mp hcard
    have hN_ne_top : N ≠ ⊤ := by simp [N]
    calc (∑ i ∈ s, f i) ^ 2 / N
        = N⁻¹ * (∑ i ∈ s, f i) ^ 2 := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ N⁻¹ * (N * ∑ i ∈ s, f i ^ 2) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq s f
      _ = ∑ i ∈ s, f i ^ 2 := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hN_ne_zero hN_ne_top, one_mul]

/-- The finite aggregation step common to forking lemmas: divided
Cauchy--Schwarz controls the square term, while the collision penalty
distributes over the selector fibers. -/
lemma mul_tsub_inv_le_sum_sq_sub_div {ι' : Type*}
    (s : Finset ι') (f : ι' → ℝ≥0∞) (h : ℝ≥0∞)
    (hsum : (∑ i ∈ s, f i) ≠ ⊤) :
    (∑ i ∈ s, f i) *
        ((∑ i ∈ s, f i) / (s.card : ℝ≥0∞) - h⁻¹) ≤
      ∑ i ∈ s, (f i ^ 2 - f i / h) := by
  calc
    (∑ i ∈ s, f i) *
          ((∑ i ∈ s, f i) / (s.card : ℝ≥0∞) - h⁻¹)
        = (∑ i ∈ s, f i) ^ 2 / (s.card : ℝ≥0∞) -
            (∑ i ∈ s, f i) / h := by
          rw [ENNReal.mul_sub (fun _ _ ↦ hsum)]
          simp only [sq, div_eq_mul_inv]
          ring_nf
    _ ≤ (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) / h := by
          gcongr
          exact sq_sum_div_card_le_sum_sq s f
    _ = (∑ i ∈ s, f i ^ 2) - ∑ i ∈ s, f i / h := by
          simp_rw [div_eq_mul_inv]
          rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ s, (f i ^ 2 - f i / h) := by
          rw [tsub_le_iff_right]
          calc
            ∑ i ∈ s, f i ^ 2 ≤
                ∑ i ∈ s, ((f i ^ 2 - f i / h) + f i / h) :=
              Finset.sum_le_sum fun i hi ↦ le_tsub_add
            _ = (∑ i ∈ s, (f i ^ 2 - f i / h)) + ∑ i ∈ s, f i / h := by
              rw [Finset.sum_add_distrib]

private lemma tsum_mul_tsum_eq {α : Type*} (g h : α → ℝ≥0∞) :
    (∑' a, g a) * (∑' b, h b) = ∑' a, ∑' b, g a * h b := by
  rw [← ENNReal.tsum_mul_right]; congr 1; ext a
  exact ENNReal.tsum_mul_left.symm

lemma sq_tsum_le_tsum_mul_tsum {α : Type*} (w f : α → ℝ≥0∞) :
    (∑' a, w a * f a) ^ 2 ≤ (∑' a, w a) * ∑' a, w a * f a ^ 2 := by
  rw [sq, tsum_mul_tsum_eq, tsum_mul_tsum_eq]
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  suffices h : 2 * ∑' a, ∑' b, (w a * f a) * (w b * f b) ≤
      2 * ∑' a, ∑' b, w a * (w b * f b ^ 2) by
    calc ∑' a, ∑' b, (w a * f a) * (w b * f b)
      _ = 2⁻¹ * (2 * ∑' a, ∑' b, (w a * f a) * (w b * f b)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2 h2', one_mul]
      _ ≤ 2⁻¹ * (2 * ∑' a, ∑' b, w a * (w b * f b ^ 2)) := by gcongr
      _ = ∑' a, ∑' b, w a * (w b * f b ^ 2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2 h2', one_mul]
  calc 2 * ∑' a, ∑' b, (w a * f a) * (w b * f b)
    _ = ∑' a, ∑' b, 2 * ((w a * f a) * (w b * f b)) := by
        rw [← ENNReal.tsum_mul_left]; congr 1; ext
        rw [← ENNReal.tsum_mul_left]
    _ ≤ ∑' a, ∑' b, (w a * (w b * f b ^ 2) + w b * (w a * f a ^ 2)) := by
        gcongr with a b
        calc 2 * ((w a * f a) * (w b * f b))
          _ = w a * w b * (2 * f a * f b) := by ring
          _ ≤ w a * w b * (f a ^ 2 + f b ^ 2) := by
              gcongr; exact two_mul_le_add_sq (f a) (f b)
          _ = w a * (w b * f b ^ 2) + w b * (w a * f a ^ 2) := by ring
    _ = (∑' a, ∑' b, w a * (w b * f b ^ 2)) +
          ∑' a, ∑' b, w b * (w a * f a ^ 2) := by
        simp_rw [← ENNReal.tsum_add]
    _ = (∑' a, ∑' b, w a * (w b * f b ^ 2)) +
          ∑' b, ∑' a, w b * (w a * f a ^ 2) := by
        congr 1; exact ENNReal.tsum_comm
    _ = 2 * ∑' a, ∑' b, w a * (w b * f b ^ 2) := by rw [two_mul]

lemma sq_tsum_le_tsum_sq {α : Type*} (w f : α → ℝ≥0∞) (hw : ∑' a, w a ≤ 1) :
    (∑' a, w a * f a) ^ 2 ≤ ∑' a, w a * f a ^ 2 :=
  calc (∑' a, w a * f a) ^ 2
    _ ≤ (∑' a, w a) * ∑' a, w a * f a ^ 2 := sq_tsum_le_tsum_mul_tsum w f
    _ ≤ 1 * ∑' a, w a * f a ^ 2 := by gcongr
    _ = ∑' a, w a * f a ^ 2 := one_mul _

/-- A simple ENNReal upper bound used in the forking lemma: if `a ≤ 1` and `q ≥ 1`, then
`a * (a / q - r)` is still bounded by `1`, regardless of `r`. -/
lemma mul_tsub_div_le_one {a q r : ℝ≥0∞} (ha : a ≤ 1) (hq : 1 ≤ q) :
    a * (a / q - r) ≤ 1 := by
  calc
    a * (a / q - r) ≤ a * (a / q) := by
      gcongr
      exact tsub_le_self
    _ ≤ a * 1 := by
      have hdiv_le_a : a / q ≤ a := by
        rw [div_eq_mul_inv]
        calc
          a * q⁻¹ ≤ a * 1 := by
            gcongr
            exact ENNReal.inv_le_one.2 hq
          _ = a := by simp
      have hdiv_le_one : a / q ≤ 1 := le_trans hdiv_le_a ha
      gcongr
    _ ≤ 1 := by simpa using ha

end ENNReal
