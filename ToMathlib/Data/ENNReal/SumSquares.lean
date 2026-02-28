/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sum-of-squares inequalities for `ℝ≥0∞`

Cauchy-Schwarz-style inequalities relating sums, products, and squares over `ℝ≥0∞`.
These are used in the forking lemma and other game-hopping arguments.
-/

open Finset ENNReal

namespace ENNReal

lemma two_mul_le_add_sq (a b : ℝ≥0∞) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [top_pow, top_add, le_top]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [top_pow, add_top, le_top]
  rw [← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb]
  exact_mod_cast _root_.two_mul_le_add_sq a.toNNReal b.toNNReal

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

end ENNReal
