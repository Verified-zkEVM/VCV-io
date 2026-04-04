/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Tail-Sum Identities for `PMF`

This file records discrete tail-sum formulas for nonnegative `ℕ`-valued random variables.

The core identity is the standard discrete expectation formula

`E[X] = ∑ i, Pr[i < X]`

for `ℕ`-valued random variables with values in `ℝ≥0∞`.

We first prove the corresponding summation identity for arbitrary nonnegative sequences, and then
specialize it to probability mass functions.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Tail-sum identity for a nonnegative sequence on `ℕ`:

`∑' n, f n * n = ∑' i, ∑' n, if i < n then f n else 0`.

This is the discrete nonnegative analogue of writing `n = ∑_{i < n} 1` and exchanging the order of
summation. -/
theorem tsum_mul_nat_eq_tsum_tail (f : ℕ → ℝ≥0∞) :
    (∑' n : ℕ, f n * (n : ℝ≥0∞)) = ∑' i : ℕ, ∑' n : ℕ, if i < n then f n else 0 := by
  calc
    ∑' n : ℕ, f n * (n : ℝ≥0∞) = ∑' n : ℕ, (n : ℝ≥0∞) * f n := by
      refine tsum_congr fun n => ?_
      rw [mul_comm]
    _ = ∑' n : ℕ, ∑' i : ℕ, if i < n then f n else 0 := by
      refine tsum_congr fun n => ?_
      rw [tsum_eq_sum (s := Finset.range n)]
      · have hsum :
            ∑ b ∈ Finset.range n, (if b < n then f n else 0) =
              ∑ _b ∈ Finset.range n, f n := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              simp [Finset.mem_range.mp hb]
        rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp [if_neg hi]
    _ = ∑' i : ℕ, ∑' n : ℕ, if i < n then f n else 0 := ENNReal.tsum_comm

end ENNReal

namespace PMF

/-- Tail-sum identity for the `ℝ≥0∞`-valued expectation of a `PMF ℕ`:

`∑' n, p n * n = ∑' i, p.toMeasure {n | i < n}`.

This is the discrete formula `E[X] = ∑ i, Pr[i < X]` for `ℕ`-valued random variables. -/
theorem tsum_coe_mul_nat_eq_tsum_measure_Ioi (p : PMF ℕ) :
    (∑' n : ℕ, p n * (n : ℝ≥0∞)) = ∑' i : ℕ, p.toMeasure (Set.Ioi i) := by
  calc
    ∑' n : ℕ, p n * (n : ℝ≥0∞) = ∑' i : ℕ, ∑' n : ℕ, if i < n then p n else 0 :=
      ENNReal.tsum_mul_nat_eq_tsum_tail p
    _ = ∑' i : ℕ, p.toMeasure (Set.Ioi i) := by
      refine tsum_congr fun i => ?_
      rw [p.toMeasure_apply_eq_tsum]
      refine tsum_congr fun n => ?_
      by_cases h : i < n <;> simp [Set.Ioi, Set.indicator, h]

end PMF
