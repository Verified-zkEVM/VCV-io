/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Distributivity of weighted `tsum`s over addition in `ℝ≥0∞`

Two algebraic identities about infinite sums
`∑' i, w i * (f i [+ c] [+ g i])` in the unweighted sense that, whenever the
weights `w` sum to one (the standard PMF normalisation), any constant added
*inside* the weighted sum can be pulled *outside*.

These are the building blocks for weighted game-hopping identities of the form
`∑' pksk, evalDist gen pksk * (Pr[good | …] + slack)` that show up in the
integrated Fiat-Shamir EUF-CMA reductions.

## Main results

- `ENNReal.tsum_mul_add_const_of_tsum_eq_one` —
  `(∑' i, w i * (f i + c)) = (∑' i, w i * f i) + c` when `(∑' i, w i) = 1`.
- `ENNReal.tsum_mul_add_const_add_of_tsum_eq_one` —
  `(∑' i, w i * (f i + c + g i)) = (∑' i, w i * f i) + c + (∑' i, w i * g i)`
  when `(∑' i, w i) = 1`.
-/

@[expose] public section

namespace ENNReal

/-- If the weights `w : ι → ℝ≥0∞` sum to `1`, a constant added inside a
weighted infinite sum pulls out unchanged:
`(∑' i, w i * (f i + c)) = (∑' i, w i * f i) + c`. -/
theorem tsum_mul_add_const_of_tsum_eq_one
    {ι : Type*} (w : ι → ℝ≥0∞) (f : ι → ℝ≥0∞) (c : ℝ≥0∞)
    (hw : (∑' i, w i) = 1) :
    (∑' i, w i * (f i + c)) = (∑' i, w i * f i) + c := by
  have hc : (∑' i, w i * c) = c := by
    rw [ENNReal.tsum_mul_right, hw, one_mul]
  calc (∑' i, w i * (f i + c))
      = ∑' i, (w i * f i + w i * c) := by simp_rw [mul_add]
    _ = (∑' i, w i * f i) + (∑' i, w i * c) := ENNReal.tsum_add
    _ = (∑' i, w i * f i) + c := by rw [hc]

/-- If the weights `w : ι → ℝ≥0∞` sum to `1`, a constant flanked by two
index-dependent summands inside a weighted infinite sum pulls out unchanged:
`(∑' i, w i * (f i + c + g i)) = (∑' i, w i * f i) + c + (∑' i, w i * g i)`. -/
theorem tsum_mul_add_const_add_of_tsum_eq_one
    {ι : Type*} (w : ι → ℝ≥0∞) (f g : ι → ℝ≥0∞) (c : ℝ≥0∞)
    (hw : (∑' i, w i) = 1) :
    (∑' i, w i * (f i + c + g i)) =
      (∑' i, w i * f i) + c + (∑' i, w i * g i) := by
  have hc : (∑' i, w i * c) = c := by
    rw [ENNReal.tsum_mul_right, hw, one_mul]
  calc (∑' i, w i * (f i + c + g i))
      = ∑' i, ((w i * f i + w i * c) + w i * g i) := by simp_rw [mul_add]
    _ = (∑' i, (w i * f i + w i * c)) + (∑' i, w i * g i) := ENNReal.tsum_add
    _ = ((∑' i, w i * f i) + (∑' i, w i * c)) + (∑' i, w i * g i) := by
        rw [ENNReal.tsum_add]
    _ = (∑' i, w i * f i) + c + (∑' i, w i * g i) := by rw [hc]

end ENNReal
