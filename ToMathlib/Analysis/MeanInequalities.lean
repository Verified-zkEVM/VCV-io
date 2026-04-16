/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Hölder Inequality for ENNReal-Valued Infinite Sums

This file provides a `tsum` version of Hölder's inequality for `ℝ≥0∞`-valued functions,
obtained by specializing the `lintegral` Hölder inequality to the counting measure.

The main advantage over `NNReal.inner_le_Lp_mul_Lq_tsum` in Mathlib is that no
`Summable` hypotheses are needed: `ℝ≥0∞` sums always converge (to `⊤` in the worst case).

## Main Results

- `ENNReal.inner_le_Lp_mul_Lq_tsum`: Hölder's inequality for `ℝ≥0∞`-valued `tsum`.
-/


noncomputable section

open MeasureTheory ENNReal

namespace ENNReal

variable {ι : Type*}

/-- Hölder's inequality for `ℝ≥0∞`-valued infinite sums:
`∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1/p) * (∑' i, g i ^ q) ^ (1/q)`.

Obtained by specializing `ENNReal.lintegral_mul_le_Lp_mul_Lq` to the counting measure
with `DiscreteMeasurableSpace`. No `Summable` hypotheses are needed. -/
theorem inner_le_Lp_mul_Lq_tsum {p q : ℝ} (hpq : p.HolderConjugate q)
    (f g : ι → ℝ≥0∞) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  letI : MeasurableSpace ι := ⊤
  haveI : DiscreteMeasurableSpace ι := ⟨fun _ => trivial⟩
  have := lintegral_mul_le_Lp_mul_Lq (α := ι) Measure.count hpq
    (AEMeasurable.of_discrete (f := f)) (AEMeasurable.of_discrete (f := g))
  simp only [lintegral_count, Pi.mul_apply] at this
  exact this

end ENNReal
