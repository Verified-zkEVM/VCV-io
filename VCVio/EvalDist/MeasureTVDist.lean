/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.TotalVariation
public import VCVio.EvalDist.TVDist

/-!
# Total variation for measure-valued computation semantics

This module is the primary total-variation interface for VCVio computations. It applies
Mathlib-measure total variation directly to `𝒟[…]`; no finite-distribution backend, countability
assumption, or failure completion appears in its definitions.

The older `VCVio.EvalDist.TVDist` module remains the discrete compatibility development.  New
measure-native security statements should use `measureTVDist` and `measureETVDist` from this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

universe u v

variable {m : Type u → Type v} {α : Type u}

/-- Extended total variation between the primary measure denotations of two computations. -/
noncomputable def measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : ℝ≥0∞ :=
  Measure.etvDist (𝒟[mx]) (𝒟[my])

/-- Real-valued total variation between the primary measure denotations of two computations. -/
noncomputable def measureTVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : ℝ :=
  Measure.tvDist (𝒟[mx]) (𝒟[my])

@[simp]
theorem measureETVDist_self [EvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    measureETVDist mx mx = 0 :=
  Measure.etvDist_self _

theorem measureETVDist_comm [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my = measureETVDist my mx :=
  Measure.etvDist_comm _ _

theorem measureETVDist_triangle [EvalDistSemantics m] [MeasurableSpace α]
    (mx my mz : m α) :
    measureETVDist mx mz ≤ measureETVDist mx my + measureETVDist my mz :=
  Measure.etvDist_triangle _ _ _

@[simp]
theorem measureETVDist_eq_zero_iff [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureETVDist mx my = 0 ↔ 𝒟[mx] = 𝒟[my] :=
  Measure.etvDist_eq_zero_iff

theorem measureETVDist_le_one [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureETVDist mx my ≤ 1 :=
  Measure.etvDist_le_one _ _ (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

@[simp]
theorem measureTVDist_self [EvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    measureTVDist mx mx = 0 :=
  Measure.tvDist_self _

theorem measureTVDist_comm [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureTVDist mx my = measureTVDist my mx :=
  Measure.tvDist_comm _ _

theorem measureTVDist_nonneg [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    0 ≤ measureTVDist mx my :=
  Measure.tvDist_nonneg _ _

theorem measureTVDist_triangle [EvalDistSemantics m] [MeasurableSpace α]
    (mx my mz : m α) :
    measureTVDist mx mz ≤ measureTVDist mx my + measureTVDist my mz :=
  Measure.tvDist_triangle _ _ _
    (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)
    (evalDist_apply_univ_le_one mz)

theorem measureTVDist_le_one [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) :
    measureTVDist mx my ≤ 1 :=
  Measure.tvDist_le_one _ _ (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

@[simp]
theorem measureTVDist_eq_zero_iff [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) : measureTVDist mx my = 0 ↔ 𝒟[mx] = 𝒟[my] :=
  Measure.tvDist_eq_zero_iff _ _
    (evalDist_apply_univ_le_one mx) (evalDist_apply_univ_le_one my)

/-- Every measurable-event discrepancy is bounded by measure-native extended TV. -/
theorem measure_absDiff_apply_le_measureETVDist [EvalDistSemantics m] [MeasurableSpace α]
    (mx my : m α) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.absDiff (𝒟[mx] s) (𝒟[my] s) ≤ measureETVDist mx my :=
  Measure.absDiff_apply_le_etvDist _ _ hs

/-! ## Total variation of canonical discrete readings

Definitions stated on bare result types carry no ambient measurable structure, so the primary
measure notation cannot be applied to them directly. `discreteETVDist` and `discreteTVDist`
read both computations at the top σ-algebra via `discreteEvalDist`, mirroring how the
traditional point/event probability notation selects its σ-algebra implicitly. -/

/-- Extended total variation between the canonical discrete measure readings of two
computations. -/
noncomputable def discreteETVDist [EvalDistSemantics m] (mx my : m α) : ℝ≥0∞ :=
  @Measure.etvDist α ⊤ (discreteEvalDist mx) (discreteEvalDist my)

/-- Total variation between the canonical discrete measure readings of two computations.

This is the measure-native distance for developments whose result types carry no ambient
measurable structure. -/
noncomputable def discreteTVDist [EvalDistSemantics m] (mx my : m α) : ℝ :=
  @Measure.tvDist α ⊤ (discreteEvalDist mx) (discreteEvalDist my)

section discreteTVDist

variable [EvalDistSemantics m]

@[simp]
theorem discreteTVDist_self (mx : m α) : discreteTVDist mx mx = 0 :=
  @Measure.tvDist_self α ⊤ (discreteEvalDist mx)

theorem discreteTVDist_comm (mx my : m α) : discreteTVDist mx my = discreteTVDist my mx :=
  @Measure.tvDist_comm α ⊤ (discreteEvalDist mx) (discreteEvalDist my)

theorem discreteTVDist_nonneg (mx my : m α) : 0 ≤ discreteTVDist mx my :=
  @Measure.tvDist_nonneg α ⊤ (discreteEvalDist mx) (discreteEvalDist my)

theorem discreteTVDist_triangle (mx my mz : m α) :
    discreteTVDist mx mz ≤ discreteTVDist mx my + discreteTVDist my mz :=
  @Measure.tvDist_triangle α ⊤ (discreteEvalDist mx) (discreteEvalDist my)
    (discreteEvalDist mz) (discreteEvalDist_apply_univ_le_one mx)
    (discreteEvalDist_apply_univ_le_one my) (discreteEvalDist_apply_univ_le_one mz)

theorem discreteTVDist_le_one (mx my : m α) : discreteTVDist mx my ≤ 1 :=
  @Measure.tvDist_le_one α ⊤ (discreteEvalDist mx) (discreteEvalDist my)
    (discreteEvalDist_apply_univ_le_one mx) (discreteEvalDist_apply_univ_le_one my)

@[simp]
theorem discreteTVDist_eq_zero_iff (mx my : m α) :
    discreteTVDist mx my = 0 ↔ discreteEvalDist mx = discreteEvalDist my :=
  @Measure.tvDist_eq_zero_iff α ⊤ (discreteEvalDist mx) (discreteEvalDist my)
    (discreteEvalDist_apply_univ_le_one mx) (discreteEvalDist_apply_univ_le_one my)

end discreteTVDist

/-! The exact dictionary between the measure total variation of successful-output measures and
the executable `SPMF` total variation on discrete spaces — including the zero-distance relation
and the one-point observation space used by bundled UC semantics — lives in
`VCVio.EvalDist.DiscreteMeasureCompat` as corollaries of the general agreement theorem
`SPMF.toMeasure_etvDist`. -/
