/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.MeasureTheory.MeasurableSpace.Option
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Discarding the `none` part of an option-valued measure

`Measure.dropNone` turns a measure on `Option α` into the submeasure of successful values on
`α`. It is the effect-preserving boundary needed by `OptionT` and by finite observations of a
possibly nonterminating computation: the `none` mass is discarded instead of being confused with
an ordinary result.

The definition uses the Giry bind. The coproduct measurable structure makes the success/failure
case split measurable without requiring `α` itself to be discrete.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Keep the mass at `some x` as mass at `x`, and discard the mass at `none`. -/
noncomputable def dropNone (μ : Measure (Option α)) : Measure α :=
  Measure.bind μ fun
    | none => 0
    | some x => Measure.dirac x

/-- The measure family used by `dropNone` is measurable for every measurable result space. -/
@[fun_prop]
theorem measurable_dropNoneKernel : Measurable fun value : Option α =>
    match value with
    | none => 0
    | some x => Measure.dirac x :=
  Option.measurable_elim measurable_const Measure.measurable_dirac

@[simp]
theorem dropNone_zero : dropNone (0 : Measure (Option α)) = 0 := by
  simp [dropNone, Measure.bind_zero_left]

@[simp]
theorem dropNone_dirac_none :
    dropNone (Measure.dirac (none : Option α)) = 0 := by
  rw [dropNone, Measure.dirac_bind measurable_dropNoneKernel]

@[simp]
theorem dropNone_dirac_some (x : α) :
    dropNone (Measure.dirac (some x)) = Measure.dirac x := by
  rw [dropNone, Measure.dirac_bind measurable_dropNoneKernel]

/-- The success mass at `x` is the original mass at `some x`.

This is the computation rule that carries a pointwise mass statement across `dropNone`. -/
theorem dropNone_apply_singleton [MeasurableSingletonClass α]
    (μ : Measure (Option α)) (x : α) :
    dropNone μ {x} = μ {some x} := by
  rw [dropNone, Measure.bind_apply (measurableSet_singleton x)
    measurable_dropNoneKernel.aemeasurable]
  refine Eq.trans (lintegral_congr (g := Set.indicator {some x} 1) ?_) ?_
  · rintro (_ | y)
    · simp
    · by_cases hy : y = x <;> simp [hy]
  · exact lintegral_indicator_one (measurableSet_singleton (some x))

/-- Discarding `none` cannot increase the total mass. -/
theorem dropNone_apply_univ_le (μ : Measure (Option α)) :
    dropNone μ Set.univ ≤ μ Set.univ := by
  rw [dropNone, Measure.bind_apply MeasurableSet.univ measurable_dropNoneKernel.aemeasurable,
    ← lintegral_one]
  apply lintegral_mono
  intro value
  cases value <;> simp

/-! ## Completing a subprobability measure with an explicit failure outcome -/

/-- Turn a subprobability measure into a measure on `Option α` by mapping successful outcomes
through `some` and assigning all missing mass to `none`.

The definition is meaningful for every measure. The expected probability-measure law requires
the explicit subprobability hypothesis `μ univ ≤ 1`; keeping that hypothesis visible avoids a
blanket bundled subprobability type at the primary semantics boundary. -/
noncomputable def withFailure (μ : Measure α) : Measure (Option α) :=
  Measure.map some μ + (1 - μ Set.univ) • Measure.dirac none

/-- Completing a subprobability measure assigns total mass one. -/
@[simp]
theorem withFailure_apply_univ (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    withFailure μ Set.univ = 1 := by
  rw [withFailure, Measure.add_apply, Measure.map_apply Option.measurable_some MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply' none MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.indicator_of_mem (Set.mem_univ none), Pi.one_apply,
    smul_eq_mul, mul_one]
  simpa [add_comm] using tsub_add_cancel_of_le hμ

/-- The failure completion of a subprobability measure is a probability measure. -/
theorem withFailure_isProbabilityMeasure (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    IsProbabilityMeasure (withFailure μ) := by
  rw [isProbabilityMeasure_iff]
  exact withFailure_apply_univ μ hμ

/-- The mass of the explicit failure outcome is exactly the missing mass. -/
theorem withFailure_apply_none [DiscreteMeasurableSpace α] (μ : Measure α) :
    withFailure μ {none} = 1 - μ Set.univ := by
  rw [withFailure, Measure.add_apply,
    Measure.map_apply Option.measurable_some (measurableSet_singleton none),
    Measure.smul_apply, Measure.dirac_apply' none (measurableSet_singleton none)]
  rw [show some ⁻¹' ({none} : Set (Option α)) = ∅ by ext y; simp]
  rw [Set.indicator_of_mem (Set.mem_singleton none)]
  simp only [measure_empty, Pi.one_apply, smul_eq_mul, zero_add, mul_one]

/-- Failure completion preserves the mass of every successful singleton. -/
theorem withFailure_apply_some [DiscreteMeasurableSpace α] (μ : Measure α) (x : α) :
    withFailure μ {some x} = μ {x} := by
  rw [withFailure, Measure.add_apply,
    Measure.map_apply Option.measurable_some (measurableSet_singleton (some x)),
    Measure.smul_apply, Measure.dirac_apply' none (measurableSet_singleton (some x))]
  rw [show some ⁻¹' ({some x} : Set (Option α)) = {x} by ext y; simp]
  rw [Set.indicator_of_notMem (by simp)]
  simp only [smul_zero, add_zero]

end MeasureTheory.Measure
