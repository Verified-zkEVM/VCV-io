/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.Probability.UniformOn

/-!
# Event bounds for subprobability measures

A measurable bad event can be charged separately from a uniform bound on the
remaining continuations. Uniform finite sampling identifies event mass with
normalized cardinality directly through counting measure.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A bad-event bound and a uniform good-branch bound control sequential composition. -/
theorem bind_apply_le_add_of_bad (μ : Measure α) [IsSubprobabilityMeasure μ]
    (f : α → Measure β) (hf : Measurable f) [∀ a, IsSubprobabilityMeasure (f a)]
    {bad : Set α} (hbad : MeasurableSet bad) {event : Set β} (hevent : MeasurableSet event)
    {ε₁ ε₂ : ENNReal} (hbadBound : μ bad ≤ ε₁)
    (hgood : ∀ a, a ∉ bad → f a event ≤ ε₂) :
    μ.bind f event ≤ ε₁ + ε₂ := by
  rw [bind_apply hevent hf.aemeasurable]
  calc
    _ ≤ ∫⁻ a, ε₂ + bad.indicator 1 a ∂μ := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ bad
      · simpa [ha] using (measure_le_one (f a) event).trans
          (le_add_self : (1 : ENNReal) ≤ ε₂ + 1)
      · simpa [ha] using hgood a ha
    _ = ε₂ * μ Set.univ + μ bad := by
      rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_one hbad]
    _ ≤ ε₂ + ε₁ := add_le_add
      ((mul_le_mul' le_rfl (measure_univ_le μ)).trans_eq (mul_one ε₂)) hbadBound
    _ = _ := add_comm _ _

end MeasureTheory.Measure

namespace ProbabilityTheory

/-- The uniform measure of a predicate on a finite type is its normalized cardinality. -/
theorem uniformOn_univ_apply_setOf {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] (p : α → Prop) [DecidablePred p] :
    (uniformOn Set.univ : Measure α) {x | p x} =
      ((Finset.univ.filter p).card : ENNReal) / Fintype.card α := by
  rw [uniformOn_univ]
  have hset : {x | p x} = (↑(Finset.univ.filter p) : Set α) := by ext; simp
  rw [hset, Measure.count_apply_finset]

end ProbabilityTheory
