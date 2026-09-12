/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Defs.Support
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.Option
public import ToMathlib.Probability.ProbabilityMassFunction.Measure

/-!
# Measure-valued evaluation and discrete compatibility

This module reexports `VCVio.EvalDist.Defs.Measure.Core` and supplies the discrete
compatibility adapters. An
`EvalDistSemantics m` interprets `m α` as a Mathlib `Measure α` with total mass at most one.
Missing mass represents failure or nontermination. In particular, the output distribution itself
does not introduce an `Option` outcome.

Measurable spaces are explicit arguments to the semantics. There is deliberately no blanket
measurable-space instance for finite types: discrete adapters state their countability and
measurability assumptions at the boundary where they are used.

`LawfulEvalDistSemantics` records the Giry `pure` and `bind` laws. The bind law keeps the
measurability of the continuation visible; `evalDist_bind_of_discrete` is the usual cryptographic
specialization.
-/

@[expose] public section

open MeasureTheory

universe u v

namespace SPMF

variable {α : Type u} [MeasurableSpace α] (p : SPMF α)

/-- Read an `SPMF` as the measure of its successful outputs. This is the explicit compatibility
bridge from the finite executable backend to the primary measure API. -/
noncomputable def toMeasure : Measure α :=
  p.toPMF.toMeasure.dropNone

theorem toMeasure_apply_univ_le_one : p.toMeasure Set.univ ≤ 1 := by
  have hTotal : p.toPMF.toMeasure Set.univ = 1 := measure_univ
  exact (Measure.dropNone_apply_univ_le p.toPMF.toMeasure).trans_eq hTotal

@[simp]
theorem toMeasure_pure (x : α) : (pure x : SPMF α).toMeasure = Measure.dirac x := by
  simp [toMeasure, PMF.toMeasure_pure, Measure.dropNone_dirac_some]

/-- Failure carries no successful-output mass. -/
@[simp]
theorem toMeasure_failure : (failure : SPMF α).toMeasure = 0 := by
  rw [toMeasure, SPMF.toPMF_failure, PMF.toMeasure_pure, Measure.dropNone_dirac_none]

@[simp]
theorem toMeasure_apply_singleton [MeasurableSingletonClass α] (x : α) :
    p.toMeasure {x} = p x := by
  rw [toMeasure, Measure.dropNone_apply_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (some x))]
  rfl

/-- Integrating a measurable function against the successful-output measure is the
mass-weighted sum over successful outputs, with the mass on the left as in
`bind_apply_eq_tsum`. This is the one place where the transitional option-valued backend meets
Lebesgue integration; every singleton, event and expectation bridge derives from it, and it is
the glue that disappears once the façade is defined from `𝒟[…]` directly. -/
theorem lintegral_toMeasure {g : α → ENNReal} (hg : Measurable g) :
    ∫⁻ x, g x ∂p.toMeasure = ∑' x, p x * g x := by
  rw [toMeasure, Measure.lintegral_dropNone _ hg]
  refine (PMF.lintegral_toMeasure p.toPMF (g := fun o => o.elim 0 g)
    (by fun_prop)).trans ?_
  rw [tsum_option _ ENNReal.summable]
  simp [SPMF.apply_eq_toPMF_some]

/-- The successful-output measure of a measurable set is the sum of the point masses it
contains. -/
theorem toMeasure_apply {s : Set α} (hs : MeasurableSet s) :
    p.toMeasure s = ∑' x, p x * s.indicator 1 x := by
  rw [← lintegral_indicator_one hs, lintegral_toMeasure _ (measurable_one.indicator hs)]

/-- The total mass of the successful-output measure is the sum of the `SPMF` point masses. -/
@[simp]
theorem toMeasure_apply_univ : p.toMeasure Set.univ = ∑' x, p x := by
  rw [toMeasure_apply _ MeasurableSet.univ]
  simp

/-- The successful-output measure retains the complete `SPMF`.

Failure mass is determined by the successful masses, so dropping the explicit `none` outcome does
not lose information. -/
theorem toMeasure_injective [MeasurableSingletonClass α] :
    Function.Injective (toMeasure (α := α)) := by
  intro p q hpq
  apply SPMF.ext
  intro x
  rw [← toMeasure_apply_singleton p x, ← toMeasure_apply_singleton q x, hpq]

/-- The successful-output measure commutes with measurable maps. -/
theorem toMeasure_map {β : Type u} [MeasurableSpace β] (f : α → β) (hf : Measurable f) :
    (f <$> p).toMeasure = p.toMeasure.map f := by
  have hOptionMap : Measurable (Option.map f) := by fun_prop
  ext s hs
  rw [toMeasure, SPMF.toPMF_map]
  change (p.toPMF.map (Option.map f)).toMeasure.dropNone s = _
  rw [← p.toPMF.toMeasure_map (Option.map f) hOptionMap, toMeasure,
    Measure.map_apply hf hs]
  simp only [Measure.dropNone]
  rw [
    Measure.bind_apply hs Measure.measurable_dropNoneKernel.aemeasurable,
    Measure.bind_apply (hf hs) Measure.measurable_dropNoneKernel.aemeasurable]
  · rw [MeasureTheory.lintegral_map]
    · apply lintegral_congr
      intro value
      cases value with
      | none => simp
      | some x =>
          by_cases hx : f x ∈ s <;>
            simp [Option.map, hs, hf hs, hx]
    · exact (Measure.measurable_coe hs).comp Measure.measurable_dropNoneKernel
    · exact hOptionMap

/-- Successful-output measures commute with `SPMF` bind whenever the measure-valued
continuation is measurable. -/
theorem toMeasure_bind' {β : Type u} [MeasurableSpace β] (f : α → SPMF β)
    (hf : Measurable fun x => (f x).toMeasure) :
    (p >>= f).toMeasure = Measure.bind p.toMeasure fun x => (f x).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs hf.aemeasurable,
    lintegral_toMeasure p (g := fun x => (f x).toMeasure s) ((Measure.measurable_coe hs).comp hf),
    toMeasure_apply _ hs]
  simp only [toMeasure_apply _ hs, bind_apply_eq_tsum, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

/-- On a discrete source type every measure-valued continuation is measurable. -/
theorem toMeasure_bind {β : Type u} [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (f : α → SPMF β) :
    (p >>= f).toMeasure = Measure.bind p.toMeasure fun x => (f x).toMeasure :=
  toMeasure_bind' p f Measurable.of_discrete

end SPMF

/-- Compatibility semantics for monads that still expose an `SPMF` lift.

The low priority lets a direct measure interpretation, such as the free-monad fold in
`PFunctorMeasure`, win whenever both are available. -/
noncomputable instance (priority := 10) instEvalDistSemanticsOfMonadLiftTSPMF
    {m : Type u → Type v} [MonadLiftT m SPMF] : EvalDistSemantics m where
  denote mx := (liftM mx : SPMF _).toMeasure
  apply_univ_le_one mx := SPMF.toMeasure_apply_univ_le_one (liftM mx : SPMF _)

namespace MeasureTheory.Measure

variable {α : Type u} [MeasurableSpace α]

/-- Convert a countable discrete subprobability measure to the compatibility `SPMF` backend.

The missing mass is first made explicit as `none`; the resulting probability measure can then use
Mathlib's `Measure.toPMF` bridge. -/
noncomputable def toSPMF [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) : SPMF α := by
  let _ : IsProbabilityMeasure μ.withFailure := μ.withFailure_isProbabilityMeasure hμ
  exact SPMF.mk μ.withFailure.toPMF

@[simp]
theorem toSPMF_apply [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) (x : α) :
    μ.toSPMF hμ x = μ {x} := by
  rw [toSPMF, SPMF.apply_eq_toPMF_some, SPMF.toPMF_mk, Measure.toPMF_apply,
    Measure.withFailure_apply_some]

theorem toSPMF_apply_none [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    (μ.toSPMF hμ).run none = 1 - μ Set.univ := by
  let _ : IsProbabilityMeasure μ.withFailure := μ.withFailure_isProbabilityMeasure hμ
  change μ.withFailure.toPMF none = 1 - μ Set.univ
  rw [Measure.toPMF_apply, Measure.withFailure_apply_none]

/-- Converting a discrete subprobability measure to `SPMF` and back preserves the measure. -/
@[simp]
theorem toSPMF_toMeasure [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    (μ.toSPMF hμ).toMeasure = μ := by
  apply Measure.ext_of_singleton
  intro x
  simp

/-- Converting an `SPMF` to its successful-output measure and back preserves the `SPMF`. -/
@[simp]
theorem _root_.SPMF.toMeasure_toSPMF [Countable α] [DiscreteMeasurableSpace α]
    (p : SPMF α) :
    p.toMeasure.toSPMF (SPMF.toMeasure_apply_univ_le_one p) = p := by
  apply SPMF.ext
  intro x
  simp

end MeasureTheory.Measure
