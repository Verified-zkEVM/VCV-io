/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# `PMF.toMeasure` as a sum of Dirac masses, and as a monad morphism

Mathlib records two thirds of the monad-morphism statement: `PMF.toMeasure_pure` sends
`PMF.pure` to `Measure.dirac`, and `PMF.toMeasure_map` commutes `toMeasure` with `map`. For
`bind` it provides only the applied form `PMF.toMeasure_bind_apply`, which evaluates
`(p.bind f).toMeasure` at a measurable set as a `tsum`.

The lemmas here derive everything from one decomposition, `PMF.toMeasure_eq_sum_smul_dirac`:
`p.toMeasure` is the weighted sum of the Dirac masses at its outcomes. Integrals against it are
then mass-weighted sums with the mass on the *left* (`PMF.lintegral_toMeasure`), the orientation
of `PMF.bind_apply`, with no commutativity step and no countability assumption on the carrier;
Mathlib's `lintegral_countable'` puts the mass on the right and needs `[Countable α]`.

`PMF.toMeasure_bind'` is the measure-level bind law under the natural measurability hypothesis
on the continuation, and `PMF.toMeasure_bind` its discrete specialization. Both stay in
`ToMathlib` during the migration and can go once the upstream API acquires the same equalities.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace PMF

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (p : PMF α) (f : α → PMF β)

/-- A probability mass function's measure is the weighted sum of the Dirac masses at its
outcomes. No countability of the carrier is needed: both sides are determined on measurable
sets by `PMF.toMeasure_apply`. -/
theorem toMeasure_eq_sum_smul_dirac :
    p.toMeasure = Measure.sum fun a => p a • Measure.dirac a := by
  ext s hs
  rw [toMeasure_apply p hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  exact tsum_congr fun a => by by_cases ha : a ∈ s <;> simp [ha]

/-- Integrating a measurable function against `p.toMeasure` is the mass-weighted sum of its
values, with the mass on the left as in `PMF.bind_apply`. -/
theorem lintegral_toMeasure {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g a ∂p.toMeasure = ∑' a, p a * g a := by
  rw [toMeasure_eq_sum_smul_dirac, lintegral_sum_measure]
  exact tsum_congr fun a => by rw [lintegral_smul_measure, lintegral_dirac' a hg, smul_eq_mul]

/-- `PMF.toMeasure` commutes with `bind` whenever the measure-valued continuation is measurable.

This is the measure-level form of `PMF.toMeasure_bind_apply`, and together with
`PMF.toMeasure_pure` it says that `PMF.toMeasure` is a monad morphism from `PMF` into the Giry
monad. -/
theorem toMeasure_bind' (hf : Measurable fun a => (f a).toMeasure) :
    (p.bind f).toMeasure = Measure.bind p.toMeasure fun a => (f a).toMeasure := by
  ext s hs
  rw [toMeasure_bind_apply _ _ _ hs, Measure.bind_apply hs hf.aemeasurable,
    lintegral_toMeasure p (g := fun a => (f a).toMeasure s) ((Measure.measurable_coe hs).comp hf)]

/-- On a discrete source type every measure-valued continuation is measurable. -/
theorem toMeasure_bind [DiscreteMeasurableSpace α] :
    (p.bind f).toMeasure = Measure.bind p.toMeasure fun a => (f a).toMeasure :=
  toMeasure_bind' p f Measurable.of_discrete

end PMF
