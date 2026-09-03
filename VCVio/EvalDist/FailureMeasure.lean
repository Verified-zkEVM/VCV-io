/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.ExpectationMeasure
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Instances.OptionT

/-!
# Failure on the measure side

On the measure side a computation's failure is *missing mass*: `𝒟[mx]` is a subprobability
measure and `Pr[⊥ | mx]` is what it lacks to be a probability measure. This module records that
account of failure against the façade bridge `DiscreteEvalDistCompatible`:

* `probFailure_eq_one_sub_evalDist_univ`, `evalDist_apply_univ_eq_one_iff`,
  `isProbabilityMeasure_evalDist_iff` — failure is the missing mass, and a computation denotes a
  probability measure exactly when it never fails; `NeverFail mx` gives the
  `IsProbabilityMeasure 𝒟[mx]` instance.
* `evalDist_failure` — `failure` denotes the zero measure.
* `evalDist_withFailure_apply_none`/`_some` — the failure-completed denotation
  `(𝒟[mx]).withFailure : Measure (Option α)` is the probability measure with the failure mass at
  `none` and the point probabilities at `some x`.
* `evalDist_bind_apply_univ`, `evalDist_map_apply_univ`, `probFailure_bind_eq_add_expectedValue`
  — how success mass moves through `bind` and `map`, in `expectedValue` form.
* `OptionT.evalDist_eq_dropNone` — an `OptionT` computation denotes the `dropNone` of its run:
  the `none` branch is discarded mass, not an output.
-/

@[expose] public section

open MeasureTheory OracleComp.EvalDist
open scoped ENNReal

universe u v

variable {m : Type u → Type v} {α β : Type u}

section compatible

variable [MonadLiftT m SPMF] [EvalDistSemantics m] [DiscreteEvalDistCompatible m]
  [MeasurableSpace α]

/-- Failure is the mass missing from the denoted measure. -/
theorem probFailure_eq_one_sub_evalDist_univ (mx : m α) :
    Pr[⊥ | mx] = 1 - 𝒟[mx] Set.univ := by
  rw [evalDist_apply_univ, ENNReal.sub_sub_cancel ENNReal.one_ne_top probFailure_le_one]

/-- The denoted measure has total mass one exactly when the computation never fails. -/
theorem evalDist_apply_univ_eq_one_iff (mx : m α) : 𝒟[mx] Set.univ = 1 ↔ Pr[⊥ | mx] = 0 := by
  constructor
  · intro h
    rw [probFailure_eq_one_sub_evalDist_univ, h, tsub_self]
  · intro h
    rw [evalDist_apply_univ, h, tsub_zero]

/-- A computation denotes a probability measure exactly when it never fails. -/
theorem isProbabilityMeasure_evalDist_iff (mx : m α) :
    IsProbabilityMeasure 𝒟[mx] ↔ Pr[⊥ | mx] = 0 := by
  rw [isProbabilityMeasure_iff, evalDist_apply_univ_eq_one_iff]

/-- A computation that never fails denotes a probability measure. -/
instance [Monad m] (mx : m α) [NeverFail mx] : IsProbabilityMeasure 𝒟[mx] :=
  (isProbabilityMeasure_evalDist_iff mx).mpr probFailure_eq_zero

/-- `failure` denotes the zero measure. -/
@[simp]
theorem evalDist_failure [AlternativeMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalSet.LawfulFailure m] : 𝒟[(failure : m α)] = 0 := by
  rw [← Measure.measure_univ_eq_zero, evalDist_apply_univ, probFailure_failure, tsub_self]

variable [DiscreteMeasurableSpace α]

/-- The failure-completed denotation puts the failure probability at `none`. -/
@[simp]
theorem evalDist_withFailure_apply_none (mx : m α) :
    (𝒟[mx]).withFailure {none} = Pr[⊥ | mx] := by
  rw [Measure.withFailure_apply_none, evalDist_apply_univ,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top probFailure_le_one]

/-- The failure-completed denotation keeps every point probability at `some x`. -/
@[simp]
theorem evalDist_withFailure_apply_some (mx : m α) (x : α) :
    (𝒟[mx]).withFailure {some x} = Pr[= x | mx] := by
  rw [Measure.withFailure_apply_some, evalDist_apply_singleton]

/-- The failure-completed denotation is a probability measure. -/
instance (mx : m α) : IsProbabilityMeasure (𝒟[mx]).withFailure :=
  Measure.withFailure_isProbabilityMeasure _ (evalDist_apply_univ_le_one mx)

end compatible

section lawful

variable [Monad m] [MonadLiftT m SPMF] [EvalDistSemantics m] [DiscreteEvalDistCompatible m]
  [LawfulEvalDistSemantics m] [MeasurableSpace α] [DiscreteMeasurableSpace α]
  [MeasurableSpace β]

/-- The success mass of a bind is the expected success mass of the continuation. -/
theorem evalDist_bind_apply_univ (mx : m α) (f : α → m β) :
    𝒟[mx >>= f] Set.univ = expectedValue mx fun x => 𝒟[f x] Set.univ := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.univ
    Measurable.of_discrete.aemeasurable, lintegral_evalDist]

omit [MonadLiftT m SPMF] [DiscreteEvalDistCompatible m] [DiscreteMeasurableSpace α] in
/-- A measurable map preserves success mass. -/
theorem evalDist_map_apply_univ [LawfulMonad m] (mx : m α) {f : α → β} (hf : Measurable f) :
    𝒟[f <$> mx] Set.univ = 𝒟[mx] Set.univ := by
  rw [evalDist_map mx hf, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

end lawful

/-- `probFailure_bind_eq_add_tsum` with the sum packaged as an `expectedValue`: the failure of
a bind is the prefix failure plus the expected failure of the continuation. -/
theorem probFailure_bind_eq_add_expectedValue [Monad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + expectedValue mx fun x => Pr[⊥ | my x] :=
  probFailure_bind_eq_add_tsum mx my

namespace OptionT

variable [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MeasurableSpace α]
  [DiscreteMeasurableSpace α]

/-- An `OptionT` computation denotes the `dropNone` of its run: the `none` branch is discarded
mass, not an output. -/
theorem evalDist_eq_dropNone (mx : OptionT m α) : 𝒟[mx] = (𝒟[mx.run]).dropNone := by
  change (𝒮[mx]).toMeasure = Measure.dropNone (𝒮[mx.run]).toMeasure
  rw [OptionT.evalSPMF_eq, OptionT.mapM', Measure.dropNone, SPMF.toMeasure_bind]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun o => ?_)
  cases o <;> simp

end OptionT
