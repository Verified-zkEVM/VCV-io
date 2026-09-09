/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.ProbabilityMassFunction.Measure
public import VCVio.EvalDist.PFunctor
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Primary and discrete compatibility for free-program measure semantics

The dependency-light native fold lives in `VCVio.EvalDist.PFunctorMeasure.Core`. This module
reexports the fold's primary `EvalDistSemantics` and connects it to the legacy discrete
`IsProbabilitySpec` evaluator.

## Main statements

* `PFunctor.IsMeasureSpec.Compatible` — the measure and probability specifications of an
  interface agree; `IsProbabilitySpec.toMeasureSpec` satisfies it definitionally.
* `PFunctor.FreeM.denote_eq_toMeasure` — under agreement, the fold is the measure of the `PMF`
  denotation of `VCVio.EvalDist.PFunctor`.
* The `DiscreteEvalDistCompatible (FreeM P)` instance — under agreement, `𝒟[…]` satisfies the
  façade bridge, so `evalDist_apply_singleton`, `evalDist_apply_setOf` and `lintegral_evalDist`
  read existing `Pr[…]` facts off the measure denotation.
-/

@[expose] public section

open MeasureTheory ENNReal

universe u uA

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  {α β : Type u}

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-! ### Agreement with the `PMF` denotation

For a polynomial interface carrying both interpretations compatibly, the measure denotation is
the measure of the `PMF` denotation. This is what lets a `Pr[…]` statement proved against
`VCVio.EvalDist.PFunctor` be transported here rather than reproved. -/

/-- The measure and probability interpretations of an interface agree. Instances are explicit
(`IsProbabilitySpec.toMeasureSpec`) or proved per interface, never derived from finiteness
alone. -/
class _root_.PFunctor.IsMeasureSpec.Compatible (P : PFunctor.{uA, u})
    [∀ a, MeasurableSpace (P.B a)] [probSpec : P.IsProbabilitySpec]
    [measureSpec : P.IsMeasureSpec] : Prop where
  /-- Every answer measure is the measure of the answer distribution. -/
  toMeasure_eq (a : P.A) : IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure

theorem denote_eq_toMeasure [P.IsProbabilitySpec] [IsMeasureSpec.Compatible P]
    [MeasurableSpace α] (program : FreeM P α) :
    denote program = (program.liftM IsProbabilitySpec.toPMF).toMeasure := by
  induction program with
  | pure x => simpa using (PMF.toMeasure_pure x).symm
  | lift_bind a cont ih =>
      change Measure.bind (IsMeasureSpec.toMeasure a) (fun b => denote (cont b))
          = ((IsProbabilitySpec.toPMF a).bind
              fun u => (cont u).liftM IsProbabilitySpec.toPMF).toMeasure
      rw [PMF.toMeasure_bind, IsMeasureSpec.Compatible.toMeasure_eq a]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

/-- Every `PMF`-valued interpretation induces a measure-valued one, by taking the measure of
each answer distribution.

Deliberately not an instance, matching `PFunctor.IsUniformSpec.ofFintypeInhabited`: measure
semantics stay an explicit opt-in rather than being derived silently wherever a `PMF`
interpretation happens to be in scope. Introduce it with `letI` or a local instance at a use
site; it is `IsMeasureSpec.Compatible` by `rfl`. -/
@[instance_reducible]
noncomputable def _root_.PFunctor.IsProbabilitySpec.toMeasureSpec (P : PFunctor.{uA, u})
    [∀ a, MeasurableSpace (P.B a)] [P.IsProbabilitySpec] : P.IsMeasureSpec where
  toMeasure a := (IsProbabilitySpec.toPMF a).toMeasure
  isProbabilityMeasure _ := inferInstance

instance _root_.PFunctor.IsProbabilitySpec.toMeasureSpec_compatible (P : PFunctor.{uA, u})
    [∀ a, MeasurableSpace (P.B a)] [P.IsProbabilitySpec] :
    IsMeasureSpec.Compatible P (measureSpec := IsProbabilitySpec.toMeasureSpec P) := by
  let _ := IsProbabilitySpec.toMeasureSpec P
  exact ⟨fun _ => rfl⟩

/-- Under an agreeing measure specification the free-monad fold satisfies the façade bridge, so
the generic `evalDist_apply_singleton`/`evalDist_apply_setOf`/`lintegral_evalDist` read existing
`Pr[…]` facts off the measure denotation. -/
instance [P.IsProbabilitySpec] [IsMeasureSpec.Compatible P] :
    DiscreteEvalDistCompatible (FreeM P) where
  lintegral_evalDist mx _ hg := by
    rw [evalDist_eq_denote, denote_eq_toMeasure, PMF.lintegral_toMeasure _ hg]
    exact tsum_congr fun x => by
      rw [probOutput_def]
      exact congrArg (fun r => r * _) (SPMF.liftM_apply _ x).symm

end FreeM
end PFunctor
