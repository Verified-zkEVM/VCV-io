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
installs that fold as VCVio's primary `EvalDistSemantics` when an `IsMeasureSpec` is available and
connects it to the legacy discrete `IsProbabilitySpec` evaluator.

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

/-- Every free program denotes a subprobability measure, even before a measurability invariant is
available for its continuations. `Measure.bind_apply_le` gives exactly the one-sided bound needed
here; measurability is only needed to strengthen this to a probability-measure equality. -/
theorem denote_apply_univ_le_one [MeasurableSpace α] (program : FreeM P α) :
    denote program Set.univ ≤ 1 := by
  induction program with
  | pure _ => simp
  | lift_bind a cont ih =>
      refine (Measure.bind_apply_le _ MeasurableSet.univ).trans ?_
      calc
        (∫⁻ b, denote (cont b) Set.univ ∂IsMeasureSpec.toMeasure a) ≤
            ∫⁻ _b, 1 ∂IsMeasureSpec.toMeasure a := lintegral_mono ih
        _ = 1 := by simp

/-- The direct free-monad fold supplies the primary measure semantics whenever an
`IsMeasureSpec` is available. Its priority is above the generic finite-distribution adapter, so
installing a measure specification makes `𝒟[…]` unfold to `denote`; computations that only have
the legacy probability specification continue to use the adapter. -/
noncomputable instance (priority := 20) instEvalDistSemanticsFreeM :
    EvalDistSemantics (FreeM P) where
  denote := denote
  apply_univ_le_one := denote_apply_univ_le_one

/-- With a measure specification in scope, primary notation is definitionally the direct
free-monad measure fold. `𝒟[…]` is the public head: this is a transport lemma, not a simp rule,
so the `𝒟`-keyed laws below and in `Defs.Measure` are the ones `simp` uses. -/
theorem evalDist_eq_denote [MeasurableSpace α] (program : FreeM P α) :
    𝒟[program] = denote program := rfl

/-- A one-operation program denotes its configured answer measure. -/
@[simp]
theorem evalDist_lift (a : P.A) :
    𝒟[(FreeM.lift a : FreeM P (P.B a))] = IsMeasureSpec.toMeasure a :=
  denote_lift a

/-- An operation followed by a continuation denotes the Giry bind of its answer measure with
the denotation of the continuation. -/
@[simp]
theorem evalDist_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α) :
    𝒟[FreeM.liftBind a cont] = Measure.bind (IsMeasureSpec.toMeasure a) fun b => 𝒟[cont b] :=
  rfl

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Over a discrete-answer interface, the direct measure semantics satisfies the Giry monad
laws. -/
noncomputable instance (priority := 20) instLawfulEvalDistSemanticsFreeM :
    LawfulEvalDistSemantics (FreeM P) where
  denote_pure := denote_pure
  denote_bind := denote_bind

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
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

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
