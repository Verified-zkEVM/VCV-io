/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.Coinductive.Responder
public import VCVio.EvalDist.FailureMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Canaries for kernel-valued semantics

Checks the subprobability closure layer, the coherent executable responder bridge, and a
kernel-native responder whose state space is genuinely continuous.
-/

public section

open MeasureTheory ProbabilityTheory OracleSpec

namespace VCVioTest.KernelSemantics

/-! ## Subprobability computation families -/

@[expose] noncomputable def lossyFamily (input : Bool) : SPMF Bool :=
  if input then pure true else failure

noncomputable def lossyKernel : Kernel Bool Bool :=
  evalDistKernelOfDiscrete lossyFamily

example : IsSubprobabilityKernel lossyKernel := by
  unfold lossyKernel
  infer_instance

example (input : Bool) : lossyKernel input Set.univ ≤ 1 := by
  unfold lossyKernel
  exact Kernel.measure_univ_le (evalDistKernelOfDiscrete lossyFamily) input

example : lossyKernel true = Measure.dirac true := by
  simp [lossyKernel, lossyFamily]

example : lossyKernel false = 0 := by
  simp [lossyKernel, lossyFamily]

example : lossyKernel true Set.univ = 1 := by
  simp [lossyKernel, lossyFamily]

example : lossyKernel false Set.univ = 0 := by
  simp [lossyKernel, lossyFamily]

/-! ## Executable responders -/

@[expose, reducible] def boolAnswerSpec : OracleSpec PUnit := fun _ => Bool

@[reducible] noncomputable def togglingResponder : ProbResponder boolAnswerSpec :=
  .ofSPMF fun _ state => pure (state, !state)

noncomputable example : togglingResponder.IsExecutable := by
  unfold togglingResponder
  infer_instance

/-- Any two executable witnesses for one responder have the same observable program. -/
example (E₁ E₂ : togglingResponder.IsExecutable) (state : Bool) :
    E₁.answerSPMF state PUnit.unit = E₂.answerSPMF state PUnit.unit :=
  ProbResponder.IsExecutable.answerSPMF_unique togglingResponder E₁ E₂ state PUnit.unit

example : IsSubprobabilityKernel
    (togglingResponder.answerKernel PUnit.unit) := by
  unfold togglingResponder
  infer_instance

example (state : Bool) :
    togglingResponder.answerKernel PUnit.unit state =
      (pure (state, !state) : SPMF (Bool × Bool)).toMeasure :=
  rfl

section DiscreteWiredCanaries

noncomputable local instance : MeasurableSpace Bool :=
  togglingResponder.instMeasurableSpaceRange PUnit.unit
local instance : DiscreteMeasurableSpace Bool := ⟨fun _ => trivial⟩

def echoStrategy : OracleStrategy Bool boolAnswerSpec :=
  PFunctor.DynSystem.mk' (fun _ => PUnit.unit) fun _ answer => answer

theorem echoUpdate_measurable : ∀ p : togglingResponder.State × Bool,
    letI := togglingResponder.instMeasurableSpaceRange
      (echoStrategy.expose p.2)
    Measurable fun q : boolAnswerSpec.Range (echoStrategy.expose p.2) ×
        togglingResponder.State =>
      (q.2, echoStrategy.update p.2 q.1) :=
  fun _ => Measurable.of_discrete

theorem echoStepFamily_measurable : Measurable
    (OracleStrategy.stepAgainstMeasure echoStrategy togglingResponder
      echoUpdate_measurable) :=
  Measurable.of_discrete

noncomputable def togglingIterKernel (n : ℕ) : Kernel (Bool × Bool) (Bool × Bool) :=
  OracleStrategy.iterateAgainstKernel echoStrategy togglingResponder
    echoUpdate_measurable echoStepFamily_measurable n

example (p : Bool × Bool) :
    OracleStrategy.iterateAgainst echoStrategy togglingResponder 0 p = pure p := rfl

example (p : Bool × Bool) :
    OracleStrategy.iterateAgainst echoStrategy togglingResponder 1 p =
      pure (!p.1, p.1) := by
  simp [OracleStrategy.iterateAgainst_succ, OracleStrategy.stepAgainst_apply,
    togglingResponder, echoStrategy]

example (p : Bool × Bool) :
    OracleStrategy.iterateAgainst echoStrategy togglingResponder 2 p =
      pure (p.1, !p.1) := by
  simp [OracleStrategy.iterateAgainst_succ, OracleStrategy.stepAgainst_apply,
    togglingResponder, echoStrategy]

example (p : Bool × Bool) : togglingIterKernel 0 p = Measure.dirac p := by
  rw [togglingIterKernel, OracleStrategy.iterateAgainstKernel_eq_toMeasure]
  simp

example (p : Bool × Bool) :
    togglingIterKernel 1 p = Measure.dirac (!p.1, p.1) := by
  rw [togglingIterKernel, OracleStrategy.iterateAgainstKernel_eq_toMeasure]
  simp [OracleStrategy.iterateAgainst_succ, OracleStrategy.stepAgainst_apply, togglingResponder,
    echoStrategy]

example (p : Bool × Bool) :
    togglingIterKernel 2 p = Measure.dirac (p.1, !p.1) := by
  rw [togglingIterKernel, OracleStrategy.iterateAgainstKernel_eq_toMeasure]
  simp [OracleStrategy.iterateAgainst_succ, OracleStrategy.stepAgainst_apply, togglingResponder,
    echoStrategy]

end DiscreteWiredCanaries

/-! ## A kernel-native continuous-state responder -/

@[expose, reducible] def realAnswerSpec : OracleSpec PUnit := fun _ => ℝ

noncomputable def realEchoResponder : ProbResponder realAnswerSpec where
  State := ℝ
  instMeasurableSpaceState := inferInstance
  instMeasurableSpaceRange := fun _ => inferInstance
  answerKernel _ := Kernel.deterministic (fun state => (state, state)) (by fun_prop)
  answerKernel_isSubprobability _ := by infer_instance

example : IsMarkovKernel (realEchoResponder.answerKernel PUnit.unit) := by
  unfold realEchoResponder
  infer_instance

example (state : ℝ) :
    realEchoResponder.answerKernel PUnit.unit state = Measure.dirac (state, state) := by
  unfold realEchoResponder
  rw [Kernel.deterministic_apply]

end VCVioTest.KernelSemantics
