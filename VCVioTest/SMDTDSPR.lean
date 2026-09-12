/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR

/-!
# SM-DT-DSPR mutation canaries

These small executable games pin the security-critical parts of the rejection-on-arrival
definition: the hidden-seed phase split, the three-way challenge rejection, the `SPprob`
subtraction in the exported advantage, issue-order history, and that a rejected query is never
recorded and so leaves nothing for the guess phase to be evaluated against.
-/

public section

open OracleComp OracleSpec TweakableHash

namespace SMDTDSPRTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- Every Boolean target has a second preimage. -/
@[expose] def collidingHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

/-- No Boolean target has a second preimage. -/
@[expose] def injectiveHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m

/-- Whether a target has a second preimage depends on its tweak, not its message: at tweak
`false` the hash is constant (both messages collide), at tweak `true` it is the identity (neither
does). Needed because with `M := Bool`, a message-only-dependent `eval` can't discriminate
`SecondPreimageExists` between the two possible messages at a fixed tweak — it is necessarily
all-or-nothing per tweak. -/
@[expose] def tweakDependentHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ t m := if t then m else false

@[expose] def collidingProblem : SM_DT_DSPR_Problem Empty Seed Bool Bool Bool :=
  .standalone collidingHash 1

@[expose] def injectiveProblem : SM_DT_DSPR_Problem Empty Seed Bool Bool Bool :=
  .standalone injectiveHash 1

@[expose] def orderProblem : SM_DT_DSPR_Problem Empty Seed Bool Bool Bool :=
  .standalone tweakDependentHash 2

@[expose] def rejectProblem : SM_DT_DSPR_Problem Empty Seed Bool Bool Bool :=
  .standalone collidingHash 2

@[simp] lemma collidingProblem_seedGen : collidingProblem.th.seedGen = pure .only := rfl
@[simp] lemma injectiveProblem_seedGen : injectiveProblem.th.seedGen = pure .only := rfl
@[simp] lemma orderProblem_seedGen : orderProblem.th.seedGen = pure .only := rfl
@[simp] lemma rejectProblem_seedGen : rejectProblem.th.seedGen = pure .only := rfl

abbrev Specs (prob : SM_DT_DSPR_Problem Empty Seed Bool Bool Bool) :=
  unifSpec + (SM_DT_DSPR_challengeSpec Bool Bool Bool + collectionSpec prob.thColl)

/-- The challenge oracle answers `Option Y`, unlike the always-answering monitor sibling's
challenge oracle. -/
@[expose] def challenge (prob : SM_DT_DSPR_Problem Empty Seed Bool Bool Bool) (t m : Bool) :
    OracleComp (Specs prob) (Option Bool) :=
  liftM ((Specs prob).query (.inr (.inl (t, m))))

/-! ## Canary 1: the `SPProbability` baseline is the source probability, not adversary success -/

/-- This adversary predicts the collision that always exists for `collidingHash`. -/
@[expose] def predictCollision : SM_DT_DSPR_Adversary collidingProblem where
  State := Unit
  choose := challenge collidingProblem false false *> pure ()
  guess _ _ := pure (0, true)

/-- This adversary correctly predicts that the injective target has no second preimage. -/
@[expose] def predictNoCollision : SM_DT_DSPR_Adversary injectiveProblem where
  State := Unit
  choose := challenge injectiveProblem false false *> pure ()
  guess _ _ := pure (0, false)

private lemma run_predictCollision :
    (simulateQ (SM_DT_DSPR_oracles collidingProblem .only) predictCollision.choose).run
      ([], []) = pure ((), ([(false, false)], [])) := by
  rfl

private lemma run_predictNoCollision :
    (simulateQ (SM_DT_DSPR_oracles injectiveProblem .only) predictNoCollision.choose).run
      ([], []) = pure ((), ([(false, false)], [])) := by
  rfl

private lemma experiment_predictCollision :
    SM_DT_DSPR_Experiment predictCollision = pure true := by
  simp only [SM_DT_DSPR_Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl

private lemma baseline_predictCollision :
    SM_DT_DSPR_SPExperiment predictCollision = pure true := by
  simp only [SM_DT_DSPR_SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl

private lemma experiment_predictNoCollision :
    SM_DT_DSPR_Experiment predictNoCollision = pure true := by
  simp only [SM_DT_DSPR_Experiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl

private lemma baseline_predictNoCollision :
    SM_DT_DSPR_SPExperiment predictNoCollision = pure false := by
  simp only [SM_DT_DSPR_SPExperiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl

/-- Prediction success and `SPprob` differ on the no-second-preimage instance, while both equal
one on the collision instance. This pins the baseline subtraction: swapping `Success` and
`SPProbability` in `Advantage`'s definition would flip these two results. -/
theorem baseline_subtraction_canary :
    SM_DT_DSPR_Experiment predictCollision = pure true ∧
      SM_DT_DSPR_SPExperiment predictCollision = pure true ∧
      SM_DT_DSPR_Advantage predictCollision = 0 ∧
      SM_DT_DSPR_Experiment predictNoCollision = pure true ∧
      SM_DT_DSPR_SPExperiment predictNoCollision = pure false ∧
      SM_DT_DSPR_Advantage predictNoCollision = 1 := by
  simp [experiment_predictCollision, baseline_predictCollision, experiment_predictNoCollision,
    baseline_predictNoCollision, SM_DT_DSPR_Advantage, SM_DT_DSPR_Success,
    SM_DT_DSPR_SPProbability]

/-! ## Canary 2: two-query end-to-end order check -/

/-- Issues the two queries in a fixed order: tweak `false` (constant, collides) then tweak `true`
(identity, does not). Shared by both order-check adversaries below; they differ only in `guess`. -/
@[expose] def orderChoose : OracleComp (Specs orderProblem) (Option Bool × Option Bool) := do
  let y₁ ← challenge orderProblem false false
  let y₂ ← challenge orderProblem true true
  return (y₁, y₂)

/-- Names the first-issued query and predicts its (true) second-preimage existence. -/
@[expose] def orderCheckFirst : SM_DT_DSPR_Adversary orderProblem where
  State := Option Bool × Option Bool
  choose := orderChoose
  guess _ _ := pure (0, true)

/-- Names the second-issued query and predicts its (false) second-preimage existence. -/
@[expose] def orderCheckSecond : SM_DT_DSPR_Adversary orderProblem where
  State := Option Bool × Option Bool
  choose := orderChoose
  guess _ _ := pure (1, false)

private lemma run_orderChoose :
    (simulateQ (SM_DT_DSPR_oracles orderProblem .only) orderChoose).run ([], []) =
      pure ((some false, some true), ([(false, false), (true, true)], [])) := by
  rfl

/-- The history is in issue order: index `0` is the first-issued query (tweak `false`), index `1`
the second (tweak `true`). Mutating `qsChal ++ [tm]` to `tm :: qsChal` in the challenge oracle
breaks this `rfl` immediately, since the literal on the right no longer matches. -/
theorem two_query_order_canary :
    (simulateQ (SM_DT_DSPR_oracles orderProblem .only) orderChoose).run ([], []) =
      pure ((some false, some true), ([(false, false), (true, true)], [])) ∧
      SM_DT_DSPR_Experiment orderCheckFirst = pure true ∧
      SM_DT_DSPR_Experiment orderCheckSecond = pure true := by
  refine ⟨run_orderChoose, ?_, ?_⟩
  · simp only [SM_DT_DSPR_Experiment, orderProblem_seedGen, pure_bind]
    rw [show (simulateQ (SM_DT_DSPR_oracles orderProblem .only) orderCheckFirst.choose).run
        ([], []) = pure ((some false, some true), ([(false, false), (true, true)], [])) from
      run_orderChoose]
    rfl
  · simp only [SM_DT_DSPR_Experiment, orderProblem_seedGen, pure_bind]
    rw [show (simulateQ (SM_DT_DSPR_oracles orderProblem .only) orderCheckSecond.choose).run
        ([], []) = pure ((some false, some true), ([(false, false), (true, true)], [])) from
      run_orderChoose]
    rfl

/-! ## Canary 3: a rejected query leaves nothing to guess against -/

/-- Issues one accepted query, then a second query reusing the same tweak — rejected by
`TweakFresh`, leaving the state untouched. -/
@[expose] def rejectChoose : OracleComp (Specs rejectProblem) (Option Bool × Option Bool) := do
  let y₁ ← challenge rejectProblem false false
  let y₂ ← challenge rejectProblem false true
  return (y₁, y₂)

/-- Guesses index `1` — the slot the rejected query would have occupied had it been accepted —
predicting `true`. -/
@[expose] def reuseThenGuessSecond : SM_DT_DSPR_Adversary rejectProblem where
  State := Option Bool × Option Bool
  choose := rejectChoose
  guess _ _ := pure (1, true)

/-- Same history, opposite guessed bit at the same out-of-range index, so that "the experiment
rejects regardless of the guessed bit" is a checked fact rather than a single data point. -/
@[expose] def reuseThenGuessSecondFalse : SM_DT_DSPR_Adversary rejectProblem where
  State := Option Bool × Option Bool
  choose := rejectChoose
  guess _ _ := pure (1, false)

private lemma run_rejectChoose :
    (simulateQ (SM_DT_DSPR_oracles rejectProblem .only) rejectChoose).run ([], []) =
      pure ((some false, none), ([(false, false)], [])) := by
  rfl

/-- The reused-tweak query is answered `none` and never recorded: the history has exactly one
entry. Both guesses at index `1` — regardless of the predicted bit — find nothing there and lose.
Contrast the monitor sibling's `poison_not_rejection_canary`: there, a poisoning query is still
recorded and its real answer is reported; here the rejected query is never recorded, so there is
nothing at that index to report at all. -/
theorem rejection_not_poison_canary :
    (simulateQ (SM_DT_DSPR_oracles rejectProblem .only) rejectChoose).run ([], []) =
      pure ((some false, none), ([(false, false)], [])) ∧
      SM_DT_DSPR_Experiment reuseThenGuessSecond = pure false ∧
      SM_DT_DSPR_Experiment reuseThenGuessSecondFalse = pure false := by
  refine ⟨run_rejectChoose, ?_, ?_⟩
  · simp only [SM_DT_DSPR_Experiment, rejectProblem_seedGen, pure_bind]
    rw [show (simulateQ (SM_DT_DSPR_oracles rejectProblem .only)
        reuseThenGuessSecond.choose).run ([], []) =
        pure ((some false, none), ([(false, false)], [])) from run_rejectChoose]
    rfl
  · simp only [SM_DT_DSPR_Experiment, rejectProblem_seedGen, pure_bind]
    rw [show (simulateQ (SM_DT_DSPR_oracles rejectProblem .only)
        reuseThenGuessSecondFalse.choose).run ([], []) =
        pure ((some false, none), ([(false, false)], [])) from run_rejectChoose]
    rfl

end SMDTDSPRTest
