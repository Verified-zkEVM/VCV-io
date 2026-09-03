/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity

/-!
# SM-DT-DSPR mutation canaries

These small executable games pin the security-critical parts of the definition: the hidden-seed
phase split, always-answering final-validity semantics, cap and cross-oracle poisoning, and the
`SPprob` subtraction in the exported advantage.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace SMDTDSPRFinalValidityTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- Every Boolean target has a second preimage. -/
def collidingHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

/-- No Boolean target has a second preimage. -/
def injectiveHash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def collidingProblem : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool where
  th := collidingHash
  thColl := collection
  numTargets := 1

def injectiveProblem : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool where
  th := injectiveHash
  thColl := collection
  numTargets := 1

@[simp] lemma collidingProblem_seedGen : collidingProblem.th.seedGen = pure .only := rfl

@[simp] lemma injectiveProblem_seedGen : injectiveProblem.th.seedGen = pure .only := rfl

abbrev Specs (prob : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool) :=
  unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec Bool Bool Bool +
    SourceFinalValidity.collectionSpec prob.thColl)

def challenge (prob : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool)
    (t m : Bool) : OracleComp (Specs prob) Bool :=
  liftM ((Specs prob).query (.inr (.inl (t, m))))

def collectionQuery (prob : SM_DT_DSPR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool)
    (t : Bool) (m : prob.thColl.Msg ()) : OracleComp (Specs prob) Bool :=
  liftM ((Specs prob).query (.inr (.inr ⟨(), t, m⟩)))

/-- This adversary predicts the collision that always exists for `collidingHash`. -/
def predictCollision : SM_DT_DSPR_SourceFinalValidity.Adversary collidingProblem where
  State := Unit
  choose := challenge collidingProblem false false *> pure ()
  guess _ _ := pure (0, true)

/-- This adversary correctly predicts that the injective target has no second preimage. -/
def predictNoCollision : SM_DT_DSPR_SourceFinalValidity.Adversary injectiveProblem where
  State := Unit
  choose := challenge injectiveProblem false false *> pure ()
  guess _ _ := pure (0, false)

/-- A second target query exceeds the cap but is still answered and recorded. -/
def exceedCap : SM_DT_DSPR_SourceFinalValidity.Adversary collidingProblem where
  State := Bool
  choose := do
    let _ ← challenge collidingProblem false false
    challenge collidingProblem true false
  guess answer _ := pure (if answer then 1 else 0, true)

/-- A challenge/collection tweak clash is answered by both oracles but poisons the game. -/
def clashCollection : SM_DT_DSPR_SourceFinalValidity.Adversary collidingProblem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge collidingProblem false false
    let y₂ ← collectionQuery collidingProblem false true
    return (y₁, y₂)
  guess _ _ := pure (0, true)

private lemma run_predictCollision :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles collidingProblem .only)
      predictCollision.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl

private lemma run_predictNoCollision :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles injectiveProblem .only)
      predictNoCollision.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl

private lemma run_exceedCap :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles collidingProblem .only)
      exceedCap.choose).run .initial =
      pure (false, ⟨[(false, false), (true, false)], [], false⟩) := by
  rfl

private lemma run_clashCollection :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles collidingProblem .only)
      clashCollection.choose).run .initial =
      pure ((false, true), ⟨[(false, false)], [false], false⟩) := by
  rfl

private lemma experiment_predictCollision :
    SM_DT_DSPR_SourceFinalValidity.Experiment predictCollision = pure true := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl

private lemma baseline_predictCollision :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment predictCollision = pure true := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_predictCollision]
  rfl

private lemma experiment_predictNoCollision :
    SM_DT_DSPR_SourceFinalValidity.Experiment predictNoCollision = pure true := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl

private lemma baseline_predictNoCollision :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment predictNoCollision = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, injectiveProblem_seedGen, pure_bind]
  rw [run_predictNoCollision]
  rfl

private lemma experiment_exceedCap :
    SM_DT_DSPR_SourceFinalValidity.Experiment exceedCap = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_exceedCap]
  rfl

private lemma baseline_exceedCap :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment exceedCap = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_exceedCap]
  rfl

private lemma experiment_clashCollection :
    SM_DT_DSPR_SourceFinalValidity.Experiment clashCollection = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, collidingProblem_seedGen, pure_bind]
  rw [run_clashCollection]
  rfl

private lemma baseline_clashCollection :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment clashCollection = pure false := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, collidingProblem_seedGen, pure_bind]
  rw [run_clashCollection]
  rfl

/-- Prediction success and `SPprob` differ on the no-second-preimage instance, while both equal one
on the collision instance. This pins the baseline subtraction: the corresponding advantages are
respectively one and zero. -/
theorem baseline_subtraction_canary :
    SM_DT_DSPR_SourceFinalValidity.Experiment predictCollision = pure true ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment predictCollision = pure true ∧
      SM_DT_DSPR_SourceFinalValidity.Advantage predictCollision = 0 ∧
      SM_DT_DSPR_SourceFinalValidity.Experiment predictNoCollision = pure true ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment predictNoCollision = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.Advantage predictNoCollision = 1 := by
  simp [experiment_predictCollision, baseline_predictCollision, experiment_predictNoCollision,
    baseline_predictNoCollision, SM_DT_DSPR_SourceFinalValidity.Advantage,
    SM_DT_DSPR_SourceFinalValidity.Success, SM_DT_DSPR_SourceFinalValidity.SPProbability]

/-- Invalid queries are not rejected: their concrete answers are visible in the private state, all
queries are recorded, and only the sticky final-validity bit makes both experiments lose. -/
theorem poison_not_rejection_canary :
    SM_DT_DSPR_SourceFinalValidity.Experiment exceedCap = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment exceedCap = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.Experiment clashCollection = pure false ∧
      SM_DT_DSPR_SourceFinalValidity.SPExperiment clashCollection = pure false := by
  exact ⟨experiment_exceedCap, baseline_exceedCap, experiment_clashCollection,
    baseline_clashCollection⟩

section RunLevelInvariant

open SM_DT_DSPR_SourceFinalValidity

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate holds. -/
private lemma valid_of_run {prob : Problem Unit Seed Bool Bool Bool} {adv : Adversary prob}
    {ps : adv.State} {gs : State Bool Bool}
    (hrun : (simulateQ (oracles prob .only) adv.choose).run .initial = pure (ps, gs))
    (hvalid : gs.valid = true) :
    ∀ z ∈ support ((simulateQ (oracles prob .only) adv.choose).run .initial),
      SourceFinalValidity.Valid prob.numTargets Prod.fst z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate fails. -/
private lemma not_valid_of_run {prob : Problem Unit Seed Bool Bool Bool} {adv : Adversary prob}
    {ps : adv.State} {gs : State Bool Bool}
    (hrun : (simulateQ (oracles prob .only) adv.choose).run .initial = pure (ps, gs))
    (hvalid : gs.valid = false) :
    ∀ z ∈ support ((simulateQ (oracles prob .only) adv.choose).run .initial),
      ¬ SourceFinalValidity.Valid prob.numTargets Prod.fst z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- The lifted monitor invariant decides the final predicate correctly on every canary transcript.
`exceedCap` isolates the target-cap conjunct: `collidingProblem` allows one target and the two
committed tweaks are distinct and unused by the collection oracle, so the cap is the only conjunct
that fails. `clashCollection` isolates target/collection disjointness. -/
theorem reachable_valid_decides_canary :
    (∀ z ∈ support
          ((simulateQ (oracles collidingProblem .only) predictCollision.choose).run .initial),
        SourceFinalValidity.Valid collidingProblem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles injectiveProblem .only) predictNoCollision.choose).run .initial),
        SourceFinalValidity.Valid injectiveProblem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles collidingProblem .only) exceedCap.choose).run .initial),
        ¬ SourceFinalValidity.Valid collidingProblem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles collidingProblem .only) clashCollection.choose).run .initial),
        ¬ SourceFinalValidity.Valid collidingProblem.numTargets Prod.fst z.2) :=
  ⟨valid_of_run run_predictCollision rfl, valid_of_run run_predictNoCollision rfl,
    not_valid_of_run run_exceedCap rfl, not_valid_of_run run_clashCollection rfl⟩

end RunLevelInvariant

/-- The phase types themselves pin seed/oracle access: `choose` gets the oracle bundle but no seed,
whereas `guess` gets the seed but has type `ProbComp` and therefore no challenge oracle. -/
example : OracleComp (Specs collidingProblem) predictCollision.State :=
  predictCollision.choose

example : predictCollision.State → Seed → ProbComp (ℕ × Bool) := predictCollision.guess

end SMDTDSPRFinalValidityTest
