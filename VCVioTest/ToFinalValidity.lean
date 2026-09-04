/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.ToFinalValidity

/-!
# Tweak-discipline bridge canaries

One transcript separates the two presentations: take a target, then query the collection oracle at
that same tweak. The rejection-on-arrival oracles refuse the second query and leave the state
untouched, so the earlier target is still there to be used and the adversary **wins**. The monitor
answers that query and poisons final validity, so the same transcript run naively **loses** — the
sibling test modules for the two families pin both outcomes, and both are correct for their own
game.

This file pins that the conversion resolves the disagreement in the winning direction, for each of
the four games that have both presentations. The wrapper declines to forward the poisoning query and
synthesises the `none` its counterpart received, so the converted adversary wins where the naive one
would not. A conversion that merely renamed the phases would inherit the losing outcome.

Every fixture is chosen so the experiments reduce to a closed `pure`: the seed type and the SM-PRE
message subspace are one-element, and the SM-UD input and output distributions are `pure`. The
SM-TCR and SM-DSPR challenge oracles draw nothing to begin with.

The SM-UD adversary additionally reads the challenge answer, so its canary separates the two worlds
as well as pinning the refusal: it is the one game here whose advantage is a gap between two
experiments rather than a single success probability.
-/

public section

open OracleComp OracleSpec TweakableHash

namespace ToFinalValidityTest

/-! ## Shared fixtures -/

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

inductive Input
  | only

instance : SampleableType Input where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

/-- A constant tweakable hash. Every message collides at every tweak, so the adversary wins exactly
when the game lets it keep its target. -/
@[expose] def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

@[expose] def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ _ := false

/-! ## SM-DT-TCR -/

@[expose] def problem : SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec + (SM_DT_TCR_challengeSpec Bool Bool Bool +
  collectionSpec problem.thColl)

@[expose] def challenge (tm : Bool × Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl tm)))

@[expose] def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) :
    OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, then query the collection at that same tweak. The rejection-on-arrival oracles
refuse the second query, and the adversary branches on that refusal to forge against the target it
already holds. -/
@[expose] def challengeThenCollection : SM_DT_TCR_Adversary problem where
  State := Option Bool
  choose := do
    let _ ← challenge (false, false)
    collectionQuery false false
  forge answer _ := match answer with
    | none => pure (0, true)
    | some _ => pure (0, false)

/-- The rejection-on-arrival game: the clash is refused and the adversary wins. -/
theorem experiment_challengeThenCollection :
    SM_DT_TCR_Experiment challengeThenCollection = pure true := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_TCR_oracles problem .only) challengeThenCollection.choose).run
      ([], []) = pure (none, ([(false, false)], [])) from rfl]
  rfl

/-- The converted adversary wins the source-final-validity game: the wrapper suppresses the
poisoning collection query, so the monitor is still valid at the end and the collision counts. -/
theorem toSourceFinalValidity_suppresses_poison_canary :
    SM_DT_TCR_SourceFinalValidity.Experiment
        challengeThenCollection.toSourceFinalValidity = pure true := by
  rw [SM_DT_TCR_experiment_toSourceFinalValidity, experiment_challengeThenCollection]

/-- The conversion is advantage-preserving on this adversary, at advantage one. -/
theorem advantage_challengeThenCollection_canary :
    SM_DT_TCR_Advantage challengeThenCollection = 1 ∧
      SM_DT_TCR_SourceFinalValidity.Advantage
        challengeThenCollection.toSourceFinalValidity = 1 := by
  refine ⟨?_, ?_⟩ <;>
    simp [SM_DT_TCR_Advantage, SM_DT_TCR_SourceFinalValidity.Advantage,
      experiment_challengeThenCollection, toSourceFinalValidity_suppresses_poison_canary]

/-! ## SM-DT-PRE

The same transcript at the game whose challenge oracle draws its own message, over a one-element
subspace so the draw reduces. -/

@[expose] def preProblem : SM_DT_PRE_Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb := fun _ => false
  emb_injective a b _ := by cases a; cases b; rfl
  thColl := collection
  numTargets := 1

@[simp] lemma preProblem_seedGen : preProblem.th.seedGen = pure .only := rfl

abbrev PreSpecs := unifSpec + (SM_DT_PRE_challengeSpec Bool Bool +
  collectionSpec preProblem.thColl)

@[expose] def preChallenge (t : Bool) : OracleComp PreSpecs (Option Bool) :=
  liftM (PreSpecs.query (.inr (.inl t)))

@[expose] def preCollectionQuery (t : Bool) (m : preProblem.thColl.Msg ()) :
    OracleComp PreSpecs (Option Bool) :=
  liftM (PreSpecs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, then clash with it on the collection oracle. -/
@[expose] def preChallengeThenCollection : SM_DT_PRE_Adversary preProblem where
  State := Option Bool
  choose := do
    let _ ← preChallenge false
    preCollectionQuery false false
  invert answer _ := match answer with
    | none => pure (0, .only)
    | some _ => pure (1, .only)

/-- End-to-end SM-PRE: the clash is refused, and the inversion at the recorded target wins. -/
theorem pre_experiment_challengeThenCollection :
    SM_DT_PRE_Experiment preChallengeThenCollection = pure true := by
  simp only [SM_DT_PRE_Experiment, preProblem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_PRE_oracles preProblem .only) preChallengeThenCollection.choose).run
      ([], []) = pure (none, ([(false, Input.only)], [])) from rfl]
  rfl

/-- The SM-PRE conversion carries that win across to the monitor game. -/
theorem pre_toSourceFinalValidity_suppresses_poison_canary :
    SM_DT_PRE_SourceFinalValidity.Experiment
        preChallengeThenCollection.toSourceFinalValidity = pure true := by
  rw [SM_DT_PRE_experiment_toSourceFinalValidity, pre_experiment_challengeThenCollection]

/-! ## SM-DT-UD

The adversary keeps the challenge answer as well as the refusal, so one transcript pins both facts
at once: the collection clash is refused in either world, and the answer still separates them,
`hash` being constantly `false` while `outputGen` is `pure true`. -/

@[expose] def udProblem : SM_DT_UD_Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb := fun _ => false
  emb_injective a b _ := by cases a; cases b; rfl
  inputGen := pure .only
  outputGen := pure true
  thColl := collection
  numTargets := 1

@[simp] lemma udProblem_seedGen : udProblem.th.seedGen = pure .only := rfl

abbrev UdSpecs := unifSpec + (SM_DT_UD_challengeSpec Bool Bool +
  collectionSpec udProblem.thColl)

@[expose] def udChallenge (t : Bool) : OracleComp UdSpecs (Option Bool) :=
  liftM (UdSpecs.query (.inr (.inl t)))

@[expose] def udCollectionQuery (t : Bool) (m : udProblem.thColl.Msg ()) :
    OracleComp UdSpecs (Option Bool) :=
  liftM (UdSpecs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, clash with it on the collection oracle, and report the challenge answer together
with the refusal. -/
@[expose] def udChallengeThenCollection : SM_DT_UD_Adversary udProblem where
  State := Option Bool × Option Bool
  pick := do
    let y ← udChallenge false
    let c ← udCollectionQuery false false
    return (y, c)
  distinguish state _ := pure (state.2 == none && state.1 == some false)

/-- The real world answers with a hash image, which is `false`; the clash is refused. -/
theorem ud_experiment_real :
    SM_DT_UD_Experiment .real udChallengeThenCollection = pure true := by
  simp only [SM_DT_UD_Experiment, udProblem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_UD_oracles .real udProblem .only)
      udChallengeThenCollection.pick).run ([], []) =
        pure ((some false, none), ([false], [])) from rfl]
  rfl

/-- The ideal world answers from `outputGen`, which is `true`, so the same adversary loses. -/
theorem ud_experiment_ideal :
    SM_DT_UD_Experiment .ideal udChallengeThenCollection = pure false := by
  simp only [SM_DT_UD_Experiment, udProblem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_UD_oracles .ideal udProblem .only)
      udChallengeThenCollection.pick).run ([], []) =
        pure ((some true, none), ([false], [])) from rfl]
  rfl

/-- The SM-UD conversion carries both worlds across: the wrapper suppresses the poisoning query in
each, so neither outcome moves. -/
theorem ud_toSourceFinalValidity_suppresses_poison_canary :
    SM_DT_UD_SourceFinalValidity.Experiment .real
        udChallengeThenCollection.toSourceFinalValidity = pure true ∧
      SM_DT_UD_SourceFinalValidity.Experiment .ideal
        udChallengeThenCollection.toSourceFinalValidity = pure false := by
  refine ⟨?_, ?_⟩
  · rw [← SM_DT_UD_World.toSourceFinalValidity_real,
      SM_DT_UD_experiment_toSourceFinalValidity, ud_experiment_real]
  · rw [← SM_DT_UD_World.toSourceFinalValidity_ideal,
      SM_DT_UD_experiment_toSourceFinalValidity, ud_experiment_ideal]

/-- The signed gap survives the conversion with its orientation: real minus ideal is `1`, not
`-1`. -/
theorem ud_directedAdvantage_canary :
    SM_DT_UD_DirectedAdvantage udChallengeThenCollection = 1 ∧
      SM_DT_UD_SourceFinalValidity.DirectedAdvantage
        udChallengeThenCollection.toSourceFinalValidity = 1 := by
  refine ⟨?_, ?_⟩
  · simp [SM_DT_UD_DirectedAdvantage, SM_DT_UD_RealSuccess, SM_DT_UD_IdealSuccess,
      ud_experiment_real, ud_experiment_ideal]
  · rw [← SM_DT_UD_directedAdvantage_toSourceFinalValidity]
    simp [SM_DT_UD_DirectedAdvantage, SM_DT_UD_RealSuccess, SM_DT_UD_IdealSuccess,
      ud_experiment_real, ud_experiment_ideal]

/-! ## SM-DT-DSPR

The same transcript at the game whose winning condition is a prediction against a baseline. `hash`
is constant, so every target has a second preimage and the correct prediction is `true`; both the
prediction experiment and the `SPprob` baseline accept, and the advantage is the truncated
difference of two ones. -/

@[expose] def dsprProblem : SM_DT_DSPR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

@[simp] lemma dsprProblem_seedGen : dsprProblem.th.seedGen = pure .only := rfl

abbrev DsprSpecs := unifSpec + (SM_DT_DSPR_challengeSpec Bool Bool Bool +
  collectionSpec dsprProblem.thColl)

@[expose] def dsprChallenge (tm : Bool × Bool) : OracleComp DsprSpecs (Option Bool) :=
  liftM (DsprSpecs.query (.inr (.inl tm)))

@[expose] def dsprCollectionQuery (t : Bool) (m : dsprProblem.thColl.Msg ()) :
    OracleComp DsprSpecs (Option Bool) :=
  liftM (DsprSpecs.query (.inr (.inr ⟨(), t, m⟩)))

/-- Take a target, clash with it on the collection oracle, and predict on the refusal. -/
@[expose] def dsprChallengeThenCollection : SM_DT_DSPR_Adversary dsprProblem where
  State := Option Bool
  choose := do
    let _ ← dsprChallenge (false, false)
    dsprCollectionQuery false false
  guess answer _ := match answer with
    | none => pure (0, true)
    | some _ => pure (0, false)

/-- The rejection-on-arrival prediction game: the clash is refused and the prediction is right. -/
theorem dspr_experiment_challengeThenCollection :
    SM_DT_DSPR_Experiment dsprChallengeThenCollection = pure true := by
  simp only [SM_DT_DSPR_Experiment, dsprProblem_seedGen, pure_bind]
  rw [show (simulateQ (SM_DT_DSPR_oracles dsprProblem .only)
      dsprChallengeThenCollection.choose).run ([], []) =
        pure (none, ([(false, false)], [])) from rfl]
  rfl

/-- The SM-DSPR conversion carries the prediction across to the monitor game. -/
theorem dspr_toSourceFinalValidity_suppresses_poison_canary :
    SM_DT_DSPR_SourceFinalValidity.Experiment
        dsprChallengeThenCollection.toSourceFinalValidity = pure true := by
  rw [SM_DT_DSPR_experiment_toSourceFinalValidity, dspr_experiment_challengeThenCollection]

end ToFinalValidityTest
