/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD

/-!
# SM-DT-UD rejection-on-arrival canaries

These executable games pin real/ideal separation and its orientation, each of the three refusal
causes separately, the fact that a refused query draws nothing in either world, that repeated
collection-only tweaks are accepted, the issue order of the challenge history at two queries in
both worlds, and the game's behaviour at a strict message subspace.

Every adversary here wins by *observing a refusal*: its distinguishing bit tests the second answer
against `none`. That polarity is what makes the refusal canaries bite — dropping a refusal cause
turns the toy game into a loss rather than leaving it silently true. It is also the opposite of the
sticky-monitor presentation's polarity, where the analogous transcript is answered and loses
through final validity instead.
-/

public section

open OracleComp OracleSpec TweakableHash

namespace SMDTUDTest

/-! ## Fixtures -/

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- Real challenges are always `false`; ideal challenges are always `true`. -/
@[expose] def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m

@[expose] def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

/-- The one-target problem: enough room for a single challenge, so a second challenge is refused by
the cap. -/
@[expose] def problem : SM_DT_UD_Problem Unit Seed Bool Bool Bool Bool where
  th := hash
  emb := id
  emb_injective := Function.injective_id
  inputGen := pure false
  outputGen := pure true
  thColl := collection
  numTargets := 1

/-- The two-target problem. Raising the cap is what isolates the duplicate-target refusal from the
cap refusal, and it is what lets two challenges be accepted for the order check. -/
@[expose] def capacityProblem : SM_DT_UD_Problem Unit Seed Bool Bool Bool Bool where
  th := hash
  emb := id
  emb_injective := Function.injective_id
  inputGen := pure false
  outputGen := pure true
  thColl := collection
  numTargets := 2

/-- The zero-target problem, whose generators are genuine uniform samples. Every challenge is
refused, so a `pure` right-hand side witnesses that refusal consumes no randomness: hoisting the
draw above the refusal test would leave a `$ᵗ Bool` bind in both worlds. -/
@[expose] def capZeroProblem : SM_DT_UD_Problem Unit Seed Bool Bool Bool Bool where
  th := hash
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ Bool
  outputGen := $ᵗ Bool
  thColl := collection
  numTargets := 0

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

@[simp] lemma capacityProblem_seedGen : capacityProblem.th.seedGen = pure .only := rfl

@[simp] lemma capZeroProblem_seedGen : capZeroProblem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec +
  (SM_DT_UD_challengeSpec Bool Bool + collectionSpec collection)

@[expose] def challenge (t : Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl t)))

@[expose] def collectionQuery (t : Bool) (m : collection.Msg ()) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

/-! ## Adversaries -/

/-- One accepted challenge, answered `some false` in the real world and `some true` in the ideal
world. Wins in the real world. -/
@[expose] def separate : SM_DT_UD_Adversary problem where
  State := Option Bool
  pick := challenge false
  distinguish y _ := pure (y == some false)

/-- The same transcript, with the guess inverted. Wins in the ideal world, so the signed advantage
is negative. -/
@[expose] def separateReverse : SM_DT_UD_Adversary problem where
  State := Option Bool
  pick := challenge false
  distinguish y _ := pure (y == some true)

/-- A second challenge at a fresh tweak, over the one-target cap. -/
@[expose] def exceedCap : SM_DT_UD_Adversary problem where
  State := Option Bool × Option Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge true
    return (y₁, y₂)
  distinguish y _ := pure (y.2 == none)

/-- A second challenge at the tweak the first one spent, below the two-target cap. -/
@[expose] def duplicateTarget : SM_DT_UD_Adversary capacityProblem where
  State := Option Bool × Option Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge false
    return (y₁, y₂)
  distinguish y _ := pure (y.2 == none)

/-- A collection query at a tweak the challenge oracle has reserved. -/
@[expose] def challengeThenCollection : SM_DT_UD_Adversary problem where
  State := Option Bool × Option Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  distinguish y _ := pure (y.2 == none)

/-- A challenge at a tweak already spent on the collection oracle. -/
@[expose] def collectionThenChallenge : SM_DT_UD_Adversary problem where
  State := Option Bool × Option Bool
  pick := do
    let y₁ ← collectionQuery false true
    let y₂ ← challenge false
    return (y₁, y₂)
  distinguish y _ := pure (y.2 == none)

/-- The same collection tweak twice, with no challenge reserving it. Both queries are answered. -/
@[expose] def repeatCollection : SM_DT_UD_Adversary problem where
  State := Option Bool × Option Bool
  pick := do
    let y₁ ← collectionQuery false true
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  distinguish y _ := pure (y.1 == some true && y.2 == some true)

/-- Two accepted challenges at distinct tweaks, below the two-target cap. -/
@[expose] def orderProbe : SM_DT_UD_Adversary capacityProblem where
  State := Option Bool × Option Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge true
    return (y₁, y₂)
  distinguish y _ := pure (y.2 == some false)

/-- One refused challenge and nothing else, at genuinely random generators. -/
@[expose] def refusedOnly : SM_DT_UD_Adversary capZeroProblem where
  State := Option Bool
  pick := challenge false
  distinguish y _ := pure (y == none)

/-! ## Transcripts -/

private lemma run_separate_real :
    (simulateQ (SM_DT_UD_oracles .real problem .only) separate.pick).run ([], []) =
      pure (some false, ([false], [])) := by
  rfl

private lemma run_separate_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal problem .only) separate.pick).run ([], []) =
      pure (some true, ([false], [])) := by
  rfl

private lemma run_separateReverse_real :
    (simulateQ (SM_DT_UD_oracles .real problem .only) separateReverse.pick).run ([], []) =
      pure (some false, ([false], [])) := by
  rfl

private lemma run_separateReverse_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal problem .only) separateReverse.pick).run ([], []) =
      pure (some true, ([false], [])) := by
  rfl

private lemma run_exceedCap_real :
    (simulateQ (SM_DT_UD_oracles .real problem .only) exceedCap.pick).run ([], []) =
      pure ((some false, none), ([false], [])) := by
  rfl

private lemma run_exceedCap_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal problem .only) exceedCap.pick).run ([], []) =
      pure ((some true, none), ([false], [])) := by
  rfl

private lemma run_duplicateTarget_real :
    (simulateQ (SM_DT_UD_oracles .real capacityProblem .only) duplicateTarget.pick).run ([], []) =
      pure ((some false, none), ([false], [])) := by
  rfl

private lemma run_duplicateTarget_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal capacityProblem .only) duplicateTarget.pick).run ([], []) =
      pure ((some true, none), ([false], [])) := by
  rfl

private lemma run_challengeThenCollection_real :
    (simulateQ (SM_DT_UD_oracles .real problem .only)
      challengeThenCollection.pick).run ([], []) =
      pure ((some false, none), ([false], [])) := by
  rfl

private lemma run_challengeThenCollection_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal problem .only)
      challengeThenCollection.pick).run ([], []) =
      pure ((some true, none), ([false], [])) := by
  rfl

private lemma run_collectionThenChallenge_real :
    (simulateQ (SM_DT_UD_oracles .real problem .only)
      collectionThenChallenge.pick).run ([], []) =
      pure ((some true, none), ([], [false])) := by
  rfl

private lemma run_collectionThenChallenge_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal problem .only)
      collectionThenChallenge.pick).run ([], []) =
      pure ((some true, none), ([], [false])) := by
  rfl

private lemma run_repeatCollection_real :
    (simulateQ (SM_DT_UD_oracles .real problem .only) repeatCollection.pick).run ([], []) =
      pure ((some true, some true), ([], [false, false])) := by
  rfl

private lemma run_repeatCollection_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal problem .only) repeatCollection.pick).run ([], []) =
      pure ((some true, some true), ([], [false, false])) := by
  rfl

private lemma run_orderProbe_real :
    (simulateQ (SM_DT_UD_oracles .real capacityProblem .only) orderProbe.pick).run ([], []) =
      pure ((some false, some false), ([false, true], [])) := by
  rfl

private lemma run_orderProbe_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal capacityProblem .only) orderProbe.pick).run ([], []) =
      pure ((some true, some true), ([false, true], [])) := by
  rfl

private lemma run_refusedOnly_real :
    (simulateQ (SM_DT_UD_oracles .real capZeroProblem .only) refusedOnly.pick).run ([], []) =
      pure (none, ([], [])) := by
  rfl

private lemma run_refusedOnly_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal capZeroProblem .only) refusedOnly.pick).run ([], []) =
      pure (none, ([], [])) := by
  rfl

/-! ## Experiments -/

private lemma experiment_separate_real :
    SM_DT_UD_Experiment .real separate = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_separate_real]
  rfl

private lemma experiment_separate_ideal :
    SM_DT_UD_Experiment .ideal separate = pure false := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_separate_ideal]
  rfl

private lemma experiment_separateReverse_real :
    SM_DT_UD_Experiment .real separateReverse = pure false := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_separateReverse_real]
  rfl

private lemma experiment_separateReverse_ideal :
    SM_DT_UD_Experiment .ideal separateReverse = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_separateReverse_ideal]
  rfl

private lemma experiment_exceedCap_real :
    SM_DT_UD_Experiment .real exceedCap = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_exceedCap_real]
  rfl

private lemma experiment_exceedCap_ideal :
    SM_DT_UD_Experiment .ideal exceedCap = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_exceedCap_ideal]
  rfl

private lemma experiment_duplicateTarget_real :
    SM_DT_UD_Experiment .real duplicateTarget = pure true := by
  simp only [SM_DT_UD_Experiment, capacityProblem_seedGen, pure_bind]
  rw [run_duplicateTarget_real]
  rfl

private lemma experiment_duplicateTarget_ideal :
    SM_DT_UD_Experiment .ideal duplicateTarget = pure true := by
  simp only [SM_DT_UD_Experiment, capacityProblem_seedGen, pure_bind]
  rw [run_duplicateTarget_ideal]
  rfl

private lemma experiment_challengeThenCollection_real :
    SM_DT_UD_Experiment .real challengeThenCollection = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_challengeThenCollection_real]
  rfl

private lemma experiment_challengeThenCollection_ideal :
    SM_DT_UD_Experiment .ideal challengeThenCollection = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_challengeThenCollection_ideal]
  rfl

private lemma experiment_collectionThenChallenge_real :
    SM_DT_UD_Experiment .real collectionThenChallenge = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge_real]
  rfl

private lemma experiment_collectionThenChallenge_ideal :
    SM_DT_UD_Experiment .ideal collectionThenChallenge = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge_ideal]
  rfl

private lemma experiment_repeatCollection_real :
    SM_DT_UD_Experiment .real repeatCollection = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_repeatCollection_real]
  rfl

private lemma experiment_repeatCollection_ideal :
    SM_DT_UD_Experiment .ideal repeatCollection = pure true := by
  simp only [SM_DT_UD_Experiment, problem_seedGen, pure_bind]
  rw [run_repeatCollection_ideal]
  rfl

private lemma experiment_refusedOnly_real :
    SM_DT_UD_Experiment .real refusedOnly = pure true := by
  simp only [SM_DT_UD_Experiment, capZeroProblem_seedGen, pure_bind]
  rw [run_refusedOnly_real]
  rfl

private lemma experiment_refusedOnly_ideal :
    SM_DT_UD_Experiment .ideal refusedOnly = pure true := by
  simp only [SM_DT_UD_Experiment, capZeroProblem_seedGen, pure_bind]
  rw [run_refusedOnly_ideal]
  rfl

/-! ## The canaries -/

/-- The two worlds are distinguishable, and the four quantities agree on which way. -/
theorem real_ideal_separation_canary :
    SM_DT_UD_Experiment .real separate = pure true ∧
      SM_DT_UD_Experiment .ideal separate = pure false ∧
      SM_DT_UD_RealSuccess separate = 1 ∧
      SM_DT_UD_IdealSuccess separate = 0 ∧
      SM_DT_UD_DirectedAdvantage separate = 1 ∧
      SM_DT_UD_AbsoluteAdvantage separate = 1 := by
  simp [SM_DT_UD_RealSuccess, SM_DT_UD_IdealSuccess, SM_DT_UD_DirectedAdvantage,
    SM_DT_UD_AbsoluteAdvantage, ENNReal.absDiff, experiment_separate_real,
    experiment_separate_ideal]

/-- Swapping the guess flips the sign of the directed advantage while leaving the absolute one
alone. A symmetric-only API would fail to pin this orientation. -/
theorem orientation_reverse_canary :
    SM_DT_UD_Experiment .real separateReverse = pure false ∧
      SM_DT_UD_Experiment .ideal separateReverse = pure true ∧
      SM_DT_UD_RealSuccess separateReverse = 0 ∧
      SM_DT_UD_IdealSuccess separateReverse = 1 ∧
      SM_DT_UD_DirectedAdvantage separateReverse = -1 ∧
      SM_DT_UD_AbsoluteAdvantage separateReverse = 1 := by
  simp [SM_DT_UD_RealSuccess, SM_DT_UD_IdealSuccess, SM_DT_UD_DirectedAdvantage,
    SM_DT_UD_AbsoluteAdvantage, ENNReal.absDiff, experiment_separateReverse_real,
    experiment_separateReverse_ideal]

/-- All three refusal causes fire, separately and in both worlds: the target cap, a duplicate
target tweak below the cap, and a clash with the collection oracle in either query order. Each
adversary wins by seeing `none`, so dropping a cause makes the corresponding conjunct false rather
than leaving it silently true. -/
theorem rejection_on_arrival_canary :
    SM_DT_UD_Experiment .real exceedCap = pure true ∧
      SM_DT_UD_Experiment .ideal exceedCap = pure true ∧
      SM_DT_UD_Experiment .real duplicateTarget = pure true ∧
      SM_DT_UD_Experiment .ideal duplicateTarget = pure true ∧
      SM_DT_UD_Experiment .real challengeThenCollection = pure true ∧
      SM_DT_UD_Experiment .ideal challengeThenCollection = pure true ∧
      SM_DT_UD_Experiment .real collectionThenChallenge = pure true ∧
      SM_DT_UD_Experiment .ideal collectionThenChallenge = pure true :=
  ⟨experiment_exceedCap_real, experiment_exceedCap_ideal,
    experiment_duplicateTarget_real, experiment_duplicateTarget_ideal,
    experiment_challengeThenCollection_real, experiment_challengeThenCollection_ideal,
    experiment_collectionThenChallenge_real, experiment_collectionThenChallenge_ideal⟩

/-- A refused query draws nothing, in both worlds, at generators that are genuine uniform samples.

`capZeroProblem` draws from `$ᵗ Bool` in both worlds, so a right-hand side of `pure` says the
refusing branch never reached either generator: had the draw been hoisted above the refusal test,
both runs would carry a `$ᵗ Bool` bind and neither equation would hold. The zero advantage is the
consequence that matters — an adversary that only ever gets refused learns nothing, in either
orientation. -/
theorem refusal_draws_nothing_canary :
    (simulateQ (SM_DT_UD_oracles .real capZeroProblem .only) refusedOnly.pick).run ([], []) =
        pure (none, ([], [])) ∧
      (simulateQ (SM_DT_UD_oracles .ideal capZeroProblem .only) refusedOnly.pick).run ([], []) =
        pure (none, ([], [])) ∧
      SM_DT_UD_Experiment .real refusedOnly = pure true ∧
      SM_DT_UD_Experiment .ideal refusedOnly = pure true ∧
      SM_DT_UD_DirectedAdvantage refusedOnly = 0 ∧
      SM_DT_UD_AbsoluteAdvantage refusedOnly = 0 := by
  refine ⟨run_refusedOnly_real, run_refusedOnly_ideal, experiment_refusedOnly_real,
    experiment_refusedOnly_ideal, ?_, ?_⟩ <;>
  simp [SM_DT_UD_RealSuccess, SM_DT_UD_IdealSuccess, SM_DT_UD_DirectedAdvantage,
    SM_DT_UD_AbsoluteAdvantage, ENNReal.absDiff, experiment_refusedOnly_real,
    experiment_refusedOnly_ideal]

/-- Repeating a collection-only tweak is accepted in both worlds, and both occurrences are
recorded. This fails if collection tweaks are wrongly required to be distinct. -/
theorem repeated_collection_allowed_canary :
    (simulateQ (SM_DT_UD_oracles .real problem .only) repeatCollection.pick).run ([], []) =
        pure ((some true, some true), ([], [false, false])) ∧
      SM_DT_UD_Experiment .real repeatCollection = pure true ∧
      SM_DT_UD_Experiment .ideal repeatCollection = pure true :=
  ⟨run_repeatCollection_real, experiment_repeatCollection_real,
    experiment_repeatCollection_ideal⟩

/-- Two accepted challenges are recorded in issue order, in both worlds. Appending is what makes
this hold; consing would give `[true, false]` and misattribute every target index, while leaving
every single-query transcript unchanged. -/
theorem history_in_issue_order_canary :
    (simulateQ (SM_DT_UD_oracles .real capacityProblem .only) orderProbe.pick).run ([], []) =
        pure ((some false, some false), ([false, true], [])) ∧
      (simulateQ (SM_DT_UD_oracles .ideal capacityProblem .only) orderProbe.pick).run ([], []) =
        pure ((some true, some true), ([false, true], [])) :=
  ⟨run_orderProbe_real, run_orderProbe_ideal⟩

/-! ## A proper subspace

`problem` above runs at `M' = M` with `emb := id`, where `emb` is unobservable. The declarations
below run the same game at a strict subspace `M' ⊊ M`.
-/

/-- A one-element type standing in for a strict subspace of the message space `Bool`. -/
inductive Input
  | only

instance : SampleableType Input where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

/-- Inputs are drawn uniformly from a one-element subspace whose embedding is `true`. Since
`hash.eval` is the identity, the real world's answer is exactly the element of `M` that `emb`
selects, so replacing `emb` changes the observable transcript. -/
@[expose] def subspaceProblem : SM_DT_UD_Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb := fun _ => true
  emb_injective a b _ := by cases a; cases b; rfl
  inputGen := $ᵗ Input
  outputGen := pure false
  thColl := collection
  numTargets := 1

@[simp] lemma subspaceProblem_seedGen : subspaceProblem.th.seedGen = pure .only := rfl

/-- Returning the challenge answer verbatim exposes which element of `M` was hashed. -/
@[expose] def subspaceProbe : SM_DT_UD_Adversary subspaceProblem where
  State := Option Bool
  pick := challenge false
  distinguish y _ := pure (y == some true)

private lemma run_subspaceProbe_real :
    (simulateQ (SM_DT_UD_oracles .real subspaceProblem .only) subspaceProbe.pick).run ([], []) =
      pure (some true, ([false], [])) := by
  rfl

private lemma run_subspaceProbe_ideal :
    (simulateQ (SM_DT_UD_oracles .ideal subspaceProblem .only) subspaceProbe.pick).run ([], []) =
      pure (some false, ([false], [])) := by
  rfl

private lemma experiment_subspaceProbe_real :
    SM_DT_UD_Experiment .real subspaceProbe = pure true := by
  simp only [SM_DT_UD_Experiment, subspaceProblem_seedGen, pure_bind]
  rw [run_subspaceProbe_real]
  rfl

private lemma experiment_subspaceProbe_ideal :
    SM_DT_UD_Experiment .ideal subspaceProbe = pure false := by
  simp only [SM_DT_UD_Experiment, subspaceProblem_seedGen, pure_bind]
  rw [run_subspaceProbe_ideal]
  rfl

/-- The real world hashes `emb x`, not `x`, and the subspace's uniform generator is what
`HasUniformInputs` asks for. Replacing `emb` by a different map into `M` changes the transcript, so
the field is observable rather than decorative here. -/
theorem subspace_emb_applied_canary :
    subspaceProblem.HasUniformInputs ∧
      SM_DT_UD_Experiment .real subspaceProbe = pure true ∧
      SM_DT_UD_Experiment .ideal subspaceProbe = pure false ∧
      SM_DT_UD_DirectedAdvantage subspaceProbe = 1 := by
  refine ⟨rfl, experiment_subspaceProbe_real, experiment_subspaceProbe_ideal, ?_⟩
  simp [SM_DT_UD_RealSuccess, SM_DT_UD_IdealSuccess, SM_DT_UD_DirectedAdvantage,
    experiment_subspaceProbe_real, experiment_subspaceProbe_ideal]

/-! ## The phase split -/

/-- The challenge and collection bundle is available only before the seed is revealed. -/
example : OracleComp Specs separate.State := separate.pick

/-- The second phase receives the seed and has no oracle. -/
example : separate.State → Seed → ProbComp Bool := separate.distinguish

/-- At the empty collection the collection oracle cannot be queried at all, so the `standalone`
constructor recovers the stand-alone notion rather than approximating it. -/
example : IsEmpty (collectionSpec
    (SM_DT_UD_Problem.standalone hash id Function.injective_id
      (pure false) (pure true) 1).thColl).Domain :=
  isEmpty_domain_collectionSpec_empty

end SMDTUDTest
