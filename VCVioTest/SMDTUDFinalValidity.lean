/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDFinalValidity

/-!
# SM-DT-UD final-validity canaries

These executable games pin real/ideal separation, always-answering cap/duplicate/cross poisoning,
the fact that repeated collection-only tweaks remain valid, and the game's behaviour at a strict
message subspace.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace SMDTUDFinalValidityTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- Real challenges are always `false`; ideal challenges are always `true`. -/
def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def problem : SM_DT_UD_SourceFinalValidity.Problem Unit Seed Bool Bool Bool Bool where
  th := hash
  emb := id
  emb_injective := Function.injective_id
  inputGen := pure false
  outputGen := pure true
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec +
  (SM_DT_UD_SourceFinalValidity.challengeSpec Bool Bool +
    SourceFinalValidity.collectionSpec problem.thColl)

def challenge (t : Bool) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inl t)))

def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

/-- The response itself distinguishes the deliberately separated real and ideal generators. -/
def separate : SM_DT_UD_SourceFinalValidity.Adversary problem where
  State := Bool
  pick := challenge false
  distinguish y _ := pure (!y)

/-- The reverse distinguisher pins the other direction of the symmetric advantage. -/
def separateReverse : SM_DT_UD_SourceFinalValidity.Adversary problem where
  State := Bool
  pick := challenge false
  distinguish y _ := pure y

/-- The second distinct target exceeds the cap, but its answer is still returned. -/
def exceedCap : SM_DT_UD_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge true
    return (y₁, y₂)
  distinguish _ _ := pure true

/-- Reusing a target tweak is answered twice and poisons final validity. -/
def duplicateTarget : SM_DT_UD_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← challenge false
    return (y₁, y₂)
  distinguish _ _ := pure true

/-- A collection query at a target tweak is answered and poisons final validity. -/
def crossClash : SM_DT_UD_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← challenge false
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  distinguish _ _ := pure true

/-- Repeating a collection-only tweak is valid; collection tweaks need not be distinct. -/
def repeatCollection : SM_DT_UD_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  pick := do
    let y₁ ← collectionQuery false false
    let y₂ ← collectionQuery false false
    return (y₁, y₂)
  distinguish _ _ := pure true

private lemma run_separate_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real problem .only)
      separate.pick).run .initial =
      pure (false, ⟨[false], [], true⟩) := by
  rfl

private lemma run_separate_ideal :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .ideal problem .only)
      separate.pick).run .initial =
      pure (true, ⟨[false], [], true⟩) := by
  rfl

private lemma run_separateReverse_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real problem .only)
      separateReverse.pick).run .initial =
      pure (false, ⟨[false], [], true⟩) := by
  rfl

private lemma run_separateReverse_ideal :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .ideal problem .only)
      separateReverse.pick).run .initial =
      pure (true, ⟨[false], [], true⟩) := by
  rfl

private lemma run_exceedCap_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real problem .only)
      exceedCap.pick).run .initial =
      pure ((false, false), ⟨[false, true], [], false⟩) := by
  rfl

private lemma run_duplicateTarget_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real problem .only)
      duplicateTarget.pick).run .initial =
      pure ((false, false), ⟨[false, false], [], false⟩) := by
  rfl

private lemma run_crossClash_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real problem .only)
      crossClash.pick).run .initial =
      pure ((false, true), ⟨[false], [false], false⟩) := by
  rfl

private lemma run_repeatCollection_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real problem .only)
      repeatCollection.pick).run .initial =
      pure ((false, false), ⟨[], [false, false], true⟩) := by
  rfl

private lemma run_repeatCollection_ideal :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .ideal problem .only)
      repeatCollection.pick).run .initial =
      pure ((false, false), ⟨[], [false, false], true⟩) := by
  rfl

private lemma experiment_separate_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real separate = pure true := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_separate_real]
  rfl

private lemma experiment_separate_ideal :
    SM_DT_UD_SourceFinalValidity.Experiment .ideal separate = pure false := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_separate_ideal]
  rfl

private lemma experiment_separateReverse_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real separateReverse = pure false := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_separateReverse_real]
  rfl

private lemma experiment_separateReverse_ideal :
    SM_DT_UD_SourceFinalValidity.Experiment .ideal separateReverse = pure true := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_separateReverse_ideal]
  rfl

private lemma experiment_exceedCap_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real exceedCap = pure false := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_exceedCap_real]
  rfl

private lemma experiment_duplicateTarget_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real duplicateTarget = pure false := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_duplicateTarget_real]
  rfl

private lemma experiment_crossClash_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real crossClash = pure false := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_crossClash_real]
  rfl

private lemma experiment_repeatCollection_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real repeatCollection = pure true := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_repeatCollection_real]
  rfl

private lemma experiment_repeatCollection_ideal :
    SM_DT_UD_SourceFinalValidity.Experiment .ideal repeatCollection = pure true := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_repeatCollection_ideal]
  rfl

/-- The explicit input/output generators separate the worlds in the source orientation: real minus
ideal is positive one, and its absolute magnitude is one. -/
theorem real_ideal_separation_canary :
    SM_DT_UD_SourceFinalValidity.Experiment .real separate = pure true ∧
      SM_DT_UD_SourceFinalValidity.Experiment .ideal separate = pure false ∧
      SM_DT_UD_SourceFinalValidity.RealSuccess separate = 1 ∧
      SM_DT_UD_SourceFinalValidity.IdealSuccess separate = 0 ∧
      SM_DT_UD_SourceFinalValidity.DirectedAdvantage separate = 1 ∧
      SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage separate = 1 := by
  simp [experiment_separate_real, experiment_separate_ideal,
    SM_DT_UD_SourceFinalValidity.RealSuccess, SM_DT_UD_SourceFinalValidity.IdealSuccess,
    SM_DT_UD_SourceFinalValidity.DirectedAdvantage,
    SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage, ENNReal.absDiff]

/-- Reversing the distinguisher makes the directed advantage negative one while its absolute
magnitude remains one. A symmetric-only API would fail to pin this source-game orientation. -/
theorem source_orientation_reverse_canary :
    SM_DT_UD_SourceFinalValidity.Experiment .real separateReverse = pure false ∧
      SM_DT_UD_SourceFinalValidity.Experiment .ideal separateReverse = pure true ∧
      SM_DT_UD_SourceFinalValidity.RealSuccess separateReverse = 0 ∧
      SM_DT_UD_SourceFinalValidity.IdealSuccess separateReverse = 1 ∧
      SM_DT_UD_SourceFinalValidity.DirectedAdvantage separateReverse = -1 ∧
      SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage separateReverse = 1 := by
  simp [experiment_separateReverse_real, experiment_separateReverse_ideal,
    SM_DT_UD_SourceFinalValidity.RealSuccess, SM_DT_UD_SourceFinalValidity.IdealSuccess,
    SM_DT_UD_SourceFinalValidity.DirectedAdvantage,
    SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage, ENNReal.absDiff]

/-- Cap, duplicate-target, and cross-oracle violations poison only the final conjunction: all
queries returned their concrete real-world answers and were recorded in the run lemmas above. -/
theorem final_validity_poison_canary :
    SM_DT_UD_SourceFinalValidity.Experiment .real exceedCap = pure false ∧
      SM_DT_UD_SourceFinalValidity.Experiment .real duplicateTarget = pure false ∧
      SM_DT_UD_SourceFinalValidity.Experiment .real crossClash = pure false := by
  exact ⟨experiment_exceedCap_real, experiment_duplicateTarget_real,
    experiment_crossClash_real⟩

/-- Repeated collection-only tweaks remain valid in both worlds. -/
theorem repeated_collection_allowed_canary :
    SM_DT_UD_SourceFinalValidity.Experiment .real repeatCollection = pure true ∧
      SM_DT_UD_SourceFinalValidity.Experiment .ideal repeatCollection = pure true := by
  exact ⟨experiment_repeatCollection_real, experiment_repeatCollection_ideal⟩

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
def subspaceProblem : SM_DT_UD_SourceFinalValidity.Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb := fun _ => true
  emb_injective a b _ := by cases a; cases b; rfl
  inputGen := $ᵗ Input
  outputGen := pure false
  thColl := collection
  numTargets := 1

@[simp] lemma subspaceProblem_seedGen : subspaceProblem.th.seedGen = pure .only := rfl

/-- Returning the challenge answer verbatim exposes which element of `M` was hashed. -/
def subspaceProbe : SM_DT_UD_SourceFinalValidity.Adversary subspaceProblem where
  State := Bool
  pick := challenge false
  distinguish y _ := pure y

private lemma run_subspaceProbe_real :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .real subspaceProblem .only)
      subspaceProbe.pick).run .initial =
      pure (true, ⟨[false], [], true⟩) := by
  rfl

private lemma run_subspaceProbe_ideal :
    (simulateQ (SM_DT_UD_SourceFinalValidity.oracles .ideal subspaceProblem .only)
      subspaceProbe.pick).run .initial =
      pure (false, ⟨[false], [], true⟩) := by
  rfl

private lemma experiment_subspaceProbe_real :
    SM_DT_UD_SourceFinalValidity.Experiment .real subspaceProbe = pure true := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, subspaceProblem_seedGen, pure_bind]
  rw [run_subspaceProbe_real]
  rfl

private lemma experiment_subspaceProbe_ideal :
    SM_DT_UD_SourceFinalValidity.Experiment .ideal subspaceProbe = pure false := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, subspaceProblem_seedGen, pure_bind]
  rw [run_subspaceProbe_ideal]
  rfl

/-- The strict subspace is a usable instantiation: the hidden input is uniform on `M'` rather than
on `M`, which is the hypothesis a bound in `|M'|` needs, and the real world hashes `emb x`, so the
transcript records the embedded element. -/
theorem subspace_emb_applied_canary :
    subspaceProblem.HasUniformInputs ∧
      SM_DT_UD_SourceFinalValidity.Experiment .real subspaceProbe = pure true ∧
      SM_DT_UD_SourceFinalValidity.Experiment .ideal subspaceProbe = pure false ∧
      SM_DT_UD_SourceFinalValidity.DirectedAdvantage subspaceProbe = 1 := by
  refine ⟨rfl, experiment_subspaceProbe_real, experiment_subspaceProbe_ideal, ?_⟩
  simp [SM_DT_UD_SourceFinalValidity.DirectedAdvantage,
    SM_DT_UD_SourceFinalValidity.RealSuccess, SM_DT_UD_SourceFinalValidity.IdealSuccess,
    experiment_subspaceProbe_real, experiment_subspaceProbe_ideal]

section RunLevelInvariant

open TweakableHash TweakableHash.SM_DT_UD_SourceFinalValidity

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate holds. -/
private lemma valid_of_run {world : World} {adv : Adversary problem} {ps : adv.State}
    {gs : State Bool}
    (hrun : (simulateQ (oracles world problem .only) adv.pick).run .initial = pure (ps, gs))
    (hvalid : gs.valid = true) :
    ∀ z ∈ support ((simulateQ (oracles world problem .only) adv.pick).run .initial),
      SourceFinalValidity.Valid problem.numTargets id z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable world adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate fails. -/
private lemma not_valid_of_run {world : World} {adv : Adversary problem} {ps : adv.State}
    {gs : State Bool}
    (hrun : (simulateQ (oracles world problem .only) adv.pick).run .initial = pure (ps, gs))
    (hvalid : gs.valid = false) :
    ∀ z ∈ support ((simulateQ (oracles world problem .only) adv.pick).run .initial),
      ¬ SourceFinalValidity.Valid problem.numTargets id z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable world adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- The sticky bit decides the final predicate on every reachable state, in both worlds. Reading the
outcome off `SourceFinalValidity.Valid` at the reachable state rather than off the recorded bit is
what makes this more than a restatement of the transcript: a vacuously lifted invariant would not
close these. The real and ideal runs of the same adversary reach the same state, because the
challenge response is drawn before the state is written. -/
theorem reachable_valid_decides_canary :
    (∀ z ∈ support ((simulateQ (oracles .real problem .only) separate.pick).run .initial),
        SourceFinalValidity.Valid problem.numTargets id z.2) ∧
      (∀ z ∈ support ((simulateQ (oracles .ideal problem .only) separate.pick).run .initial),
        SourceFinalValidity.Valid problem.numTargets id z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles .real problem .only) repeatCollection.pick).run .initial),
        SourceFinalValidity.Valid problem.numTargets id z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles .ideal problem .only) repeatCollection.pick).run .initial),
        SourceFinalValidity.Valid problem.numTargets id z.2) ∧
      (∀ z ∈ support ((simulateQ (oracles .real problem .only) exceedCap.pick).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets id z.2) ∧
      (∀ z ∈ support ((simulateQ (oracles .real problem .only) duplicateTarget.pick).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets id z.2) ∧
      (∀ z ∈ support ((simulateQ (oracles .real problem .only) crossClash.pick).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets id z.2) :=
  ⟨valid_of_run run_separate_real rfl, valid_of_run run_separate_ideal rfl,
    valid_of_run run_repeatCollection_real rfl, valid_of_run run_repeatCollection_ideal rfl,
    not_valid_of_run run_exceedCap_real rfl,
    not_valid_of_run run_duplicateTarget_real rfl,
    not_valid_of_run run_crossClash_real rfl⟩

end RunLevelInvariant

/-- The phase types expose the challenge/collection bundle only before seed reveal. -/
example : OracleComp Specs separate.State := separate.pick

example : separate.State → Seed → ProbComp Bool := separate.distinguish

end SMDTUDFinalValidityTest
