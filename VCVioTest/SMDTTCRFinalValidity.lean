/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity

/-!
# Source-final-validity SM-DT-TCR canaries

These concrete games pin the source-final-predicate branch behavior. Both query orders across the
challenge/collection boundary are answered and recorded but poison the final result. Repeated
collection-only tweaks remain legal, while a repeated target tweak is invalid even though its
second digest is returned.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SMDTTCRFinalValidityTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def problem : TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 2

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec +
  (TweakableHash.SM_DT_TCR_SourceFinalValidity.challengeSpec Bool Bool Bool +
    TweakableHash.SourceFinalValidity.collectionSpec problem.thColl)

def challenge (t m : Bool) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inl (t, m))))

def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

def challengeOnly : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Unit
  choose := challenge false false *> pure ()
  forge _ _ := pure (0, true)

def challengeThenCollection : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← collectionQuery false true
    return (y₁, y₂)
  forge _ _ := pure (0, true)

def collectionThenChallenge : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false true
    let y₂ ← challenge false false
    return (y₁, y₂)
  forge _ _ := pure (0, true)

/-- Repeating a collection tweak is permitted; the subsequent fresh challenge remains valid. -/
def repeatedCollection : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false false
    let y₂ ← collectionQuery false true
    let _ ← challenge true false
    return (y₁, y₂)
  forge _ _ := pure (0, true)

/-- A repeated target tweak is answered and recorded, then final validity rejects the forgery. -/
def repeatedTarget : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← challenge false true
    return (y₁, y₂)
  forge _ _ := pure (0, true)

/-- A collection query after target duplication still returns its digest and is appended. -/
def poisonThenCollection : TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary problem where
  State := Bool × Bool × Bool
  choose := do
    let y₁ ← challenge false false
    let y₂ ← challenge false true
    let y₃ ← collectionQuery true true
    return (y₁, y₂, y₃)
  forge _ _ := pure (0, true)

private lemma run_challengeOnly :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      challengeOnly.choose).run .initial =
      pure ((), ⟨[(false, false)], [], true⟩) := by
  rfl

private lemma run_challengeThenCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      challengeThenCollection.choose).run .initial =
      pure ((false, true), ⟨[(false, false)], [false], false⟩) := by
  rfl

private lemma run_collectionThenChallenge :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      collectionThenChallenge.choose).run .initial =
      pure ((true, false), ⟨[(false, false)], [false], false⟩) := by
  rfl

private lemma run_repeatedCollection :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      repeatedCollection.choose).run .initial =
      pure ((false, true), ⟨[(true, false)], [false, false], true⟩) := by
  rfl

private lemma run_repeatedTarget :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      repeatedTarget.choose).run .initial =
      pure ((false, false), ⟨[(false, false), (false, true)], [], false⟩) := by
  rfl

/-- Once poisoned, the monitor remains always-answering: the later collection digest and its tweak
are both observable, while validity remains false. -/
theorem poison_then_collection_history_canary :
    (simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles problem .only)
      poisonThenCollection.choose).run .initial =
      pure ((false, false, true),
        ⟨[(false, false), (false, true)], [true], false⟩) := by
  rfl

private lemma experiment_challengeOnly :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeOnly = pure true := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_challengeOnly]
  rfl

private lemma experiment_challengeThenCollection :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeThenCollection =
      pure false := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_challengeThenCollection]
  rfl

private lemma experiment_collectionThenChallenge :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment collectionThenChallenge =
      pure false := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge]
  rfl

private lemma experiment_repeatedCollection :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedCollection = pure true := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_repeatedCollection]
  rfl

private lemma experiment_repeatedTarget :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedTarget = pure false := by
  simp only [TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_repeatedTarget]
  rfl

/-- Both clash orders and a repeated target lose through final validity, while the legal control
cases win. The run equalities also pin that invalid queries still return their real answers. -/
theorem final_validity_branch_canary :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeOnly = pure true ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment challengeThenCollection =
        pure false ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment collectionThenChallenge =
        pure false ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedCollection = pure true ∧
      TweakableHash.SM_DT_TCR_SourceFinalValidity.Experiment repeatedTarget = pure false :=
  ⟨experiment_challengeOnly, experiment_challengeThenCollection,
    experiment_collectionThenChallenge, experiment_repeatedCollection, experiment_repeatedTarget⟩

section RunLevelInvariant

open TweakableHash TweakableHash.SM_DT_TCR_SourceFinalValidity

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate holds. -/
private lemma valid_of_run {adv : Adversary problem} {ps : adv.State} {gs : State Bool Bool}
    (hrun : (simulateQ (oracles problem .only) adv.choose).run .initial = pure (ps, gs))
    (hvalid : gs.valid = true) :
    ∀ z ∈ support ((simulateQ (oracles problem .only) adv.choose).run .initial),
      SourceFinalValidity.Valid problem.numTargets Prod.fst z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate fails. -/
private lemma not_valid_of_run {adv : Adversary problem} {ps : adv.State} {gs : State Bool Bool}
    (hrun : (simulateQ (oracles problem .only) adv.choose).run .initial = pure (ps, gs))
    (hvalid : gs.valid = false) :
    ∀ z ∈ support ((simulateQ (oracles problem .only) adv.choose).run .initial),
      ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- The lifted monitor invariant decides the final predicate correctly on every canary transcript:
`SourceFinalValidity.Valid` holds on the two legal runs and fails on both clash orders and on the
repeated target, including after the monitor keeps answering.

Quantifying over the whole support is what makes the run-level lifting load-bearing: the outcome is
read off `SourceFinalValidity.Valid` at the reachable state, not off the recorded bit. The
`repeatedTarget` and `poisonThenCollection` cases pin the distinct-target-tweak conjunct and the
clash orders pin target/collection disjointness. -/
theorem reachable_valid_decides_canary :
    (∀ z ∈ support ((simulateQ (oracles problem .only) challengeOnly.choose).run .initial),
        SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support ((simulateQ (oracles problem .only) repeatedCollection.choose).run .initial),
        SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles problem .only) challengeThenCollection.choose).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles problem .only) collectionThenChallenge.choose).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support ((simulateQ (oracles problem .only) repeatedTarget.choose).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles problem .only) poisonThenCollection.choose).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) :=
  ⟨valid_of_run run_challengeOnly rfl, valid_of_run run_repeatedCollection rfl,
    not_valid_of_run run_challengeThenCollection rfl,
    not_valid_of_run run_collectionThenChallenge rfl,
    not_valid_of_run run_repeatedTarget rfl,
    not_valid_of_run poison_then_collection_history_canary rfl⟩

end RunLevelInvariant

end SMDTTCRFinalValidityTest
