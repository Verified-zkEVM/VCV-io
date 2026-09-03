/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity

/-!
# Source-final-validity SM-DT-PRE canaries

A valid inversion wins. Duplicate targets and target/collection clashes still receive their
sampled image, remain in the histories, and poison the final result. The target cap is two so the
duplicate-target canary isolates tweak distinctness from cap overflow.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SMDTPREFinalValidityTest

inductive Seed
  | only

inductive Input
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

instance : SampleableType Input where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def problem :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Problem Unit Seed Bool Bool Input Bool where
  th := hash
  emb _ := false
  emb_injective := fun _ _ _ => rfl
  thColl := collection
  numTargets := 2

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec +
  (TweakableHash.SM_DT_PRE_SourceFinalValidity.challengeSpec Bool Bool +
    TweakableHash.SourceFinalValidity.collectionSpec problem.thColl)

def challenge (t : Bool) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inl t)))

def collectionQuery (t : Bool) (m : problem.thColl.Msg ()) : OracleComp Specs Bool :=
  liftM (Specs.query (.inr (.inr ⟨(), t, m⟩)))

def valid : TweakableHash.SM_DT_PRE_SourceFinalValidity.Adversary problem where
  State := Bool
  choose := challenge false
  invert _ _ := pure (0, .only)

def duplicateTarget : TweakableHash.SM_DT_PRE_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← challenge false
    let y₂ ← challenge false
    return (y₁, y₂)
  invert _ _ := pure (0, .only)

def collectionClash : TweakableHash.SM_DT_PRE_SourceFinalValidity.Adversary problem where
  State := Bool × Bool
  choose := do
    let y₁ ← collectionQuery false true
    let y₂ ← challenge false
    return (y₁, y₂)
  invert _ _ := pure (0, .only)

private lemma run_valid :
    (simulateQ (TweakableHash.SM_DT_PRE_SourceFinalValidity.oracles problem .only)
      valid.choose).run .initial =
      pure (false, ⟨[(false, .only)], [], true⟩) := by
  rfl

private lemma run_duplicateTarget :
    (simulateQ (TweakableHash.SM_DT_PRE_SourceFinalValidity.oracles problem .only)
      duplicateTarget.choose).run .initial =
      pure ((false, false), ⟨[(false, .only), (false, .only)], [], false⟩) := by
  rfl

private lemma run_collectionClash :
    (simulateQ (TweakableHash.SM_DT_PRE_SourceFinalValidity.oracles problem .only)
      collectionClash.choose).run .initial =
      pure ((true, false), ⟨[(false, .only)], [false], false⟩) := by
  rfl

private lemma experiment_valid :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment valid = pure true := by
  simp only [TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_valid]
  rfl

private lemma experiment_duplicateTarget :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment duplicateTarget = pure false := by
  simp only [TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_duplicateTarget]
  rfl

private lemma experiment_collectionClash :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment collectionClash = pure false := by
  simp only [TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment, problem_seedGen, pure_bind]
  rw [run_collectionClash]
  rfl

/-- Valid inversion wins, while answered-and-recorded duplicate and cross-oracle queries lose
through final validity. -/
theorem final_validity_branch_canary :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment valid = pure true ∧
      TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment duplicateTarget = pure false ∧
      TweakableHash.SM_DT_PRE_SourceFinalValidity.Experiment collectionClash = pure false :=
  ⟨experiment_valid, experiment_duplicateTarget, experiment_collectionClash⟩

section RunLevelInvariant

open TweakableHash TweakableHash.SM_DT_PRE_SourceFinalValidity

/-- Transfer of the run-level monitor invariant along a transcript pinned to one outcome, in the
direction that concludes the final predicate holds. -/
private lemma valid_of_run {adv : Adversary problem} {ps : adv.State} {gs : State Bool Input}
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
private lemma not_valid_of_run {adv : Adversary problem} {ps : adv.State} {gs : State Bool Input}
    (hrun : (simulateQ (oracles problem .only) adv.choose).run .initial = pure (ps, gs))
    (hvalid : gs.valid = false) :
    ∀ z ∈ support ((simulateQ (oracles problem .only) adv.choose).run .initial),
      ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2 := by
  intro z hz
  have hdecide := valid_eq_decide_valid_of_reachable adv .only hz
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simpa [hvalid] using hdecide.symm

/-- The lifted monitor invariant decides the final predicate correctly on every canary transcript,
including across the oracle-side message draw: the sampled preimage enters the recorded history but
the predicate depends only on the tweaks. -/
theorem reachable_valid_decides_canary :
    (∀ z ∈ support ((simulateQ (oracles problem .only) valid.choose).run .initial),
        SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles problem .only) duplicateTarget.choose).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) ∧
      (∀ z ∈ support
          ((simulateQ (oracles problem .only) collectionClash.choose).run .initial),
        ¬ SourceFinalValidity.Valid problem.numTargets Prod.fst z.2) :=
  ⟨valid_of_run run_valid rfl, not_valid_of_run run_duplicateTarget rfl,
    not_valid_of_run run_collectionClash rfl⟩

end RunLevelInvariant

end SMDTPREFinalValidityTest
