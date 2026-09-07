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

end SMDTPREFinalValidityTest
