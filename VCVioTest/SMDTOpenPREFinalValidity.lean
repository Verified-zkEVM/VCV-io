/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR

/-! # SM-DT-OpenPRE exact-game canaries -/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace SMDTOpenPREFinalValidityTest

inductive Seed
  | only

inductive Input
  | only
  deriving DecidableEq, Inhabited

instance : Fintype Input where
  elems := {.only}
  complete x := by cases x; simp

instance : Unique Input where
  default := .only
  uniq x := by cases x; rfl

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

instance : SampleableType Input where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

@[simp] lemma uniformSample_input : ($ᵗ Input : ProbComp Input) = pure .only := rfl

def hash : TweakableHash Seed Bool Input Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ m := m

def problem1 : SM_DT_OpenPRE_SourceFinalValidity.Problem Unit Seed Bool Input Bool where
  th := hash
  inputGen := $ᵗ Input
  thColl := collection
  numTargets := 1

def problem2 : SM_DT_OpenPRE_SourceFinalValidity.Problem Unit Seed Bool Input Bool where
  th := hash
  inputGen := $ᵗ Input
  thColl := collection
  numTargets := 2

@[simp] lemma problem1_seedGen : problem1.th.seedGen = pure .only := rfl

@[simp] lemma problem2_seedGen : problem2.th.seedGen = pure .only := rfl

def collectionQuery1 (t m : Bool) :
    OracleComp (unifSpec + SourceFinalValidity.collectionSpec problem1.thColl) Bool :=
  liftM ((unifSpec + SourceFinalValidity.collectionSpec problem1.thColl).query
    (.inr ⟨(), t, m⟩))

def open1 (j : ℕ) :
    OracleComp (unifSpec + SM_DT_OpenPRE_SourceFinalValidity.openSpec Input) Input :=
  liftM ((unifSpec + SM_DT_OpenPRE_SourceFinalValidity.openSpec Input).query (.inr j))

def valid : SM_DT_OpenPRE_SourceFinalValidity.Adversary problem1 where
  State := Unit
  pick := pure ((), [false])
  find _ _ _ := pure (0, .only)

/-- A committed list longer than the cap must be truncated, not used to poison validity. -/
def overlong : SM_DT_OpenPRE_SourceFinalValidity.Adversary problem1 where
  State := Unit
  pick := pure ((), [false, true])
  find _ _ _ := pure (0, .only)

def collectionClash : SM_DT_OpenPRE_SourceFinalValidity.Adversary problem1 where
  State := Bool
  pick := do
    let y ← collectionQuery1 false true
    return (y, [false])
  find _ _ _ := pure (0, .only)

def openedSelected : SM_DT_OpenPRE_SourceFinalValidity.Adversary problem1 where
  State := Unit
  pick := pure ((), [false])
  find _ _ _ := do
    let _ ← open1 0
    return (0, .only)

def duplicateTargets : SM_DT_OpenPRE_SourceFinalValidity.Adversary problem2 where
  State := Unit
  pick := pure ((), [false, false])
  find _ _ _ := pure (0, .only)

/-- Opening a different target remains legal. -/
def openedOther : SM_DT_OpenPRE_SourceFinalValidity.Adversary problem2 where
  State := Unit
  pick := pure ((), [false, true])
  find _ _ _ := do
    let _ ← open1 1
    return (0, .only)

private lemma initialize_one :
    (SM_DT_OpenPRE_SourceFinalValidity.initializeTargets problem1 .only [false]).run .initial =
      pure ([false], ⟨[(false, .only)], [], true⟩) := by
  rfl

/-- This pins the source's bounded-prefix behavior independently of the final winning predicate. -/
private lemma initialize_bounded_prefix :
    (SM_DT_OpenPRE_SourceFinalValidity.initializeTargets problem1 .only
      ([false, true].take problem1.numTargets)).run .initial =
      pure ([false], ⟨[(false, .only)], [], true⟩) := by
  rfl

private lemma experiment_valid :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment valid = pure true := by
  rfl

private lemma experiment_overlong :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment overlong = pure true := by
  rfl

private lemma experiment_collectionClash :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment collectionClash = pure false := by
  rfl

private lemma experiment_openedSelected :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment openedSelected = pure false := by
  rfl

private lemma experiment_duplicateTargets :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment duplicateTargets = pure false := by
  rfl

private lemma experiment_openedOther :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment openedOther = pure true := by
  rfl

private lemma tcr_reduction_valid :
    SM_DT_TCR_SourceFinalValidity.Experiment (SM_DT_OpenPRE_SourceFinalValidity.toTCR valid) =
      pure false := by
  rfl

private lemma dspr_reduction_valid :
    SM_DT_DSPR_SourceFinalValidity.Experiment (SM_DT_OpenPRE_SourceFinalValidity.toDSPR valid) =
      pure true := by
  rfl

private lemma dspr_reduction_openedSelected :
    SM_DT_DSPR_SourceFinalValidity.Experiment
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR openedSelected) = pure false := by
  rfl

private lemma sp_reduction_valid :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment (SM_DT_OpenPRE_SourceFinalValidity.toDSPR valid) =
      pure false := by
  rfl

/-- The singleton canary has a fiber of size one and no second preimage. -/
theorem preimage_count_canary :
    SM_DT_OpenPRE_SourceFinalValidity.PreimageCount hash .only false false = 1 ∧
      ¬SecondPreimageExists hash .only false .only := by
  constructor
  · have hle : SM_DT_OpenPRE_SourceFinalValidity.PreimageCount hash .only false false ≤ 1 := by
      calc
        SM_DT_OpenPRE_SourceFinalValidity.PreimageCount hash .only false false ≤
            Fintype.card Input :=
          SM_DT_OpenPRE_SourceFinalValidity.preimageCount_le_card hash .only false false
        _ = 1 := Fintype.card_unique
    have hge : 1 ≤ SM_DT_OpenPRE_SourceFinalValidity.PreimageCount hash .only false false :=
      SM_DT_OpenPRE_SourceFinalValidity.one_le_preimageCount_image hash .only false .only
    exact Nat.le_antisymm hle hge
  · simp [SecondPreimageExists]

lemma no_multiple_index (k : Fin (Fintype.card Input - 1)) : False :=
  Fin.elim0 k

/-- Concrete witness that the quantitative theorem interface asks for a cardinality-stratified
decomposition rather than assuming its conclusion. -/
noncomputable def validCountingInterface :
    SM_DT_OpenPRE_SourceFinalValidity.CountingInterface valid where
  uniformInputs := rfl
  singleMass := 1
  multipleMass := fun k => (no_multiple_index k).elim
  openPRE_decomposition := by
    simp only [SM_DT_OpenPRE_SourceFinalValidity.Advantage, experiment_valid]
    rw [Finset.sum_eq_zero (fun k _ => (no_multiple_index k).elim)]
    simp
  dspr_decomposition := by
    simp only [SM_DT_DSPR_SourceFinalValidity.Advantage, SM_DT_DSPR_SourceFinalValidity.Success,
      SM_DT_DSPR_SourceFinalValidity.SPProbability, dspr_reduction_valid, sp_reduction_valid,
      SM_DT_OpenPRE_SourceFinalValidity.reciprocalMass]
    rw [Finset.sum_eq_zero (fun k _ => (no_multiple_index k).elim)]
    simp
  tcr_strata_le := by
    simp only [SM_DT_OpenPRE_SourceFinalValidity.collisionMass]
    rw [Finset.sum_eq_zero (fun k _ => (no_multiple_index k).elim)]
    simp

theorem quantitative_reduction_interface_canary :
    SM_DT_OpenPRE_SourceFinalValidity.Advantage valid ≤
      SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound valid :=
  SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound valid validCountingInterface

/-- Mutation-resistant pins for prefix truncation, final validity, and the adaptive opening
phase. -/
theorem exact_game_canary :
    SM_DT_OpenPRE_SourceFinalValidity.Experiment valid = pure true ∧
      SM_DT_OpenPRE_SourceFinalValidity.Experiment overlong = pure true ∧
      SM_DT_OpenPRE_SourceFinalValidity.Experiment collectionClash = pure false ∧
      SM_DT_OpenPRE_SourceFinalValidity.Experiment openedSelected = pure false ∧
      SM_DT_OpenPRE_SourceFinalValidity.Experiment duplicateTargets = pure false ∧
      SM_DT_OpenPRE_SourceFinalValidity.Experiment openedOther = pure true ∧
      SM_DT_TCR_SourceFinalValidity.Experiment (SM_DT_OpenPRE_SourceFinalValidity.toTCR valid) =
        pure false ∧
      SM_DT_DSPR_SourceFinalValidity.Experiment (SM_DT_OpenPRE_SourceFinalValidity.toDSPR valid) =
        pure true ∧
      SM_DT_DSPR_SourceFinalValidity.Experiment
        (SM_DT_OpenPRE_SourceFinalValidity.toDSPR openedSelected) = pure false :=
  ⟨experiment_valid, experiment_overlong, experiment_collectionClash,
    experiment_openedSelected, experiment_duplicateTargets, experiment_openedOther,
    tcr_reduction_valid, dspr_reduction_valid, dspr_reduction_openedSelected⟩

end SMDTOpenPREFinalValidityTest
