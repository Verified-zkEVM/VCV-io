/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.StrongBound

/-!
# Stateful Merkle Multi-Extractability Canaries

Small compile-time instantiations of the whole-adversary game theorem with real oracle queries,
checkpoint-dependent claims, and proof-frontier disagreement.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.MerkleTreeMultiExtractabilityCanary

open BinaryTree InductiveMerkleTree _root_.MerkleTreeMultiExtractability

abbrev Query := Bool × Bool

noncomputable local instance : IsUniformSpec (Query →ₒ Bool) :=
  IsUniformSpec.ofFintypeInhabited (Query →ₒ Bool)

/-- Unaddressed Boolean hashes packaged through the query-parametric node interface. -/
def model : MerkleTreeExtractability.NodeQueryModel Query Unit Bool where
  view := {
    address := fun _ => ()
    input := id }
  mkQuery _ input := input
  address_mkQuery := by intros; rfl
  input_mkQuery := by intros; rfl

@[expose]
def skeleton : Skeleton :=
  .internal .leaf .leaf

def config : Configuration Unit Unit where
  skeleton _ := skeleton
  addressKey _ _ := ()

private theorem per_claim_bound :
    ∀ tag, (config.skeleton tag).leafCount - 1 ≤ 1 := by
  intro tag
  cases tag
  decide

private theorem per_checkpoint_bound :
    ∀ tag, config.nodeBudget tag ≤ 3 := by
  intro tag
  cases tag
  decide

/-! ## Nonzero executable-query accounting -/

/-- Every commitment makes one real oracle query. -/
abbrev queryingCommitter : SequentialCommitter Unit Query Bool where
  State := Unit
  initialState := ()
  commit _ _ := do
    let root ← ((Query →ₒ Bool).query (false, false) : OracleComp (Query →ₒ Bool) Bool)
    return ((), root, ())

/-- The terminal opening also makes one real oracle query before emitting no claims. -/
abbrev queryingAdversary : Adversary Unit Query Unit Bool config where
  committer := queryingCommitter
  opening _ _ := do
    let _ ← ((Query →ₒ Bool).query (true, true) : OracleComp (Query →ₒ Bool) Bool)
    return []

private theorem querying_commit_bound (round : ℕ) (state : queryingCommitter.State) :
    IsTotalQueryBound (queryingCommitter.commit round state) 1 := by
  simp only [queryingCommitter]
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

private theorem querying_opening_bound (state : queryingCommitter.State)
    (extractorState : ExtractorState Unit Query Unit Bool config) :
    IsTotalQueryBound (queryingAdversary.opening state extractorState) 1 := by
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

private theorem querying_global_bound (rounds : ℕ) :
    queryingAdversary.IsAdversaryPrefixQueryBound rounds (rounds + 1) := by
  have hbound := queryingAdversary.isAdversaryPrefixQueryBound_of_schedule rounds
    (fun _ => 1) 1 querying_commit_bound querying_opening_bound
  simpa [commitmentQueryBudget_const] using hbound

private theorem querying_opening_count_bound : queryingAdversary.HasOpeningCountBound 0 := by
  intro state extractorState claims hclaims
  simpa [queryingAdversary] using hclaims

private theorem querying_verifier_bound : queryingAdversary.HasVerifierQueryBound 0 :=
  queryingAdversary.hasVerifierQueryBound_of_openingCountBound 0 1
    querying_opening_count_bound per_claim_bound

/-- Nonzero canary for the uniform-shape theorem: the adversarial budget charges one query per
commitment plus the terminal query, while the honest verifier remains separately zero-cost. -/
theorem queryingGlobalStrongBound (rounds : ℕ) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds queryingAdversary] ≤
      (multiCheckpointROMErrorNumerator (rounds * 3) rounds 0 (rounds + 1) : ENNReal) *
        (Nat.card Bool : ENNReal)⁻¹ := by
  exact anyCheckpointDisagreement_rom_bound_uniformShape model config rounds queryingAdversary
    (rounds + 1) 0 3 (querying_global_bound rounds) querying_verifier_bound
    per_checkpoint_bound

/-! ## Checkpoint-dependent opening claims -/

def selectBoth : LeafData Bool skeleton :=
  .internal (.leaf true) (.leaf true)

def claimingOpening : BatchOpening Bool skeleton where
  selector := selectBoth
  values := (false, false)
  proof := .internalBoth .leaf .leaf

/-- Turn a real recorded checkpoint into a claim against that exact checkpoint. -/
def checkpointClaim (checkpoint : Checkpoint Query Bool config ()) :
    OpeningClaim Query Bool config where
  tag := ()
  checkpoint := checkpoint
  opening := claimingOpening

/-- Read the extractor state and emit claims for its first `rounds` recorded checkpoints. On a
canonical `rounds`-round execution this covers the entire checkpoint list; `take` makes the public
resource predicate hold uniformly even on unreachable states with longer histories. -/
def checkpointClaims (rounds : ℕ)
    (extractorState : ExtractorState Unit Query Unit Bool config) :
    List (OpeningClaim Query Bool config) :=
  (extractorState.checkpoints.take rounds).map fun
    | ⟨(), checkpoint⟩ => checkpointClaim checkpoint

/-- Unlike the preceding adversaries, the opening continuation observes the extractor state and
emits nonempty claims whenever a checkpoint exists. -/
abbrev claimingAdversary (rounds : ℕ) : Adversary Unit Query Unit Bool config where
  committer := queryingCommitter
  opening _ extractorState := pure (checkpointClaims rounds extractorState)

private theorem claiming_opening_bound (rounds : ℕ) (state : queryingCommitter.State)
    (extractorState : ExtractorState Unit Query Unit Bool config) :
    IsTotalQueryBound ((claimingAdversary rounds).opening state extractorState) 0 := by
  trivial

private theorem claiming_global_bound (rounds : ℕ) :
    (claimingAdversary rounds).IsAdversaryPrefixQueryBound rounds rounds := by
  have hbound := (claimingAdversary rounds).isAdversaryPrefixQueryBound_of_schedule rounds
    (fun _ => 1) 0 querying_commit_bound (claiming_opening_bound rounds)
  simpa [commitmentQueryBudget_const] using hbound

private theorem claiming_opening_count_bound (rounds : ℕ) :
    (claimingAdversary rounds).HasOpeningCountBound rounds := by
  intro state extractorState claims hclaims
  have hclaims' : claims = checkpointClaims rounds extractorState := by
    simpa [claimingAdversary] using hclaims
  subst claims
  simp [checkpointClaims]

private theorem claiming_verifier_bound (rounds : ℕ) :
    (claimingAdversary rounds).HasVerifierQueryBound rounds := by
  simpa using (claimingAdversary rounds).hasVerifierQueryBound_of_openingCountBound
    rounds 1 (claiming_opening_count_bound rounds) per_claim_bound

/-- This owner-theorem instantiation has nonzero honest-verifier overhead and forces the terminal
opening continuation to depend on the extractor state. It exercises the accounting bridge used to
separate ghost continuation queries from real adversarial queries. -/
theorem claimingGlobalStrongBound (rounds : ℕ) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
        extractabilityGame model config rounds (claimingAdversary rounds)] ≤
      (multiCheckpointROMErrorNumerator (rounds * 3) rounds rounds rounds : ENNReal) *
        (Nat.card Bool : ENNReal)⁻¹ := by
  exact anyCheckpointDisagreement_rom_bound_uniformShape model config rounds
    (claimingAdversary rounds)
    rounds rounds 3 (claiming_global_bound rounds) (claiming_verifier_bound rounds)
    per_checkpoint_bound

/-! ## Proof-only full-opening disagreement -/

@[expose]
def selectRight : LeafData Bool skeleton :=
  .internal (.leaf false) (.leaf true)

def proofOnlyValues : SelectedValues Bool selectRight :=
  (PUnit.unit, true)

/-- The stored left sibling is deliberately wrong; the selected right value is correct. -/
def proofOnlyOpening : BatchOpening Bool skeleton where
  selector := selectRight
  values := proofOnlyValues
  proof := .pruneLeft rfl true .leaf

def extractedTree : FullData (Option Bool) skeleton :=
  .internal (some false) (.leaf (some false)) (.leaf (some true))

private theorem proof_only_disagreement :
    MerkleTreeBatchExtractability.OpeningDisagreesWithTree proofOnlyOpening extractedTree := by
  apply Or.inr
  simp only [MerkleTreeBatchExtractability.extractedOpening, proofOnlyOpening, extractedTree,
    selectRight, proofOnlyValues, FullData.toLeafData, generateBatchProof,
    FullData.getRootValue, BatchProof.map]
  intro heq
  injection heq with _ _ _ _ hroot _
  change some true = some false at hroot
  simp at hroot

/-- The full-opening witness theorem accepts a proof-frontier-only mismatch, not merely unequal
selected leaf values. -/
example :
    ∃ index : SkeletonLeafIndex skeleton,
      ∃ selected : proofOnlyOpening.selector.get index = true,
        some (selectedValueAt proofOnlyOpening.values index selected) ≠
            extractedTree.get index.toNodeIndex ∨
          (batchToSingleProofAddressed (fun _ _ _ => false) proofOnlyOpening.values
            proofOnlyOpening.proof index selected).toList.map some ≠
            (generateProof extractedTree index).toList :=
  proof_only_disagreement.exists_selectedValue_or_path_disagreement
    (fun _ _ _ => false) proofOnlyOpening extractedTree

/-! ## Ordered transcript and phase execution -/

private def orderedView :
    MerkleTreeExtractor.QueryView (Bool × (Nat × Nat)) Bool Nat where
  address := Prod.fst
  input := Prod.snd

private def orderedConfig : Configuration Unit Bool where
  skeleton _ := .internal .leaf .leaf
  addressKey _ _ := false

private def orderedCheckpoint : Checkpoint (Bool × (Nat × Nat)) Nat orderedConfig () where
  root := 7
  cumulativeLog := [⟨(true, (11, 13)), 7⟩, ⟨(false, (2, 3)), 7⟩]

/-- Extraction uses the matching address and preserves the order of query children. -/
example : Checkpoint.extractedTree orderedView orderedCheckpoint =
    FullData.internal (some 7) (FullData.leaf (some 2)) (FullData.leaf (some 3)) := by
  rfl

private abbrev phaseOrderCommitter : SequentialCommitter Bool Unit Nat where
  State := Nat
  initialState := 0
  commit round state := pure (round == 1, 10 + state, state + 1)

private def phaseOrderConfig : Configuration Bool Unit where
  skeleton _ := .leaf
  addressKey _ index := nomatch index

/-- Two phases advance private state and retain checkpoints in commitment order. -/
example : phaseOrderCommitter.runFromEmpty phaseOrderConfig 2 =
    let initial : ExtractorState Bool Unit Unit Nat phaseOrderConfig := ExtractorState.empty
    pure (2, (initial.record false [] 10).record true [] 11) := by
  rfl

end VCVioTest.MerkleTreeMultiExtractabilityCanary
