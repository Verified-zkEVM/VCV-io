/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Map
public import VCVio.CryptoFoundations.MerkleTree.Inductive.QueryBound

/-!
# Query Bounds for Batch Merkle Openings

This file gives exact structural query counts and total query bounds for the path-pruned
batch verifier. `BatchProof.queryCount` counts the internal nodes visited by
`getPutativeBatchRoot`: every visited internal node contributes one hash-oracle query,
while a selected leaf contributes none.

The count is bounded by the number of internal nodes in the whole skeleton. It also
dominates the depth of every selected leaf, reflecting that a batch verifier contains the
entire authentication path of each leaf that it opens.
-/

@[expose] public section

namespace InductiveMerkleTree

open OracleComp OracleSpec BinaryTree

universe u v

variable {α : Type u} {β : Type v}

/-- The exact number of internal-node hash queries made while checking a batch proof. -/
@[simp, grind]
def BatchProof.queryCount : {s : Skeleton} → {sel : LeafData Bool s} → BatchProof α sel → ℕ
  | _, _, .leaf => 0
  | _, _, .internalBoth pl pr => pl.queryCount + pr.queryCount + 1
  | _, _, .pruneRight _ _ pl => pl.queryCount + 1
  | _, _, .pruneLeft _ _ pr => pr.queryCount + 1

/-- Pointwise mapping changes stored values but not the pruned verifier's query count. -/
@[simp]
theorem BatchProof.queryCount_map (f : α → β) {s : Skeleton} {sel : LeafData Bool s}
    (proof : BatchProof α sel) : (proof.map f).queryCount = proof.queryCount := by
  induction proof <;> simp_all only [BatchProof.map, BatchProof.queryCount]

section TotalQueryBound

variable {α : Type}

/-- Computing a putative batch root makes at most `proof.queryCount` oracle queries. -/
theorem getPutativeBatchRoot_isTotalQueryBound {s : Skeleton} {sel : LeafData Bool s}
    (values : SelectedValues α sel) (proof : BatchProof α sel) :
    IsTotalQueryBound
      (getPutativeBatchRoot (m := OracleComp (spec α)) values proof)
      proof.queryCount := by
  induction proof with
  | leaf => trivial
  | internalBoth pl pr ihl ihr =>
      simp only [getPutativeBatchRoot, BatchProof.queryCount]
      simpa only [Nat.add_assoc] using
        isTotalQueryBound_bind (ihl values.1) fun _ =>
          isTotalQueryBound_bind (ihr values.2) fun _ => singleHash_isTotalQueryBound _ _
  | pruneRight hr rightRoot pl ih =>
      simp only [getPutativeBatchRoot, BatchProof.queryCount]
      exact isTotalQueryBound_bind (ih values.1) fun _ => singleHash_isTotalQueryBound _ _
  | pruneLeft hl leftRoot pr ih =>
      simp only [getPutativeBatchRoot, BatchProof.queryCount]
      exact isTotalQueryBound_bind (ih values.2) fun _ => singleHash_isTotalQueryBound _ _

/-- Batch verification has the same query count as putative-root computation; its final
root comparison is pure. -/
theorem verifyBatchProof_isTotalQueryBound [DecidableEq α]
    {s : Skeleton} {sel : LeafData Bool s} (values : SelectedValues α sel)
    (rootValue : α) (proof : BatchProof α sel) :
    IsTotalQueryBound
      (verifyBatchProof (m := OracleComp (spec α)) values rootValue proof)
      proof.queryCount := by
  unfold verifyBatchProof
  exact isTotalQueryBound_bind (n₂ := 0)
    (getPutativeBatchRoot_isTotalQueryBound values proof) fun _ => trivial

end TotalQueryBound

/-- The pruned verifier never visits more internal nodes than exist in the skeleton. -/
theorem BatchProof.queryCount_le_leafCount_sub_one :
    {s : Skeleton} → {sel : LeafData Bool s} → (proof : BatchProof α sel) →
      proof.queryCount ≤ s.leafCount - 1
  | _, _, .leaf => by simp
  | .internal sₗ sᵣ, _, .internalBoth pl pr => by
      simp only [BatchProof.queryCount, Skeleton.leafCount_internal]
      have hl : pl.queryCount ≤ sₗ.leafCount - 1 := pl.queryCount_le_leafCount_sub_one
      have hr : pr.queryCount ≤ sᵣ.leafCount - 1 := pr.queryCount_le_leafCount_sub_one
      have hposl := Skeleton.leafCount_pos sₗ
      have hposr := Skeleton.leafCount_pos sᵣ
      omega
  | .internal sₗ sᵣ, _, .pruneRight _ _ pl => by
      simp only [BatchProof.queryCount, Skeleton.leafCount_internal]
      have hl : pl.queryCount ≤ sₗ.leafCount - 1 := pl.queryCount_le_leafCount_sub_one
      have hposl := Skeleton.leafCount_pos sₗ
      have hposr := Skeleton.leafCount_pos sᵣ
      omega
  | .internal sₗ sᵣ, _, .pruneLeft _ _ pr => by
      simp only [BatchProof.queryCount, Skeleton.leafCount_internal]
      have hr : pr.queryCount ≤ sᵣ.leafCount - 1 := pr.queryCount_le_leafCount_sub_one
      have hposl := Skeleton.leafCount_pos sₗ
      have hposr := Skeleton.leafCount_pos sᵣ
      omega

/-- Every selected leaf contributes its entire root path to the batch-verification trace. -/
theorem BatchProof.depth_le_queryCount {s : Skeleton} {sel : LeafData Bool s}
    (proof : BatchProof α sel) (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true) :
    idx.depth ≤ proof.queryCount := by
  induction proof with
  | leaf =>
      cases idx
      rfl
  | internalBoth pl pr ihl ihr =>
      cases idx with
      | ofLeft idxL =>
          simp only [SkeletonLeafIndex.depth, BatchProof.queryCount]
          have h := ihl idxL (by simpa using hidx)
          omega
      | ofRight idxR =>
          simp only [SkeletonLeafIndex.depth, BatchProof.queryCount]
          have h := ihr idxR (by simpa using hidx)
          omega
  | pruneRight hr rightRoot pl ih =>
      cases idx with
      | ofLeft idxL =>
          simp only [SkeletonLeafIndex.depth, BatchProof.queryCount]
          have h := ih idxL (by simpa using hidx)
          omega
      | ofRight idxR =>
          exact absurd (LeafData.anySelected_of_get idxR (by simpa using hidx)) (by simp [hr])
  | pruneLeft hl leftRoot pr ih =>
      cases idx with
      | ofRight idxR =>
          simp only [SkeletonLeafIndex.depth, BatchProof.queryCount]
          have h := ih idxR (by simpa using hidx)
          omega
      | ofLeft idxL =>
          exact absurd (LeafData.anySelected_of_get idxL (by simpa using hidx)) (by simp [hl])

section TotalQueryBound

variable {α : Type}

/-- Skeleton-uniform query bound for computing a putative batch root. -/
theorem getPutativeBatchRoot_isTotalQueryBound_leafCount {s : Skeleton}
    {sel : LeafData Bool s} (values : SelectedValues α sel) (proof : BatchProof α sel) :
    IsTotalQueryBound
      (getPutativeBatchRoot (m := OracleComp (spec α)) values proof)
      (s.leafCount - 1) :=
  (getPutativeBatchRoot_isTotalQueryBound values proof).mono
    proof.queryCount_le_leafCount_sub_one

/-- Skeleton-uniform query bound for batch verification. -/
theorem verifyBatchProof_isTotalQueryBound_leafCount [DecidableEq α] {s : Skeleton}
    {sel : LeafData Bool s} (values : SelectedValues α sel) (rootValue : α)
    (proof : BatchProof α sel) :
    IsTotalQueryBound
      (verifyBatchProof (m := OracleComp (spec α)) values rootValue proof)
      (s.leafCount - 1) :=
  (verifyBatchProof_isTotalQueryBound values rootValue proof).mono
    proof.queryCount_le_leafCount_sub_one

end TotalQueryBound

end InductiveMerkleTree
