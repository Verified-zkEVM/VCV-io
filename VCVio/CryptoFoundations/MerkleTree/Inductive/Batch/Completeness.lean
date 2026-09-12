/-
Copyright (c) 2026 IAOM / Equation Capital dba Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abraxas1010 (IAOM / Apoth3osis)
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Completeness of Batch Openings for Inductive Merkle Trees

This file proves the completeness theorem for the batch openings defined in
`VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs`: an honestly generated batch proof,
together with the true values of the selected leaves, recomputes exactly the root of the
honestly built Merkle tree — for *every* selector that opens at least one leaf.

As with the single-index case, the proof is split into two pieces:

* `InductiveMerkleTree.functional_batch_completeness` is a purely functional statement about
  `getPutativeBatchRootWithHash` and `buildMerkleTreeWithHash`, proven by induction on the
  leaf data with the selector case-split at each internal node (both children selected /
  right pruned / left pruned).
* `InductiveMerkleTree.batch_completeness` lifts the functional statement to the monadic API
  under the random oracle, reducing through `simulateQ` exactly as the single-index
  `completeness` theorem does.
-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/--
A functional form of the batch completeness theorem: the honest batch proof generated from
an honestly built tree, together with the true selected leaf values, recomputes the tree's
root — under any hash function and any selector opening at least one leaf.
-/
@[grind =]
theorem functional_batch_completeness {s : Skeleton}
    (leaves : LeafData α s) (sel : LeafData Bool s) (h : sel.anySelected = true)
    (hash : α → α → α) :
    getPutativeBatchRootWithHash hash (selectedValues leaves sel)
      (generateBatchProof (buildMerkleTreeWithHash leaves hash) sel h)
    = (buildMerkleTreeWithHash leaves hash).getRootValue := by
  induction sel with
  | leaf b =>
    cases leaves with
    | leaf a =>
      cases b with
      | false => simp [LeafData.anySelected] at h
      | true => rfl
  | internal l r ihl ihr =>
    cases leaves with
    | internal la ra =>
      simp only [LeafData.anySelected, Bool.or_eq_true] at h
      simp only [buildMerkleTreeWithHash, populateUp, generateBatchProof]
      split
      all_goals simp_all [getPutativeBatchRootWithHash, selectedValues,
        buildMerkleTreeWithHash]

/--
Batch completeness theorem for Merkle trees: building the tree honestly, generating the
batch proof for any selector opening at least one leaf, and verifying it against the tree's
root succeeds with probability `1` under the random oracle.

The proof reduces to `functional_batch_completeness` through `simulateQ`, exactly as the
single-index `completeness` theorem reduces to `functional_completeness`.
-/
theorem batch_completeness [DecidableEq α] [Inhabited α] [SampleableType α] {s : Skeleton}
    (leaf_data_tree : LeafData α s) (sel : LeafData Bool s) (h : sel.anySelected = true)
    (preexisting_cache : (spec α).QueryCache) :
    Pr[fun v => v.1 = true | (simulateQ (spec α).randomOracle (do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateBatchProof cache sel h
      let verified ← (verifyBatchProof (m := OracleComp (spec α))
        (selectedValues leaf_data_tree sel) (cache.getRootValue) proof)
      return verified)).run preexisting_cache] = 1 := by
  refine (probEvent_eq_one_simulateQ_randomOracle_run_iff (spec := spec α)
    (p := fun b : Bool => b = true) _ _).mpr ?_
  intro f _hf
  simp only [evalWithAnswerFn, verifyBatchProof, simulateQ_bind, simulateQ_pure,
    simulateQ_buildMerkleTree, simulateQ_getPutativeBatchRoot]
  change ((_ : α) == _) = true
  rw [beq_iff_eq]
  exact functional_batch_completeness leaf_data_tree sel h fun left right => f (left, right)

end InductiveMerkleTree
