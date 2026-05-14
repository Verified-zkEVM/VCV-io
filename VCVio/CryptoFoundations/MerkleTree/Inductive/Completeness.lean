/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Completeness of Inductive Merkle Trees

This file proves the completeness theorem for the inductive Merkle tree
construction defined in `VCVio.CryptoFoundations.MerkleTree.Inductive.Defs`:
honestly generated proofs verify against honestly built roots.

The proof is split into two pieces:

* `InductiveMerkleTree.functional_completeness` is a purely functional
  statement about `getPutativeRootWithHash` and `buildMerkleTreeWithHash`,
  proven by induction on the leaf index.
* `InductiveMerkleTree.completeness` lifts the functional statement to the
  monadic API by reducing through `simulateQ`.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/--
A functional form of the completeness theorem for Merkle trees.
This references the functional versions of `getPutativeRoot` and `buildMerkleTreeWithHash`
-/
@[simp, grind =]
theorem functional_completeness {s : Skeleton}
  (idx : SkeletonLeafIndex s)
  (leaf_data_tree : LeafData α s)
  (hash : α → α → α) :
  getPutativeRootWithHash
    idx
    (leaf_data_tree.get idx)
    (generateProof (buildMerkleTreeWithHash leaf_data_tree hash) idx)
    hash =
  (buildMerkleTreeWithHash leaf_data_tree hash).getRootValue := by
  induction idx with
  | ofLeaf =>
      cases leaf_data_tree with
      | leaf a =>
          grind
  | ofLeft idxLeft ih =>
      cases leaf_data_tree with
      | internal left right =>
          grind [Vector.tail_cons, Vector.head_cons]
  | ofRight idxRight ih =>
      cases leaf_data_tree with
      | internal left right =>
          grind [Vector.tail_cons, Vector.head_cons]


/--
Completeness theorem for Merkle trees.

The proof proceeds by reducing to the functional completeness theorem by a theorem about
the OracleComp monad,
and then applying the functional version of the completeness theorem.
-/
@[simp]
theorem completeness [DecidableEq α] [Inhabited α] [SampleableType α] {s}
    (leaf_data_tree : LeafData α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    Pr[fun v => v.1 = true | (simulateQ (spec α).randomOracle (do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateProof cache idx
      let verified ← (verifyProof (m := OracleComp (spec α)) idx (leaf_data_tree.get idx)
        (cache.getRootValue) proof)
      return verified)).run preexisting_cache] = 1 := by
  -- Reduce a probability-one claim about the random-oracle simulation to a value-level claim
  -- about `evalWithAnswerFn` for every answer function agreeing with the cache.
  refine (probEvent_eq_one_simulateQ_randomOracle_run_iff (spec := spec α)
    (p := fun b : Bool => b = true) _ _).mpr ?_
  intro f _hf
  -- Unfold `evalWithAnswerFn` and reduce simulation through the do-block, then collapse the
  -- residual `BEq` test to a value equality and finish by `functional_completeness`.
  change (simulateQ f (do
    let cache ← buildMerkleTree leaf_data_tree
    let proof := generateProof cache idx
    let verified ← (verifyProof (m := OracleComp (spec α)) idx (leaf_data_tree.get idx)
      (cache.getRootValue) proof)
    return verified) : Id Bool) = (true : Bool)
  simp only [verifyProof, simulateQ_bind, simulateQ_pure,
    simulateQ_buildMerkleTree, simulateQ_getPutativeRoot]
  change ((_ : α) == _) = true
  rw [beq_iff_eq]
  exact functional_completeness idx leaf_data_tree fun left right => f (left, right)

end InductiveMerkleTree
