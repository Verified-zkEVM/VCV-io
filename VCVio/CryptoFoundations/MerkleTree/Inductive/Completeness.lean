/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

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
          simp only [buildMerkleTreeWithHash, getPutativeRootWithHash, LeafData.get_leaf,
            FullData.getRootValue_leaf]
  | ofLeft idxLeft ih =>
      cases leaf_data_tree with
      | internal left right =>
          simp only [getPutativeRootWithHash, LeafData.get_ofLeft, LeafData.leftSubtree_internal,
            generateProof, buildMerkleTreeWithHash, FullData.rightSubtree_internal,
            FullData.leftSubtree_internal, List.Vector.head_cons, FullData.internal_getRootValue]
          have hproof :=
            congrArg (fun p => getPutativeRootWithHash idxLeft (left.get idxLeft) p hash)
              (List.Vector.tail_cons (buildMerkleTreeWithHash right hash).getRootValue
                (generateProof (buildMerkleTreeWithHash left hash) idxLeft))
          let r := (buildMerkleTreeWithHash right hash).getRootValue
          exact (congrArg (fun x => hash x r) hproof).trans (congrArg (fun x => hash x r) (ih left))
  | ofRight idxRight ih =>
      cases leaf_data_tree with
      | internal left right =>
          simp only [getPutativeRootWithHash, generateProof, buildMerkleTreeWithHash,
            FullData.leftSubtree_internal, FullData.rightSubtree_internal, List.Vector.head_cons,
            LeafData.get_ofRight, LeafData.rightSubtree_internal, FullData.internal_getRootValue]
          have hproof :=
            congrArg (fun p => getPutativeRootWithHash idxRight (right.get idxRight) p hash)
              (List.Vector.tail_cons (buildMerkleTreeWithHash left hash).getRootValue
                (generateProof (buildMerkleTreeWithHash right hash) idxRight))
          let l := (buildMerkleTreeWithHash left hash).getRootValue
          exact (congrArg (hash l) hproof).trans (congrArg (hash l) (ih right))


/--
Completeness theorem for Merkle trees.

The proof proceeds by reducing to the functional completeness theorem by a theorem about
the OracleComp monad,
and then applying the functional version of the completeness theorem.
-/
@[simp]
theorem completeness [DecidableEq α] [SampleableType α] {s}
    (leaf_data_tree : LeafData α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    NeverFail ((simulateQ (randomOracle) (do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateProof cache idx
      let _ ← (verifyProof (m := OracleComp (spec α)) idx (leaf_data_tree.get idx)
        (cache.getRootValue) proof)
      )).run preexisting_cache) := by
  grind only [= HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

end InductiveMerkleTree
