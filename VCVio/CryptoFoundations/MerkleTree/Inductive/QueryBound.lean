/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import VCVio.OracleComp.QueryTracking.QueryBound
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Total query bounds for inductive Merkle tree primitives

This file establishes `IsTotalQueryBound` lemmas for the oracle computations
defined in `Defs.lean`:

* `singleHash_isTotalQueryBound` — `singleHash` makes one oracle query.
* `getPutativeRoot_isTotalQueryBound` — `getPutativeRoot` makes `idx.depth`
  queries, one per level walked from the leaf to the root.
* `verifyProof_isTotalQueryBound` — `verifyProof` inherits the same bound.
* `verifyProof_isTotalQueryBound_skeleton_depth` — coarsening to the uniform
  `s.depth` bound, useful when the bound must not depend on `idx`.

These bounds are consumed downstream by the extractability argument, which
needs to know the total number of queries any honest Merkle operation issues.
-/

namespace InductiveMerkleTree

open OracleSpec OracleComp BinaryTree

variable {α : Type}

/-! ### Total query bounds for Merkle-tree primitives -/

/-- `singleHash` makes exactly one oracle query, hence has total query bound `1`. -/
lemma singleHash_isTotalQueryBound (left right : α) :
    IsTotalQueryBound (singleHash (m := OracleComp (spec α)) left right) 1 := by
  simp only [singleHash, HasQuery.instOfMonadLift_query, isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.zero_lt_one, fun _ => trivial⟩

/-- `getPutativeRoot` makes one oracle query per level of `idx`, so it has total query
bound `idx.depth`. -/
lemma getPutativeRoot_isTotalQueryBound {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leafValue : α) (proof : List.Vector α idx.depth) :
    IsTotalQueryBound
      (getPutativeRoot (m := OracleComp (spec α)) idx leafValue proof)
      idx.depth := by
  induction idx with
  | ofLeaf =>
      simp only [getPutativeRoot, SkeletonLeafIndex.depth]
      trivial
  | ofLeft idxLeft ih | ofRight idxRight ih =>
      simp only [getPutativeRoot, SkeletonLeafIndex.depth]
      exact isTotalQueryBound_bind (ih proof.tail) fun h => singleHash_isTotalQueryBound _ _

/-- `verifyProof` makes the same `idx.depth` queries as `getPutativeRoot`; the
trailing equality test is pure. -/
lemma verifyProof_isTotalQueryBound
    [DecidableEq α] {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leafValue rootValue : α)
    (proof : List.Vector α idx.depth) :
    IsTotalQueryBound
      (verifyProof (m := OracleComp (spec α)) idx leafValue rootValue proof)
      idx.depth := by
  unfold verifyProof
  exact isTotalQueryBound_bind (n₂ := 0)
    (getPutativeRoot_isTotalQueryBound idx leafValue proof) fun _ => trivial

/-- Coarser form of `verifyProof_isTotalQueryBound` bounded by the full skeleton
depth `s.depth` rather than the per-leaf `idx.depth`. Useful when the bound must be
uniform across all leaf indices of `s`. -/
lemma verifyProof_isTotalQueryBound_skeleton_depth
    [DecidableEq α] {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leafValue rootValue : α)
    (proof : List.Vector α idx.depth) :
    IsTotalQueryBound
      (verifyProof (m := OracleComp (spec α)) idx leafValue rootValue proof)
      s.depth :=
  (verifyProof_isTotalQueryBound idx leafValue rootValue proof).mono idx.depth_le_skeleton_depth

end InductiveMerkleTree
