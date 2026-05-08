/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import VCVio.OracleComp.QueryTracking.QueryBound
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Inductive Merkle Tree Lemmas

This file collects reusable structural lemmas about the inductive Merkle tree
operations defined in `Defs.lean`. In particular, it provides total-query-bound
lemmas for `singleHash`, `getPutativeRoot`, and `verifyProof`, plus a generic
bind-extraction utility on `IsTotalQueryBound` used to combine them.
-/

namespace InductiveMerkleTree

open OracleSpec OracleComp BinaryTree

variable {α : Type}

/-! ### Total query bounds for Merkle-tree primitives -/

/-- If `oa >>= ob` has a total query bound `n`, then `oa` alone has total query bound `n`
(the continuation can only add queries, not remove them). -/
lemma _root_.IsTotalQueryBound.of_bind_left
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsTotalQueryBound (oa >>= ob) n) :
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- `singleHash` makes exactly one oracle query, hence has total query bound `1`. -/
lemma singleHash_isTotalQueryBound (left right : α) :
    IsTotalQueryBound (singleHash (m := OracleComp (spec α)) left right) 1 := by
  simp only [singleHash, HasQuery.instOfMonadLift_query]
  rw [isTotalQueryBound_query_bind_iff]
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
  | ofLeft idxLeft ih =>
      simp only [getPutativeRoot, SkeletonLeafIndex.depth]
      refine isTotalQueryBound_bind (n₁ := idxLeft.depth) (n₂ := 1) ?_ ?_
      · exact ih proof.tail
      · intro h
        exact singleHash_isTotalQueryBound h proof.head
  | ofRight idxRight ih =>
      simp only [getPutativeRoot, SkeletonLeafIndex.depth]
      refine isTotalQueryBound_bind (n₁ := idxRight.depth) (n₂ := 1) ?_ ?_
      · exact ih proof.tail
      · intro h
        exact singleHash_isTotalQueryBound proof.head h

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
  refine isTotalQueryBound_bind (n₁ := idx.depth) (n₂ := 0) ?_ ?_
  · exact getPutativeRoot_isTotalQueryBound idx leafValue proof
  · intro _; trivial

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
  (verifyProof_isTotalQueryBound idx leafValue rootValue proof).mono
    idx.depth_le_skeleton_depth

end InductiveMerkleTree
