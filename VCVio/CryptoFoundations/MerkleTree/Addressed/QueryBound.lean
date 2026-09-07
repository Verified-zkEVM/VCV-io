/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic
public import VCVio.OracleComp.QueryTracking.QueryBound
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Query bounds for effectful addressed Merkle traversals

This module owns structural query bounds for the typed addressed engine.  Adapters such as the
natural-number-indexed perfect-tree API and security proofs should instantiate these theorems
rather than repeat the induction over a leaf index.
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree OracleComp OracleSpec

universe u

variable {ι Y : Type u} {spec : OracleSpec.{u, u} ι}

/-- Root recovery invokes its internal-node callback once per authentication-path entry. -/
theorem isTotalQueryBound_getPutativeRootAddressedM
    {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y)
    (nodeBudget : ℕ) (idx : SkeletonLeafIndex s) (node : Y)
    (proof : List.Vector Y idx.depth)
    (hnode : ∀ a l r, IsTotalQueryBound (nodeHash a l r) nodeBudget) :
    IsTotalQueryBound (getPutativeRootAddressedM nodeHash idx node proof)
      (idx.depth * nodeBudget) := by
  induction idx generalizing node with
  | ofLeaf => exact trivial
  | ofLeft idx ih =>
      simp only [getPutativeRootAddressedM]
      have hchild := ih (nodeHash := fun a => nodeHash (.ofLeft a))
        (node := node) (proof := proof.tail) (fun a => hnode (.ofLeft a))
      have hroot := hnode .ofInternal
      simpa [SkeletonLeafIndex.depth, Nat.add_mul] using
        isTotalQueryBound_bind hchild fun child => hroot child proof.head
  | ofRight idx ih =>
      simp only [getPutativeRootAddressedM]
      have hchild := ih (nodeHash := fun a => nodeHash (.ofRight a))
        (node := node) (proof := proof.tail) (fun a => hnode (.ofRight a))
      have hroot := hnode .ofInternal
      simpa [SkeletonLeafIndex.depth, Nat.add_mul] using
        isTotalQueryBound_bind hchild fun child => hroot proof.head child

/-- Unit-cost root recovery makes at most the depth of the containing skeleton many queries. -/
theorem isTotalQueryBound_getPutativeRootAddressedM_skeleton_depth
    {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y)
    (idx : SkeletonLeafIndex s) (node : Y) (proof : List.Vector Y idx.depth)
    (hnode : ∀ a l r, IsTotalQueryBound (nodeHash a l r) 1) :
    IsTotalQueryBound (getPutativeRootAddressedM nodeHash idx node proof) s.depth := by
  have h := isTotalQueryBound_getPutativeRootAddressedM nodeHash 1 idx node proof hnode
  exact h.mono (by simpa using idx.depth_le_skeleton_depth)

end AddressedMerkleTree
