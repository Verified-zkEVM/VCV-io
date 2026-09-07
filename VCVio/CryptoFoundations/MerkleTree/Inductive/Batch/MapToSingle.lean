/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Map
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.ToSingle

/-!
# Mapping Batch Openings to Single-Path Witnesses

Pointwise mapping of a batch opening commutes with reading a selected value and, for a
homomorphism of binary hash algebras, with expanding the pruned proof at any selected leaf.
These laws connect `Option.some`-mapped openings to the single-path deterministic security
kernel without changing the canonical batch-proof representation.
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree

universe u v

variable {α : Type u} {β : Type v}

/-- Reading a selected value from the selected tuple of a full tree recovers the tree value at
the corresponding leaf node. -/
theorem selectedValueAt_selectedValues_toLeafData {s : Skeleton}
    (tree : FullData α s) (selector : LeafData Bool s)
    (idx : SkeletonLeafIndex s) (hidx : selector.get idx = true) :
    selectedValueAt (selectedValues tree.toLeafData selector) idx hidx =
      tree.get idx.toNodeIndex := by
  induction idx with
  | ofLeaf =>
      cases tree with
      | leaf value =>
          cases selector with
          | leaf selected =>
              cases selected with
              | false => simp at hidx
              | true => rfl
  | ofLeft idx ih =>
      cases tree with
      | internal root left right =>
          cases selector with
          | internal leftSelector rightSelector =>
              change selectedValueAt
                (selectedValues left.toLeafData leftSelector) idx _ =
                  left.get idx.toNodeIndex
              convert ih left leftSelector (by simpa using hidx) using 1
  | ofRight idx ih =>
      cases tree with
      | internal root left right =>
          cases selector with
          | internal leftSelector rightSelector =>
              change selectedValueAt
                (selectedValues right.toLeafData rightSelector) idx _ =
                  right.get idx.toNodeIndex
              convert ih right rightSelector (by simpa using hidx) using 1

/-- Reading a selected value commutes with pointwise mapping. -/
@[simp]
theorem selectedValueAt_map (f : α → β) {s : Skeleton} {sel : LeafData Bool s}
    (values : SelectedValues α sel) (idx : SkeletonLeafIndex s)
    (hidx : sel.get idx = true) :
    selectedValueAt (values.map f) idx hidx = f (selectedValueAt values idx hidx) := by
  induction idx with
  | ofLeaf =>
      cases sel with
      | leaf b =>
          cases b with
          | true => rfl
          | false => exact (by simp at hidx)
  | ofLeft idx ih =>
      cases sel with
      | internal l r =>
          change selectedValueAt (SelectedValues.map f values.1) idx _ =
            f (selectedValueAt values.1 idx _)
          convert ih values.1 (by simpa using hidx) using 1
  | ofRight idx ih =>
      cases sel with
      | internal l r =>
          change selectedValueAt (SelectedValues.map f values.2) idx _ =
            f (selectedValueAt values.2 idx _)
          convert ih values.2 (by simpa using hidx) using 1

/-- Expanding a mapped pruned proof at a selected leaf is the pointwise map of the original
single authentication path, provided the value map preserves the binary hash operation. -/
theorem batchToSingleProof_map
    (f : α → β) (hashα : α → α → α) (hashβ : β → β → β)
    (hhash : ∀ left right, f (hashα left right) = hashβ (f left) (f right))
    {s : Skeleton} {sel : LeafData Bool s} (values : SelectedValues α sel)
    (proof : BatchProof α sel) (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true) :
    batchToSingleProof hashβ (values.map f) (proof.map f) idx hidx =
      (batchToSingleProof hashα values proof idx hidx).map f := by
  induction proof with
  | leaf =>
      cases idx
      rfl
  | internalBoth pl pr ihl ihr =>
      cases idx with
      | ofLeft idx =>
          simp only [SelectedValues.map, BatchProof.map, batchToSingleProof,
            List.Vector.map_cons]
          apply congrArg₂ List.Vector.cons
          · exact getPutativeBatchRootWithHash_map f hashα hashβ hhash values.2 pr
          · convert ihl values.1 idx (by simpa using hidx) using 1
      | ofRight idx =>
          simp only [SelectedValues.map, BatchProof.map, batchToSingleProof,
            List.Vector.map_cons]
          apply congrArg₂ List.Vector.cons
          · exact getPutativeBatchRootWithHash_map f hashα hashβ hhash values.1 pl
          · convert ihr values.2 idx (by simpa using hidx) using 1
  | pruneRight hr rightRoot pl ih =>
      cases idx with
      | ofLeft idx =>
          simp only [SelectedValues.map, BatchProof.map, batchToSingleProof,
            List.Vector.map_cons]
          apply congrArg₂ List.Vector.cons
          · rfl
          · convert ih values.1 idx (by simpa using hidx) using 1
      | ofRight idx =>
          exact absurd (LeafData.anySelected_of_get idx (by simpa using hidx)) (by simp [hr])
  | pruneLeft hl leftRoot pr ih =>
      cases idx with
      | ofRight idx =>
          simp only [SelectedValues.map, BatchProof.map, batchToSingleProof,
            List.Vector.map_cons]
          apply congrArg₂ List.Vector.cons
          · rfl
          · convert ih values.2 idx (by simpa using hidx) using 1
      | ofLeft idx =>
          exact absurd (LeafData.anySelected_of_get idx (by simpa using hidx)) (by simp [hl])

end InductiveMerkleTree
