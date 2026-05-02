/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Data.IndexedBinaryTree.Basic


/-!
# Lemmas about Indexed Binary Trees

## TODOs

- More relationships between tree navigations
  - Which navigation sequences are equivalent to each other?
  - How do these navigations affect depth?
- API for flattening a tree to a list
- Define `Lattice` structure on trees
  - a subset relation on trees, mappings of indices to indices of supertrees


-/

namespace BinaryTree

section Navigation

/-- The parent of a left child, when it exists, is the node itself. -/
theorem SkeletonNodeIndex.leftChild_bind_parent {s : Skeleton}
    (idx : SkeletonNodeIndex s) :
    idx.leftChild >>= parent = idx.leftChild.map (fun _ => idx) := by
  induction idx with
  | ofLeaf =>
    simp [SkeletonNodeIndex.leftChild, Option.bind]
  | @ofInternal left right =>
    cases left
    <;>
    simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, getRootIndex]
  | @ofLeft left right idxLeft ih =>
    -- Analyze whether the left child of idxLeft exists
    cases hchild : idxLeft.leftChild with
    | none =>
      simp [SkeletonNodeIndex.leftChild, Option.bind, hchild]
    | some child =>
      -- From the IH specialized with hchild, we get that the parent of child is idxLeft
      have hc : parent child = some idxLeft := by
        simpa [SkeletonNodeIndex.leftChild, Option.bind, hchild] using ih
      -- Now consider the shape of the child to compute the parent of (ofLeft child)
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
  | @ofRight left right idxRight ih =>
    -- Analyze whether the left child of idxRight exists
    cases hchild : idxRight.leftChild with
    | none =>
      simp [SkeletonNodeIndex.leftChild, Option.bind, hchild]
    | some child =>
      have hc : parent child = some idxRight := by
        simpa [SkeletonNodeIndex.leftChild, Option.bind, hchild] using ih
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]

/-- The parent of a right child, when it exists, is the node itself. -/
theorem SkeletonNodeIndex.rightChild_bind_parent {s : Skeleton}
    (idx : SkeletonNodeIndex s) :
    idx.rightChild >>= parent = idx.rightChild.map (fun _ => idx) := by
  induction idx with
  | ofLeaf =>
    simp [SkeletonNodeIndex.rightChild, Option.bind]
  | @ofInternal left right =>
    cases right
    <;>
    simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, getRootIndex]
  | @ofLeft left right idxLeft ih =>
    -- Analyze whether the right child of idxLeft exists
    cases hchild : idxLeft.rightChild with
    | none =>
      simp [SkeletonNodeIndex.rightChild, Option.bind, hchild]
    | some child =>
      have hc : parent child = some idxLeft := by
        simpa [SkeletonNodeIndex.rightChild, Option.bind, hchild] using ih
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
  | @ofRight left right idxRight ih =>
    -- Analyze whether the right child of idxRight exists
    cases hchild : idxRight.rightChild with
    | none =>
      simp [SkeletonNodeIndex.rightChild, Option.bind, hchild]
    | some child =>
      have hc : parent child = some idxRight := by
        simpa [SkeletonNodeIndex.rightChild, Option.bind, hchild] using ih
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]

/-- The parent of a node of depth zero is none. -/
theorem SkeletonNodeIndex.parent_of_depth_zero {s : Skeleton}
    (idx : SkeletonNodeIndex s) (h : idx.depth = 0) :
    parent idx = none := by
  cases idx with
  | ofLeaf => rfl
  | ofInternal => rfl
  | ofLeft idxLeft =>
    unfold depth at h
    simp_all
  | ofRight idxRight =>
    unfold depth at h
    simp_all

-- TODO?: reorder the arguments to `LeafData` etc. so that the skeleton comes first?

instance {s} : Functor (fun α => LeafData α s) where
  map f x := x.map f

instance {s} : Functor (fun α => InternalData α s) where
  map f x := x.map f

instance {s} : Functor (fun α => FullData α s) where
  map f x := x.map f


instance {s} : LawfulFunctor (fun α => LeafData α s) where
  map_const := rfl
  id_map x := by
    induction x with
    | leaf value => simp [Functor.map, LeafData.map]
    | internal left right ihL ihR => simp_all [Functor.map, LeafData.map]
  comp_map g h x := by
    induction x with
    | leaf value => simp [Functor.map, LeafData.map]
    | internal left right ihL ihR => simp_all [Functor.map, LeafData.map]

instance {s} : LawfulFunctor (fun α => InternalData α s) where
  map_const := rfl
  id_map x := by
    induction x with
    | leaf => simp [Functor.map, InternalData.map]
    | internal value tL tR ihL ihR => simp_all [Functor.map, InternalData.map]
  comp_map g h x := by
    induction x with
    | leaf => simp [Functor.map, InternalData.map]
    | internal value tL tR ihL ihR => simp_all [Functor.map, InternalData.map]

instance {s} : LawfulFunctor (fun α => FullData α s) where
  map_const := rfl
  id_map x := by
    induction x with
    | leaf value => simp [Functor.map, FullData.map]
    | internal value tL tR ihL ihR => simp_all [Functor.map, FullData.map]
  comp_map g h x := by
    induction x with
    | leaf value => simp [Functor.map, FullData.map]
    | internal value tL tR ihL ihR => simp_all [Functor.map, FullData.map]

end Navigation

/-! ## Skeleton size: depth and leafCount -/

section Size

@[simp]
theorem Skeleton.depth_leaf : Skeleton.leaf.depth = 0 := rfl

@[simp]
theorem Skeleton.depth_internal (left right : Skeleton) :
    (Skeleton.internal left right).depth = max left.depth right.depth + 1 := rfl

@[simp]
theorem Skeleton.leafCount_leaf : Skeleton.leaf.leafCount = 1 := rfl

@[simp]
theorem Skeleton.leafCount_internal (left right : Skeleton) :
    (Skeleton.internal left right).leafCount = left.leafCount + right.leafCount := rfl

/-- Every skeleton has at least one leaf. -/
theorem Skeleton.leafCount_pos : ∀ s : Skeleton, 0 < s.leafCount
  | Skeleton.leaf => Nat.zero_lt_one
  | Skeleton.internal left _ =>
    Nat.add_pos_left (Skeleton.leafCount_pos left) _

/-- The depth of any leaf index is bounded by the depth of its skeleton. -/
theorem SkeletonLeafIndex.depth_le_skeleton_depth :
    ∀ {s : Skeleton} (idx : SkeletonLeafIndex s), idx.depth ≤ s.depth
  | _, SkeletonLeafIndex.ofLeaf => Nat.le_refl 0
  | Skeleton.internal left right, SkeletonLeafIndex.ofLeft idxLeft => by
    simp only [SkeletonLeafIndex.depth, Skeleton.depth_internal]
    exact Nat.succ_le_succ
      (Nat.le_trans idxLeft.depth_le_skeleton_depth (Nat.le_max_left left.depth right.depth))
  | Skeleton.internal left right, SkeletonLeafIndex.ofRight idxRight => by
    simp only [SkeletonLeafIndex.depth, Skeleton.depth_internal]
    exact Nat.succ_le_succ
      (Nat.le_trans idxRight.depth_le_skeleton_depth (Nat.le_max_right left.depth right.depth))

/-- The depth of any node index is bounded by the depth of its skeleton. -/
theorem SkeletonNodeIndex.depth_le_skeleton_depth :
    ∀ {s : Skeleton} (idx : SkeletonNodeIndex s), idx.depth ≤ s.depth
  | _, SkeletonNodeIndex.ofLeaf => Nat.le_refl 0
  | _, SkeletonNodeIndex.ofInternal => Nat.zero_le _
  | Skeleton.internal left right, SkeletonNodeIndex.ofLeft idxLeft => by
    simp only [SkeletonNodeIndex.depth, Skeleton.depth_internal]
    exact Nat.succ_le_succ
      (Nat.le_trans idxLeft.depth_le_skeleton_depth (Nat.le_max_left left.depth right.depth))
  | Skeleton.internal left right, SkeletonNodeIndex.ofRight idxRight => by
    simp only [SkeletonNodeIndex.depth, Skeleton.depth_internal]
    exact Nat.succ_le_succ
      (Nat.le_trans idxRight.depth_le_skeleton_depth (Nat.le_max_right left.depth right.depth))

end Size

end BinaryTree
