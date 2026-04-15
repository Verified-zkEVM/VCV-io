/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

-- TODO minimize imports
import Mathlib.Tactic.Use
import Mathlib.Data.Set.Basic


/-!
# Inductive Indexed Binary Trees

## A Note about Process/API when working with this

I am trying to follow a process of making simp theorems and procedures
that decompose the trees as much as possible.

1. Use casework to take a tree of a known structure and specify the parts of that structure
2. Push maps or other functions on this down to the bottom of the (tree / syntax tree)
3. I then have e.g. `FullData.internal value1 left1 right1 = FullData.internal value2 left2 right2`
4. and then I can congruence the values and subtrees

## Notes & TODOs

- [ ] `aesop` extension for the above?
- [ ] Split off a `Defs.lean` file

- Functions for navigating tree
  - [x] Go to parent if it exists
  - [ ] Go to left child if it exists
  - [ ] Go to right child if it exists
  - [ ] Go to sibling if it exists
  - [ ] Return pair of left and right children if they exist
- Define a datatype for indices of trees agnostic of the skeleton,
  - This type has an equivalence to lists of bools,
  - and maps from the the other indexing types.
  - get? functions

-/

namespace BinaryTree

section Skeleton

/--
Inductive data type for a binary tree skeleton.
A skeleton is a binary tree without values, used to represent the structure of the tree.
-/
inductive Skeleton where
  | leaf : Skeleton
  | internal : Skeleton → Skeleton → Skeleton

/-- Type of indices of leaves of a skeleton -/
inductive SkeletonLeafIndex : Skeleton → Type
  | ofLeaf : SkeletonLeafIndex Skeleton.leaf
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonLeafIndex left) :
      SkeletonLeafIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonLeafIndex right) :
      SkeletonLeafIndex (Skeleton.internal left right)

/-- Type of indices of internal nodes of a skeleton -/
inductive SkeletonInternalIndex : Skeleton → Type
  | ofInternal {left right} : SkeletonInternalIndex (Skeleton.internal left right)
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonInternalIndex left) :
      SkeletonInternalIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonInternalIndex right) :
      SkeletonInternalIndex (Skeleton.internal left right)

/-- Type of indices of any node of a skeleton -/
inductive SkeletonNodeIndex : Skeleton → Type
  | ofLeaf : SkeletonNodeIndex Skeleton.leaf
  | ofInternal {left right} :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonNodeIndex left) :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonNodeIndex right) :
      SkeletonNodeIndex (Skeleton.internal left right)

/-- Construct a `SkeletonNodeIndex` from a `SkeletonLeafIndex` -/
def SkeletonLeafIndex.toNodeIndex {s : Skeleton} (idx : SkeletonLeafIndex s) :
    SkeletonNodeIndex s :=
  match idx with
  | SkeletonLeafIndex.ofLeaf => SkeletonNodeIndex.ofLeaf
  | SkeletonLeafIndex.ofLeft idxLeft =>
    SkeletonNodeIndex.ofLeft (SkeletonLeafIndex.toNodeIndex idxLeft)
  | SkeletonLeafIndex.ofRight idxRight =>
    SkeletonNodeIndex.ofRight (SkeletonLeafIndex.toNodeIndex idxRight)

/-- Construct a `SkeletonNodeIndex` from a `SkeletonInternalIndex` -/
def SkeletonInternalIndex.toNodeIndex {s : Skeleton} (idx : SkeletonInternalIndex s) :
    SkeletonNodeIndex s :=
  match idx with
  | SkeletonInternalIndex.ofInternal => SkeletonNodeIndex.ofInternal
  | SkeletonInternalIndex.ofLeft idxLeft =>
    SkeletonNodeIndex.ofLeft (SkeletonInternalIndex.toNodeIndex idxLeft)
  | SkeletonInternalIndex.ofRight idxRight =>
    SkeletonNodeIndex.ofRight (SkeletonInternalIndex.toNodeIndex idxRight)

end Skeleton

/-!
This section contains predicates about indices determined by their neighborhood in the tree.
-/

section Local

/-- Check whether a leaf index is the root of its tree. -/
def SkeletonLeafIndex.isRoot {s : Skeleton} (idx : SkeletonLeafIndex s) : Bool :=
  match idx with
  | SkeletonLeafIndex.ofLeaf => true
  | SkeletonLeafIndex.ofLeft _ => false
  | SkeletonLeafIndex.ofRight _ => false

/-- Check whether an internal-node index is the root of its tree. -/
def SkeletonInternalIndex.isRoot {s : Skeleton} (idx : SkeletonInternalIndex s) : Bool :=
  match idx with
  | SkeletonInternalIndex.ofInternal => true
  | SkeletonInternalIndex.ofLeft _ => false
  | SkeletonInternalIndex.ofRight _ => false

/-- Check whether a node index is the root of its tree. -/
def SkeletonNodeIndex.isRoot {s : Skeleton} (idx : SkeletonNodeIndex s) : Bool :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => true
  | SkeletonNodeIndex.ofInternal => true
  | SkeletonNodeIndex.ofLeft _ => false
  | SkeletonNodeIndex.ofRight _ => false

/-- Every `SkeletonLeafIndex` points to a leaf. -/
def SkeletonLeafIndex.isLeaf {s : Skeleton} (_ : SkeletonLeafIndex s) : Bool :=
  true

/-- No `SkeletonInternalIndex` points to a leaf. -/
def SkeletonInternalIndex.isLeaf {s : Skeleton} (_ : SkeletonInternalIndex s) : Bool :=
  false

/-- Check whether a node index points to a leaf of the tree. -/
def SkeletonNodeIndex.isLeaf {s : Skeleton} (idx : SkeletonNodeIndex s) : Bool :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => true
  | SkeletonNodeIndex.ofInternal => false
  | SkeletonNodeIndex.ofLeft idxLeft => idxLeft.isLeaf
  | SkeletonNodeIndex.ofRight idxRight => idxRight.isLeaf

end Local

section Data

/--
A binary tree with values stored at leaves.
-/
inductive LeafData (α : Type _) : Skeleton → Type _
  | leaf (value : α) : LeafData α Skeleton.leaf
  | internal {left right} (leftData : LeafData α left) (rightData : LeafData α right) :
      LeafData α (Skeleton.internal left right)
  deriving Repr

/--
A binary tree with values stored in internal nodes.
-/
inductive InternalData (α : Type _) : Skeleton → Type _
  | leaf : InternalData α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : InternalData α left)
      (rightData : InternalData α right) : InternalData α (Skeleton.internal left right)
  deriving Repr

/--
A binary tree with values stored at both leaves and internal nodes.
-/
inductive FullData (α : Type _) : Skeleton → Type _
  | leaf (value : α) : FullData α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : FullData α left)
      (rightData : FullData α right) :
      FullData α (Skeleton.internal left right)
  deriving Repr

end Data

section Subtree

/--
Get the left subtree of a `LeafData`.
-/
def LeafData.leftSubtree {α : Type _} {s_left s_right : Skeleton}
    (tree : LeafData α (Skeleton.internal s_left s_right)) :
    LeafData α s_left :=
  match tree with
  | LeafData.internal left _right =>
    left

/-- Get the right subtree of a `LeafData`. -/
def LeafData.rightSubtree {α : Type _} {s_left s_right : Skeleton}
    (tree : LeafData α (Skeleton.internal s_left s_right)) :
    LeafData α s_right :=
  match tree with
  | LeafData.internal _left right =>
    right

/-- Get the left subtree of a `InternalData`. -/
def InternalData.leftSubtree {α : Type _} {s_left s_right : Skeleton}
    (tree : InternalData α (Skeleton.internal s_left s_right)) :
    InternalData α s_left :=
  match tree with
  | InternalData.internal _ left _right =>
    left

/-- Get the right subtree of a `InternalData`. -/
def InternalData.rightSubtree {α : Type _} {s_left s_right : Skeleton}
    (tree : InternalData α (Skeleton.internal s_left s_right)) :
    InternalData α s_right :=
  match tree with
  | InternalData.internal _ _left right =>
    right

/-- Get the left subtree of a `FullData`. -/
def FullData.leftSubtree {α : Type _} {s_left s_right : Skeleton}
    (tree : FullData α (Skeleton.internal s_left s_right)) :
    FullData α s_left :=
  match tree with
  | FullData.internal _ left _right =>
    left

/-- Get the right subtree of a `FullData`. -/
def FullData.rightSubtree {α : Type _} {s_left s_right : Skeleton}
    (tree : FullData α (Skeleton.internal s_left s_right)) :
    FullData α s_right :=
  match tree with
  | FullData.internal _ _left right =>
    right

@[simp]
theorem LeafData.leftSubtree_internal {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right) :
    (LeafData.internal left right).leftSubtree = left := by
  rfl

@[simp]
theorem LeafData.rightSubtree_internal {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right) :
    (LeafData.internal left right).rightSubtree = right := by
  rfl

@[simp]
theorem InternalData.leftSubtree_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : InternalData α s_left) (right : InternalData α s_right) :
    (InternalData.internal value left right).leftSubtree = left := by
  rfl

@[simp]
theorem InternalData.rightSubtree_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : InternalData α s_left) (right : InternalData α s_right) :
    (InternalData.internal value left right).rightSubtree = right := by
  rfl

@[simp]
theorem FullData.leftSubtree_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : FullData α s_left) (right : FullData α s_right) :
    (FullData.internal value left right).leftSubtree = left := by
  rfl

@[simp]
theorem FullData.rightSubtree_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : FullData α s_left) (right : FullData α s_right) :
    (FullData.internal value left right).rightSubtree = right := by
  rfl

end Subtree

section get

/-- Get a value of a `LeafData` at an index. -/
def LeafData.get {s} {α : Type _}
    (tree : LeafData α s) (idx : SkeletonLeafIndex s) : α :=
  match tree, idx with
  | LeafData.leaf value, SkeletonLeafIndex.ofLeaf => value
  | LeafData.internal left _, SkeletonLeafIndex.ofLeft idxLeft =>
    LeafData.get left idxLeft
  | LeafData.internal _ right, SkeletonLeafIndex.ofRight idxRight =>
    LeafData.get right idxRight

/-- Get a value of a `InternalData` at an index. -/
def InternalData.get {s} {α : Type _}
    (tree : InternalData α s) (idx : SkeletonInternalIndex s) : α :=
  match tree, idx with
  | InternalData.internal value _ _, SkeletonInternalIndex.ofInternal => value
  | InternalData.internal _ left _, SkeletonInternalIndex.ofLeft idxLeft =>
    InternalData.get left idxLeft
  | InternalData.internal _ _ right, SkeletonInternalIndex.ofRight idxRight =>
    InternalData.get right idxRight

/-- Get a value of a `FullData` at an index. -/
def FullData.get {s} {α : Type _}
    (tree : FullData α s) (idx : SkeletonNodeIndex s) : α :=
  match tree, idx with
  | FullData.leaf value, SkeletonNodeIndex.ofLeaf => value
  | FullData.internal value _ _, SkeletonNodeIndex.ofInternal => value
  | FullData.internal _ left _, SkeletonNodeIndex.ofLeft idxLeft =>
    FullData.get left idxLeft
  | FullData.internal _ _ right, SkeletonNodeIndex.ofRight idxRight =>
    FullData.get right idxRight

@[simp]
theorem LeafData.get_leaf {α} (a : α) :
    (LeafData.leaf a).get SkeletonLeafIndex.ofLeaf = a := by
  rfl

@[simp]
theorem LeafData.get_ofLeft {s_left s_right : Skeleton} {α : Type _}
    (tree : LeafData α (Skeleton.internal s_left s_right))
    (idxLeft : SkeletonLeafIndex s_left) :
    tree.get (SkeletonLeafIndex.ofLeft idxLeft) =
      tree.leftSubtree.get idxLeft := by
  match tree with
  | LeafData.internal left _ =>
    rfl

@[simp]
theorem LeafData.get_ofRight {s_left s_right : Skeleton} {α : Type _}
    (tree : LeafData α (Skeleton.internal s_left s_right))
    (idxRight : SkeletonLeafIndex s_right) :
    tree.get (SkeletonLeafIndex.ofRight idxRight) =
      tree.rightSubtree.get idxRight := by
  match tree with
  | LeafData.internal _ right =>
    rfl

@[simp]
theorem LeafData.get_internal_ofLeft {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right)
    (idxLeft : SkeletonLeafIndex s_left) :
    (LeafData.internal left right).get (SkeletonLeafIndex.ofLeft idxLeft) =
      left.get idxLeft := by
  rfl

@[simp]
theorem LeafData.get_internal_ofRight {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right)
    (idxRight : SkeletonLeafIndex s_right) :
    (LeafData.internal left right).get (SkeletonLeafIndex.ofRight idxRight) =
      right.get idxRight := by
  rfl

@[simp]
theorem FullData.get_leaf {α} (a : α) :
    (FullData.leaf a).get SkeletonNodeIndex.ofLeaf = a := by
  rfl

@[simp]
theorem InternalData.get_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : InternalData α s_left) (right : InternalData α s_right) :
    (InternalData.internal value left right).get SkeletonInternalIndex.ofInternal = value := by
  rfl

@[simp]
theorem InternalData.get_ofLeft {s_left s_right : Skeleton} {α}
    (tree : InternalData α (Skeleton.internal s_left s_right))
    (idxLeft : SkeletonInternalIndex s_left) :
    tree.get (SkeletonInternalIndex.ofLeft idxLeft) =
      tree.leftSubtree.get idxLeft := by
  match tree with
  | InternalData.internal _ left _ =>
    rfl

@[simp]
theorem InternalData.get_ofRight {s_left s_right : Skeleton} {α}
    (tree : InternalData α (Skeleton.internal s_left s_right))
    (idxRight : SkeletonInternalIndex s_right) :
    tree.get (SkeletonInternalIndex.ofRight idxRight) =
      tree.rightSubtree.get idxRight := by
  match tree with
  | InternalData.internal _ _ right =>
    rfl

@[simp]
theorem InternalData.get_internal_ofLeft {α} {s_left s_right : Skeleton}
    (value : α) (left : InternalData α s_left) (right : InternalData α s_right)
    (idxLeft : SkeletonInternalIndex s_left) :
    (InternalData.internal value left right).get (SkeletonInternalIndex.ofLeft idxLeft) =
      left.get idxLeft := by
  rfl

@[simp]
theorem InternalData.get_internal_ofRight {α} {s_left s_right : Skeleton}
    (value : α) (left : InternalData α s_left) (right : InternalData α s_right)
    (idxRight : SkeletonInternalIndex s_right) :
    (InternalData.internal value left right).get (SkeletonInternalIndex.ofRight idxRight) =
      right.get idxRight := by
  rfl

@[simp]
theorem FullData.get_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : FullData α s_left) (right : FullData α s_right) :
    (FullData.internal value left right).get SkeletonNodeIndex.ofInternal = value := by
  rfl

@[simp]
theorem FullData.get_ofLeft {s_left s_right : Skeleton} {α}
    (tree : FullData α (Skeleton.internal s_left s_right))
    (idxLeft : SkeletonNodeIndex s_left) :
    tree.get (SkeletonNodeIndex.ofLeft idxLeft) =
      tree.leftSubtree.get idxLeft := by
  match tree with
  | FullData.internal _ left _ =>
    rfl

@[simp]
theorem FullData.get_ofRight {s_left s_right : Skeleton} {α}
    (tree : FullData α (Skeleton.internal s_left s_right))
    (idxRight : SkeletonNodeIndex s_right) :
    tree.get (SkeletonNodeIndex.ofRight idxRight) =
      tree.rightSubtree.get idxRight := by
  match tree with
  | FullData.internal _ _ right =>
    rfl

@[simp]
theorem FullData.get_internal_ofLeft {α} {s_left s_right : Skeleton}
    (value : α) (left : FullData α s_left) (right : FullData α s_right)
    (idxLeft : SkeletonNodeIndex s_left) :
    (FullData.internal value left right).get (SkeletonNodeIndex.ofLeft idxLeft) =
      left.get idxLeft := by
  rfl

@[simp]
theorem FullData.get_internal_ofRight {α} {s_left s_right : Skeleton}
    (value : α) (left : FullData α s_left) (right : FullData α s_right)
    (idxRight : SkeletonNodeIndex s_right) :
    (FullData.internal value left right).get (SkeletonNodeIndex.ofRight idxRight) =
      right.get idxRight := by
  rfl

end get

section forget

/-- Convert a `FullData` to a `LeafData` by dropping the internal node values. -/
def FullData.toLeafData {α : Type _} {s : Skeleton}
    (tree : FullData α s) : LeafData α s :=
  match tree with
  | FullData.leaf value => LeafData.leaf value
  | FullData.internal _ left right =>
    LeafData.internal (left.toLeafData) (right.toLeafData)

/-- Convert a `FullData` to a `InternalData` by dropping the leaf node values. -/
def FullData.toInternalData {α : Type _} {s : Skeleton}
    (tree : FullData α s) : InternalData α s :=
  match tree with
  | FullData.leaf _ => InternalData.leaf
  | FullData.internal value left right =>
    InternalData.internal value (left.toInternalData) (right.toInternalData)

@[simp]
theorem FullData.toLeafData_leaf {α} (a : α) :
    (FullData.leaf a).toLeafData = LeafData.leaf a := by
  rfl

@[simp]
theorem FullData.toLeafData_leftSubtree {α} {s_left s_right : Skeleton}
    (tree : FullData α (Skeleton.internal s_left s_right)) :
    tree.toLeafData.leftSubtree =
      tree.leftSubtree.toLeafData := by
  match tree with
  | FullData.internal _ left _right =>
    rfl

@[simp]
theorem FullData.toLeafData_rightSubtree {α} {s_left s_right : Skeleton}
    (tree : FullData α (Skeleton.internal s_left s_right)) :
    tree.toLeafData.rightSubtree =
      tree.rightSubtree.toLeafData := by
  match tree with
  | FullData.internal _ _left right =>
    rfl

theorem FullData.toLeafData_eq_leaf {α} (a : α) (tree : FullData α Skeleton.leaf)
    (h : LeafData.leaf a = tree.toLeafData) :
    tree = FullData.leaf a := by
  cases tree with
  | leaf value =>
    simp only [FullData.toLeafData] at h
    cases h
    rfl

@[simp]
theorem FullData.toLeafData_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : FullData α s_left) (right : FullData α s_right) :
    (FullData.internal value left right).toLeafData =
      LeafData.internal (left.toLeafData) (right.toLeafData) := by
  rfl

end forget

section root

/-- Get the root index of a skeleton. -/
def getRootIndex (s : Skeleton) : SkeletonNodeIndex s := match s with
  | Skeleton.leaf => SkeletonNodeIndex.ofLeaf
  | Skeleton.internal _ _ =>
    SkeletonNodeIndex.ofInternal

/-- Get the root value of a FullData. -/
def FullData.getRootValue {s} {α : Type _} (tree : FullData α s) :=
  tree.get (getRootIndex s)

@[simp]
theorem FullData.getRootValue_leaf {α} (a : α) :
    (FullData.leaf a).getRootValue = a := by
  rfl

@[simp]
theorem FullData.internal_getRootValue {s_left s_right : Skeleton} {α : Type _}
    (value : α) (left : FullData α s_left) (right : FullData α s_right) :
    (FullData.internal value left right).getRootValue =
      value := by
  rfl

end root

section depth

/-- Depth of a SkeletonLeafIndex -/
def SkeletonLeafIndex.depth {s : Skeleton} : SkeletonLeafIndex s → Nat
  | SkeletonLeafIndex.ofLeaf => 0
  | SkeletonLeafIndex.ofLeft idxLeft => idxLeft.depth + 1
  | SkeletonLeafIndex.ofRight idxRight => idxRight.depth + 1

/-- Depth of a SkeletonInternalIndex -/
def SkeletonInternalIndex.depth {s : Skeleton} : SkeletonInternalIndex s → Nat
  | SkeletonInternalIndex.ofInternal => 0
  | SkeletonInternalIndex.ofLeft idxLeft => idxLeft.depth + 1
  | SkeletonInternalIndex.ofRight idxRight => idxRight.depth + 1

/-- Depth of a SkeletonNodeIndex -/
def SkeletonNodeIndex.depth {s : Skeleton} : SkeletonNodeIndex s → Nat
  | SkeletonNodeIndex.ofLeaf => 0
  | SkeletonNodeIndex.ofInternal => 0
  | SkeletonNodeIndex.ofLeft idxLeft => idxLeft.depth + 1
  | SkeletonNodeIndex.ofRight idxRight => idxRight.depth + 1

end depth

section Navigation

/--
Get the parent of a `SkeletonNodeIndex`, or `none` if the index is the root.
-/
def SkeletonNodeIndex.parent {s : Skeleton} (idx : SkeletonNodeIndex s) :
    Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | SkeletonNodeIndex.ofInternal => none
  | SkeletonNodeIndex.ofLeft (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofLeft (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofLeft idxLeft =>
    idxLeft.parent.map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofRight (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofRight idxRight =>
    idxRight.parent.map (SkeletonNodeIndex.ofRight)

/--
Return the sibling node index of a given `SkeletonNodeIndex`. Or `none` if the node is the root.
-/
def SkeletonNodeIndex.sibling {s : Skeleton} (idx : SkeletonNodeIndex s) :
    Option (SkeletonNodeIndex s) :=
  match idx with
  | .ofLeaf => none
  | .ofInternal => none
  | @SkeletonNodeIndex.ofLeft _ right .ofLeaf => some (.ofRight (getRootIndex right))
  | @SkeletonNodeIndex.ofLeft _ right .ofInternal => some (.ofRight (getRootIndex right))
  | .ofLeft (.ofLeft idxLL) => idxLL.ofLeft.sibling.map .ofLeft
  | .ofLeft (.ofRight idxLR) => idxLR.ofRight.sibling.map .ofLeft
  | @SkeletonNodeIndex.ofRight left _ .ofLeaf => some (.ofLeft (getRootIndex left))
  | @SkeletonNodeIndex.ofRight left _ .ofInternal => some (.ofLeft (getRootIndex left))
  | .ofRight (.ofLeft idxRL) => idxRL.ofLeft.sibling.map .ofRight
  | .ofRight (.ofRight idxRR) => idxRR.ofRight.sibling.map .ofRight

/--
Return the left child of a `SkeletonNodeIndex`, or `none` if the index is a leaf.
-/
def SkeletonNodeIndex.leftChild {s : Skeleton} (idx : SkeletonNodeIndex s) :
    Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | @SkeletonNodeIndex.ofInternal left right =>
    some (SkeletonNodeIndex.ofLeft (getRootIndex left))
  | SkeletonNodeIndex.ofLeft idxLeft =>
    idxLeft.leftChild.map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight idxRight =>
    idxRight.leftChild.map (SkeletonNodeIndex.ofRight)

/--
Return the right child of a `SkeletonNodeIndex`, or `none` if the index is a leaf.
-/
def SkeletonNodeIndex.rightChild {s : Skeleton} (idx : SkeletonNodeIndex s) :
    Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | @SkeletonNodeIndex.ofInternal left right =>
    some (SkeletonNodeIndex.ofRight (getRootIndex right))
  | SkeletonNodeIndex.ofLeft idxLeft =>
    idxLeft.rightChild.map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight idxRight =>
    idxRight.rightChild.map (SkeletonNodeIndex.ofRight)


end Navigation

section Paths


/--
Given a `Skeleton`, and a node index of the skeleton,
return a list of node indices which are the ancestors of the node,
starting with the root node, and going down to but not including the node itself.
-/
def SkeletonNodeIndex.path {s : Skeleton} (idx : SkeletonNodeIndex s) :
    List (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => []
  | SkeletonNodeIndex.ofInternal => []
  | SkeletonNodeIndex.ofLeft idxLeft =>
    SkeletonNodeIndex.ofInternal :: idxLeft.path.map SkeletonNodeIndex.ofLeft
  | SkeletonNodeIndex.ofRight idxRight =>
    SkeletonNodeIndex.ofInternal :: idxRight.path.map SkeletonNodeIndex.ofRight

/-- Find the siblings of a node and its ancestors, starting with the child of the root -/
def FullData.copath {α} {s} (cache_tree : FullData α s) :
    BinaryTree.SkeletonLeafIndex s → List α
  | .ofLeaf => []
  | .ofLeft idxLeft =>
    (cache_tree.rightSubtree).getRootValue ::
      (copath cache_tree.leftSubtree idxLeft)
  | .ofRight idxRight =>
    (cache_tree.leftSubtree).getRootValue ::
      (copath cache_tree.rightSubtree idxRight)

end Paths

section map


/-- Apply a function to every value stored in a `LeafData`. -/
def LeafData.map {α β : Type _} (f : α → β) {s : Skeleton}
    (tree : LeafData α s) : LeafData β s :=
  match tree with
  | LeafData.leaf value => LeafData.leaf (f value)
  | LeafData.internal left right =>
    LeafData.internal (left.map f) (right.map f)

/-- Apply a function to every value stored in an `InternalData`. -/
def InternalData.map {α β : Type _} (f : α → β) {s : Skeleton}
    (tree : InternalData α s) : InternalData β s :=
  match tree with
  | InternalData.leaf => InternalData.leaf
  | InternalData.internal value left right =>
    InternalData.internal (f value) (left.map f) (right.map f)

/-- Apply a function to every value stored in a `FullData`. -/
def FullData.map {α β : Type _} (f : α → β) {s : Skeleton}
    (tree : FullData α s) : FullData β s :=
  match tree with
  | FullData.leaf value => FullData.leaf (f value)
  | FullData.internal value left right =>
    FullData.internal (f value) (left.map f) (right.map f)

@[simp]
theorem FullData.map_leaf {α β} (f : α → β) (a : α) :
    (FullData.leaf a).map f = FullData.leaf (f a) := by
  rfl

@[simp]
theorem FullData.map_internal {α β} {s_left s_right : Skeleton}
    (f : α → β) (value : α) (left : FullData α s_left) (right : FullData α s_right) :
    (FullData.internal value left right).map f =
      FullData.internal (f value) (left.map f) (right.map f) := by
  rfl

@[simp]
theorem LeafData.map_leaf {α β} (f : α → β) (a : α) :
    (LeafData.leaf a).map f = LeafData.leaf (f a) := by
  rfl

@[simp]
theorem LeafData.map_internal {α β} {s_left s_right : Skeleton}
    (f : α → β) (left : LeafData α s_left) (right : LeafData α s_right) :
    (LeafData.internal left right).map f =
      LeafData.internal (left.map f) (right.map f) := by
  rfl


theorem FullData.map_getRootValue {α β : Type _} {s : Skeleton}
    (f : α → β) (tree : FullData α s) :
    (tree.map f).getRootValue = f (tree.getRootValue) := by
  cases tree <;> rfl

end map

section ComposeBuild

/-!
## Build

This section contains theorems about building full trees from leaf trees.
-/

/-- Build a `FullData` tree by hashing together the roots of child subtrees. -/
def LeafData.composeBuild {α : Type _} {s : Skeleton} (leaf_data_tree : LeafData α s)
    (compose : α → α → α) :
    FullData α s :=
  match leaf_data_tree with
  | .leaf value =>
    .leaf value
  | .internal left right =>
    let leftTree := left.composeBuild compose
    let rightTree := right.composeBuild compose
    .internal
      (compose leftTree.getRootValue rightTree.getRootValue)
      leftTree
      rightTree

@[simp]
theorem LeafData.composeBuild_leaf {α} (a : α)
    (compose : α → α → α) :
    (LeafData.leaf a).composeBuild compose = FullData.leaf a := by
  rfl

@[simp]
theorem LeafData.composeBuild_internal {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right)
    (compose : α → α → α) :
    (LeafData.internal left right).composeBuild compose =
      FullData.internal
        (compose (left.composeBuild compose).getRootValue (right.composeBuild compose).getRootValue)
        (left.composeBuild compose)
        (right.composeBuild compose) := by
  rfl

@[simp]
theorem LeafData.composeBuild_getRootValue {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right)
    (compose : α → α → α) :
    ((LeafData.internal left right).composeBuild compose).getRootValue =
      compose (left.composeBuild compose).getRootValue
        (right.composeBuild compose).getRootValue := by
  rfl

/-- Lift a binary function through two `Option` arguments. -/
def Option.doubleBind {α β γ : Type _} (f : α → β → Option γ)
    (x : Option α) (y : Option β) : Option γ := do
  f (← x) (← y)

/-- Build a tree while allowing failures in the composition function. -/
def LeafData.optionComposeBuild {α : Type _} {s : Skeleton} (leaf_data_tree : LeafData α s)
    (compose : α → α → Option α) :
    FullData (Option α) s :=
  (leaf_data_tree.map (.some)).composeBuild (Option.doubleBind compose)

@[simp]
theorem LeafData.optionComposeBuild_leaf {α} (a : α)
    (compose : α → α → Option α) :
    (LeafData.leaf a).optionComposeBuild compose = FullData.leaf (.some a) := by
  rfl

@[simp]
theorem LeafData.optionComposeBuild_internal {α} {s_left s_right : Skeleton}
    (left : LeafData α s_left) (right : LeafData α s_right)
    (compose : α → α → Option α) :
    (LeafData.internal left right).optionComposeBuild compose =
      FullData.internal
        (Option.doubleBind compose
          (left.optionComposeBuild compose).getRootValue
          (right.optionComposeBuild compose).getRootValue)
        (left.optionComposeBuild compose)
        (right.optionComposeBuild compose) := by
  rfl

end ComposeBuild

end BinaryTree
