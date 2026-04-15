/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Data.IndexedBinaryTree.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Equivalences

This section contains theorems about equivalences between different tree indexing types
and data structures.
-/

namespace BinaryTree

section Equivalences

/-- Build `LeafData` from a function on leaf indices. -/
def LeafData.ofFun {α : Type _} (s : Skeleton)
    (f : SkeletonLeafIndex s → α) : LeafData α s :=
  match s with
  | .leaf => LeafData.leaf (f SkeletonLeafIndex.ofLeaf)
  | .internal l r =>
      LeafData.internal
        (LeafData.ofFun l (fun idx => f (SkeletonLeafIndex.ofLeft idx)))
        (LeafData.ofFun r (fun idx => f (SkeletonLeafIndex.ofRight idx)))

@[simp]
theorem LeafData.ofFun_get {α} {s} (tree : LeafData α s) :
    LeafData.ofFun s (fun idx => tree.get idx) = tree := by
  cases tree with
  | leaf value =>
    simp [LeafData.ofFun, LeafData.get_leaf]
  | @internal l r left right =>
    have ihL := LeafData.ofFun_get (s := l) left
    have ihR := LeafData.ofFun_get (s := r) right
    simp [LeafData.ofFun, ihL, ihR]

@[simp]
theorem LeafData.get_ofFun {α} {s} (f : SkeletonLeafIndex s → α) :
    (LeafData.ofFun s f).get = f := by
  funext idx
  induction idx with
  | ofLeaf => simp [LeafData.ofFun, LeafData.get_leaf]
  | ofLeft idx ih => simp [LeafData.ofFun, ih]
  | ofRight idx ih => simp [LeafData.ofFun, ih]

/-- Build `InternalData` from a function on internal indices. -/
def InternalData.ofFun {α : Type _} (s : Skeleton)
    (f : SkeletonInternalIndex s → α) : InternalData α s :=
  match s with
  | .leaf => InternalData.leaf
  | .internal l r =>
      InternalData.internal
        (f SkeletonInternalIndex.ofInternal)
        (InternalData.ofFun l (fun idx => f (SkeletonInternalIndex.ofLeft idx)))
        (InternalData.ofFun r (fun idx => f (SkeletonInternalIndex.ofRight idx)))

@[simp]
theorem InternalData.ofFun_get {α} {s} (tree : InternalData α s) :
    InternalData.ofFun s (fun idx => tree.get idx) = tree := by
  cases tree with
  | leaf => simp [InternalData.ofFun]
  | @internal l r value left right =>
    have ihL := InternalData.ofFun_get (s := l) left
    have ihR := InternalData.ofFun_get (s := r) right
    simp [InternalData.ofFun, ihL, ihR]

@[simp]
theorem InternalData.get_ofFun {α} {s} (f : SkeletonInternalIndex s → α) :
    (InternalData.ofFun s f).get = f := by
  funext idx
  induction idx with
  | ofInternal => simp [InternalData.ofFun]
  | ofLeft idx ih => simp [InternalData.ofFun, ih]
  | ofRight idx ih => simp [InternalData.ofFun, ih]

/-- Build `FullData` from a function on all node indices. -/
def FullData.ofFun {α : Type _} (s : Skeleton)
    (f : SkeletonNodeIndex s → α) : FullData α s :=
  match s with
  | .leaf => FullData.leaf (f SkeletonNodeIndex.ofLeaf)
  | .internal l r =>
      FullData.internal
        (f SkeletonNodeIndex.ofInternal)
        (FullData.ofFun l (fun idx => f (SkeletonNodeIndex.ofLeft idx)))
        (FullData.ofFun r (fun idx => f (SkeletonNodeIndex.ofRight idx)))

@[simp]
theorem FullData.ofFun_get {α} {s} (tree : FullData α s) :
    FullData.ofFun s (fun idx => tree.get idx) = tree := by
  cases tree with
  | leaf value => simp [FullData.ofFun, FullData.get_leaf]
  | @internal l r value left right =>
    have ihL := FullData.ofFun_get (s := l) left
    have ihR := FullData.ofFun_get (s := r) right
    simp [FullData.ofFun, ihL, ihR]

@[simp]
theorem FullData.get_ofFun {α} {s} (f : SkeletonNodeIndex s → α) :
    (FullData.ofFun s f).get = f := by
  funext idx
  induction idx with
  | ofLeaf => simp [FullData.ofFun, FullData.get_leaf]
  | ofInternal => simp [FullData.ofFun]
  | ofLeft idx ih => simp [FullData.ofFun, ih]
  | ofRight idx ih => simp [FullData.ofFun, ih]

/-- `LeafData`s are equivalent to functions from `SkeletonLeafIndex` to values -/
def LeafData.equivIndexFun {α : Type _} (s : Skeleton) :
    LeafData α s ≃ (SkeletonLeafIndex s → α) where
  toFun := fun tree idx => tree.get idx
  invFun := fun f => LeafData.ofFun s f
  left_inv := LeafData.ofFun_get (s := s)
  right_inv := LeafData.get_ofFun (s := s)

/-- `InternalData`s are equivalent to functions from `SkeletonInternalIndex` to values -/
def InternalData.equivIndexFun {α : Type _} (s : Skeleton) :
    InternalData α s ≃ (SkeletonInternalIndex s → α) where
  toFun := fun tree idx => tree.get idx
  invFun := fun f => InternalData.ofFun s f
  left_inv := InternalData.ofFun_get (s := s)
  right_inv := InternalData.get_ofFun (s := s)

/-- `FullData`s are equivalent to functions from `SkeletonNodeIndex` to values -/
def FullData.equivIndexFun {α : Type _} (s : Skeleton) :
    FullData α s ≃ (SkeletonNodeIndex s → α) where
  toFun := fun tree idx => tree.get idx
  invFun := fun f => FullData.ofFun s f
  left_inv := FullData.ofFun_get (s := s)
  right_inv := FullData.get_ofFun (s := s)

/-- A `LeafData` can be interpreted as a function from `SkeletonLeafIndex` to values -/
instance {α : Type _} {s : Skeleton} :
    CoeFun (LeafData α s) fun (_ : LeafData α s) => SkeletonLeafIndex s → α where
  coe := fun tree idx => tree.get idx

/-- An `InternalData` can be interpreted as a function from `SkeletonInternalIndex` to values -/
instance {α : Type _} {s : Skeleton} :
    CoeFun (InternalData α s) fun (_ : InternalData α s) => SkeletonInternalIndex s → α where
  coe := fun tree idx => tree.get idx

/-- A `FullData` can be interpreted as a function from `SkeletonNodeIndex` to values -/
instance {α : Type _} {s : Skeleton} :
    CoeFun (FullData α s) fun (_ : FullData α s) => SkeletonNodeIndex s → α where
  coe := fun tree idx => tree.get idx

/--
A function taking a `SkeletonNodeIndex s`
to either a `SkeletonInternalIndex s` or a `SkeletonLeafIndex s`
-/
def SkeletonNodeIndex.toSum {s : Skeleton} :
    SkeletonNodeIndex s → SkeletonInternalIndex s ⊕ SkeletonLeafIndex s :=
  fun idx =>
    match idx with
    | SkeletonNodeIndex.ofLeaf => Sum.inr (SkeletonLeafIndex.ofLeaf)
    | SkeletonNodeIndex.ofInternal => Sum.inl (SkeletonInternalIndex.ofInternal)
    | SkeletonNodeIndex.ofLeft idxLeft => match idxLeft.toSum with
      | .inl idxLeft => Sum.inl (SkeletonInternalIndex.ofLeft idxLeft)
      | .inr idxLeft => Sum.inr (SkeletonLeafIndex.ofLeft idxLeft)
    | SkeletonNodeIndex.ofRight idxRight => match idxRight.toSum with
      | .inl idxRight => Sum.inl (SkeletonInternalIndex.ofRight idxRight)
      | .inr idxRight => Sum.inr (SkeletonLeafIndex.ofRight idxRight)

/-- Equivalence between node indices and the sum of internal and leaf indices. -/
def SkeletonNodeIndex.sumEquiv (s : Skeleton) :
    SkeletonInternalIndex s ⊕ SkeletonLeafIndex s ≃ SkeletonNodeIndex s where
  toFun
    | Sum.inl idx => idx.toNodeIndex
    | Sum.inr idx => idx.toNodeIndex
  invFun := fun idx => idx.toSum
  left_inv := by
    intro x
    cases x with
    | inl i =>
        induction i with
        | ofInternal =>
            simp [SkeletonNodeIndex.toSum, SkeletonInternalIndex.toNodeIndex]
        | ofLeft i ih =>
            cases hSum : (i.toNodeIndex).toSum with
            | inl _ =>
                simpa [SkeletonNodeIndex.toSum, hSum, SkeletonInternalIndex.toNodeIndex] using ih
            | inr _ =>
                simp [hSum] at ih
        | ofRight i ih =>
            cases hSum : (i.toNodeIndex).toSum with
            | inl _ =>
                simpa [SkeletonNodeIndex.toSum, hSum, SkeletonInternalIndex.toNodeIndex] using ih
            | inr _ =>
                simp [hSum] at ih
    | inr j =>
        induction j with
        | ofLeaf =>
            simp [SkeletonNodeIndex.toSum, SkeletonLeafIndex.toNodeIndex]
        | ofLeft j ih =>
            cases hSum : (j.toNodeIndex).toSum with
            | inl _ =>
                simp [hSum] at ih
            | inr _ =>
                simpa [SkeletonNodeIndex.toSum, hSum, SkeletonLeafIndex.toNodeIndex] using ih
        | ofRight j ih =>
            cases hSum : (j.toNodeIndex).toSum with
            | inl _ =>
                simp [hSum] at ih
            | inr _ =>
                simpa [SkeletonNodeIndex.toSum, hSum, SkeletonLeafIndex.toNodeIndex] using ih
  right_inv := by
    intro idx
    induction idx with
    | ofLeaf => simp [SkeletonNodeIndex.toSum, SkeletonLeafIndex.toNodeIndex]
    | ofInternal => simp [SkeletonNodeIndex.toSum, SkeletonInternalIndex.toNodeIndex]
    | ofLeft idx ih =>
        cases hSum : idx.toSum with
        | inl _ =>
            simpa [SkeletonNodeIndex.toSum, hSum, SkeletonInternalIndex.toNodeIndex,
              SkeletonLeafIndex.toNodeIndex] using ih
        | inr _ =>
            simpa [SkeletonNodeIndex.toSum, hSum, SkeletonInternalIndex.toNodeIndex,
              SkeletonLeafIndex.toNodeIndex] using ih
    | ofRight idx ih =>
        cases hSum : idx.toSum with
        | inl _ =>
            simpa [SkeletonNodeIndex.toSum, hSum, SkeletonInternalIndex.toNodeIndex,
              SkeletonLeafIndex.toNodeIndex] using ih
        | inr _ =>
            simpa [SkeletonNodeIndex.toSum, hSum, SkeletonInternalIndex.toNodeIndex,
              SkeletonLeafIndex.toNodeIndex] using ih

/-- Equivalence between `FullData` and the product of `InternalData` and `LeafData` -/
def FullData.equiv {α : Type _} (s : Skeleton) :
    FullData α s ≃ InternalData α s × LeafData α s :=
  (FullData.equivIndexFun s).trans <|
    (Equiv.arrowCongr (SkeletonNodeIndex.sumEquiv s).symm (Equiv.refl α)).trans <|
      (Equiv.sumArrowEquivProdArrow (SkeletonInternalIndex s) (SkeletonLeafIndex s) α).trans <|
        Equiv.prodCongr (InternalData.equivIndexFun s).symm (LeafData.equivIndexFun s).symm


end Equivalences

end BinaryTree
