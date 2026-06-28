/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import VCVio.CryptoFoundations.VectorCommitment.Basic
import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

/-!
# Inductive Merkle trees as (batch-opening) vector commitments

This file realizes the inductive Merkle tree of
`VCVio.CryptoFoundations.MerkleTree.Inductive.Defs` against the abstract positional commitment
interfaces of `VCVio.CryptoFoundations.VectorCommitment.Basic`:

- `InductiveMerkleTree.vectorCommitment` — the Merkle `VectorCommitment` (single-position opening);
- `InductiveMerkleTree.naiveBatchOpenMerkleTree` — a `BatchOpeningVectorCommitment` obtained from
  the above via `VectorCommitment.toBatchOpening`. It is *naive* in that a batch opening is just the
  list of individual leaf authentication paths, with no sharing of common interior hashes; a
  purpose-built batch proof could be more succinct.

These instances are what a consumer such as the Kilian transformation
(`VCVio.CryptoFoundations.Kilian`) is meant to be supplied with; that file depends on the abstract
commitment interface only, not on this concrete Merkle realization.

The construction is in the standard-model / collision-resistant-hash formulation: hashing is a pure
two-to-one function `hashFn`, so all commitment operations are pure and the instances live in any
monad. Positions are laid out on a caller-supplied skeleton `s` via a position-to-leaf equivalence
`e : ι ≃ SkeletonLeafIndex s`; an opening is the authentication path (the sibling hashes along the
leaf's branch), carried as a plain `List` of hashes.
-/

open OracleComp OracleSpec BinaryTree

namespace InductiveMerkleTree

variable {α : Type}

/-- Build the leaf data of a Merkle tree of skeleton `s` from a function assigning a value to each
leaf position. -/
def leafDataOfFn : (s : Skeleton) → (SkeletonLeafIndex s → α) → LeafData α s
  | Skeleton.leaf, f => LeafData.leaf (f SkeletonLeafIndex.ofLeaf)
  | Skeleton.internal _ _, f =>
      LeafData.internal
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofLeft i))
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofRight i))

/-- The inductive Merkle tree as a `VectorCommitment`.

Positions `ι` are mapped to the leaves of skeleton `s` by the equivalence `e`, and `hashFn` is the
two-to-one compression function. Committing builds the full tree and exposes its root; an opening
for a position is its authentication path (`generateProof`), carried as a `List`; verification
recomputes the putative root from the leaf value and path (`getPutativeRootWithHash`) and compares
it to the commitment. The operations are pure, so the instance is available in any monad `m`. -/
def vectorCommitment {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    VectorCommitment m ι α α (FullData α s) (List α) where
  commit data :=
    let tree := buildMerkleTreeWithHash (leafDataOfFn s fun i => data (e.symm i)) hashFn
    pure (tree.getRootValue, tree)
  decode tree i := tree.toLeafData.get (e i)
  openAt tree i := pure (generateProof tree (e i)).toList
  verifyOpen root i v op :=
    if h : op.length = (e i).depth then
      decide (getPutativeRootWithHash (e i) v ⟨op, h⟩ hashFn = root)
    else false

/-- The inductive Merkle tree as a `BatchOpeningVectorCommitment`, obtained from
`InductiveMerkleTree.vectorCommitment` via `VectorCommitment.toBatchOpening`.

A batch opening for a list of positions is simply the list of their individual authentication paths
(each as `(position, value, path)`); verification checks each claimed position against its path
independently. This shares no interior hashes between paths, hence *naive* — a dedicated multi-leaf
Merkle proof could compress the common prefixes — but it is correct and requires nothing beyond the
single-position instance. -/
def naiveBatchOpenMerkleTree {ι : Type} {m : Type → Type} [Monad m]
    [DecidableEq ι] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    BatchOpeningVectorCommitment m ι α α (FullData α s) (List (ι × α × List α)) :=
  (vectorCommitment s e hashFn).toBatchOpening

end InductiveMerkleTree
