/-
Copyright (c) 2024 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import ToMathlib.Data.IndexedBinaryTree.Basic

/-!
# Inductive Merkle Trees

This file implements Merkle Trees. In contrast to the other Merkle tree implementation in
`VCVio.CryptoFoundations.MerkleTree`, this one is defined inductively.

## Implementation Notes

This works with trees that are indexed inductive binary trees,
(i.e. indexed in that their definitions and methods carry parameters regarding their structure)
as defined in `ToMathlib.Data.IndexedBinaryTree`.

* We found that the inductive definition seems likely to be convenient for a few reasons:
  * It allows us to handle non-perfect trees.
  * It can allow us to use trees of arbitrary structure in the extractor.
* I considered the indexed type useful because the completeness theorem and extractibility theorems
  take indices or sets of indices as parameters,
  and because we are working with trees of arbitrary structure,
  this lets us avoid having to check that these indices are valid.

## Plan/TODOs

- [x] Basic Merkle tree API
  - [x] `buildMerkleTree`
  - [x] `generateProof`
  - [x] `getPutativeRoot`
  - [x] `verifyProof`
- [x] Completeness theorem
- [ ] Collision Lemma (See SNARGs book 18.3)
  - (this is really not a lemma about oracles, so it could go with the binary tree API)
- [ ] Extractibility (See SNARGs book 18.5)
- [ ] Multi-leaf proofs
- [ ] Arbirary arity trees
- [ ] Multi-instance

-/


namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

section spec

variable (α : Type _)

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with
    elements from some type `α`.

  We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct a Merkle tree for boolean
  vectors of length `n`. -/
@[reducible]
def spec : OracleSpec (α × α) := (α × α) →ₒ α

@[simp, grind =]
lemma domain_def : (spec α).Domain = (α × α) := rfl

@[simp]
lemma range_def (z) : (spec α).Range z = α := rfl

end spec


variable {α : Type _}

/-- Example: a single hash computation -/
@[simp, grind]
def singleHash {m : Type _ → Type _} [Monad m] [MonadLiftT (OracleQuery (spec α)) m]
    (left : α) (right : α) : m α := do
  let out ← (spec α).query ⟨left, right⟩
  return out

/-- Build the full Merkle tree, returning the tree populated with data on all its nodes -/
@[simp, grind]
def buildMerkleTree {m : Type _ → Type _} [Monad m] [MonadLiftT (OracleQuery (spec α)) m]
    {s} (leaf_tree : LeafData α s) : m (FullData α s) :=
  match leaf_tree with
  | LeafData.leaf a => do return (FullData.leaf a)
  | LeafData.internal left right => do
    let leftTree ← buildMerkleTree left
    let rightTree ← buildMerkleTree right
    let rootHash ← singleHash leftTree.getRootValue rightTree.getRootValue
    return FullData.internal rootHash leftTree rightTree

/--
A functional form of merkle tree construction, that doesn't depend on the monad.
This receives an explicit hash function
-/
@[simp, grind]
def buildMerkleTreeWithHash {s} (leaf_tree : LeafData α s) (hashFn : α → α → α) :
    (FullData α s) :=
  match leaf_tree with
  | LeafData.leaf a => FullData.leaf a
  | LeafData.internal left right =>
    let leftTree := buildMerkleTreeWithHash left hashFn
    let rightTree := buildMerkleTreeWithHash right hashFn
    let rootHash := hashFn (leftTree.getRootValue) (rightTree.getRootValue)
    FullData.internal rootHash leftTree rightTree

/--
Running the monadic version of `buildMerkleTree` with an oracle function `f`
is equivalent to running the functional version of `buildMerkleTreeWithHash`
with the same oracle function.
-/
@[simp, grind =]
lemma simulateQ_buildMerkleTree {s} (leaf_data_tree : LeafData α s)
    (f : QueryImpl (spec α) Id) :
    simulateQ f (buildMerkleTree leaf_data_tree)
    = buildMerkleTreeWithHash leaf_data_tree fun (left right : α) =>
      (f ⟨left, right⟩) := by
  induction s with
  | leaf =>
    match leaf_data_tree with
    | LeafData.leaf a =>
      rfl
  | internal s_left s_right left_ih right_ih =>
    match leaf_data_tree with
    | LeafData.internal left right =>
      simp only [buildMerkleTree, buildMerkleTreeWithHash, singleHash,
        simulateQ_bind, simulateQ_pure]
      rw [left_ih left, right_ih right]; rfl

/--
Generate a Merkle proof for a leaf at a given idx
The proof consists of the sibling hashes needed to recompute the root.
Its length is indexed by the leaf depth, so malformed extra hashes are unrepresentable.

TODO rename this to copath and move to BinaryTree?
-/
@[simp, grind]
def generateProof {s} (cache_tree : FullData α s) :
    (idx : BinaryTree.SkeletonLeafIndex s) → List.Vector α idx.depth
  | .ofLeaf => List.Vector.nil
  | .ofLeft idxLeft =>
    List.Vector.cons ((cache_tree.rightSubtree).getRootValue)
      (generateProof cache_tree.leftSubtree idxLeft)
  | .ofRight idxRight =>
    List.Vector.cons ((cache_tree.leftSubtree).getRootValue)
      (generateProof cache_tree.rightSubtree idxRight)

/--
Given a leaf index, a leaf value at that index, and a proof of the corresponding depth,
returns the hash that would be the root of the tree if the proof was valid.
i.e. the hash obtained by combining the leaf in sequence with each member of the proof,
according to its index.
-/
@[simp, grind]
def getPutativeRoot {m : Type _ → Type _} [Monad m] [MonadLiftT (OracleQuery (spec α)) m] {s} :
    (idx : BinaryTree.SkeletonLeafIndex s) → (leafValue : α) →
      List.Vector α idx.depth → m α
  | BinaryTree.SkeletonLeafIndex.ofLeaf, leafValue, _ => do
      return leafValue
  | BinaryTree.SkeletonLeafIndex.ofLeft idxLeft, leafValue, proof => do
      let ancestorBelowRootHash ← getPutativeRoot idxLeft leafValue proof.tail
      singleHash ancestorBelowRootHash proof.head
  | BinaryTree.SkeletonLeafIndex.ofRight idxRight, leafValue, proof => do
      let ancestorBelowRootHash ← getPutativeRoot idxRight leafValue proof.tail
      singleHash proof.head ancestorBelowRootHash

/--
A functional version of `getPutativeRoot` that does not depend on the monad.
It receives an explicit hash function `hashFn` that combines two hashes into one.
And recursively calls itself down the tree.
-/
@[simp, grind]
def getPutativeRootWithHash {s} :
    (idx : BinaryTree.SkeletonLeafIndex s) → (leafValue : α) →
      List.Vector α idx.depth → (hashFn : α → α → α) → α
  | BinaryTree.SkeletonLeafIndex.ofLeaf, leafValue, _, _ =>
      leafValue
  | BinaryTree.SkeletonLeafIndex.ofLeft idxLeft, leafValue, proof, hashFn =>
      hashFn (getPutativeRootWithHash idxLeft leafValue proof.tail hashFn) proof.head
  | BinaryTree.SkeletonLeafIndex.ofRight idxRight, leafValue, proof, hashFn =>
      hashFn proof.head (getPutativeRootWithHash idxRight leafValue proof.tail hashFn)

/--
Running the monadic version of `getPutativeRoot` with an oracle function `f`,
it is equivalent to running the functional version of `getPutativeRootWithHash`
-/
@[simp, grind =]
lemma simulateQ_getPutativeRoot {s} (idx : BinaryTree.SkeletonLeafIndex s)
    (leafValue : α) (proof : List.Vector α idx.depth) (f : QueryImpl (spec α) Id) :
    simulateQ f (getPutativeRoot idx leafValue proof)
      =
    getPutativeRootWithHash idx leafValue proof fun (left right : α) => (f ⟨left, right⟩) := by
  induction idx generalizing leafValue with
  | ofLeaf =>
      rfl
  | ofLeft idxLeft ih =>
      simp only [getPutativeRoot, getPutativeRootWithHash, singleHash,
        simulateQ_bind]
      rw [ih]
      rfl
  | ofRight idxRight ih =>
      simp only [getPutativeRoot, getPutativeRootWithHash, singleHash,
        simulateQ_bind]
      rw [ih]
      rfl

/--
Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
`root`.
Works by computing the putative root based on the branch, and comparing that to the actual root.
Outputs `failure` if the proof is invalid.
-/
@[simp, grind]
def verifyProof {m : Type _ → Type _} [Monad m] [MonadLiftT (OracleQuery (spec α)) m]
    [DecidableEq α] {s} (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α) (rootValue : α)
    (proof : List.Vector α idx.depth) : OptionT m Unit := do
  let putative_root ← (getPutativeRoot idx leafValue proof : m α)
  guard (putative_root = rootValue)

end InductiveMerkleTree
