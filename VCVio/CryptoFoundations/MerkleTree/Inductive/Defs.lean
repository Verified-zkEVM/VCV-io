/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ToMathlib.Data.IndexedBinaryTree.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Inductive Merkle Trees

This file defines the core raw-leaf Merkle tree over finite ordered binary-tree skeletons.
Every internal node has two children, but the tree need not be perfect or balanced. The same
type `α` represents leaf labels and internal digests, and only internal nodes query the binary
oracle `spec α`; callers that hash structured leaf payloads do so before entering this layer.

The API builds a full labeled tree, generates the intrinsically sized authentication path for a
leaf index, recomputes a putative root, and verifies it against a claimed root. Completeness,
binding, uniqueness, query bounds, transcript extraction, batch openings, and addressed hashing
are developed in the sibling `MerkleTree` modules.

## Representation

Trees use the indexed inductive representation from `ToMathlib.Data.IndexedBinaryTree`. The
skeleton appears in the types of leaf data, node data, leaf indices, and authentication paths.
Consequently, an index is valid for its tree by construction, and a proof contains exactly one
sibling digest per ancestor of the selected leaf.

This core deliberately models a homogeneous binary hash with already-labeled leaves and one root.
Leaf encodings and leaf hashing, non-binary hash operations, commitment caps, and logical data
layouts require separate abstractions rather than additional cases in this skeleton.

-/

@[expose] public section

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
def singleHash {m : Type _ → Type _} [Monad m] [hq : HasQuery (spec α) m]
    (left : α) (right : α) : m α := do
  let out ← hq.query ⟨left, right⟩
  return out

/-- Interpreting one Merkle hash query applies the supplied hash implementation. -/
lemma simulateQ_singleHash (f : QueryImpl (spec α) Id) (left right : α) :
    simulateQ f
        (singleHash (m := OracleComp (spec α)) left right) =
      f (left, right) := by
  change simulateQ f (liftM ((spec α).query (left, right))) = _
  rw [simulateQ_spec_query]

/-- Build the full Merkle tree, returning the tree populated with data on all its nodes -/
@[simp, grind]
def buildMerkleTree {m : Type _ → Type _} [Monad m] [HasQuery (spec α) m]
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
This receives an explicit hash function. Implemented as the bottom-up
`populateUp` from `ToMathlib.Data.IndexedBinaryTree.Basic`.
-/
@[simp, grind]
def buildMerkleTreeWithHash {s} (leaf_tree : LeafData α s) (hashFn : α → α → α) :
    (FullData α s) :=
  populateUp leaf_tree hashFn

/--
Running the monadic version of `buildMerkleTree` with an oracle function `f`
is equivalent to running the functional version of `buildMerkleTreeWithHash`
with the same oracle function.
-/
@[simp, grind =]
lemma simulateQ_buildMerkleTree {s} (leaf_data_tree : LeafData α s) (f : QueryImpl (spec α) Id) :
    simulateQ f (buildMerkleTree leaf_data_tree)
    = buildMerkleTreeWithHash leaf_data_tree fun (left right : α) =>
      (f ⟨left, right⟩) := by
  induction s with
  | leaf => match leaf_data_tree with | LeafData.leaf a => rfl
  | internal s_left s_right left_ih right_ih =>
    match leaf_data_tree with
    | LeafData.internal left right =>
      simp only [buildMerkleTree, buildMerkleTreeWithHash, singleHash,
        simulateQ_bind, simulateQ_pure, left_ih, right_ih]
      rfl

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
def getPutativeRoot {m : Type _ → Type _} [Monad m] [HasQuery (spec α) m] {s} :
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
lemma simulateQ_getPutativeRoot {s} (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α)
    (proof : List.Vector α idx.depth) (f : QueryImpl (spec α) Id) :
    simulateQ f (getPutativeRoot idx leafValue proof)
      =
    getPutativeRootWithHash idx leafValue proof fun (left right : α) => (f ⟨left, right⟩) := by
  induction idx generalizing leafValue with
  | ofLeaf => rfl
  | ofLeft idxLeft ih | ofRight idxRight ih =>
    change List.Vector α (_ + 1) at proof
    simp only [getPutativeRoot, getPutativeRootWithHash,
      SkeletonLeafIndex.depth]
    rw [simulateQ_bind, ih]
    change simulateQ f (singleHash _ _) = _
    rw [simulateQ_singleHash]

/--
Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
`root`.
Works by computing the putative root based on the branch, and comparing that to the actual root.
Returns `true` if the proof is valid, and `false` otherwise.
-/
@[simp, grind]
def verifyProof {m : Type _ → Type _} [Monad m] [HasQuery (spec α) m] [DecidableEq α]
    {s} (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α) (rootValue : α)
    (proof : List.Vector α idx.depth) : m Bool := do
  let putative_root ← (getPutativeRoot idx leafValue proof : m α)
  return (putative_root == rootValue)

end InductiveMerkleTree
