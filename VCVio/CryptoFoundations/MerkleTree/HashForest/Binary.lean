/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.HashForest.Defs

/-!
# Binary Merkle trees as hash forests

The addressed binary Merkle engine embeds into `MerkleHashForest` without changing its query
semantics. Leaf and internal operations remain disjoint, leaf and node addresses retain their
types, ordered pairs remain ordered, and a caller-provided leaf digest still performs no query.

The translation theorem states agreement at the public commitment boundary. It makes the binary
engine a proved specialization of the variadic forest semantics rather than a second competing
implementation of binary Merkle construction.
-/

@[expose] public section

namespace MerkleHashForest

open BinaryTree MerkleTreeHashing OracleComp

universe u v w x y

/-- The two operation domains used by an embedded binary Merkle tree. -/
inductive BinaryOperationKind where
  | leaf
  | node
deriving DecidableEq

/-- Leaf and internal addresses remain disjoint in an embedded binary tree. -/
inductive BinaryAddress (LeafAddress : Type u) (NodeAddress : Type v) where
  | leaf (address : LeafAddress)
  | node (address : NodeAddress)
deriving DecidableEq

variable {LeafAddress : Type u} {NodeAddress : Type v}
  {Payload : Type w} {EncodedLeaf : Type x} {Digest : Type y}

/-- Translate one tagged binary Merkle query into the general operation-query language. -/
def binaryQuery :
    HashQuery LeafAddress NodeAddress EncodedLeaf Digest →
      Query BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress) EncodedLeaf Digest
  | .leaf address input => {
      kind := .leaf
      context := ()
      address := .leaf address
      inputs := [.payload input]
    }
  | .node address left right => {
      kind := .node
      context := ()
      address := .node address
      inputs := [.child left, .child right]
    }

/-- The binary-query translation preserves every query distinction, including leaf/node domain
separation and the order of internal children. -/
theorem binaryQuery_injective :
    Function.Injective
      (binaryQuery (LeafAddress := LeafAddress) (NodeAddress := NodeAddress)
        (EncodedLeaf := EncodedLeaf) (Digest := Digest)) := by
  intro left right h
  cases left <;> cases right <;> simp [binaryQuery] at h ⊢
  all_goals simp_all

/-- Restrict a general hash-forest implementation to the translated binary query language. -/
def binaryAnswer
    (answer : Query BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
      EncodedLeaf Digest → Digest) :
    HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest :=
  answer ∘ binaryQuery

/-- Interpret binary Merkle queries by issuing their injective translations in the general
hash-forest oracle. -/
def binaryQueryImpl :
    QueryImpl (MerkleTreeHashing.spec LeafAddress NodeAddress EncodedLeaf Digest)
      (OracleComp (spec BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
        EncodedLeaf Digest)) :=
  fun query => HasQuery.query
    (spec := spec BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
      EncodedLeaf Digest) (binaryQuery query)

/-- Recursively translate a binary Merkle computation at an arbitrary subtree position. -/
def binaryTreeAt {s : Skeleton}
    (leafAddress : SkeletonLeafIndex s → LeafAddress)
    (nodeAddress : SkeletonInternalIndex s → NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    Tree BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress) EncodedLeaf Digest :=
  match payloads with
  | .leaf payload =>
      match leafHashing with
      | .providedDigest digest => .providedDigest (digest payload)
      | .hash encode =>
          .operation .leaf () (.leaf (leafAddress .ofLeaf)) [.payload (encode payload)]
  | .internal left right =>
      let leftTree := binaryTreeAt
        (fun index => leafAddress (.ofLeft index))
        (fun index => nodeAddress (.ofLeft index)) leafHashing left
      let rightTree := binaryTreeAt
        (fun index => leafAddress (.ofRight index))
        (fun index => nodeAddress (.ofRight index)) leafHashing right
      .operation .node () (.node (nodeAddress .ofInternal)) [.child leftTree, .child rightTree]

/-- Translate an addressed binary Merkle construction into one hash-computation tree. -/
def binaryTree {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    Tree BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress) EncodedLeaf Digest :=
  binaryTreeAt addressing.leaf addressing.node leafHashing payloads

/-- The one-root forest corresponding to an ordinary binary Merkle commitment. -/
def binaryForest {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    Forest BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
      EncodedLeaf Digest 1 :=
  (binaryTree addressing leafHashing payloads).toForest

private def binaryRoot {s : Skeleton}
    (leafAddress : SkeletonLeafIndex s → LeafAddress)
    (nodeAddress : SkeletonInternalIndex s → NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    OracleComp (MerkleTreeHashing.spec LeafAddress NodeAddress EncodedLeaf Digest) Digest :=
  match payloads with
  | .leaf payload => leafDigest
      (NodeAddress := NodeAddress) leafHashing (leafAddress .ofLeaf) payload
  | .internal left right => do
      let leftRoot ← binaryRoot
        (fun index => leafAddress (.ofLeft index))
        (fun index => nodeAddress (.ofLeft index)) leafHashing left
      let rightRoot ← binaryRoot
        (fun index => leafAddress (.ofRight index))
        (fun index => nodeAddress (.ofRight index)) leafHashing right
      nodeDigest (LeafAddress := LeafAddress) (EncodedLeaf := EncodedLeaf)
        (nodeAddress .ofInternal) leftRoot rightRoot

private theorem evaluateTree_binaryTreeAt {s : Skeleton}
    (leafAddress : SkeletonLeafIndex s → LeafAddress)
    (nodeAddress : SkeletonInternalIndex s → NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    evaluateTree
        (m := OracleComp (spec BinaryOperationKind Unit
          (BinaryAddress LeafAddress NodeAddress) EncodedLeaf Digest))
        (binaryTreeAt leafAddress nodeAddress leafHashing payloads) =
      simulateQ binaryQueryImpl (binaryRoot leafAddress nodeAddress leafHashing payloads) := by
  induction payloads with
  | leaf payload =>
      cases leafHashing <;>
        simp [binaryTreeAt, binaryRoot, evaluateTree, Internal.evaluateTree,
          Internal.evaluateInputs, Internal.evaluateInput, leafDigest,
          binaryQueryImpl, binaryQuery]
  | internal left right leftIH rightIH =>
      simp only [binaryTreeAt, evaluateTree, Internal.evaluateTree,
        Internal.evaluateInputs, Internal.evaluateInput, binaryRoot, simulateQ_bind]
      have leftIH' := leftIH
        (fun index => leafAddress (.ofLeft index))
        (fun index => nodeAddress (.ofLeft index))
      have rightIH' := rightIH
        (fun index => leafAddress (.ofRight index))
        (fun index => nodeAddress (.ofRight index))
      change Internal.evaluateTree _ = _ at leftIH'
      change Internal.evaluateTree _ = _ at rightIH'
      rw [leftIH', rightIH']
      rfl

private theorem binaryRoot_eq_build_root {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    binaryRoot addressing.leaf addressing.node leafHashing payloads =
      (fun tree => tree.getRootValue) <$>
        build
          (m := OracleComp
            (MerkleTreeHashing.spec LeafAddress NodeAddress EncodedLeaf Digest))
          addressing leafHashing payloads := by
  induction payloads with
  | leaf payload => cases leafHashing <;> rfl
  | @internal leftSkeleton rightSkeleton left right leftIH rightIH =>
      simp only [binaryRoot, build, LeafData.get,
        AddressedMerkleTree.buildMerkleTreeAddressedM]
      rw [leftIH {
        leaf := fun index => addressing.leaf (.ofLeft index)
        node := fun index => addressing.node (.ofLeft index)
      }, rightIH {
        leaf := fun index => addressing.leaf (.ofRight index)
        node := fun index => addressing.node (.ofRight index)
      }]
      simp only [Function.comp_apply, monad_norm]
      rfl

/-- Translating binary queries preserves the entire effectful addressed construction, including
left-to-right query order and multiplicity, before projecting its public root. -/
theorem evaluateTree_binaryTree {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    evaluateTree
        (m := OracleComp (spec BinaryOperationKind Unit
          (BinaryAddress LeafAddress NodeAddress) EncodedLeaf Digest))
        (binaryTree addressing leafHashing payloads) =
      (fun tree => tree.getRootValue) <$>
        simulateQ binaryQueryImpl
          (build
            (m := OracleComp
              (MerkleTreeHashing.spec LeafAddress NodeAddress EncodedLeaf Digest))
            addressing leafHashing payloads) := by
  rw [binaryTree, evaluateTree_binaryTreeAt, binaryRoot_eq_build_root,
    simulateQ_map]

private theorem compose_binaryQueryImpl
    (answer : Query BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
      EncodedLeaf Digest → Digest) :
    (answer : QueryImpl
      (spec BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
        EncodedLeaf Digest) Id) ∘ₛ binaryQueryImpl =
      (fun query => (binaryAnswer answer query : Id Digest)) := by
  funext query
  cases query <;> simp [QueryImpl.compose, binaryQueryImpl, binaryAnswer, binaryQuery]

/-- The general hash-forest evaluator preserves the public root of every addressed binary Merkle
construction. -/
theorem evaluateTreeWithHash_binaryTree {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s)
    (answer : Query BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
      EncodedLeaf Digest → Digest) :
    evaluateTreeWithHash answer (binaryTree addressing leafHashing payloads) =
      (buildWithHash addressing leafHashing payloads (binaryAnswer answer)).getRootValue := by
  let answerImpl : QueryImpl
      (spec BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
        EncodedLeaf Digest) Id := answer
  have h := congrArg (simulateQ answerImpl)
    (evaluateTree_binaryTree addressing leafHashing payloads)
  rw [simulateQ_evaluateTree, simulateQ_map,
    ← QueryImpl.simulateQ_compose, compose_binaryQueryImpl,
    MerkleTreeHashing.simulateQ_build] at h
  exact h

/-- A singleton forest exposes exactly the existing binary root and no synthetic cap parent. -/
theorem evaluateForestWithHash_binaryForest {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s)
    (answer : Query BinaryOperationKind Unit (BinaryAddress LeafAddress NodeAddress)
      EncodedLeaf Digest → Digest) :
    (evaluateForestWithHash answer (binaryForest addressing leafHashing payloads)).toList =
      [(buildWithHash addressing leafHashing payloads (binaryAnswer answer)).getRootValue] := by
  change [evaluateTreeWithHash answer (binaryTree addressing leafHashing payloads)] = [_]
  rw [evaluateTreeWithHash_binaryTree]

end MerkleHashForest
