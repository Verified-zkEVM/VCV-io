/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic

/-!
# Merkle leaf encoding and hashing

This module separates application payloads, their committed encodings, and Merkle digests.  A
single tagged oracle domain distinguishes leaf hashes from internal-node hashes, while explicit
address maps connect the tree's intrinsic positions to the concrete address types used by a hash
instantiation.

The `LeafHashing.prehashed` specialization retains the raw-digest behavior of
`InductiveMerkleTree`: leaves are already Merkle labels and issue no leaf query.
`LeafHashing.providedDigest` also permits a caller-owned payload-to-digest map, whose collisions
must be accounted for separately.  The `LeafHashing.hash` case first applies an explicit payload
encoding and then issues a leaf-domain query.  All cases reuse
`AddressedMerkleTree` for tree construction and root reconstruction, so this layer adds no second
Merkle-tree recursion.
-/

@[expose] public section

namespace MerkleTreeHashing

open BinaryTree InductiveMerkleTree OracleComp OracleSpec

universe u v w x y

/-- The disjoint hash domains used by a binary Merkle tree.

Leaf queries commit to an encoded payload at a leaf address.  Node queries commit to an ordered
pair of child digests at an internal-node address. -/
inductive HashQuery (LeafAddress : Type u) (NodeAddress : Type v)
    (EncodedLeaf : Type w) (Digest : Type x) where
  | leaf (address : LeafAddress) (input : EncodedLeaf)
  | node (address : NodeAddress) (left right : Digest)
deriving DecidableEq

/-- The homogeneous oracle specification for tagged Merkle hash queries. -/
@[reducible]
def spec (LeafAddress : Type u) (NodeAddress : Type v)
    (EncodedLeaf : Type w) (Digest : Type x) :
    OracleSpec (HashQuery LeafAddress NodeAddress EncodedLeaf Digest) :=
  HashQuery LeafAddress NodeAddress EncodedLeaf Digest →ₒ Digest

/-- How application payloads become the digest labels stored at Merkle leaves.

`providedDigest` performs no query: the caller supplies and owns the payload-to-digest map and its
collision behavior.  `hash` exposes the payload encoding and hashes the resulting value in the
tagged leaf domain. -/
inductive LeafHashing (Payload : Type u) (EncodedLeaf : Type v) (Digest : Type w) where
  | providedDigest (digest : Payload → Digest)
  | hash (encode : Payload → EncodedLeaf)

namespace LeafHashing

/-- Raw-digest leaves: the payload already is the Merkle leaf label, so no leaf query is issued. -/
def prehashed {EncodedLeaf : Type v} {Digest : Type w} :
    LeafHashing Digest EncodedLeaf Digest :=
  .providedDigest id

end LeafHashing

/-- Concrete address keys for every leaf and internal node of a fixed tree skeleton. -/
structure Addressing (s : Skeleton) (LeafAddress : Type u) (NodeAddress : Type v) where
  /-- Concrete address used to hash each leaf. -/
  leaf : SkeletonLeafIndex s → LeafAddress
  /-- Concrete address used to hash each internal node. -/
  node : SkeletonInternalIndex s → NodeAddress

variable {LeafAddress : Type u} {NodeAddress : Type v}
  {Payload : Type w} {EncodedLeaf : Type x} {Digest : Type y}

/-- Interpret one leaf payload under a deterministic hash-query implementation. -/
def leafDigestWith (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest) (address : LeafAddress)
    (payload : Payload) : Digest :=
  match leafHashing with
  | .providedDigest digest => digest payload
  | .hash encode => answer (.leaf address (encode payload))

/-- Interpret one internal-node hash under a deterministic hash-query implementation. -/
def nodeDigestWith (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (address : NodeAddress) (left right : Digest) : Digest :=
  answer (.node address left right)

/-- Produce a leaf digest, issuing a query exactly in the encoded-and-hashed case. -/
def leafDigest {m : Type y → Type*} [Monad m]
    [HasQuery (spec LeafAddress NodeAddress EncodedLeaf Digest) m]
    (leafHashing : LeafHashing Payload EncodedLeaf Digest) (address : LeafAddress)
    (payload : Payload) : m Digest :=
  match leafHashing with
  | .providedDigest digest => pure (digest payload)
  | .hash encode => HasQuery.query
      (spec := spec LeafAddress NodeAddress EncodedLeaf Digest)
      (HashQuery.leaf address (encode payload))

/-- Hash an ordered pair of child digests in the internal-node domain. -/
def nodeDigest {m : Type y → Type*} [Monad m]
    [HasQuery (spec LeafAddress NodeAddress EncodedLeaf Digest) m]
    (address : NodeAddress) (left right : Digest) : m Digest :=
  HasQuery.query (spec := spec LeafAddress NodeAddress EncodedLeaf Digest)
    (HashQuery.node address left right)

/-- Build a Merkle cache from payloads using explicit leaf hashing and address maps. -/
def build {m : Type y → Type*} [Monad m]
    [HasQuery (spec LeafAddress NodeAddress EncodedLeaf Digest) m]
    {s : Skeleton} (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) : m (FullData Digest s) :=
  AddressedMerkleTree.buildMerkleTreeAddressedM
    (fun i => leafDigest (LeafAddress := LeafAddress) (NodeAddress := NodeAddress)
      leafHashing (addressing.leaf i) (payloads.get i))
    (fun i left right => nodeDigest (LeafAddress := LeafAddress)
      (EncodedLeaf := EncodedLeaf) (addressing.node i) left right)

/-- Recompute a putative root from a payload and authentication path. -/
def getPutativeRoot {m : Type y → Type*} [Monad m]
    [HasQuery (spec LeafAddress NodeAddress EncodedLeaf Digest) m]
    {s : Skeleton} (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (idx : SkeletonLeafIndex s) (payload : Payload)
    (proof : List.Vector Digest idx.depth) : m Digest := do
  let leaf ← leafDigest (LeafAddress := LeafAddress) (NodeAddress := NodeAddress)
    leafHashing (addressing.leaf idx) payload
  AddressedMerkleTree.getPutativeRootAddressedM
    (fun i left right => nodeDigest (LeafAddress := LeafAddress)
      (EncodedLeaf := EncodedLeaf) (addressing.node i) left right) idx leaf proof

/-- Verify a payload opening while preserving the leaf and node oracle-query trace.

The result type is `Bool`, so this operational wrapper is stated for ordinary `Type`-valued
digests.  The underlying builder, root reconstruction, and deterministic verifier remain fully
universe-polymorphic. -/
def verify {LeafAddress : Type u} {NodeAddress : Type v} {Payload : Type w}
    {EncodedLeaf : Type x} {Digest : Type} [DecidableEq Digest]
    {m : Type → Type*} [Monad m]
    [HasQuery (spec LeafAddress NodeAddress EncodedLeaf Digest) m]
    {s : Skeleton} (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (idx : SkeletonLeafIndex s) (payload : Payload) (root : Digest)
    (proof : List.Vector Digest idx.depth) : m Bool := do
  return (← getPutativeRoot addressing leafHashing idx payload proof) == root

/-- Deterministic interpretation of `build`. -/
def buildWithHash {s : Skeleton} (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) :
    FullData Digest s :=
  AddressedMerkleTree.buildMerkleTreeAddressedWithHash
    (LeafData.ofFun s fun i =>
      leafDigestWith answer leafHashing (addressing.leaf i) (payloads.get i))
    (fun i left right => nodeDigestWith answer (addressing.node i) left right)

/-- Deterministic interpretation of `getPutativeRoot`. -/
def getPutativeRootWithHash {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (idx : SkeletonLeafIndex s) (payload : Payload)
    (proof : List.Vector Digest idx.depth)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) : Digest :=
  AddressedMerkleTree.getPutativeRootAddressedWithHash
    (fun i left right => nodeDigestWith answer (addressing.node i) left right) idx
    (leafDigestWith answer leafHashing (addressing.leaf idx) payload) proof

/-- Verify a payload opening under a deterministic hash-query implementation. -/
def verifyWithHash [DecidableEq Digest] {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (idx : SkeletonLeafIndex s) (payload : Payload) (root : Digest)
    (proof : List.Vector Digest idx.depth)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) : Bool :=
  getPutativeRootWithHash addressing leafHashing idx payload proof answer == root

@[simp]
theorem simulateQ_leafDigest
    (answer : QueryImpl (spec LeafAddress NodeAddress EncodedLeaf Digest) Id)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest) (address : LeafAddress)
    (payload : Payload) :
    simulateQ answer
      (leafDigest (m := OracleComp (spec LeafAddress NodeAddress EncodedLeaf Digest))
        (LeafAddress := LeafAddress) (NodeAddress := NodeAddress)
        leafHashing address payload) =
      leafDigestWith answer leafHashing address payload := by
  cases leafHashing with
  | providedDigest => rfl
  | hash => simp [leafDigest, leafDigestWith]

@[simp]
theorem simulateQ_nodeDigest
    (answer : QueryImpl (spec LeafAddress NodeAddress EncodedLeaf Digest) Id)
    (address : NodeAddress) (left right : Digest) :
    simulateQ answer
      (nodeDigest (m := OracleComp (spec LeafAddress NodeAddress EncodedLeaf Digest))
        (LeafAddress := LeafAddress) (EncodedLeaf := EncodedLeaf)
        address left right) =
      nodeDigestWith answer address left right := by
  simp [nodeDigest, nodeDigestWith]

@[simp]
theorem simulateQ_build {s : Skeleton}
    (answer : QueryImpl (spec LeafAddress NodeAddress EncodedLeaf Digest) Id)
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) :
    simulateQ answer
      (build (m := OracleComp (spec LeafAddress NodeAddress EncodedLeaf Digest))
        addressing leafHashing payloads) =
      buildWithHash addressing leafHashing payloads answer := by
  simp [build, buildWithHash]
  rfl

@[simp]
theorem simulateQ_getPutativeRoot {s : Skeleton}
    (answer : QueryImpl (spec LeafAddress NodeAddress EncodedLeaf Digest) Id)
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (idx : SkeletonLeafIndex s) (payload : Payload)
    (proof : List.Vector Digest idx.depth) :
    simulateQ answer
      (getPutativeRoot (m := OracleComp (spec LeafAddress NodeAddress EncodedLeaf Digest))
        addressing leafHashing idx payload proof) =
      getPutativeRootWithHash addressing leafHashing idx payload proof answer := by
  simp [getPutativeRoot, getPutativeRootWithHash]
  rfl

@[simp]
theorem simulateQ_verify {LeafAddress : Type u} {NodeAddress : Type v}
    {Payload : Type w} {EncodedLeaf : Type x} {Digest : Type} [DecidableEq Digest]
    {s : Skeleton}
    (answer : QueryImpl (spec LeafAddress NodeAddress EncodedLeaf Digest) Id)
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (idx : SkeletonLeafIndex s) (payload : Payload) (root : Digest)
    (proof : List.Vector Digest idx.depth) :
    simulateQ answer
      (verify (m := OracleComp (spec LeafAddress NodeAddress EncodedLeaf Digest))
        addressing leafHashing idx payload root proof) =
      verifyWithHash addressing leafHashing idx payload root proof answer := by
  unfold verify verifyWithHash
  rw [simulateQ_bind, simulateQ_getPutativeRoot]
  rfl

/-- Honest openings recompute the root of a deterministically interpreted tree. -/
theorem functional_completeness {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) (idx : SkeletonLeafIndex s)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) :
    getPutativeRootWithHash addressing leafHashing idx (payloads.get idx)
        (generateProof (buildWithHash addressing leafHashing payloads answer) idx) answer =
      (buildWithHash addressing leafHashing payloads answer).getRootValue := by
  simpa only [getPutativeRootWithHash, buildWithHash, LeafData.get_ofFun] using
    AddressedMerkleTree.addressed_functional_completeness idx
      (LeafData.ofFun s fun i =>
        leafDigestWith answer leafHashing (addressing.leaf i) (payloads.get i))
      (fun i left right => nodeDigestWith answer (addressing.node i) left right)

/-- The deterministic verifier accepts every honestly generated opening. -/
@[simp]
theorem verifyWithHash_completeness [DecidableEq Digest] {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) (idx : SkeletonLeafIndex s)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) :
    verifyWithHash addressing leafHashing idx (payloads.get idx)
      (buildWithHash addressing leafHashing payloads answer).getRootValue
      (generateProof (buildWithHash addressing leafHashing payloads answer) idx) answer = true := by
  simp [verifyWithHash, functional_completeness]

/-- The monadic verifier accepts an honest opening under every deterministic oracle handler. -/
@[simp]
theorem simulateQ_verify_completeness {LeafAddress : Type u} {NodeAddress : Type v}
    {Payload : Type w} {EncodedLeaf : Type x} {Digest : Type} [DecidableEq Digest]
    {s : Skeleton} (addressing : Addressing s LeafAddress NodeAddress)
    (leafHashing : LeafHashing Payload EncodedLeaf Digest)
    (payloads : LeafData Payload s) (idx : SkeletonLeafIndex s)
    (answer : QueryImpl (spec LeafAddress NodeAddress EncodedLeaf Digest) Id) :
    simulateQ answer
      (verify (m := OracleComp (spec LeafAddress NodeAddress EncodedLeaf Digest))
        addressing leafHashing idx (payloads.get idx)
        (buildWithHash addressing leafHashing payloads answer).getRootValue
        (generateProof (buildWithHash addressing leafHashing payloads answer) idx)) = true := by
  simp

/-- Prehashed identity leaves recover the existing addressed raw-digest builder. -/
theorem buildWithHash_prehashed_id {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (leaves : LeafData Digest s)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) :
    buildWithHash addressing .prehashed leaves answer =
      AddressedMerkleTree.buildMerkleTreeAddressedWithHash leaves
        (fun i left right => answer (.node (addressing.node i) left right)) := by
  simp [buildWithHash, LeafHashing.prehashed, leafDigestWith, nodeDigestWith]

/-- Prehashed identity leaves recover the existing addressed raw-digest root reconstruction. -/
theorem getPutativeRootWithHash_prehashed_id {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (idx : SkeletonLeafIndex s) (leaf : Digest) (proof : List.Vector Digest idx.depth)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest) :
    getPutativeRootWithHash addressing .prehashed idx leaf proof answer =
      AddressedMerkleTree.getPutativeRootAddressedWithHash
        (fun i left right => answer (.node (addressing.node i) left right)) idx leaf proof := by
  rfl

end MerkleTreeHashing
