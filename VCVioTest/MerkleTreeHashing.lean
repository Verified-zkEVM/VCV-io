/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Hashing.Binding

/-!
# Canary tests for Merkle payload hashing

These examples pin the executable distinction between leaf and node hash domains, concrete leaf
addresses, ordered child digests, and the query-free prehashed-leaf specialization.
-/

public section

namespace VCVioTest.MerkleTreeHashingCanary

open BinaryTree MerkleTreeHashing

def twoLeaves : Skeleton := .internal .leaf .leaf

def addressing : Addressing twoLeaves Bool Unit where
  leaf
    | .ofLeft .ofLeaf => false
    | .ofRight .ofLeaf => true
  node
    | .ofInternal => ()

def payloads : LeafData Nat twoLeaves := .internal (.leaf 3) (.leaf 5)

/-- Branch-distinguishing leaf hashes and a noncommutative node hash. -/
def answer : HashQuery Bool Unit Nat Nat → Nat
  | .leaf false input => 100 + input
  | .leaf true input => 200 + input
  | .node () left right => 10 * left + right

abbrev TraceM := StateM (List (HashQuery Bool Unit Nat Nat))

instance : HasQuery (spec Bool Unit Nat Nat) TraceM where
  query query := fun trace => (answer query, trace ++ [query])

def hashedBuildRun := Id.run ((build (m := TraceM)
    (LeafAddress := Bool) (NodeAddress := Unit) (Payload := Nat)
    (EncodedLeaf := Nat) (Digest := Nat)
    addressing (.hash fun payload => payload + 1) payloads).run [])

def prehashedBuildRun := Id.run ((build (m := TraceM)
    (LeafAddress := Bool) (NodeAddress := Unit) (Payload := Nat)
    (EncodedLeaf := Nat) (Digest := Nat) addressing .prehashed payloads).run [])

def verifyRun := Id.run ((verify (m := TraceM)
    (LeafAddress := Bool) (NodeAddress := Unit) (Payload := Nat)
    (EncodedLeaf := Nat) (Digest := Nat) addressing
    (.hash fun payload => payload + 1) (.ofLeft .ofLeaf) 3 1246
      (List.Vector.cons 206 .nil)).run [])

/-- Encoded leaves use both the leaf-domain tag and the concrete leaf address. -/
example : (buildWithHash addressing (.hash fun payload => payload + 1) payloads answer).getRootValue
    = 1246 := by
  decide

/-- Root reconstruction hashes the encoded payload at the opened leaf before climbing the path. -/
example : getPutativeRootWithHash addressing (.hash fun payload => payload + 1)
    (.ofLeft .ofLeaf) 3 (List.Vector.cons 206 .nil) answer = 1246 := by
  decide

/-- The verifier accepts the same addressed, encoded opening. -/
example : verifyWithHash addressing (.hash fun payload => payload + 1)
    (.ofLeft .ofLeaf) 3 1246 (List.Vector.cons 206 .nil) answer = true := by
  decide

/-- A wrong root is rejected rather than accepted after the same reconstruction. -/
example : verifyWithHash addressing (.hash fun payload => payload + 1)
    (.ofLeft .ofLeaf) 3 1247 (List.Vector.cons 206 .nil) answer = false := by
  decide

/-- Prehashed leaves bypass the leaf domain and retain their supplied digest labels. -/
example : (buildWithHash addressing .prehashed payloads answer).getRootValue = 35 := by
  decide

/-- A two-leaf build queries the left leaf, the right leaf, then their ordered parent. -/
example : hashedBuildRun.2 =
    [HashQuery.leaf false 4, HashQuery.leaf true 6, HashQuery.node () 104 206] := by
  decide

/-- Raw digest leaves issue no leaf queries; only their ordered parent is hashed. -/
example : prehashedBuildRun.2 = [HashQuery.node () 3 5] := by
  decide

/-- The operational verifier preserves its leaf-then-parent query trace. -/
example : (verifyRun.1, verifyRun.2) =
    (true, [HashQuery.leaf false 4, HashQuery.node () 104 206]) := by
  decide

/-- Encoded leaves and digests may inhabit different universes. -/
example {LargeEncoding : Type 1} (encode : Nat → LargeEncoding)
    (largeAnswer : HashQuery Bool Unit LargeEncoding Nat → Nat) :
    FullData Nat twoLeaves :=
  buildWithHash addressing (.hash encode) payloads largeAnswer

/-- The provided-digest mode names its caller-owned transformation explicitly. -/
example : (buildWithHash addressing (.providedDigest fun payload => payload + 7)
    payloads answer).getRootValue = 112 := by
  decide

/-- Ordinary imports simplify honest verification through the general simulation and
completeness rules, without a separate overlapping simp rule. -/
example {s : Skeleton} (a : Addressing s Bool Unit) (p : LeafData Nat s)
    (i : SkeletonLeafIndex s) (impl : QueryImpl (spec Bool Unit Nat Nat) Id) :
    simulateQ impl
      (verify (m := OracleComp (spec Bool Unit Nat Nat)) a (.hash id) i (p.get i)
        (buildWithHash a (.hash id) p impl).getRootValue
        (InductiveMerkleTree.generateProof (buildWithHash a (.hash id) p impl) i)) = true := by
  simp only [simulateQ_verify, verifyWithHash_completeness]

/-! ## Internal-node addressing -/

private def threeLeaves : Skeleton := .internal (.internal .leaf .leaf) .leaf

private inductive DeepNodeAddress where
  | root
  | left
deriving DecidableEq

private def deepAddressing : Addressing threeLeaves (Fin 3) DeepNodeAddress where
  leaf
    | .ofLeft (.ofLeft .ofLeaf) => 0
    | .ofLeft (.ofRight .ofLeaf) => 1
    | .ofRight .ofLeaf => 2
  node
    | .ofInternal => .root
    | .ofLeft .ofInternal => .left

private def deepPayloads : LeafData Nat threeLeaves :=
  .internal (.internal (.leaf 1) (.leaf 2)) (.leaf 3)

private def deepAnswer : HashQuery (Fin 3) DeepNodeAddress Nat Nat → Nat
  | .leaf address input => 10 * address.val + input
  | .node .left left right => 100 + 10 * left + right
  | .node .root left right => 1000 + 10 * left + right

private abbrev DeepTraceM :=
  StateM (List (HashQuery (Fin 3) DeepNodeAddress Nat Nat))

private instance : HasQuery (spec (Fin 3) DeepNodeAddress Nat Nat) DeepTraceM where
  query query := fun trace => (deepAnswer query, trace ++ [query])

private def deepBuildRun := Id.run ((build (m := DeepTraceM)
    (LeafAddress := Fin 3) (NodeAddress := DeepNodeAddress) (Payload := Nat)
    (EncodedLeaf := Nat) (Digest := Nat) deepAddressing (.hash id) deepPayloads).run [])

/-- A depth-two build forwards distinct internal addresses and retains postorder query order. -/
example : (deepBuildRun.1.getRootValue, deepBuildRun.2) =
    (2243,
      [HashQuery.leaf 0 1, HashQuery.leaf 1 2, HashQuery.node .left 1 12,
       HashQuery.leaf 2 3, HashQuery.node .root 122 23]) := by
  decide

/-! ## Degenerate collision boundaries -/

private def leafCollisionAnswer : HashQuery Bool Unit Nat Nat → Nat
  | .leaf _ _ => 7
  | .node _ left right => 10 * left + right

private def nodeCollisionAnswer : HashQuery Bool Unit Nat Nat → Nat
  | .leaf _ input => input
  | .node _ _ _ => 0

/-- A constant encoding is reported at the caller-owned encoding boundary. -/
example : EncodingCollision (fun _ : Bool => 0) false true := by
  unfold EncodingCollision
  decide

/-- A constant caller-provided digest is reported at the digest-map boundary. -/
example : DigestMapCollision (fun _ : Bool => 7) false true := by
  unfold DigestMapCollision
  decide

/-- Distinct encoded leaves can collide within one concrete leaf domain. -/
example : LeafHashCollision leafCollisionAnswer false 1 2 := by
  unfold LeafHashCollision
  decide

/-- Distinct ordered pairs can collide within one concrete internal-node domain. -/
example : NodeHashCollision addressing nodeCollisionAnswer
    ((.ofInternal, 1, 9, 2, 8) :
      SkeletonInternalIndex twoLeaves × Nat × Nat × Nat × Nat) := by
  unfold NodeHashCollision
  decide

/-- The public binding theorem reaches the node-collision branch in a concrete model where
encoding is injective and leaf hashing is collision-free on the two openings. -/
example : ∃ witness, NodeHashCollision addressing nodeCollisionAnswer witness := by
  obtain leafCollision | nodeCollision :=
    hashed_binding_of_injective addressing id Function.injective_id nodeCollisionAnswer
      (.ofLeft .ofLeaf) (List.Vector.cons 9 .nil) (List.Vector.cons 8 .nil)
      1 2 (by decide) (by decide)
  · simp [LeafHashCollision, nodeCollisionAnswer] at leafCollision
  · exact nodeCollision

end VCVioTest.MerkleTreeHashingCanary
