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

@[expose] public section

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

end VCVioTest.MerkleTreeHashingCanary
