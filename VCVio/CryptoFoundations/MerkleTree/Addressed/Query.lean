/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Basic

/-!
# Addressed Merkle node queries

This module gives addressed Merkle hashing a canonical query identity. A query records an address
in the caller's actual oracle-key type and the ordered pair of child labels. The explicit
`addressKey : SkeletonInternalIndex s → Address` map connects typed Merkle positions to those
keys. It may be non-injective: if two positions encode to the same concrete key, the definitions
correctly treat them as the same oracle address rather than silently distinguishing them.

`openingQueries` enumerates the exact node-hash queries induced by a complete opening. These
definitions are shared by queried-domain uniqueness and addressed random-oracle extraction.
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree InductiveMerkleTree

universe u v

variable {Address : Type u} {Y : Type v}

/-- One addressed Merkle-node query: an actual oracle address and ordered child pair. -/
structure NodeQuery (Address : Type u) (Y : Type v) where
  /-- Address/key supplied to the underlying hash oracle. -/
  address : Address
  /-- Ordered left and right child labels. -/
  input : Y × Y
deriving DecidableEq

namespace NodeQuery

/-- Evaluate an addressed node query. -/
def eval (nodeHash : Address → Y → Y → Y) (query : NodeQuery Address Y) : Y :=
  nodeHash query.address query.input.1 query.input.2

end NodeQuery

/-- The addressed node-hash inputs induced by a complete opening, ordered from the root toward
the leaf. -/
def openingQueries : {s : Skeleton} →
    (addressKey : SkeletonInternalIndex s → Address) →
    (nodeHash : Address → Y → Y → Y) →
    (idx : SkeletonLeafIndex s) → Y → List.Vector Y idx.depth → List (NodeQuery Address Y)
  | _, _, _, .ofLeaf, _, _ => []
  | _, addressKey, nodeHash, .ofLeft idx, leaf, proof =>
      let child := getPutativeRootAddressedWithHash
        (fun a => nodeHash (addressKey (.ofLeft a))) idx leaf proof.tail
      ⟨addressKey .ofInternal, (child, proof.head)⟩ ::
        openingQueries (fun a => addressKey (.ofLeft a)) nodeHash idx leaf proof.tail
  | _, addressKey, nodeHash, .ofRight idx, leaf, proof =>
      let child := getPutativeRootAddressedWithHash
        (fun a => nodeHash (addressKey (.ofRight a))) idx leaf proof.tail
      ⟨addressKey .ofInternal, (proof.head, child)⟩ ::
        openingQueries (fun a => addressKey (.ofRight a)) nodeHash idx leaf proof.tail

/-- Every node query induced by an opening occurs in `log`. -/
def OpeningCovered {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (nodeHash : Address → Y → Y → Y)
    (log : List (NodeQuery Address Y)) (idx : SkeletonLeafIndex s)
    (leaf : Y) (proof : List.Vector Y idx.depth) : Prop :=
  ∀ query ∈ openingQueries addressKey nodeHash idx leaf proof, query ∈ log

end AddressedMerkleTree
