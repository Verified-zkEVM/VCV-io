/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Query
public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.OracleComp.OracleComp

/-!
# Address-key specialization of the generic Merkle transcript extractor

This module does not define a second extraction recurrence. It specializes
`MerkleTreeExtractor` to `NodeQuery Address Y`, retaining the caller's actual oracle address type
and an explicit map from typed skeleton positions to those keys. In particular, a caller may use
`Address := PkSeed × AdrsKey` for an SLH-DSA `Thash` oracle query; the public seed is then part of
query identity exactly as it is in `PublicHashQuery.thash`.

The pure recovery theorem is inherited from the shared generic owner. A probabilistic theorem over
a heterogeneous super-oracle still requires a proved projection of that oracle's transcript onto
this homogeneous node-query log; no direct identification of those log types is made here.
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree OracleSpec

universe u v

variable {Address : Type u} {Y : Type v}

/-- Homogeneous oracle interface for addressed binary-node hashing. -/
@[reducible] def nodeSpec (Address : Type u) (Y : Type v) :
    OracleSpec (NodeQuery Address Y) := fun _ => Y

namespace Extractor

variable [DecidableEq Address] [DecidableEq Y]

/-- Interpret a canonical addressed node query for the shared generic extractor. -/
def queryView : MerkleTreeExtractor.QueryView (NodeQuery Address Y) Address Y where
  address := NodeQuery.address
  input := NodeQuery.input

/-- Recover children at an actual oracle address and response. -/
def children (log : (nodeSpec Address Y).QueryLog) (address : Address) (root : Y) :
    Option (Y × Y) :=
  MerkleTreeExtractor.children queryView log address root

/-- Reconstruct a partial tree using the caller's typed-position-to-oracle-key map. -/
def tree (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address)
    (log : (nodeSpec Address Y).QueryLog) (root : Y) : FullData (Option Y) s :=
  MerkleTreeExtractor.tree queryView s addressKey log root

/-- The non-dummy labels reached by addressed extraction from `root`. -/
def targets (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address)
    (log : (nodeSpec Address Y).QueryLog) (root : Y) : List Y :=
  MerkleTreeExtractor.targets queryView s addressKey log root

/-- Addressed extraction exposes at most one target for each node of the skeleton. -/
theorem targets_length_le (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (nodeSpec Address Y).QueryLog) (root : Y) :
    (targets s addressKey log root).length ≤ 2 * s.leafCount - 1 :=
  MerkleTreeExtractor.targets_length_le queryView s addressKey log root

/-- Every addressed extractor target is the claimed root or one component of a complete logged
node query. -/
theorem mem_targets_root_or_log_input (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (nodeSpec Address Y).QueryLog) (root : Y) {target : Y}
    (htarget : target ∈ targets s addressKey log root) :
    target = root ∨
      ∃ entry ∈ log, target = entry.1.input.1 ∨ target = entry.1.input.2 := by
  simpa [queryView] using
    (MerkleTreeExtractor.mem_targets_root_or_log_input queryView s addressKey log root htarget)

/-- The leaf and authentication path exposed by an extracted partial tree. -/
abbrev ExtractedOpening (Y : Type v) {s : Skeleton} (idx : SkeletonLeafIndex s) :=
  MerkleTreeExtractor.ExtractedOpening Y idx

/-- Inspect one opening of an extracted partial tree. -/
abbrev opening {s : Skeleton} (tree : FullData (Option Y) s)
    (idx : SkeletonLeafIndex s) : ExtractedOpening Y idx :=
  MerkleTreeExtractor.opening tree idx

/-- Equal responses in the finite log imply equality of complete addressed queries. -/
abbrev ResponseInjectiveOn (log : (nodeSpec Address Y).QueryLog) : Prop :=
  MerkleTreeExtractor.ResponseInjectiveOn log

/-- The addressed log contains the query chain from `leaf` to `root`. -/
def ChainInLog {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address)
    (log : (nodeSpec Address Y).QueryLog) (leaf root : Y)
    (idx : SkeletonLeafIndex s) (proof : List.Vector Y idx.depth) : Prop :=
  MerkleTreeExtractor.ChainInLogAt queryView log leaf addressKey root idx proof

/-- **Deterministic addressed extraction.** A collision-free addressed log containing an opening's
complete query chain determines both the leaf and every authentication-path sibling recovered by
the shared extractor. -/
theorem opening_eq_of_chainInLog {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (nodeSpec Address Y).QueryLog) (hinj : ResponseInjectiveOn log)
    (root leaf : Y) (idx : SkeletonLeafIndex s) (proof : List.Vector Y idx.depth)
    (hchain : ChainInLog addressKey log leaf root idx proof) :
    (tree s addressKey log root).get idx.toNodeIndex = some leaf ∧
      (InductiveMerkleTree.generateProof (tree s addressKey log root) idx).toList =
        proof.toList.map some :=
  MerkleTreeExtractor.opening_eq_of_chainInLogAt queryView log hinj addressKey
    root leaf idx proof hchain

end Extractor

end AddressedMerkleTree
