/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import HashSig.SLHDSA.Oracle
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Extractor

/-!
# SLH-DSA public-hash log projection for Merkle extraction

The SLH-DSA public-hash oracle is heterogeneous: `thash` returns a node, while `hmsg` returns a
message digest. The generic Merkle extractor consumes a homogeneous binary-node log. This module
defines the explicit, lossless-on-binary-`thash` projection between them. It prevents a proof from
silently identifying the full `publicHashSpec` transcript with the node-hash subtranscript.

The Merkle query address is `(PK.seed, encodedADRS)`, exactly the non-message portion of a
`PublicHashQuery.thash`; the ordered children remain in `NodeQuery.input`. Unary `F`, other-arity
`T_ℓ`, and `H_msg` entries are excluded by construction.

That exclusion is only a typed view for deterministic extraction. Any later probability bound
must charge the adversary's **full heterogeneous `publicHashSpec` query log**, not merely
`merkleNodeLog`: responses to unary or other-arity `thash` queries live in the same `Y` space and
can still collide with, or hit, node values used by the extractor.
-/

@[expose] public section

namespace SLHDSA.PublicHash

open AddressedMerkleTree OracleSpec

variable {p : Params} (core : CorePrimitives p)

/-- Actual oracle address used by binary SLH-DSA node hashing. -/
abbrev NodeAddress := core.PkSeed × core.AdrsKey

/-- Homogeneous binary-node query extracted from `PublicHashQuery.thash`. -/
abbrev MerkleNodeQuery := NodeQuery (NodeAddress core) core.Y

/-- Embed a homogeneous Merkle node query into the exact SLH-DSA public-hash query domain. -/
def ofMerkleNodeQuery (query : MerkleNodeQuery core) :
    PublicHashQuery core.PkSeed core.AdrsKey core.Y :=
  .thash query.address.1 query.address.2 [query.input.1, query.input.2]

/-- Project one heterogeneous public-hash log entry when it is exactly a binary `thash` query. -/
def merkleNodeEntry? :
    (query : (publicHashSpec core).Domain) →
      (publicHashSpec core).Range query →
      Option ((_query : MerkleNodeQuery core) × core.Y)
  | .thash pkSeed adrsKey [left, right], response =>
      some ⟨⟨(pkSeed, adrsKey), (left, right)⟩, response⟩
  | .thash _ _ _, _ => none
  | .hmsg _ _ _ _, _ => none

/-- Retain exactly the binary `thash` entries from a heterogeneous public-hash transcript. -/
def merkleNodeLog (log : (publicHashSpec core).QueryLog) :
    (AddressedMerkleTree.nodeSpec (NodeAddress core) core.Y).QueryLog :=
  log.filterMap fun entry => merkleNodeEntry? core entry.1 entry.2

/-- Embedding a Merkle-node query and then projecting it recovers the exact query and response. -/
@[simp]
theorem merkleNodeEntry?_ofMerkleNodeQuery (query : MerkleNodeQuery core)
    (response : core.Y) :
    merkleNodeEntry? core (ofMerkleNodeQuery core query) response = some ⟨query, response⟩ := by
  cases query
  rfl

/-- Exact image characterization of membership in the projected binary-node log. -/
theorem mem_merkleNodeLog_iff (log : (publicHashSpec core).QueryLog)
    (entry : (_query : MerkleNodeQuery core) × core.Y) :
    entry ∈ merkleNodeLog core log ↔
      ∃ publicEntry ∈ log,
        merkleNodeEntry? core publicEntry.1 publicEntry.2 = some entry := by
  exact List.mem_filterMap

/-- Every logged binary `thash` entry appears unchanged in the projected Merkle-node log. -/
theorem mem_merkleNodeLog_of_mem_thash
    (log : (publicHashSpec core).QueryLog)
    (pkSeed : core.PkSeed) (adrsKey : core.AdrsKey) (left right response : core.Y)
    (hmem : (⟨.thash pkSeed adrsKey [left, right], response⟩ :
      (_query : PublicHashQuery core.PkSeed core.AdrsKey core.Y) ×
        (publicHashSpec core).Range _query) ∈ log) :
    (⟨⟨(pkSeed, adrsKey), (left, right)⟩, response⟩ :
      (_query : MerkleNodeQuery core) × core.Y) ∈
        merkleNodeLog core log := by
  apply List.mem_filterMap.mpr
  exact ⟨⟨.thash pkSeed adrsKey [left, right], response⟩, hmem, rfl⟩

end SLHDSA.PublicHash
