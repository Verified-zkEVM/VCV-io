/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractability
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Extractor

/-!
# Addressed Merkle tree extractability

This is the complete-query specialization of `MerkleTreeExtractability`: random-oracle query
identity is the pair of the concrete node address and the ordered children. The position map
`addressKey` need not be injective. Reusing an address with the same children is one repeated
query; reusing it with different children produces distinct complete queries.

The probability proof, stopping-time argument, extractor, and error numerator are inherited from
the generic owner. This file deliberately exposes no parallel proof kernel.

`Address` and `Y` are currently `Type` because `NodeQuery Address Y` is the homogeneous query type
passed to the Type-0 birthday-bound machinery. This is an inherited framework boundary, not a
mathematical restriction of addressed extraction.
-/

@[expose] public section

namespace AddressedMerkleTree.Extractability

open BinaryTree OracleComp OracleSpec

variable {Address Y : Type}

/-- Complete addressed-node queries as the query model used by the generic game. -/
def queryModel :
    MerkleTreeExtractability.NodeQueryModel (NodeQuery Address Y) Address Y where
  view := Extractor.queryView
  mkQuery address input := ⟨address, input⟩
  address_mkQuery := by intros; rfl
  input_mkQuery := by intros; rfl

/-- Addressed extractability syntax before choosing random-oracle semantics. -/
def inner [DecidableEq Address] [DecidableEq Y] {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : MerkleTreeExtractability.Adversary (NodeQuery Address Y) Y s) :=
  MerkleTreeExtractability.extractabilityInner queryModel addressKey 𝒜

/-- One shared lazy random function interprets commit, opening, and verification queries. -/
def game [DecidableEq Address] [DecidableEq Y] {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : MerkleTreeExtractability.Adversary (NodeQuery Address Y) Y s) :=
  MerkleTreeExtractability.extractabilityGame queryModel addressKey 𝒜

/-- Exact stopping-time ROM extractability bound for complete addressed queries. -/
theorem rom_bound [DecidableEq Address] [DecidableEq Y] [Fintype Y] [Inhabited Y]
    [IsUniformSpec (nodeSpec Address Y)] {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : MerkleTreeExtractability.Adversary (NodeQuery Address Y) Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[MerkleTreeExtractability.OpeningExtractionFailure |
      game addressKey 𝒜] ≤
      (MerkleTreeExtractability.extractabilityROMErrorNumerator s qb : ENNReal) *
        (Fintype.card Y : ENNReal)⁻¹ := by
  simpa [game] using
    MerkleTreeExtractability.extractability_rom_bound queryModel addressKey 𝒜 qb h

/-- Unconditional two-endpoint relaxation of `rom_bound`. -/
theorem rom_bound_coarse [DecidableEq Address] [DecidableEq Y] [Fintype Y] [Inhabited Y]
    [IsUniformSpec (nodeSpec Address Y)] {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : MerkleTreeExtractability.Adversary (NodeQuery Address Y) Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[MerkleTreeExtractability.OpeningExtractionFailure |
      game addressKey 𝒜] ≤
      ((max ((2 * s.leafCount - 1) * qb) (qb.choose 2) +
        (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card Y : ENNReal)⁻¹ := by
  simpa [game] using
    MerkleTreeExtractability.extractability_rom_bound_coarse queryModel addressKey 𝒜 qb h

/-- Birthday-dominant specialization once the total query budget is large enough. -/
theorem rom_bound_birthday_dominates
    [DecidableEq Address] [DecidableEq Y] [Fintype Y] [Inhabited Y]
    [IsUniformSpec (nodeSpec Address Y)] {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : MerkleTreeExtractability.Adversary (NodeQuery Address Y) Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hqb : 2 * (2 * s.leafCount - 1) + 1 ≤ qb) :
    Pr[MerkleTreeExtractability.OpeningExtractionFailure |
      game addressKey 𝒜] ≤
      ((qb.choose 2 + (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card Y : ENNReal)⁻¹ := by
  simpa [game] using
    MerkleTreeExtractability.extractability_rom_bound_birthday_dominates
      queryModel addressKey 𝒜 qb h hqb

/-- Textbook-shaped quadratic corollary under explicit dominance hypotheses. -/
theorem rom_bound_quadratic
    [DecidableEq Address] [DecidableEq Y] [Fintype Y] [Inhabited Y]
    [IsUniformSpec (nodeSpec Address Y)] {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : MerkleTreeExtractability.Adversary (NodeQuery Address Y) Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hdominance : 2 * (2 * s.leafCount - 1) + 1 ≤ qb)
    (hdepth : 2 * (2 * s.leafCount - 1) * s.depth ≤ qb) :
    Pr[MerkleTreeExtractability.OpeningExtractionFailure |
      game addressKey 𝒜] ≤
      (qb : ENNReal) ^ 2 / (2 * Fintype.card Y) := by
  simpa [game] using
    MerkleTreeExtractability.extractability_rom_bound_quadratic
      queryModel addressKey 𝒜 qb h hdominance hdepth

end AddressedMerkleTree.Extractability
