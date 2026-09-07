/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module

public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.FipsParams
public import HashSig.SLHDSA.ForsConformance

/-!
# Checked concrete boundary for FORS addresses

Every typed FORS coordinate from every FIPS 205 parameter set fits the four-byte address words.
Consequently the checked SHA2 adapter accepts secret, leaf/internal-node, and root-compression
addresses, while SHAKE's full address serialization round-trips them exactly.  The digest-derived
base-address theorem connects these component facts directly to `DigestParts.forsAdrs`.
-/

@[expose] public section

namespace SLHDSA.Concrete

open ForsConformance

/-- Every approved fixed-width FORS digest contains all `k*a` normative index bits. -/
theorem fips_forsDigest_capacity (set : FipsParameterSet) :
    set.params.k * set.params.a ≤ 8 * set.params.digestBytes := by
  cases set <;> decide

/-- The authoritative `DigestParts.md` extent satisfies Algorithm 4's normative width
precondition, so the typed FORS decoder's MSB-first arithmetic characterization
(`decodeIndices_get_bigEndian`) applies to every approved digest. -/
theorem fips_decodeDigestParts_capacity (set : FipsParameterSet)
    (parts : DigestParts set.params) :
    set.params.k * set.params.a ≤ 8 * parts.md.toList.length := by
  simpa using fips_forsDigest_capacity set

/-- The largest approved FORS global coordinate remains inside one four-byte address word. -/
theorem fips_forsCoordinate_bound (set : FipsParameterSet) :
    set.params.k * set.params.t ≤ 256 ^ 4 := by
  cases set <;> decide

/-- Every global FORS coordinate in an approved parameter set fits one four-byte address word. -/
theorem fips_forsGlobalIndex_fits (set : FipsParameterSet)
    (idx : Fin (set.params.k * set.params.t)) : Adrs.Fits 4 idx.val = true := by
  simpa [Adrs.Fits] using lt_of_lt_of_le idx.isLt (fips_forsCoordinate_bound set)

/-- The largest approved FORS height remains inside one four-byte address word. -/
theorem fips_forsHeight_bound (set : FipsParameterSet) :
    set.params.a + 1 ≤ 256 ^ 4 := by
  cases set <;> decide

/-- Every FORS height in an approved parameter set fits one four-byte address word. -/
theorem fips_forsHeight_fits (set : FipsParameterSet)
    (height : Fin (set.params.a + 1)) : Adrs.Fits 4 height.val = true := by
  simpa [Adrs.Fits] using lt_of_lt_of_le height.isLt (fips_forsHeight_bound set)

/-- Every approved digest-derived tree coordinate fits SHA2's eight-byte compressed field. -/
theorem fips_digestTree_fits (set : FipsParameterSet)
    (parts : DigestParts set.params) : Adrs.Fits 8 parts.idxTree.val = true := by
  have hbound : 2 ^ (set.params.h - set.params.hp) ≤ 256 ^ 8 := by
    cases set <;> decide
  simpa [Adrs.Fits] using lt_of_lt_of_le parts.idxTree.isLt hbound

/-- Every approved digest-derived key-pair coordinate fits its four-byte address word. -/
theorem fips_digestLeaf_fits (set : FipsParameterSet)
    (parts : DigestParts set.params) : Adrs.Fits 4 parts.idxLeaf.val = true := by
  have hbound : 2 ^ set.params.hp ≤ 256 ^ 4 := by
    cases set <;> decide
  simpa [Adrs.Fits] using lt_of_lt_of_le parts.idxLeaf.isLt hbound

/-- The digest-derived FIPS Algorithm 19 base address is canonical for every approved set. -/
theorem fips_digestForsAdrs_isCanonical (set : FipsParameterSet)
    (parts : DigestParts set.params) : parts.forsAdrs.isCanonical = true := by
  have htree8 := fips_digestTree_fits set parts
  have htree12 : Adrs.Fits 12 parts.idxTree.val = true := by
    have hbound : 256 ^ 8 ≤ 256 ^ 12 := by norm_num
    have hlt : parts.idxTree.val < 256 ^ 8 := by simpa [Adrs.Fits] using htree8
    simpa [Adrs.Fits] using lt_of_lt_of_le hlt hbound
  have hleaf := fips_digestLeaf_fits set parts
  rw [Adrs.isCanonical]
  simp only [DigestParts.forsAdrs, Adrs.setTreeAddress, Adrs.setTypeAndClear,
    Adrs.setKeyPairAddress]
  rw [htree12, hleaf]
  norm_num [Adrs.zero, Adrs.Fits, AddrType.toCode, AddrType.ofCode]

/-- The checked SHA2 boundary accepts every approved digest-derived FORS base address. -/
theorem sha2_digestForsAdrs_isOk (set : FipsParameterSet)
    (parts : DigestParts set.params) :
    (Sha2Address.ofAdrs parts.forsAdrs).isOk = true := by
  have hcanonical := fips_digestForsAdrs_isCanonical set parts
  have hlayer : Adrs.Fits 1 parts.forsAdrs.layer = true := by
    simp [Adrs.Fits]
  have htree : Adrs.Fits 8 parts.forsAdrs.tree = true := by
    simpa using fips_digestTree_fits set parts
  rw [Sha2Address.ofAdrs, dif_pos hcanonical, dif_pos hlayer, dif_pos htree]
  rfl

/-- The checked SHA2 boundary accepts every approved FORS secret-derivation address. -/
theorem sha2_forsSkAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (idx : Fin (set.params.k * set.params.t)) :
    (Sha2Address.ofAdrs (forsSkAdrs base.value idx.val)).isOk = true := by
  have hcanonical := forsSkAdrs_isCanonical base.value idx.val base.canonical
    (fips_forsGlobalIndex_fits set idx)
  have hlayer : Adrs.Fits 1 (forsSkAdrs base.value idx.val).layer = true := by
    simpa using base.layerFits
  have htree : Adrs.Fits 8 (forsSkAdrs base.value idx.val).tree = true := by
    simpa using base.treeFits
  rw [Sha2Address.ofAdrs, dif_pos hcanonical, dif_pos hlayer, dif_pos htree]
  rfl

/-- The checked SHA2 boundary accepts every approved typed FORS node address. -/
theorem sha2_forsNodeAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (pos : ForsConformance.NodePosition set.params) :
    (Sha2Address.ofAdrs
      (forsNodeAdrs base.value pos.height.val pos.globalIndex.val)).isOk = true := by
  have hcanonical := forsNodeAdrs_isCanonical base.value pos.height.val pos.globalIndex.val
    base.canonical (fips_forsHeight_fits set pos.height)
      (fips_forsGlobalIndex_fits set pos.globalIndex)
  have hlayer :
      Adrs.Fits 1 (forsNodeAdrs base.value pos.height.val pos.globalIndex.val).layer = true := by
    simpa using base.layerFits
  have htree :
      Adrs.Fits 8 (forsNodeAdrs base.value pos.height.val pos.globalIndex.val).tree = true := by
    simpa using base.treeFits
  rw [Sha2Address.ofAdrs, dif_pos hcanonical, dif_pos hlayer, dif_pos htree]
  rfl

/-- The checked SHA2 boundary accepts FORS root compression from any checked base address. -/
theorem sha2_forsPkAdrs_isOk (base : Sha2Address) :
    (Sha2Address.ofAdrs (forsPkAdrs base.value)).isOk = true := by
  have hcanonical := forsPkAdrs_isCanonical base.value base.canonical
  have hlayer : Adrs.Fits 1 (forsPkAdrs base.value).layer = true := by
    simpa using base.layerFits
  have htree : Adrs.Fits 8 (forsPkAdrs base.value).tree = true := by
    simpa using base.treeFits
  rw [Sha2Address.ofAdrs, dif_pos hcanonical, dif_pos hlayer, dif_pos htree]
  rfl

/-- SHAKE's full address serialization is exact for every approved typed FORS secret address. -/
theorem shake_forsSkAdrs_roundtrip (set : FipsParameterSet) (base : Adrs)
    (hbase : base.isCanonical = true) (idx : Fin (set.params.k * set.params.t)) :
    Adrs.fromVector (forsSkAdrs base idx.val).toVector = forsSkAdrs base idx.val :=
  forsSkAdrs_fromVector_toVector base idx.val hbase (fips_forsGlobalIndex_fits set idx)

/-- SHAKE's full address serialization is exact for every approved typed FORS node address. -/
theorem shake_forsNodeAdrs_roundtrip (set : FipsParameterSet) (base : Adrs)
    (hbase : base.isCanonical = true) (pos : ForsConformance.NodePosition set.params) :
    Adrs.fromVector (forsNodeAdrs base pos.height.val pos.globalIndex.val).toVector =
      forsNodeAdrs base pos.height.val pos.globalIndex.val :=
  forsNodeAdrs_fromVector_toVector base pos.height.val pos.globalIndex.val hbase
    (fips_forsHeight_fits set pos.height) (fips_forsGlobalIndex_fits set pos.globalIndex)

/-- SHAKE's full address serialization is exact for FORS root compression. -/
theorem shake_forsPkAdrs_roundtrip (base : Adrs) (hbase : base.isCanonical = true) :
    Adrs.fromVector (forsPkAdrs base).toVector = forsPkAdrs base :=
  forsPkAdrs_fromVector_toVector base hbase

end SLHDSA.Concrete
