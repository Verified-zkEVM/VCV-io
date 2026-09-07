/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Bolton Bailey
-/

module
public import HashSig.SLHDSA.Concrete.Wots
public import HashSig.SLHDSA.FipsParams
public import HashSig.SLHDSA.XmssConformance

/-!
# Checked concrete boundary for XMSS addresses

Reachable WOTS-leaf and XMSS-node addresses from every FIPS 205 parameter set remain inside the
checked SHA2 address domain.  The proof uses the approved height bound locally rather than adding a
SHA2-specific condition to `Params.Valid`.  SHAKE's full 32-byte address key is covered by exact
serialization round trips.
-/

@[expose] public section

namespace SLHDSA.Concrete

open XmssConformance

/-- Every approved XMSS subtree has height at most nine. -/
theorem fips_hp_le_nine (set : FipsParameterSet) : set.params.hp ≤ 9 := by
  cases set <;> decide

/-- Every approved XMSS leaf index fits a four-byte ADRS word. -/
theorem fips_leafIndex_fits (set : FipsParameterSet)
    (idx : LeafIndex set.params) : Adrs.Fits 4 idx.val = true := by
  have hpow : 2 ^ set.params.hp ≤ 2 ^ 9 :=
    Nat.pow_le_pow_right (by omega : 0 < 2) (fips_hp_le_nine set)
  have hi : idx.val < 256 ^ 4 := by
    exact lt_of_lt_of_le idx.isLt (le_trans hpow (by norm_num))
  simpa [Adrs.Fits] using hi

/-- Every component of an approved typed node position fits its four-byte ADRS word. -/
theorem fips_nodePosition_fits (set : FipsParameterSet)
    (pos : NodePosition set.params) :
    Adrs.Fits 4 pos.level = true ∧ Adrs.Fits 4 pos.index.val = true := by
  have hz9 : pos.level ≤ 9 := le_trans pos.level_le (fips_hp_le_nine set)
  have hz : pos.level < 256 ^ 4 := by norm_num; omega
  have hindex : pos.index.val < 2 ^ set.params.hp := pos.index_lt_leafCount
  have hpow : 2 ^ set.params.hp ≤ 2 ^ 9 :=
    Nat.pow_le_pow_right (by omega : 0 < 2) (fips_hp_le_nine set)
  have ht : pos.index.val < 256 ^ 4 := by
    exact lt_of_lt_of_le hindex (le_trans hpow (by norm_num))
  simpa [Adrs.Fits] using And.intro hz ht

/-- Proof-carrying checked SHA2 address for an approved XMSS leaf's WOTS tree. -/
def sha2WotsLeafAddress (set : FipsParameterSet) (base : Sha2Address)
    (idx : LeafIndex set.params) : Sha2Address where
  value := wotsLeafAdrs base.value idx.val
  canonical := wotsLeafAdrs_isCanonical base.value idx.val base.canonical
    (fips_leafIndex_fits set idx)
  layerFits := by simpa using base.layerFits
  treeFits := by simpa using base.treeFits

/-- The checked SHA2 boundary accepts every approved XMSS leaf address. -/
theorem sha2_wotsLeafAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (idx : LeafIndex set.params) :
    (Sha2Address.ofAdrs (wotsLeafAdrs base.value idx.val)).isOk = true := by
  have hcanonical := wotsLeafAdrs_isCanonical base.value idx.val base.canonical
    (fips_leafIndex_fits set idx)
  rw [Sha2Address.ofAdrs, dif_pos hcanonical]
  rw [dif_pos (by simpa using base.layerFits)]
  rw [dif_pos (by simpa using base.treeFits)]
  rfl

/-- The checked SHA2 boundary accepts every approved typed XMSS node address. -/
theorem sha2_xmssNodeAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (pos : NodePosition set.params) :
    (Sha2Address.ofAdrs (xmssNodeAdrs base.value pos.level pos.index.val)).isOk = true := by
  rcases fips_nodePosition_fits set pos with ⟨hz, ht⟩
  have hcanonical :=
    xmssNodeAdrs_isCanonical base.value pos.level pos.index.val base.canonical hz ht
  have hlayer :
      Adrs.Fits 1 (xmssNodeAdrs base.value pos.level pos.index.val).layer = true := by
    simpa using base.layerFits
  have htree :
      Adrs.Fits 8 (xmssNodeAdrs base.value pos.level pos.index.val).tree = true := by
    simpa using base.treeFits
  rw [Sha2Address.ofAdrs, dif_pos hcanonical, dif_pos hlayer, dif_pos htree]
  rfl

/-- Reuse the S05 WOTS boundary theorem for secret derivation at a typed XMSS leaf. -/
theorem sha2_xmssWotsSkAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (idx : LeafIndex set.params) (i : ℕ) (hi : Adrs.Fits 4 i = true) :
    (Sha2Address.ofAdrs (wotsSkAdrs (wotsLeafAdrs base.value idx.val) i)).isOk = true :=
  sha2_wotsSkAdrs_isOk (sha2WotsLeafAddress set base idx) i hi

/-- Reuse the S05 WOTS boundary theorem for every chain/hash step at a typed XMSS leaf. -/
theorem sha2_xmssWotsChainHashAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (idx : LeafIndex set.params) (i j : ℕ) (hi : Adrs.Fits 4 i = true)
    (hj : Adrs.Fits 4 j = true) :
    (Sha2Address.ofAdrs
      ((wotsChainAdrs (wotsLeafAdrs base.value idx.val) i).setHashAddress j)).isOk = true :=
  sha2_wotsChainHashAdrs_isOk (sha2WotsLeafAddress set base idx) i j hi hj

/-- Reuse the S05 WOTS boundary theorem for public-key compression at a typed XMSS leaf. -/
theorem sha2_xmssWotsPkAdrs_isOk (set : FipsParameterSet) (base : Sha2Address)
    (idx : LeafIndex set.params) :
    (Sha2Address.ofAdrs (wotsPkAdrs (wotsLeafAdrs base.value idx.val))).isOk = true :=
  sha2_wotsPkAdrs_isOk (sha2WotsLeafAddress set base idx)

/-- SHAKE's full address serialization is exact for every approved typed XMSS leaf. -/
theorem shake_wotsLeafAdrs_roundtrip (set : FipsParameterSet) (base : Adrs)
    (hbase : base.isCanonical = true) (idx : LeafIndex set.params) :
    Adrs.fromVector (wotsLeafAdrs base idx.val).toVector = wotsLeafAdrs base idx.val :=
  wotsLeafAdrs_fromVector_toVector base idx.val hbase (fips_leafIndex_fits set idx)

/-- SHAKE's full address serialization is exact for every approved typed XMSS node. -/
theorem shake_xmssNodeAdrs_roundtrip (set : FipsParameterSet) (base : Adrs)
    (hbase : base.isCanonical = true) (pos : NodePosition set.params) :
    Adrs.fromVector (xmssNodeAdrs base pos.level pos.index.val).toVector =
      xmssNodeAdrs base pos.level pos.index.val := by
  rcases fips_nodePosition_fits set pos with ⟨hz, ht⟩
  exact xmssNodeAdrs_fromVector_toVector base pos.level pos.index.val hbase hz ht

end SLHDSA.Concrete
