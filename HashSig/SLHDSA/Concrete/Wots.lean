/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Wots

/-!
# Checked SHA2 Boundary for WOTS+ Addresses

The generic WOTS+ constructors preserve the canonical, narrow address grammar required by the
checked SHA2 adapter.  These lemmas make explicit that WOTS secret derivation, every chain hash
step, and public-key compression cannot enter the total primitive bundle's zero fallback when
started from a `Sha2Address` and given four-byte indices.
-/

@[expose] public section


namespace SLHDSA.Concrete

/-- A WOTS secret-key address constructed from a checked SHA2 base address is accepted by the
checked SHA2 address boundary. -/
theorem sha2_wotsSkAdrs_isOk (base : Sha2Address) (i : ℕ)
    (hi : Adrs.Fits 4 i = true) :
    (Sha2Address.ofAdrs (wotsSkAdrs base.value i)).isOk = true := by
  have hcanonical := wotsSkAdrs_isCanonical base.value i base.canonical hi
  have hlayer : Adrs.Fits 1 (wotsSkAdrs base.value i).layer = true := by
    simpa [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress] using base.layerFits
  have htree : Adrs.Fits 8 (wotsSkAdrs base.value i).tree = true := by
    simpa [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress] using base.treeFits
  simp [Sha2Address.ofAdrs, hcanonical, hlayer, htree]
  rfl

/-- A WOTS chain-step address constructed from a checked SHA2 base address is accepted by the
checked SHA2 address boundary. -/
theorem sha2_wotsChainHashAdrs_isOk (base : Sha2Address) (i j : ℕ)
    (hi : Adrs.Fits 4 i = true) (hj : Adrs.Fits 4 j = true) :
    (Sha2Address.ofAdrs ((wotsChainAdrs base.value i).setHashAddress j)).isOk = true := by
  have hcanonical :=
    wotsChainHashAdrs_isCanonical base.value i j base.canonical hi hj
  have hlayer :
      Adrs.Fits 1 ((wotsChainAdrs base.value i).setHashAddress j).layer = true := by
    simpa [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress] using base.layerFits
  have htree :
      Adrs.Fits 8 ((wotsChainAdrs base.value i).setHashAddress j).tree = true := by
    simpa [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress] using base.treeFits
  simp [Sha2Address.ofAdrs, hcanonical, hlayer, htree]
  rfl

/-- A WOTS public-key compression address constructed from a checked SHA2 base address is
accepted by the checked SHA2 address boundary. -/
theorem sha2_wotsPkAdrs_isOk (base : Sha2Address) :
    (Sha2Address.ofAdrs (wotsPkAdrs base.value)).isOk = true := by
  have hcanonical := wotsPkAdrs_isCanonical base.value base.canonical
  have hlayer : Adrs.Fits 1 (wotsPkAdrs base.value).layer = true := by
    simpa [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress] using base.layerFits
  have htree : Adrs.Fits 8 (wotsPkAdrs base.value).tree = true := by
    simpa [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress] using base.treeFits
  simp [Sha2Address.ofAdrs, hcanonical, hlayer, htree]
  rfl

end SLHDSA.Concrete
