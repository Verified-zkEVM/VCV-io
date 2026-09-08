/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Concrete.Xmss
public import HashSig.SLHDSA.HypertreeGeneral

/-!
# Checked concrete boundary for hypertree positions

Every reachable layer/tree position in the twelve FIPS 205 parameter sets is canonical and fits
the compressed SHA2 address domain.  The same canonicality theorem gives exact SHAKE full-address
serialization.  XMSS leaf and node addresses then reuse the checked boundary in
`HashSig.SLHDSA.Concrete.Xmss`.
-/

@[expose] public section

namespace SLHDSA.Concrete

/-- Every reachable approved hypertree layer fits the one-byte SHA2 layer field. -/
theorem fips_layerPosition_layer_fits (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) :
    Adrs.Fits 1 pos.layer.val = true := by
  have h : pos.layer.val < 256 :=
    lt_of_lt_of_le pos.layer.isLt (by cases set <;> decide)
  simpa [Adrs.Fits] using h

/-- Every reachable approved hypertree tree coordinate fits the eight-byte SHA2 tree field. -/
theorem fips_layerPosition_tree_fits (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) :
    Adrs.Fits 8 pos.tree.val = true := by
  have hheight : layerTreeHeight set.validatedParams pos.layer.val ≤ 64 := by
    cases set <;>
      simp [FipsParameterSet.validatedParams, FipsParameterSet.params,
        layerTreeHeight] <;> omega
  have hpow : 2 ^ layerTreeHeight set.validatedParams pos.layer.val ≤ 256 ^ 8 := by
    calc
      2 ^ layerTreeHeight set.validatedParams pos.layer.val ≤ 2 ^ 64 :=
        Nat.pow_le_pow_right (by omega) hheight
      _ = 256 ^ 8 := by norm_num
  simpa [Adrs.Fits] using lt_of_lt_of_le pos.tree.isLt hpow

/-- Every reachable approved hypertree base address is canonical. -/
theorem fips_layerPosition_toAdrs_isCanonical (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) : pos.toAdrs.isCanonical = true := by
  have hlayer := fips_layerPosition_layer_fits set pos
  have htree8 := fips_layerPosition_tree_fits set pos
  have htree12 : Adrs.Fits 12 pos.tree.val = true := by
    have hlt : pos.tree.val < 256 ^ 8 := by simpa [Adrs.Fits] using htree8
    simpa [Adrs.Fits] using lt_of_lt_of_le hlt (by norm_num : 256 ^ 8 ≤ 256 ^ 12)
  rw [Adrs.isCanonical]
  simp only [LayerPosition.toAdrs, Adrs.setLayerAddress, Adrs.setTreeAddress, Adrs.zero]
  rw [show Adrs.Fits 4 pos.layer.val = true by
        have hlt : pos.layer.val < 256 := by simpa [Adrs.Fits] using hlayer
        simpa [Adrs.Fits] using lt_of_lt_of_le hlt (by norm_num : 256 ≤ 256 ^ 4)]
  rw [htree12]
  norm_num [Adrs.Fits, AddrType.ofCode]

/-- Proof-carrying SHA2 address for a reachable approved hypertree position. -/
def sha2LayerPositionAddress (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) : Sha2Address where
  value := pos.toAdrs
  canonical := fips_layerPosition_toAdrs_isCanonical set pos
  layerFits := fips_layerPosition_layer_fits set pos
  treeFits := fips_layerPosition_tree_fits set pos

/-- The checked SHA2 boundary accepts every reachable approved hypertree base address. -/
theorem sha2_layerPosition_toAdrs_isOk (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) :
    (Sha2Address.ofAdrs pos.toAdrs).isOk = true := by
  rw [Sha2Address.ofAdrs, dif_pos (fips_layerPosition_toAdrs_isCanonical set pos)]
  rw [dif_pos (by simpa using fips_layerPosition_layer_fits set pos)]
  rw [dif_pos (by simpa using fips_layerPosition_tree_fits set pos)]
  rfl

/-- SHAKE full-address serialization round-trips every reachable approved hypertree base
address. -/
theorem shake_layerPosition_toAdrs_roundtrip (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) :
    Adrs.fromVector pos.toAdrs.toVector = pos.toAdrs :=
  Adrs.fromVector_toVector_of_isCanonical pos.toAdrs
    (fips_layerPosition_toAdrs_isCanonical set pos)

/-- The checked XMSS boundary accepts every WOTS leaf reached from an approved hypertree
position. -/
theorem sha2_hypertreeWotsLeafAdrs_isOk (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) :
    (Sha2Address.ofAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val)).isOk = true :=
  sha2_wotsLeafAdrs_isOk set (sha2LayerPositionAddress set pos) pos.leaf

/-- The checked XMSS boundary accepts every typed internal-node address rooted at an approved
hypertree position. -/
theorem sha2_hypertreeXmssNodeAdrs_isOk (set : FipsParameterSet)
    (pos : LayerPosition set.validatedParams) (node : XmssConformance.NodePosition set.params) :
    (Sha2Address.ofAdrs
      (xmssNodeAdrs pos.toAdrs node.level node.index.val)).isOk = true :=
  sha2_xmssNodeAdrs_isOk set (sha2LayerPositionAddress set pos) node

end SLHDSA.Concrete
