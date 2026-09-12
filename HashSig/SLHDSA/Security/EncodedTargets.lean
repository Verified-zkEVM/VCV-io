/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Security.ReachableTargets
import HashSig.SLHDSA.ForsConformance

/-!
# Encoded distinctness of the SLH-DSA reachable target ledgers

`EncodedTargetLedgerConditions` records, per security target role, that the concrete tweaks a
primitive bundle derives from a reachable address ledger are still pairwise distinct.  Structural
distinctness does not give this: a concrete encoder has narrower field domains than
`ValidatedParams` imposes, and outside those domains both approved encoders collapse distinct
addresses onto one key.  SHA-2's total projection returns the all-zero key, which is the genuine
key of the all-zero WOTS-hash address rather than a sentinel; SHAKE's serialization truncates each
field to its width.

The two encoders need different amounts of the parameter set:

- SHAKE serializes the full thirty-two byte `ADRS`, so it needs only that every listed address is
  FIPS-canonical, which `CanonicalAddressBounds` secures; and
- SHA-2 compresses to twenty-two bytes with a one-byte layer and an eight-byte tree, so it needs
  `ApprovedAddressBounds`.  Only its eight-byte tree condition is an independent addition: over a
  validated parameter set the canonical record already forces at most ninety-seven layers, hence a
  one-byte layer, as `CanonicalAddressBounds.d_le_97` shows.

`AddressFacts` is what the per-ledger lemmas actually establish, and it is stated once for both
routes: an address is canonical and its layer and tree lie in the hypertree's own ranges.  The
SHA-2 domain follows from it under the narrower widths, so no ledger lemma has to be proved twice.
Canonicality is derived through the construction's own address helpers: once
`layerPosition_toAdrs_isCanonical` shows the base address of a reachable position canonical under
`CanonicalAddressBounds`, the existing `wotsChainHashAdrs_isCanonical`, `wotsPkAdrs_isCanonical`,
`XmssConformance.wotsLeafAdrs_isCanonical`, `XmssConformance.xmssNodeAdrs_isCanonical`,
`ForsConformance.forsNodeAdrs_isCanonical`, and `ForsConformance.forsPkAdrs_isCanonical` lemmas
carry it to every derived target address.

The UD field of `EncodedTargetLedgerConditions` is stated for a total one-step-per-chain cap
completion.  A later reduction may omit chains; any such partial selector inherits encoded
distinctness through `EncodedTargetLedgerConditions.wotsFUd_partial`.  Defining the reduction's
exact selector and connecting it to program traces remain downstream obligations.

Both records are satisfied by every FIPS 205 parameter set and by the limited SHA2-128-24 profile.
The scope here is the eight tweakable-hash target roles.  The two secret-key derivation address
types pass through the same SHA-2 gate but are not hash targets, so they are not covered.

## References

- NIST FIPS 205, §4.2 (ADRS), §11.2 (`ADRSc` compression, Figure 18 and Table 3)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
-/

public section

namespace SLHDSA.Security

open Concrete

/-! ## Address-field bounds -/

/-- Arithmetic conditions on a parameter set under which every reachable structural target address
is FIPS-canonical, and so lies in the domain on which SHAKE's full serialization is injective.

There is one field per bounded quantity rather than one per independent condition, so that each
proof can name the bound it is about; several fields therefore concern the same four-byte word.
Two of the seven follow from their siblings over a validated parameter set:
`CanonicalAddressBounds.a_le_of_forsIndex_le` derives `a_le` from `forsIndex_le` and `k_pos`, and
`CanonicalAddressBounds.d_le_97` derives `d ≤ 97`, sharper than `d_le`, from `treeBits_canonical`
and `hp_pos`. -/
structure CanonicalAddressBounds (p : Params) : Prop where
  /-- The four-byte layer word holds every hypertree layer. -/
  d_le : p.d ≤ 2 ^ 32
  /-- The twelve-byte tree word holds every layer-zero tree index. -/
  treeBits_canonical : (p.d - 1) * p.hp ≤ 96
  /-- The four-byte words hold every XMSS leaf index, and every XMSS node height and index. -/
  hp_le : p.hp ≤ 32
  /-- The four-byte tree-height word holds every FORS node height. -/
  a_le : p.a ≤ 32
  /-- The four-byte tree-index word holds every FORS node index. -/
  forsIndex_le : p.k * 2 ^ p.a ≤ 2 ^ 32
  /-- The four-byte chain word holds every WOTS+ chain index. -/
  len_le : p.len ≤ 2 ^ 32
  /-- The four-byte hash-address word holds every WOTS+ chain step. -/
  w_le : p.w ≤ 2 ^ 32

/-- The canonical conditions together with the narrower widths SHA-2's compressed `ADRSc` layout
imposes on the layer and the tree.  Only `treeBits_le` adds anything: over a validated parameter
set `d_le_byte` already follows from the canonical record, as `CanonicalAddressBounds.d_le_256`
shows.  The tree condition is tight, and the two fast category-five parameter sets saturate it at
exactly sixty-four bits. -/
structure ApprovedAddressBounds (p : Params) : Prop extends CanonicalAddressBounds p where
  /-- The one-byte compressed layer field holds every hypertree layer. -/
  d_le_byte : p.d ≤ 256
  /-- The eight-byte compressed tree field holds every layer-zero tree index. -/
  treeBits_le : (p.d - 1) * p.hp ≤ 64

/-- The twelve-byte tree condition already caps the layer count, because every layer below the top
contributes at least one tree-index bit. -/
theorem CanonicalAddressBounds.d_le_97 {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) : vp.params.d ≤ 97 := by
  have hhp := vp.valid.hp_pos
  have h := hb.treeBits_canonical
  have hmul : (vp.params.d - 1) * 1 ≤ (vp.params.d - 1) * vp.params.hp :=
    Nat.mul_le_mul_left _ hhp
  omega

/-- Over a validated parameter set a one-byte layer field therefore comes for free, which is why
`ApprovedAddressBounds` adds only one independent condition.  Validity is needed: without a
positive layer height the twelve-byte tree condition is vacuous and the layer count is unbounded.
The name differs from that record's field so the two do not shadow. -/
theorem CanonicalAddressBounds.d_le_256 {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) : vp.params.d ≤ 256 :=
  le_trans hb.d_le_97 (by norm_num)

/-- The FORS index condition already caps the tree height at thirty-two, because there is at least
one tree. -/
theorem CanonicalAddressBounds.a_le_of_forsIndex_le {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) : vp.params.a ≤ 32 :=
  (Nat.pow_le_pow_iff_right Nat.one_lt_two).1
    (le_trans (Nat.le_mul_of_pos_left _ vp.valid.k_pos) hb.forsIndex_le)

/-- Every FIPS 205 parameter set fits the compressed SHA-2 address layout, hence also the wider
canonical one. -/
theorem fipsApprovedAddressBounds (ps : FipsParameterSet) :
    ApprovedAddressBounds ps.params := by
  cases ps <;>
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
      by decide, by decide⟩

/-- The limited-use SHA2-128-24 profile fits the compressed SHA-2 address layout. -/
theorem limitedApprovedAddressBounds (ps : LimitedParameterSet) :
    ApprovedAddressBounds ps.params := by
  cases ps
  exact ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-! ## What a ledger lemma establishes -/

/-- The facts a reachable target address carries: it is FIPS-canonical, and its layer and tree lie
in the ranges the hypertree itself defines.  Both encoder domains are cut from this, so the ledger
lemmas below are proved once and used by both routes. -/
structure AddressFacts (vp : ValidatedParams) (a : Adrs) : Prop where
  /-- The address has the exact field widths and unused-word zeroes FIPS prescribes. -/
  canonical : a.isCanonical = true
  /-- The address sits at a layer of this hypertree. -/
  layer_lt : a.layer < vp.params.d
  /-- The address sits in a tree reachable at some layer of this hypertree. -/
  tree_lt : a.tree < 2 ^ ((vp.params.d - 1) * vp.params.hp)

/-- Structural addresses that the SHA-2 instantiation compresses without its zero fallback. -/
def Sha2Domain (a : Adrs) : Prop :=
  a.isCanonical = true ∧ Adrs.Fits 1 a.layer = true ∧ Adrs.Fits 8 a.tree = true

/-- The domain is exactly what the checked compression boundary accepts, so a canary that runs
`Sha2Address.ofAdrs` over a ledger is testing this predicate and not a weaker one. -/
theorem sha2Domain_iff_ofAdrs_isSome {a : Adrs} :
    Sha2Domain a ↔ (Sha2Address.ofAdrs a).toOption.isSome = true := by
  unfold Sha2Domain Sha2Address.ofAdrs
  by_cases hcanonical : a.isCanonical = true
  · by_cases hlayer : Adrs.Fits 1 a.layer = true
    · by_cases htree : Adrs.Fits 8 a.tree = true
      · simp [hcanonical, hlayer, htree, Except.toOption]
      · simp [hcanonical, hlayer, htree, Except.toOption]
    · simp [hcanonical, hlayer, Except.toOption]
  · simp [hcanonical, Except.toOption]

/-- Under the compressed widths, every reachable target address is in the SHA-2 domain. -/
theorem sha2Domain_of_addressFacts {vp : ValidatedParams} (hb : ApprovedAddressBounds vp.params)
    {a : Adrs} (h : AddressFacts vp a) : Sha2Domain a := by
  refine ⟨h.canonical, Adrs.fits_iff.2 ?_, Adrs.fits_iff.2 ?_⟩
  · have := h.layer_lt
    have := hb.d_le_byte
    omega
  · refine lt_of_lt_of_le h.tree_lt ?_
    calc (2 : ℕ) ^ ((vp.params.d - 1) * vp.params.hp) ≤ 2 ^ 64 :=
          Nat.pow_le_pow_right (by norm_num) hb.treeBits_le
      _ = 256 ^ 8 := by norm_num

/-! ## Coordinate bounds -/

/-- Every hypertree layer fits a four-byte word under the canonical bounds. -/
theorem layer_lt_canonical {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params)
    (layer : Fin vp.params.d) : layer.val < 2 ^ 32 :=
  lt_of_lt_of_le layer.isLt hb.d_le

/-- Every tree index at any layer is below the layer-zero tree count `2 ^ ((d - 1) * hp)`. -/
theorem tree_lt_hypertree {vp : ValidatedParams} (layer : ℕ)
    (tree : Fin (2 ^ layerTreeHeight vp layer)) :
    tree.val < 2 ^ ((vp.params.d - 1) * vp.params.hp) := by
  refine lt_of_lt_of_le tree.isLt (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold layerTreeHeight
  exact Nat.mul_le_mul_right _ (by omega)

/-- Every tree index fits the twelve-byte tree word under the canonical bounds. -/
theorem tree_lt_canonical {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params)
    (layer : ℕ) (tree : Fin (2 ^ layerTreeHeight vp layer)) : tree.val < 2 ^ 96 :=
  lt_of_lt_of_le (tree_lt_hypertree layer tree)
    (Nat.pow_le_pow_right (by norm_num) hb.treeBits_canonical)

/-- Every XMSS leaf index fits a four-byte word under the canonical bounds. -/
theorem leaf_lt_canonical {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params)
    (leaf : Fin (2 ^ vp.params.hp)) : leaf.val < 2 ^ 32 :=
  lt_of_lt_of_le leaf.isLt (Nat.pow_le_pow_right (by norm_num) hb.hp_le)

/-- A value below `2 ^ 32` passes the four-byte field check. -/
private theorem fits_four_of_lt {x : ℕ} (h : x < 2 ^ 32) : Adrs.Fits 4 x = true :=
  Adrs.fits_iff.2 (lt_of_lt_of_le h (by norm_num))

/-! ## Base-address canonicality

The reachable base addresses are `LayerPosition.toAdrs` and `LayerTreeCoord.toAdrs`, both a layer
and a tree written into the zero address.  Every derived target address is then obtained by the
construction's own address helpers, whose canonicality lemmas
(`wotsChainHashAdrs_isCanonical`, `wotsPkAdrs_isCanonical`,
`XmssConformance.wotsLeafAdrs_isCanonical`, `XmssConformance.xmssNodeAdrs_isCanonical`,
`ForsConformance.forsNodeAdrs_isCanonical`, `ForsConformance.forsPkAdrs_isCanonical`) need only a
canonical base and four-byte bounds on the words they set.  The per-address facts below reuse them
rather than recomputing the six fields of each address. -/

/-- A layer/tree base address is canonical when both coordinates fit their words. -/
private theorem baseAdrs_isCanonical {layer tree : ℕ} (hlayer : layer < 2 ^ 32)
    (htree : tree < 2 ^ 96) :
    ((Adrs.zero.setLayerAddress layer).setTreeAddress tree).isCanonical = true := by
  rw [Adrs.isCanonical]
  simp only [Adrs.setLayerAddress, Adrs.setTreeAddress, Adrs.zero]
  rw [fits_four_of_lt hlayer, Adrs.fits_iff.2 (lt_of_lt_of_le htree (by norm_num))]
  norm_num [Adrs.Fits, AddrType.ofCode]

/-- The base address of every reachable layer position is canonical under the canonical bounds.
`Concrete.fips_layerPosition_toAdrs_isCanonical` is the per-parameter-set instance of this. -/
theorem layerPosition_toAdrs_isCanonical {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : LayerPosition vp) :
    pos.toAdrs.isCanonical = true :=
  baseAdrs_isCanonical (layer_lt_canonical hb pos.layer) (tree_lt_canonical hb _ pos.tree)

/-- The base address of every reachable XMSS tree is canonical under the canonical bounds. -/
theorem layerTreeCoord_toAdrs_isCanonical {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (coord : LayerTreeCoord vp) :
    coord.toAdrs.isCanonical = true :=
  baseAdrs_isCanonical (layer_lt_canonical hb coord.layer) (tree_lt_canonical hb _ coord.tree)

/-- Every reachable WOTS+ instance base address is canonical under the canonical bounds. -/
theorem wotsInstanceAdrs_isCanonical {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : LayerPosition vp) :
    (wotsInstanceAdrs pos).isCanonical = true :=
  XmssConformance.wotsLeafAdrs_isCanonical pos.toAdrs pos.leaf.val
    (layerPosition_toAdrs_isCanonical hb pos)
    (fits_four_of_lt (leaf_lt_canonical hb pos.leaf))

/-- The FORS analogue of `wotsLeafAdrs_isCanonical`: setting the `FORS_TREE` type and a four-byte
key pair on a canonical base keeps the address canonical. -/
private theorem setTypeAndClear_forsTree_setKeyPairAddress_isCanonical (adrs : Adrs) (t : ℕ)
    (hbase : adrs.isCanonical = true) (ht : Adrs.Fits 4 t = true) :
    ((adrs.setTypeAndClear .forsTree).setKeyPairAddress t).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with ⟨hlayer, htree, -, -, -, -⟩
  simp [Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.isCanonical, hlayer, htree, ht]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- Every reachable FORS base address is canonical under the canonical bounds. -/
theorem BottomPosition.forsAdrs_isCanonical {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : BottomPosition vp) :
    pos.forsAdrs.isCanonical = true :=
  setTypeAndClear_forsTree_setKeyPairAddress_isCanonical pos.toLayerPosition.toAdrs pos.leaf.val
    (layerPosition_toAdrs_isCanonical hb pos.toLayerPosition)
    (fits_four_of_lt (leaf_lt_canonical hb pos.leaf))

/-! ## Per-address facts -/

/-- Every WOTS+ chain-step address carries the address facts. -/
theorem addressFacts_wotsStepAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (coord : WotsChainCoord vp)
    (step : Fin (vp.params.w - 1)) :
    AddressFacts vp (wotsStepAdrs coord step) where
  canonical :=
    wotsChainHashAdrs_isCanonical (wotsInstanceAdrs coord.1) coord.2.val step.val
      (wotsInstanceAdrs_isCanonical hb coord.1)
      (fits_four_of_lt (by have := coord.2.isLt; have := hb.len_le; omega))
      (fits_four_of_lt (by have := step.isLt; have := hb.w_le; omega))
  layer_lt := coord.1.layer.isLt
  tree_lt := tree_lt_hypertree _ coord.1.tree

/-- Every WOTS+ public-key compression address carries the address facts. -/
theorem addressFacts_wotsPkAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : LayerPosition vp) :
    AddressFacts vp (wotsPkAdrs (wotsInstanceAdrs pos)) where
  canonical := wotsPkAdrs_isCanonical _ (wotsInstanceAdrs_isCanonical hb pos)
  layer_lt := pos.layer.isLt
  tree_lt := tree_lt_hypertree _ pos.tree

/-- Every FORS node address with four-byte height and index carries the address facts. -/
theorem addressFacts_forsNodeAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : BottomPosition vp) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    AddressFacts vp (forsNodeAdrs pos.forsAdrs z t) where
  canonical :=
    ForsConformance.forsNodeAdrs_isCanonical _ z t (BottomPosition.forsAdrs_isCanonical hb pos)
      (fits_four_of_lt hz) (fits_four_of_lt ht)
  layer_lt := vp.valid.d_pos
  tree_lt := tree_lt_hypertree 0 pos.tree

/-- Every FORS root compression address carries the address facts. -/
theorem addressFacts_forsPkAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : BottomPosition vp) :
    AddressFacts vp (forsPkAdrs pos.forsAdrs) where
  canonical := ForsConformance.forsPkAdrs_isCanonical _ (BottomPosition.forsAdrs_isCanonical hb pos)
  layer_lt := vp.valid.d_pos
  tree_lt := tree_lt_hypertree 0 pos.tree

/-- Every XMSS node address with four-byte height and index carries the address facts. -/
theorem addressFacts_xmssNodeAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (coord : LayerTreeCoord vp) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    AddressFacts vp (xmssNodeAdrs coord.toAdrs z t) where
  canonical :=
    XmssConformance.xmssNodeAdrs_isCanonical _ z t (layerTreeCoord_toAdrs_isCanonical hb coord)
      (fits_four_of_lt hz) (fits_four_of_lt ht)
  layer_lt := coord.layer.isLt
  tree_lt := tree_lt_hypertree _ coord.tree

/-! ## Per-ledger facts -/

/-- Every FORS leaf target carries the address facts; the global leaf index is below `k * 2^a`. -/
theorem addressFacts_forsLeafAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ forsLeafAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [forsLeafAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  refine addressFacts_forsNodeAdrs hb _ (by norm_num) ?_
  have hk := coord.1.2.isLt
  have hbound := hb.forsIndex_le
  have hstep : coord.1.2.val * vp.params.t + coord.2.val < vp.params.k * vp.params.t := by
    have hsucc : coord.1.2.val + 1 ≤ vp.params.k := hk
    have hmul : coord.1.2.val * vp.params.t + vp.params.t ≤ vp.params.k * vp.params.t := by
      calc coord.1.2.val * vp.params.t + vp.params.t = (coord.1.2.val + 1) * vp.params.t := by ring
        _ ≤ vp.params.k * vp.params.t := Nat.mul_le_mul_right _ hsucc
    have := coord.2.isLt
    omega
  simpa [Params.t] using lt_of_lt_of_le (by simpa [Params.t] using hstep) hbound

/-- Every FORS internal-node target carries the address facts; the height is at most `a` and the
global node index is below `k * 2^a`. -/
theorem addressFacts_forsTreeAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ forsTreeAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [forsTreeAddresses, List.mem_map] at ha
  obtain ⟨coord, hmem, rfl⟩ := ha
  have hnode : coord.2 ∈ perfectInternalCoords vp.params.a := by
    simpa [List.product] using (List.mem_product.1 hmem).2
  have hheight : coord.2.1 ≤ vp.params.a := perfectInternalCoords_height_le hnode
  have hindex : coord.2.2 < 2 ^ (vp.params.a - coord.2.1) := perfectInternalCoords_index_lt hnode
  have hk := coord.1.2.isLt
  have hbound := hb.forsIndex_le
  refine addressFacts_forsNodeAdrs hb _ (by have := hb.a_le; omega) ?_
  have hpow : (2 : ℕ) ^ (vp.params.a - coord.2.1) ≤ 2 ^ vp.params.a :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hstep : coord.1.2.val * 2 ^ (vp.params.a - coord.2.1) + coord.2.2 <
      vp.params.k * 2 ^ (vp.params.a - coord.2.1) := by
    have hsucc : coord.1.2.val + 1 ≤ vp.params.k := hk
    have hmul : coord.1.2.val * 2 ^ (vp.params.a - coord.2.1) + 2 ^ (vp.params.a - coord.2.1) ≤
        vp.params.k * 2 ^ (vp.params.a - coord.2.1) := by
      calc coord.1.2.val * 2 ^ (vp.params.a - coord.2.1) + 2 ^ (vp.params.a - coord.2.1)
          = (coord.1.2.val + 1) * 2 ^ (vp.params.a - coord.2.1) := by ring
        _ ≤ vp.params.k * 2 ^ (vp.params.a - coord.2.1) := Nat.mul_le_mul_right _ hsucc
    omega
  have hle : vp.params.k * 2 ^ (vp.params.a - coord.2.1) ≤ vp.params.k * 2 ^ vp.params.a :=
    Nat.mul_le_mul_left _ hpow
  omega

/-- Every FORS root compression target carries the address facts. -/
theorem addressFacts_forsRootAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ forsRootAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [forsRootAddresses, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  exact addressFacts_forsPkAdrs hb pos

/-- Every XMSS internal-node target carries the address facts; the height is at most `hp` and the
index is below `2^hp`. -/
theorem addressFacts_xmssNodeAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ xmssNodeAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [xmssNodeAddresses, List.mem_map] at ha
  obtain ⟨coord, hmem, rfl⟩ := ha
  have hnode : coord.2 ∈ perfectInternalCoords vp.params.hp := by
    simpa [List.product] using (List.mem_product.1 hmem).2
  have hheight : coord.2.1 ≤ vp.params.hp := perfectInternalCoords_height_le hnode
  have hindex : coord.2.2 < 2 ^ (vp.params.hp - coord.2.1) := perfectInternalCoords_index_lt hnode
  have hpow : (2 : ℕ) ^ (vp.params.hp - coord.2.1) ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by norm_num) (by have := hb.hp_le; omega)
  exact addressFacts_xmssNodeAdrs hb _ (by have := hb.hp_le; omega) (by omega)

/-- Every executed WOTS+ chain-step target carries the address facts. -/
theorem addressFacts_wotsStepAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ wotsStepAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [wotsStepAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  exact addressFacts_wotsStepAdrs hb coord.1 coord.2

/-- Every selected WOTS+ step target carries the address facts, whatever the selection. -/
theorem addressFacts_selectedWotsAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params)
    (select : WotsChainCoord vp → Fin (vp.params.w - 1)) :
    ∀ a ∈ selectedWotsAddresses vp select, AddressFacts vp a := by
  intro a ha
  simp only [selectedWotsAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  exact addressFacts_wotsStepAdrs hb coord (select coord)

/-- Every optionally selected WOTS+ step target carries the address facts, whatever the
selection. -/
theorem addressFacts_optionalWotsAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params)
    (select : WotsChainCoord vp → Option (Fin (vp.params.w - 1))) :
    ∀ a ∈ optionalWotsAddresses vp select, AddressFacts vp a := by
  intro a ha
  simp only [optionalWotsAddresses, List.mem_filterMap] at ha
  obtain ⟨coord, -, hmap⟩ := ha
  obtain ⟨step, -, rfl⟩ := Option.map_eq_some_iff.mp hmap
  exact addressFacts_wotsStepAdrs hb coord step

/-- Every WOTS+ public-key compression target carries the address facts. -/
theorem addressFacts_wotsPkAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ wotsPkAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [wotsPkAddresses, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  exact addressFacts_wotsPkAdrs hb pos

/-! ## Approved instantiations -/

/-- On a duplicate-free ledger inside the SHA-2 address domain, the compressed `ADRSc` tweaks of
`sha2Primitives` stay duplicate-free.  The hypothesis is what rules out the zero fallback: every
listed address compresses successfully, so its key is its own `ADRSc`. -/
theorem encodeTargets_sha2_nodup {p : Params} {addresses : List Adrs}
    (hnodup : addresses.Nodup) (hdomain : ∀ a ∈ addresses, Sha2Domain a) :
    (encodeTargets (sha2Primitives p) addresses).Nodup := by
  refine encodeTargets_nodup_of_injOn _ _ hnodup fun a ha b hb hkey => ?_
  obtain ⟨haCanonical, haLayer, haTree⟩ := hdomain a ha
  obtain ⟨hbCanonical, hbLayer, hbTree⟩ := hdomain b hb
  exact sha2AdrsKey_injective_of_domain haCanonical haLayer haTree hbCanonical hbLayer hbTree hkey

/-- On a duplicate-free ledger of canonical addresses, the full thirty-two byte tweaks of
`shakePrimitives` stay duplicate-free.  Field-width bounds are needed, and canonicality supplies
them: the serialization truncates each field to its width, so two addresses that differ only above
a field's width share a tweak. -/
theorem encodeTargets_shake_nodup {p : Params} {addresses : List Adrs}
    (hnodup : addresses.Nodup) (hcanonical : ∀ a ∈ addresses, a.isCanonical = true) :
    (encodeTargets (shakePrimitives p) addresses).Nodup := by
  refine encodeTargets_nodup_of_injOn _ _ hnodup fun a ha b hb hkey => ?_
  have ha' := Adrs.fromVector_toVector_of_isCanonical a (hcanonical a ha)
  have hb' := Adrs.fromVector_toVector_of_isCanonical b (hcanonical b hb)
  have hvec : Adrs.fromVector a.toVector = Adrs.fromVector b.toVector :=
    congrArg Adrs.fromVector hkey
  rw [ha', hb'] at hvec
  exact hvec

/-- Every reachable target ledger keeps distinct tweaks under the SHA-2 instantiation.  The UD
field covers total cap completions; `EncodedTargetLedgerConditions.wotsFUd_partial` specializes
the resulting structure to every partial UD selection. -/
theorem sha2EncodedTargetLedgerConditions (vp : ValidatedParams)
    (hb : ApprovedAddressBounds vp.params) :
    EncodedTargetLedgerConditions vp (sha2Primitives vp.params) where
  forsF := encodeTargets_sha2_nodup (forsLeafAddresses_nodup vp)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_forsLeafAddresses vp hb.toCanonicalAddressBounds a ha)
  forsH := encodeTargets_sha2_nodup (forsTreeAddresses_nodup vp)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_forsTreeAddresses vp hb.toCanonicalAddressBounds a ha)
  forsTl := encodeTargets_sha2_nodup (forsRootAddresses_nodup vp)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_forsRootAddresses vp hb.toCanonicalAddressBounds a ha)
  wotsFUd select := encodeTargets_sha2_nodup (selectedWotsAddresses_nodup vp select)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_selectedWotsAddresses vp hb.toCanonicalAddressBounds select a ha)
  wotsFTcr := encodeTargets_sha2_nodup (wotsStepAddresses_nodup vp)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_wotsStepAddresses vp hb.toCanonicalAddressBounds a ha)
  wotsFPre select := encodeTargets_sha2_nodup (optionalWotsAddresses_nodup vp select)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_optionalWotsAddresses vp hb.toCanonicalAddressBounds select a ha)
  wotsTl := encodeTargets_sha2_nodup (wotsPkAddresses_nodup vp)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_wotsPkAddresses vp hb.toCanonicalAddressBounds a ha)
  xmssH := encodeTargets_sha2_nodup (xmssNodeAddresses_nodup vp)
    fun a ha => sha2Domain_of_addressFacts hb
      (addressFacts_xmssNodeAddresses vp hb.toCanonicalAddressBounds a ha)

/-- Every reachable target ledger keeps distinct tweaks under the SHAKE instantiation.  The UD
field covers total cap completions, and `EncodedTargetLedgerConditions.wotsFUd_partial` derives
partial selections.  Only the canonical widths are needed, so this covers
parameter sets whose hypertree is too tall for SHA-2's compressed eight-byte tree field.  Being
too deep for its one-byte layer field is not possible: `CanonicalAddressBounds.d_le_256` rules
that out. -/
theorem shakeEncodedTargetLedgerConditions (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    EncodedTargetLedgerConditions vp (shakePrimitives vp.params) where
  forsF := encodeTargets_shake_nodup (forsLeafAddresses_nodup vp)
    fun a ha => (addressFacts_forsLeafAddresses vp hb a ha).canonical
  forsH := encodeTargets_shake_nodup (forsTreeAddresses_nodup vp)
    fun a ha => (addressFacts_forsTreeAddresses vp hb a ha).canonical
  forsTl := encodeTargets_shake_nodup (forsRootAddresses_nodup vp)
    fun a ha => (addressFacts_forsRootAddresses vp hb a ha).canonical
  wotsFUd select := encodeTargets_shake_nodup (selectedWotsAddresses_nodup vp select)
    fun a ha => (addressFacts_selectedWotsAddresses vp hb select a ha).canonical
  wotsFTcr := encodeTargets_shake_nodup (wotsStepAddresses_nodup vp)
    fun a ha => (addressFacts_wotsStepAddresses vp hb a ha).canonical
  wotsFPre select := encodeTargets_shake_nodup (optionalWotsAddresses_nodup vp select)
    fun a ha => (addressFacts_optionalWotsAddresses vp hb select a ha).canonical
  wotsTl := encodeTargets_shake_nodup (wotsPkAddresses_nodup vp)
    fun a ha => (addressFacts_wotsPkAddresses vp hb a ha).canonical
  xmssH := encodeTargets_shake_nodup (xmssNodeAddresses_nodup vp)
    fun a ha => (addressFacts_xmssNodeAddresses vp hb a ha).canonical

/-- The limited-use SHA2-128-24 profile satisfies them too.  It is a SHA-2 profile, so it takes the
compressed route. -/
theorem limitedEncodedTargetLedgerConditions (ps : LimitedParameterSet) :
    EncodedTargetLedgerConditions ps.validatedParams (sha2Primitives ps.params) :=
  sha2EncodedTargetLedgerConditions ps.validatedParams (limitedApprovedAddressBounds ps)

/-- Every approved FIPS 205 instantiation satisfies the encoded-ledger conditions. -/
theorem approvedEncodedTargetLedgerConditions (ps : FipsParameterSet) :
    EncodedTargetLedgerConditions ps.validatedParams (approvedPrimitives ps) := by
  have hb : ApprovedAddressBounds ps.validatedParams.params := fipsApprovedAddressBounds ps
  rw [approvedPrimitives]
  cases ps.hashFamily with
  | sha2 => exact sha2EncodedTargetLedgerConditions ps.validatedParams hb
  | shake => exact shakeEncodedTargetLedgerConditions ps.validatedParams hb.toCanonicalAddressBounds

end SLHDSA.Security
