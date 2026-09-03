/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Security.ReachableTargets

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

Both records are satisfied by every FIPS 205 parameter set and by the limited SHA2-128-24 profile.
The scope here is the eight tweakable-hash target roles.  The two secret-key derivation address
types pass through the same SHA-2 gate but are not hash targets, so they are not covered.

## References

- NIST FIPS 205, §4.2 (ADRS), §11.2.1 (`ADRSc` compression)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
-/

@[expose] public section

namespace SLHDSA.Security

open Concrete

/-! ## Address-field bounds -/

/-- Arithmetic conditions on a parameter set under which every reachable structural target address
is FIPS-canonical, and so lies in the domain on which SHAKE's full serialization is injective.

There is one field per bounded quantity rather than one per independent condition, so that each
proof can name the bound it is about; several fields therefore concern the same four-byte word.
Two of the seven are consequences of their siblings over a validated parameter set: `d_le` of
`treeBits_canonical`, and `a_le` of `forsIndex_le`.  `d_le_97` and `a_le_of_forsIndex_le` record
that. -/
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

/-- The FORS index condition already caps the tree height, because there is at least one tree. -/
theorem CanonicalAddressBounds.a_le_of_forsIndex_le {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) : 2 ^ vp.params.a ≤ 2 ^ 32 :=
  le_trans (Nat.le_mul_of_pos_left _ vp.valid.k_pos) hb.forsIndex_le

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

theorem layer_lt_canonical {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params)
    (layer : Fin vp.params.d) : layer.val < 2 ^ 32 :=
  lt_of_lt_of_le layer.isLt hb.d_le

theorem tree_lt_hypertree {vp : ValidatedParams} (layer : ℕ)
    (tree : Fin (2 ^ layerTreeHeight vp layer)) :
    tree.val < 2 ^ ((vp.params.d - 1) * vp.params.hp) := by
  refine lt_of_lt_of_le tree.isLt (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold layerTreeHeight
  exact Nat.mul_le_mul_right _ (by omega)

theorem tree_lt_canonical {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params)
    (layer : ℕ) (tree : Fin (2 ^ layerTreeHeight vp layer)) : tree.val < 2 ^ 96 :=
  lt_of_lt_of_le (tree_lt_hypertree layer tree)
    (Nat.pow_le_pow_right (by norm_num) hb.treeBits_canonical)

theorem leaf_lt_canonical {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params)
    (leaf : Fin (2 ^ vp.params.hp)) : leaf.val < 2 ^ 32 :=
  lt_of_lt_of_le leaf.isLt (Nat.pow_le_pow_right (by norm_num) hb.hp_le)

/-! ## Per-address facts -/

theorem addressFacts_wotsInstanceAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : LayerPosition vp) :
    AddressFacts vp (wotsInstanceAdrs pos) := by
  have hlayerEq : (wotsInstanceAdrs pos).layer = pos.layer.val := rfl
  have htreeEq : (wotsInstanceAdrs pos).tree = pos.tree.val := rfl
  have hword1 : (wotsInstanceAdrs pos).word1 = pos.leaf.val := rfl
  have hword2 : (wotsInstanceAdrs pos).word2 = 0 := rfl
  have hword3 : (wotsInstanceAdrs pos).word3 = 0 := rfl
  exact ⟨Adrs.isCanonical_of_fields_free (Or.inl rfl)
      (by rw [hlayerEq]; exact layer_lt_canonical hb pos.layer)
      (by rw [htreeEq]; exact tree_lt_canonical hb _ pos.tree) rfl
      (by rw [hword1]; exact leaf_lt_canonical hb pos.leaf)
      (by rw [hword2]; norm_num) (by rw [hword3]; norm_num),
    by rw [hlayerEq]; exact pos.layer.isLt,
    by rw [htreeEq]; exact tree_lt_hypertree _ pos.tree⟩

theorem addressFacts_wotsStepAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (coord : WotsChainCoord vp)
    (step : Fin (vp.params.w - 1)) :
    AddressFacts vp (wotsStepAdrs coord step) := by
  have hlayerEq : (wotsStepAdrs coord step).layer = coord.1.layer.val := rfl
  have htreeEq : (wotsStepAdrs coord step).tree = coord.1.tree.val := rfl
  have hword1 : (wotsStepAdrs coord step).word1 = coord.1.leaf.val := rfl
  have hword2 : (wotsStepAdrs coord step).word2 = coord.2.val := rfl
  have hword3 : (wotsStepAdrs coord step).word3 = step.val := rfl
  have hstep : step.val < 2 ^ 32 := by have := step.isLt; have := hb.w_le; omega
  have hchain : coord.2.val < 2 ^ 32 := by have := coord.2.isLt; have := hb.len_le; omega
  exact ⟨Adrs.isCanonical_of_fields_free (Or.inl rfl)
      (by rw [hlayerEq]; exact layer_lt_canonical hb coord.1.layer)
      (by rw [htreeEq]; exact tree_lt_canonical hb _ coord.1.tree) rfl
      (by rw [hword1]; exact leaf_lt_canonical hb coord.1.leaf)
      (by rw [hword2]; exact hchain) (by rw [hword3]; exact hstep),
    by rw [hlayerEq]; exact coord.1.layer.isLt,
    by rw [htreeEq]; exact tree_lt_hypertree _ coord.1.tree⟩

theorem addressFacts_wotsPkAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : LayerPosition vp) :
    AddressFacts vp (wotsPkAdrs (wotsInstanceAdrs pos)) := by
  have hlayerEq : (wotsPkAdrs (wotsInstanceAdrs pos)).layer = pos.layer.val := rfl
  have htreeEq : (wotsPkAdrs (wotsInstanceAdrs pos)).tree = pos.tree.val := rfl
  have hword1 : (wotsPkAdrs (wotsInstanceAdrs pos)).word1 = pos.leaf.val := rfl
  exact ⟨Adrs.isCanonical_of_fields_compress (Or.inl rfl)
      (by rw [hlayerEq]; exact layer_lt_canonical hb pos.layer)
      (by rw [htreeEq]; exact tree_lt_canonical hb _ pos.tree) rfl
      (by rw [hword1]; exact leaf_lt_canonical hb pos.leaf) rfl rfl,
    by rw [hlayerEq]; exact pos.layer.isLt,
    by rw [htreeEq]; exact tree_lt_hypertree _ pos.tree⟩

theorem addressFacts_forsNodeAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : BottomPosition vp) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    AddressFacts vp (forsNodeAdrs pos.forsAdrs z t) := by
  have hlayerEq : (forsNodeAdrs pos.forsAdrs z t).layer = 0 := rfl
  have htreeEq : (forsNodeAdrs pos.forsAdrs z t).tree = pos.tree.val := rfl
  have hword1 : (forsNodeAdrs pos.forsAdrs z t).word1 = pos.leaf.val := rfl
  have hword2 : (forsNodeAdrs pos.forsAdrs z t).word2 = z := rfl
  have hword3 : (forsNodeAdrs pos.forsAdrs z t).word3 = t := rfl
  exact ⟨Adrs.isCanonical_of_fields_free (Or.inr rfl) (by rw [hlayerEq]; norm_num)
      (by rw [htreeEq]; exact tree_lt_canonical hb 0 pos.tree) rfl
      (by rw [hword1]; exact leaf_lt_canonical hb pos.leaf)
      (by rw [hword2]; exact hz) (by rw [hword3]; exact ht),
    by rw [hlayerEq]; exact vp.valid.d_pos,
    by rw [htreeEq]; exact tree_lt_hypertree 0 pos.tree⟩

theorem addressFacts_forsPkAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (pos : BottomPosition vp) :
    AddressFacts vp (forsPkAdrs pos.forsAdrs) := by
  have hlayerEq : (forsPkAdrs pos.forsAdrs).layer = 0 := rfl
  have htreeEq : (forsPkAdrs pos.forsAdrs).tree = pos.tree.val := rfl
  have hword1 : (forsPkAdrs pos.forsAdrs).word1 = pos.leaf.val := rfl
  exact ⟨Adrs.isCanonical_of_fields_compress (Or.inr rfl) (by rw [hlayerEq]; norm_num)
      (by rw [htreeEq]; exact tree_lt_canonical hb 0 pos.tree) rfl
      (by rw [hword1]; exact leaf_lt_canonical hb pos.leaf) rfl rfl,
    by rw [hlayerEq]; exact vp.valid.d_pos,
    by rw [htreeEq]; exact tree_lt_hypertree 0 pos.tree⟩

theorem addressFacts_xmssNodeAdrs {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) (coord : LayerTreeCoord vp) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    AddressFacts vp (xmssNodeAdrs coord.toAdrs z t) := by
  have hlayerEq : (xmssNodeAdrs coord.toAdrs z t).layer = coord.layer.val := rfl
  have htreeEq : (xmssNodeAdrs coord.toAdrs z t).tree = coord.tree.val := rfl
  have hword1 : (xmssNodeAdrs coord.toAdrs z t).word1 = 0 := rfl
  have hword2 : (xmssNodeAdrs coord.toAdrs z t).word2 = z := rfl
  have hword3 : (xmssNodeAdrs coord.toAdrs z t).word3 = t := rfl
  exact ⟨Adrs.isCanonical_of_fields_tree
      (by rw [hlayerEq]; exact layer_lt_canonical hb coord.layer)
      (by rw [htreeEq]; exact tree_lt_canonical hb _ coord.tree) rfl hword1
      (by rw [hword2]; exact hz) (by rw [hword3]; exact ht),
    by rw [hlayerEq]; exact coord.layer.isLt,
    by rw [htreeEq]; exact tree_lt_hypertree _ coord.tree⟩

/-! ## Per-ledger facts -/

/-- The WOTS+ instance base addresses are not a target role of their own, being the identifier a
reduction indexes an instance by rather than a hashed target, but a reduction that carries them
needs the same facts. -/
theorem addressFacts_wotsInstanceAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ wotsInstanceAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [wotsInstanceAddresses, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  exact addressFacts_wotsInstanceAdrs hb pos

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

theorem addressFacts_forsRootAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ forsRootAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [forsRootAddresses, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  exact addressFacts_forsPkAdrs hb pos

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

theorem addressFacts_wotsStepAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    ∀ a ∈ wotsStepAddresses vp, AddressFacts vp a := by
  intro a ha
  simp only [wotsStepAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  exact addressFacts_wotsStepAdrs hb coord.1 coord.2

theorem addressFacts_selectedWotsAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params)
    (select : WotsChainCoord vp → Fin (vp.params.w - 1)) :
    ∀ a ∈ selectedWotsAddresses vp select, AddressFacts vp a := by
  intro a ha
  simp only [selectedWotsAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  exact addressFacts_wotsStepAdrs hb coord (select coord)

theorem addressFacts_optionalWotsAddresses (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params)
    (select : WotsChainCoord vp → Option (Fin (vp.params.w - 1))) :
    ∀ a ∈ optionalWotsAddresses vp select, AddressFacts vp a := by
  intro a ha
  simp only [optionalWotsAddresses, List.mem_filterMap] at ha
  obtain ⟨coord, -, hmap⟩ := ha
  obtain ⟨step, -, rfl⟩ := Option.map_eq_some_iff.mp hmap
  exact addressFacts_wotsStepAdrs hb coord step

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
`shakePrimitives` stay duplicate-free.  Canonicality is needed: the serialization truncates each
field to its width, so two addresses that differ only above a field's width share a tweak. -/
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

/-- Every reachable target ledger keeps distinct tweaks under the SHA-2 instantiation. -/
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

/-- Every reachable target ledger keeps distinct tweaks under the SHAKE instantiation.  Only the
canonical widths are needed, so this covers parameter sets whose hypertree is too tall for SHA-2's
compressed eight-byte tree field.  Being too deep for its one-byte layer field is not possible:
`CanonicalAddressBounds.d_le_256` rules that out. -/
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
