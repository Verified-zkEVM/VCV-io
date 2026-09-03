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

`EncodedTargetLedgerConditions` records, for each security target role, that the concrete tweaks a
primitive bundle derives from a reachable address ledger are still pairwise distinct.  Structural
distinctness alone does not give this: a concrete encoder has narrower field domains than
`ValidatedParams` imposes, most visibly SHA-2's one-byte layer and eight-byte tree, and its
out-of-domain fallback aliases a legitimate reachable key rather than a distinguished sentinel.

This module discharges every field of that structure for both approved instantiations:

- `sha2EncodedTargetLedgerConditions` uses `sha2AdrsKey_injective_of_domain`, so it needs each
  listed address to be canonical with a one-byte layer and eight-byte tree; and
- `shakeEncodedTargetLedgerConditions` uses full 32-byte serialization, so it needs only
  canonicality.

Both are parameterized by `Params.ApprovedAddressBounds`, arithmetic side conditions that every
FIPS 205 parameter set and the limited SHA2-128-24 profile satisfy by evaluation.

## References

- NIST FIPS 205, §4.2 (ADRS), §11.2.1 (`ADRSc` compression)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
-/

@[expose] public section

namespace SLHDSA.Security

open Concrete

/-! ## Address-field bounds -/

/-- Arithmetic side conditions on a parameter set under which every reachable structural address
lies in the domain of both approved address encoders.

The first seven fields make an address FIPS-canonical, which is all the SHAKE encoder needs: it
serializes the full thirty-two byte `ADRS`.  The last two are what SHA-2's narrower compressed
`ADRSc` additionally requires, since it gives the layer one byte and the tree eight.  They are
stated together as one record because every approved profile satisfies all nine, and because a
security context that fixes a parameter set should discharge the address side conditions once. -/
structure Params.ApprovedAddressBounds (p : Params) : Prop where
  /-- The four-byte layer field holds every hypertree layer. -/
  d_le : p.d ≤ 2 ^ 32
  /-- The twelve-byte tree field holds every layer-zero tree index. -/
  treeBits_canonical : (p.d - 1) * p.hp ≤ 96
  /-- The four-byte key-pair field holds every XMSS leaf index. -/
  hp_le : p.hp ≤ 32
  /-- The four-byte tree-height field holds every FORS node height. -/
  a_le : p.a ≤ 32
  /-- The four-byte tree-index field holds every FORS node index. -/
  forsIndex_le : p.k * 2 ^ p.a ≤ 2 ^ 32
  /-- The four-byte chain field holds every WOTS+ chain index. -/
  len_le : p.len ≤ 2 ^ 32
  /-- The four-byte hash-address field holds every WOTS+ chain step. -/
  w_le : p.w ≤ 2 ^ 32
  /-- The one-byte compressed layer field holds every hypertree layer. -/
  d_le_byte : p.d ≤ 256
  /-- The eight-byte compressed tree field holds every layer-zero tree index. -/
  treeBits_le : (p.d - 1) * p.hp ≤ 64

/-- Every FIPS 205 parameter set fits the compressed SHA-2 address layout. -/
theorem fipsApprovedAddressBounds (ps : FipsParameterSet) :
    Params.ApprovedAddressBounds ps.params := by
  cases ps <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide⟩

/-- The limited-use SHA2-128-24 profile fits the compressed SHA-2 address layout. -/
theorem limitedApprovedAddressBounds (ps : LimitedParameterSet) :
    Params.ApprovedAddressBounds ps.params := by
  cases ps
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## Canonical and SHA-2 address domains -/

/-- Structural addresses that the SHA-2 instantiation compresses without its zero fallback:
canonical, with a one-byte layer and an eight-byte tree. -/
def Sha2Domain (a : Adrs) : Prop :=
  a.isCanonical = true ∧ Adrs.Fits 1 a.layer = true ∧ Adrs.Fits 8 a.tree = true

theorem fits_iff {width value : ℕ} : Adrs.Fits width value = true ↔ value < 256 ^ width := by
  simp [Adrs.Fits]

/-- Field-level sufficient condition for an address type with no unused words. -/
theorem sha2Domain_of_fields_free {a : Adrs} {ty : AddrType}
    (hfree : ty = .wotsHash ∨ ty = .forsTree)
    (hlayer : a.layer < 256) (htree : a.tree < 2 ^ 64) (hty : a.type = ty.toCode)
    (hword1 : a.word1 < 2 ^ 32) (hword2 : a.word2 < 2 ^ 32) (hword3 : a.word3 < 2 ^ 32) :
    Sha2Domain a := by
  refine ⟨?_, fits_iff.2 (by omega), fits_iff.2 (by omega)⟩
  rcases hfree with rfl | rfl <;>
    simp only [Adrs.isCanonical, hty, AddrType.toCode, AddrType.ofCode, Bool.and_eq_true,
      Adrs.Fits, decide_eq_true_eq, Option.isSome_some] <;>
    and_intros <;> first | omega | decide

/-- Field-level sufficient condition for a compression type, whose last two words are unused. -/
theorem sha2Domain_of_fields_compress {a : Adrs} {ty : AddrType}
    (hcompress : ty = .wotsPk ∨ ty = .forsRoots)
    (hlayer : a.layer < 256) (htree : a.tree < 2 ^ 64) (hty : a.type = ty.toCode)
    (hword1 : a.word1 < 2 ^ 32) (hword2 : a.word2 = 0) (hword3 : a.word3 = 0) :
    Sha2Domain a := by
  refine ⟨?_, fits_iff.2 (by omega), fits_iff.2 (by omega)⟩
  rcases hcompress with rfl | rfl <;>
    simp only [Adrs.isCanonical, hty, AddrType.toCode, AddrType.ofCode, Bool.and_eq_true,
      Adrs.Fits, decide_eq_true_eq, Option.isSome_some, hword2, hword3] <;>
    and_intros <;> first | omega | decide

/-- Field-level sufficient condition for the XMSS tree type, whose first word is unused. -/
theorem sha2Domain_of_fields_tree {a : Adrs}
    (hlayer : a.layer < 256) (htree : a.tree < 2 ^ 64) (hty : a.type = AddrType.tree.toCode)
    (hword1 : a.word1 = 0) (hword2 : a.word2 < 2 ^ 32) (hword3 : a.word3 < 2 ^ 32) :
    Sha2Domain a := by
  refine ⟨?_, fits_iff.2 (by omega), fits_iff.2 (by omega)⟩
  simp only [Adrs.isCanonical, hty, AddrType.toCode, AddrType.ofCode, Bool.and_eq_true,
    Adrs.Fits, decide_eq_true_eq, Option.isSome_some, hword1]
  and_intros <;> first | omega | decide

/-! ## Coordinate bounds -/

theorem layer_lt_of_bounds {vp : ValidatedParams} (hb : Params.ApprovedAddressBounds vp.params)
    (pos : LayerPosition vp) : pos.layer.val < 256 :=
  lt_of_lt_of_le pos.layer.isLt hb.d_le_byte

theorem tree_lt_of_bounds {vp : ValidatedParams} (hb : Params.ApprovedAddressBounds vp.params)
    (layer : ℕ) (tree : Fin (2 ^ layerTreeHeight vp layer)) : tree.val < 2 ^ 64 := by
  refine lt_of_lt_of_le tree.isLt (Nat.pow_le_pow_right (by norm_num) ?_)
  have hle : layerTreeHeight vp layer ≤ (vp.params.d - 1) * vp.params.hp := by
    unfold layerTreeHeight
    exact Nat.mul_le_mul_right _ (by omega)
  have := hb.treeBits_le
  omega

theorem leaf_lt_of_bounds {vp : ValidatedParams} (hb : Params.ApprovedAddressBounds vp.params)
    (leaf : Fin (2 ^ vp.params.hp)) : leaf.val < 2 ^ 32 :=
  lt_of_lt_of_le leaf.isLt (Nat.pow_le_pow_right (by norm_num) hb.hp_le)

/-! ## Per-address domain membership -/

theorem sha2Domain_wotsInstanceAdrs {vp : ValidatedParams}
    (hb : Params.ApprovedAddressBounds vp.params) (pos : LayerPosition vp) :
    Sha2Domain (wotsInstanceAdrs pos) := by
  have hlayerEq : (wotsInstanceAdrs pos).layer = pos.layer.val := rfl
  have htreeEq : (wotsInstanceAdrs pos).tree = pos.tree.val := rfl
  have hword1 : (wotsInstanceAdrs pos).word1 = pos.leaf.val := rfl
  have hword2 : (wotsInstanceAdrs pos).word2 = 0 := rfl
  have hword3 : (wotsInstanceAdrs pos).word3 = 0 := rfl
  exact sha2Domain_of_fields_free (Or.inl rfl)
    (by rw [hlayerEq]; exact layer_lt_of_bounds hb pos)
    (by rw [htreeEq]; exact tree_lt_of_bounds hb _ pos.tree) rfl
    (by rw [hword1]; exact leaf_lt_of_bounds hb pos.leaf)
    (by rw [hword2]; norm_num) (by rw [hword3]; norm_num)

theorem sha2Domain_wotsStepAdrs {vp : ValidatedParams}
    (hb : Params.ApprovedAddressBounds vp.params) (coord : WotsChainCoord vp)
    (step : Fin (vp.params.w - 1)) :
    Sha2Domain (wotsStepAdrs coord step) := by
  have hlayerEq : (wotsStepAdrs coord step).layer = coord.1.layer.val := rfl
  have htreeEq : (wotsStepAdrs coord step).tree = coord.1.tree.val := rfl
  have hword1 : (wotsStepAdrs coord step).word1 = coord.1.leaf.val := rfl
  have hword2 : (wotsStepAdrs coord step).word2 = coord.2.val := rfl
  have hword3 : (wotsStepAdrs coord step).word3 = step.val := rfl
  have hstep : step.val < 2 ^ 32 := by have := step.isLt; have := hb.w_le; omega
  have hchain : coord.2.val < 2 ^ 32 := by have := coord.2.isLt; have := hb.len_le; omega
  exact sha2Domain_of_fields_free (Or.inl rfl)
    (by rw [hlayerEq]; exact layer_lt_of_bounds hb coord.1)
    (by rw [htreeEq]; exact tree_lt_of_bounds hb _ coord.1.tree) rfl
    (by rw [hword1]; exact leaf_lt_of_bounds hb coord.1.leaf)
    (by rw [hword2]; exact hchain) (by rw [hword3]; exact hstep)

theorem sha2Domain_wotsPkAdrs {vp : ValidatedParams}
    (hb : Params.ApprovedAddressBounds vp.params) (pos : LayerPosition vp) :
    Sha2Domain (wotsPkAdrs (wotsInstanceAdrs pos)) := by
  have hlayerEq : (wotsPkAdrs (wotsInstanceAdrs pos)).layer = pos.layer.val := rfl
  have htreeEq : (wotsPkAdrs (wotsInstanceAdrs pos)).tree = pos.tree.val := rfl
  have hword1 : (wotsPkAdrs (wotsInstanceAdrs pos)).word1 = pos.leaf.val := rfl
  exact sha2Domain_of_fields_compress (Or.inl rfl)
    (by rw [hlayerEq]; exact layer_lt_of_bounds hb pos)
    (by rw [htreeEq]; exact tree_lt_of_bounds hb _ pos.tree) rfl
    (by rw [hword1]; exact leaf_lt_of_bounds hb pos.leaf) rfl rfl

theorem sha2Domain_forsNodeAdrs {vp : ValidatedParams}
    (hb : Params.ApprovedAddressBounds vp.params) (pos : BottomPosition vp) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    Sha2Domain (forsNodeAdrs pos.forsAdrs z t) := by
  have hlayerEq : (forsNodeAdrs pos.forsAdrs z t).layer = 0 := rfl
  have htreeEq : (forsNodeAdrs pos.forsAdrs z t).tree = pos.tree.val := rfl
  have hword1 : (forsNodeAdrs pos.forsAdrs z t).word1 = pos.leaf.val := rfl
  have hword2 : (forsNodeAdrs pos.forsAdrs z t).word2 = z := rfl
  have hword3 : (forsNodeAdrs pos.forsAdrs z t).word3 = t := rfl
  exact sha2Domain_of_fields_free (Or.inr rfl) (by rw [hlayerEq]; norm_num)
    (by rw [htreeEq]; exact tree_lt_of_bounds hb 0 pos.tree) rfl
    (by rw [hword1]; exact leaf_lt_of_bounds hb pos.leaf)
    (by rw [hword2]; exact hz) (by rw [hword3]; exact ht)

theorem sha2Domain_forsPkAdrs {vp : ValidatedParams}
    (hb : Params.ApprovedAddressBounds vp.params) (pos : BottomPosition vp) :
    Sha2Domain (forsPkAdrs pos.forsAdrs) := by
  have hlayerEq : (forsPkAdrs pos.forsAdrs).layer = 0 := rfl
  have htreeEq : (forsPkAdrs pos.forsAdrs).tree = pos.tree.val := rfl
  have hword1 : (forsPkAdrs pos.forsAdrs).word1 = pos.leaf.val := rfl
  exact sha2Domain_of_fields_compress (Or.inr rfl) (by rw [hlayerEq]; norm_num)
    (by rw [htreeEq]; exact tree_lt_of_bounds hb 0 pos.tree) rfl
    (by rw [hword1]; exact leaf_lt_of_bounds hb pos.leaf) rfl rfl

theorem sha2Domain_xmssNodeAdrs {vp : ValidatedParams}
    (hb : Params.ApprovedAddressBounds vp.params) (coord : LayerTreeCoord vp) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    Sha2Domain (xmssNodeAdrs coord.toAdrs z t) := by
  have hlayerEq : (xmssNodeAdrs coord.toAdrs z t).layer = coord.layer.val := rfl
  have htreeEq : (xmssNodeAdrs coord.toAdrs z t).tree = coord.tree.val := rfl
  have hword1 : (xmssNodeAdrs coord.toAdrs z t).word1 = 0 := rfl
  have hword2 : (xmssNodeAdrs coord.toAdrs z t).word2 = z := rfl
  have hword3 : (xmssNodeAdrs coord.toAdrs z t).word3 = t := rfl
  exact sha2Domain_of_fields_tree
    (by rw [hlayerEq]; exact lt_of_lt_of_le coord.layer.isLt hb.d_le_byte)
    (by rw [htreeEq]; exact tree_lt_of_bounds hb _ coord.tree) rfl hword1
    (by rw [hword2]; exact hz) (by rw [hword3]; exact ht)

/-! ## Per-ledger domain membership -/

theorem sha2Domain_forsLeafAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    ∀ a ∈ forsLeafAddresses vp, Sha2Domain a := by
  intro a ha
  simp only [forsLeafAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  refine sha2Domain_forsNodeAdrs hb _ (by norm_num) ?_
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

theorem sha2Domain_forsTreeAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    ∀ a ∈ forsTreeAddresses vp, Sha2Domain a := by
  intro a ha
  simp only [forsTreeAddresses, List.mem_map] at ha
  obtain ⟨coord, hmem, rfl⟩ := ha
  have hnode : coord.2 ∈ perfectInternalCoords vp.params.a := by
    simpa [List.product] using (List.mem_product.1 hmem).2
  have hheight : coord.2.1 ≤ vp.params.a := perfectInternalCoords_height_le hnode
  have hindex : coord.2.2 < 2 ^ (vp.params.a - coord.2.1) := perfectInternalCoords_index_lt hnode
  have hk := coord.1.2.isLt
  have hbound := hb.forsIndex_le
  refine sha2Domain_forsNodeAdrs hb _ (by have := hb.a_le; omega) ?_
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

theorem sha2Domain_forsRootAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    ∀ a ∈ forsRootAddresses vp, Sha2Domain a := by
  intro a ha
  simp only [forsRootAddresses, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  exact sha2Domain_forsPkAdrs hb pos

theorem sha2Domain_xmssNodeAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    ∀ a ∈ xmssNodeAddresses vp, Sha2Domain a := by
  intro a ha
  simp only [xmssNodeAddresses, List.mem_map] at ha
  obtain ⟨coord, hmem, rfl⟩ := ha
  have hnode : coord.2 ∈ perfectInternalCoords vp.params.hp := by
    simpa [List.product] using (List.mem_product.1 hmem).2
  have hheight : coord.2.1 ≤ vp.params.hp := perfectInternalCoords_height_le hnode
  have hindex : coord.2.2 < 2 ^ (vp.params.hp - coord.2.1) := perfectInternalCoords_index_lt hnode
  have hpow : (2 : ℕ) ^ (vp.params.hp - coord.2.1) ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by norm_num) (by have := hb.hp_le; omega)
  exact sha2Domain_xmssNodeAdrs hb _ (by have := hb.hp_le; omega) (by omega)

theorem sha2Domain_wotsStepAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    ∀ a ∈ wotsStepAddresses vp, Sha2Domain a := by
  intro a ha
  simp only [wotsStepAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  exact sha2Domain_wotsStepAdrs hb coord.1 coord.2

theorem sha2Domain_selectedWotsAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params)
    (select : WotsChainCoord vp → Fin (vp.params.w - 1)) :
    ∀ a ∈ selectedWotsAddresses vp select, Sha2Domain a := by
  intro a ha
  simp only [selectedWotsAddresses, List.mem_map] at ha
  obtain ⟨coord, -, rfl⟩ := ha
  exact sha2Domain_wotsStepAdrs hb coord (select coord)

theorem sha2Domain_optionalWotsAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params)
    (select : WotsChainCoord vp → Option (Fin (vp.params.w - 1))) :
    ∀ a ∈ optionalWotsAddresses vp select, Sha2Domain a := by
  intro a ha
  simp only [optionalWotsAddresses, List.mem_filterMap] at ha
  obtain ⟨coord, -, hmap⟩ := ha
  rcases hselect : select coord with _ | step
  · rw [hselect] at hmap; simp at hmap
  · rw [hselect] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    subst hmap
    exact sha2Domain_wotsStepAdrs hb coord step

theorem sha2Domain_wotsPkAddresses (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    ∀ a ∈ wotsPkAddresses vp, Sha2Domain a := by
  intro a ha
  simp only [wotsPkAddresses, List.mem_map] at ha
  obtain ⟨pos, -, rfl⟩ := ha
  exact sha2Domain_wotsPkAdrs hb pos

/-! ## Approved instantiations -/

/-- On a duplicate-free ledger inside the SHA-2 address domain, the compressed `ADRSc` tweaks of
`sha2Primitives` stay duplicate-free; in particular no listed address reaches the zero fallback. -/
theorem encodeTargets_sha2_nodup {p : Params} {addresses : List Adrs}
    (hnodup : addresses.Nodup) (hdomain : ∀ a ∈ addresses, Sha2Domain a) :
    (encodeTargets (sha2Primitives p) addresses).Nodup := by
  refine encodeTargets_nodup_of_injOn _ _ hnodup fun a ha b hb hkey => ?_
  obtain ⟨haCanonical, haLayer, haTree⟩ := hdomain a ha
  obtain ⟨hbCanonical, hbLayer, hbTree⟩ := hdomain b hb
  exact sha2AdrsKey_injective_of_domain haCanonical haLayer haTree
    (Adrs.fits_one_type_of_isCanonical haCanonical) hbCanonical hbLayer hbTree
    (Adrs.fits_one_type_of_isCanonical hbCanonical) hkey

/-- On a duplicate-free ledger of canonical addresses, the full 32-byte tweaks of
`shakePrimitives` stay duplicate-free. -/
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
    (hb : Params.ApprovedAddressBounds vp.params) :
    EncodedTargetLedgerConditions vp (sha2Primitives vp.params) where
  forsF := encodeTargets_sha2_nodup (forsLeafAddresses_nodup vp)
    (sha2Domain_forsLeafAddresses vp hb)
  forsH := encodeTargets_sha2_nodup (forsTreeAddresses_nodup vp)
    (sha2Domain_forsTreeAddresses vp hb)
  forsTl := encodeTargets_sha2_nodup (forsRootAddresses_nodup vp)
    (sha2Domain_forsRootAddresses vp hb)
  wotsFUd select := encodeTargets_sha2_nodup (selectedWotsAddresses_nodup vp select)
    (sha2Domain_selectedWotsAddresses vp hb select)
  wotsFTcr := encodeTargets_sha2_nodup (wotsStepAddresses_nodup vp)
    (sha2Domain_wotsStepAddresses vp hb)
  wotsFPre select := encodeTargets_sha2_nodup (optionalWotsAddresses_nodup vp select)
    (sha2Domain_optionalWotsAddresses vp hb select)
  wotsTl := encodeTargets_sha2_nodup (wotsPkAddresses_nodup vp)
    (sha2Domain_wotsPkAddresses vp hb)
  xmssH := encodeTargets_sha2_nodup (xmssNodeAddresses_nodup vp)
    (sha2Domain_xmssNodeAddresses vp hb)

/-- Every reachable target ledger keeps distinct tweaks under the SHAKE instantiation.  Only the
canonicality half of `Params.ApprovedAddressBounds` is used here: the full serialization is
injective on canonical addresses, with no narrower field domain to respect. -/
theorem shakeEncodedTargetLedgerConditions (vp : ValidatedParams)
    (hb : Params.ApprovedAddressBounds vp.params) :
    EncodedTargetLedgerConditions vp (shakePrimitives vp.params) where
  forsF := encodeTargets_shake_nodup (forsLeafAddresses_nodup vp)
    fun a ha => (sha2Domain_forsLeafAddresses vp hb a ha).1
  forsH := encodeTargets_shake_nodup (forsTreeAddresses_nodup vp)
    fun a ha => (sha2Domain_forsTreeAddresses vp hb a ha).1
  forsTl := encodeTargets_shake_nodup (forsRootAddresses_nodup vp)
    fun a ha => (sha2Domain_forsRootAddresses vp hb a ha).1
  wotsFUd select := encodeTargets_shake_nodup (selectedWotsAddresses_nodup vp select)
    fun a ha => (sha2Domain_selectedWotsAddresses vp hb select a ha).1
  wotsFTcr := encodeTargets_shake_nodup (wotsStepAddresses_nodup vp)
    fun a ha => (sha2Domain_wotsStepAddresses vp hb a ha).1
  wotsFPre select := encodeTargets_shake_nodup (optionalWotsAddresses_nodup vp select)
    fun a ha => (sha2Domain_optionalWotsAddresses vp hb select a ha).1
  wotsTl := encodeTargets_shake_nodup (wotsPkAddresses_nodup vp)
    fun a ha => (sha2Domain_wotsPkAddresses vp hb a ha).1
  xmssH := encodeTargets_shake_nodup (xmssNodeAddresses_nodup vp)
    fun a ha => (sha2Domain_xmssNodeAddresses vp hb a ha).1

/-- Every approved FIPS 205 instantiation satisfies the encoded-ledger conditions. -/
theorem approvedEncodedTargetLedgerConditions (ps : FipsParameterSet) :
    EncodedTargetLedgerConditions ps.validatedParams (approvedPrimitives ps) := by
  have hb : Params.ApprovedAddressBounds ps.validatedParams.params := fipsApprovedAddressBounds ps
  rw [approvedPrimitives]
  cases hfamily : ps.hashFamily with
  | sha2 => exact sha2EncodedTargetLedgerConditions ps.validatedParams hb
  | shake => exact shakeEncodedTargetLedgerConditions ps.validatedParams hb

end SLHDSA.Security
