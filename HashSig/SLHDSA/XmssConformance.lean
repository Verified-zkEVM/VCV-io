/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Bolton Bailey
-/

module
public import HashSig.SLHDSA.Xmss
public import Mathlib.Data.Nat.Bitwise

/-!
# Typed XMSS construction interface

This module gives FIPS 205 §6 typed indices and thin wrappers over the canonical natural-indexed
`PerfectMerkleTree` and XMSS algorithms. `XmssSig` itself carries the fixed-width authentication
path, so the wrappers refine positions without introducing a second signature representation.

## References

- NIST FIPS 205, §6 (Algorithms 9–11)
-/

@[expose] public section

namespace SLHDSA.XmssConformance

variable {Y : Type*}

/-- A valid node position in a perfect tree of height `treeHeight`: level `z` above the leaves and
horizontal index `t < 2^(treeHeight-z)`. -/
structure TreePosition (treeHeight : ℕ) where
  level : ℕ
  level_le : level ≤ treeHeight
  index : Fin (2 ^ (treeHeight - level))

/-- The horizontal index of a valid node position is also below the full leaf count. -/
theorem TreePosition.index_lt_leafCount {treeHeight : ℕ} (pos : TreePosition treeHeight) :
    pos.index.val < 2 ^ treeHeight := by
  exact lt_of_lt_of_le pos.index.isLt
    (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.sub_le treeHeight pos.level))

/-- Flip the low index bit using FIPS's `xor 1` notation. -/
theorem sibling_eq_xor_one (i : ℕ) : PerfectMerkleTree.sibling i = i ^^^ 1 := by
  unfold PerfectMerkleTree.sibling
  by_cases h : i % 2 = 0
  · rw [if_pos h]
    exact (Nat.xor_one_of_even (by simpa [Nat.even_iff] using h)).symm
  · rw [if_neg h]
    exact (Nat.xor_one_of_odd (by simpa [Nat.odd_iff] using h)).symm

/-- Authentication-path entry `j` is the root of the height-`j` sibling subtree. -/
theorem authPath_getElem_eq_merkleRoot (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z j : ℕ) (hj : j < z) :
    (PerfectMerkleTree.authPath leaf nodeHash idx z)[j]'(by simpa using hj) =
      PerfectMerkleTree.merkleRoot leaf nodeHash j
        (PerfectMerkleTree.sibling (idx / 2 ^ j)) := by
  induction z with
  | zero => omega
  | succ z ih =>
      by_cases h : j < z
      · have hpath : j < (PerfectMerkleTree.authPath leaf nodeHash idx z).length := by
          simpa using h
        simp only [PerfectMerkleTree.authPath_succ]
        rw [List.getElem_append_left hpath]
        exact ih h
      · have hjz : j = z := by omega
        subst j
        simp [PerfectMerkleTree.authPath_succ]

/-- The canonical authentication path packaged at its intrinsic tree height. -/
def authPathVector (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    {z : ℕ} (idx : Fin (2 ^ z)) : Vector Y z :=
  Vector.ofFn fun j => (PerfectMerkleTree.authPath leaf nodeHash idx.val z)[j.val]

/-- Forgetting the intrinsic width recovers the canonical Merkle authentication path exactly. -/
@[simp] theorem authPathVector_toList (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) {z : ℕ} (idx : Fin (2 ^ z)) :
    (authPathVector leaf nodeHash idx).toList =
      PerfectMerkleTree.authPath leaf nodeHash idx.val z := by
  apply List.ext_getElem
  · simp [authPathVector]
  · intro n h1 h2
    simp only [authPathVector, Vector.toList_ofFn, List.getElem_ofFn]

/-- Exact FIPS Algorithm 10 position of authentication-path entry `j`, using xor notation. -/
@[simp] theorem authPathVector_get (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    {z : ℕ} (idx : Fin (2 ^ z)) (j : Fin z) :
    (authPathVector leaf nodeHash idx)[j.val] =
      PerfectMerkleTree.merkleRoot leaf nodeHash j.val
        ((idx.val / 2 ^ j.val) ^^^ 1) := by
  simp only [authPathVector, Vector.getElem_ofFn]
  rw [authPath_getElem_eq_merkleRoot _ _ _ _ _ j.isLt]
  rw [sibling_eq_xor_one]

/-! ## Explicit FIPS climb characterization -/

/-- The honest FIPS climb written as the Algorithm 11 loop. At step `k`, the parity of
`idx / 2^k` selects the child order and the parent hash uses exact address
`(k+1, idx / 2^(k+1))`. This characterization connects the loop to canonical recovery. -/
def honestClimbFips (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx z : ℕ) : Y :=
  Nat.rec (leaf idx) (fun k node =>
      let siblingNode := PerfectMerkleTree.merkleRoot leaf nodeHash k
        (PerfectMerkleTree.sibling (idx / 2 ^ k))
      if idx / 2 ^ k % 2 = 0 then
        nodeHash (k + 1) (idx / 2 ^ (k + 1)) node siblingNode
      else
        nodeHash (k + 1) (idx / 2 ^ (k + 1)) siblingNode node) z

@[simp] theorem honestClimbFips_zero (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) :
    honestClimbFips leaf nodeHash idx 0 = leaf idx := rfl

theorem honestClimbFips_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx k : ℕ) :
    honestClimbFips leaf nodeHash idx (k + 1) =
      let node := honestClimbFips leaf nodeHash idx k
      let siblingNode := PerfectMerkleTree.merkleRoot leaf nodeHash k
        (PerfectMerkleTree.sibling (idx / 2 ^ k))
      if idx / 2 ^ k % 2 = 0 then
        nodeHash (k + 1) (idx / 2 ^ (k + 1)) node siblingNode
      else
        nodeHash (k + 1) (idx / 2 ^ (k + 1)) siblingNode node := rfl

/-- Induction over the explicit FIPS loop yields the canonical perfect-subtree root. -/
theorem honestClimbFips_eq_merkleRoot (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    honestClimbFips leaf nodeHash idx z =
      PerfectMerkleTree.merkleRoot leaf nodeHash z (idx / 2 ^ z) := by
  induction z with
  | zero => simp
  | succ z ih =>
      rw [honestClimbFips_succ, ih, PerfectMerkleTree.merkleRoot_succ]
      by_cases h : idx / 2 ^ z % 2 = 0
      · rw [if_pos h]
        have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
        have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
          rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
        have heven : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
        rw [heven]
        simp only [PerfectMerkleTree.sibling, if_pos h]
      · rw [if_neg h]
        have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
        have hmod : idx / 2 ^ z % 2 = 1 := by omega
        have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
          rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
        have hodd : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by
          rw [hdiv]
          omega
        have hleft : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z - 1 := by omega
        rw [hodd]
        simp only [PerfectMerkleTree.sibling, if_neg h]
        rw [hleft]

/-- The explicit FIPS loop is exactly the canonical `authPath`/`climb` semantics on an honest
opening. -/
theorem honestClimbFips_eq_climb_authPath (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    honestClimbFips leaf nodeHash idx z =
      PerfectMerkleTree.climb nodeHash idx (leaf idx)
        (PerfectMerkleTree.authPath leaf nodeHash idx z) := by
  rw [honestClimbFips_eq_merkleRoot, PerfectMerkleTree.climb_authPath]

variable {p : Params}

/-! ## XMSS address grammar -/

@[simp] theorem wotsLeafAdrs_layer (adrs : Adrs) (t : ℕ) :
    (wotsLeafAdrs adrs t).layer = adrs.layer := rfl

@[simp] theorem wotsLeafAdrs_tree (adrs : Adrs) (t : ℕ) :
    (wotsLeafAdrs adrs t).tree = adrs.tree := rfl

@[simp] theorem wotsLeafAdrs_type (adrs : Adrs) (t : ℕ) :
    (wotsLeafAdrs adrs t).type = AddrType.wotsHash.toCode := rfl

@[simp] theorem wotsLeafAdrs_word1 (adrs : Adrs) (t : ℕ) :
    (wotsLeafAdrs adrs t).word1 = t := rfl

@[simp] theorem wotsLeafAdrs_word2 (adrs : Adrs) (t : ℕ) :
    (wotsLeafAdrs adrs t).word2 = 0 := rfl

@[simp] theorem wotsLeafAdrs_word3 (adrs : Adrs) (t : ℕ) :
    (wotsLeafAdrs adrs t).word3 = 0 := rfl

/-- WOTS leaf construction preserves the outer address and clears every other type-dependent
field before setting the key-pair index. -/
theorem wotsLeafAdrs_isCanonical (adrs : Adrs) (t : ℕ)
    (hbase : adrs.isCanonical = true) (ht : Adrs.Fits 4 t = true) :
    (wotsLeafAdrs adrs t).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, _hword1, _hword2, _hword3⟩
  simp [wotsLeafAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.isCanonical, hlayer, htree, ht]
  norm_num [Adrs.Fits, AddrType.toCode]

@[simp] theorem xmssNodeAdrs_layer (adrs : Adrs) (z t : ℕ) :
    (xmssNodeAdrs adrs z t).layer = adrs.layer := rfl

@[simp] theorem xmssNodeAdrs_tree (adrs : Adrs) (z t : ℕ) :
    (xmssNodeAdrs adrs z t).tree = adrs.tree := rfl

@[simp] theorem xmssNodeAdrs_type (adrs : Adrs) (z t : ℕ) :
    (xmssNodeAdrs adrs z t).type = AddrType.tree.toCode := rfl

@[simp] theorem xmssNodeAdrs_word1 (adrs : Adrs) (z t : ℕ) :
    (xmssNodeAdrs adrs z t).word1 = 0 := rfl

@[simp] theorem xmssNodeAdrs_word2 (adrs : Adrs) (z t : ℕ) :
    (xmssNodeAdrs adrs z t).word2 = z := rfl

@[simp] theorem xmssNodeAdrs_word3 (adrs : Adrs) (z t : ℕ) :
    (xmssNodeAdrs adrs z t).word3 = t := rfl

/-- XMSS node construction preserves the outer address, sets type `TREE`, clears word one, and
stores the exact node height/index in words two/three. -/
theorem xmssNodeAdrs_isCanonical (adrs : Adrs) (z t : ℕ)
    (hbase : adrs.isCanonical = true) (hz : Adrs.Fits 4 z = true)
    (ht : Adrs.Fits 4 t = true) :
    (xmssNodeAdrs adrs z t).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, _hword1, _hword2, _hword3⟩
  simp [xmssNodeAdrs, Adrs.setTypeAndClear, Adrs.setTreeHeight,
    Adrs.setTreeIndex, Adrs.isCanonical, hlayer, htree, hz, ht]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- Full SHAKE-style 32-byte serialization round-trips a canonical reachable WOTS leaf address. -/
theorem wotsLeafAdrs_fromVector_toVector (adrs : Adrs) (t : ℕ)
    (hbase : adrs.isCanonical = true) (ht : Adrs.Fits 4 t = true) :
    Adrs.fromVector (wotsLeafAdrs adrs t).toVector = wotsLeafAdrs adrs t :=
  Adrs.fromVector_toVector_of_isCanonical _ (wotsLeafAdrs_isCanonical adrs t hbase ht)

/-- Full SHAKE-style 32-byte serialization round-trips a canonical reachable XMSS node address. -/
theorem xmssNodeAdrs_fromVector_toVector (adrs : Adrs) (z t : ℕ)
    (hbase : adrs.isCanonical = true) (hz : Adrs.Fits 4 z = true)
    (ht : Adrs.Fits 4 t = true) :
    Adrs.fromVector (xmssNodeAdrs adrs z t).toVector = xmssNodeAdrs adrs z t :=
  Adrs.fromVector_toVector_of_isCanonical _ (xmssNodeAdrs_isCanonical adrs z t hbase hz ht)

/-- A leaf index bounded by the leaf count of one XMSS tree. -/
abbrev LeafIndex (p : Params) := Fin (2 ^ p.hp)

/-- A valid node position in one XMSS tree. -/
abbrev NodePosition (p : Params) := TreePosition p.hp

/-- Typed access to the canonical FIPS authentication path. -/
def xmssAuthPath (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : LeafIndex p) : Vector prims.Y p.hp :=
  authPathVector (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) idx

/-- Erasing the typed authentication path recovers the exact canonical path. -/
@[simp] theorem xmssAuthPath_toList (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : LeafIndex p) :
    (xmssAuthPath prims sk pk adrs idx).toList =
      PerfectMerkleTree.authPath (xmssLeaf prims sk pk adrs)
        (xmssNodeHash prims pk adrs) idx.val p.hp := by
  simp [xmssAuthPath]

/-- Thin typed wrapper over Algorithm 9 at a valid XMSS node position. -/
def xmssNodeAt (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (pos : NodePosition p) : prims.Y :=
  xmssNode prims sk pk adrs pos.level pos.index.val

@[simp] theorem xmssNodeAt_eq (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (pos : NodePosition p) :
    xmssNodeAt prims sk pk adrs pos =
      xmssNode prims sk pk adrs pos.level pos.index.val := rfl

/-- Thin typed signing wrapper over Algorithm 10. -/
def xmssSignBounded (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : LeafIndex p) : XmssSig p prims :=
  xmssSign prims msg sk pk adrs idx.val

/-- Typed signing is definitionally the canonical Algorithm 10 result. -/
@[simp] theorem xmssSignBounded_eq (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx : LeafIndex p) :
    xmssSignBounded prims msg sk pk adrs idx =
      xmssSign prims msg sk pk adrs idx.val := rfl

/-- Thin typed recovery wrapper over Algorithm 11. -/
def xmssPkFromSigBounded (prims : Primitives p) (idx : LeafIndex p)
    (sig : XmssSig p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  xmssPkFromSig prims idx.val sig msg pk adrs

/-- Typed honest signing and recovery retains the canonical XMSS correctness theorem. -/
theorem xmssPkFromSigBounded_xmssSignBounded (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx : LeafIndex p) :
    xmssPkFromSigBounded prims idx (xmssSignBounded prims msg sk pk adrs idx) msg pk adrs =
      xmssRoot prims sk pk adrs := by
  simp only [xmssPkFromSigBounded, xmssSignBounded_eq]
  exact xmssPkFromSig_xmssSign prims msg sk pk adrs idx.val idx.isLt

/-- The canonical signature's intrinsic authentication-path width supplies the exact path shape
needed by the XMSS binding theorem. The typed wrapper additionally bounds the leaf position. -/
theorem xmssPkFromSigBounded_binding (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx : LeafIndex p)
    (sig : XmssSig p prims)
    (hroot : xmssPkFromSigBounded prims idx sig msg pk adrs = xmssRoot prims sk pk adrs)
    (hne : xmssLeaf prims sk pk adrs idx.val
      ≠ wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx.val)) :
    ∃ (h : ℕ) (c : prims.Y × prims.Y), 0 < h ∧ h ≤ p.hp ∧
      (xmssNode prims sk pk adrs (h - 1) (2 * (idx.val / 2 ^ h)),
          xmssNode prims sk pk adrs (h - 1) (2 * (idx.val / 2 ^ h) + 1))
        ≠ c ∧
      prims.H pk (xmssNodeAdrs adrs h (idx.val / 2 ^ h))
          (xmssNode prims sk pk adrs (h - 1) (2 * (idx.val / 2 ^ h)))
          (xmssNode prims sk pk adrs (h - 1) (2 * (idx.val / 2 ^ h) + 1))
        = prims.H pk (xmssNodeAdrs adrs h (idx.val / 2 ^ h)) c.1 c.2 := by
  exact xmssPkFromSig_binding prims msg sk pk adrs idx.val idx.isLt sig hroot hne

/-- The typed XMSS authentication path carries the exact FIPS sibling-subtree position. -/
@[simp] theorem xmssAuthPath_get (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : LeafIndex p) (j : Fin p.hp) :
    (xmssAuthPath prims sk pk adrs idx)[j.val] =
      xmssNode prims sk pk adrs j.val ((idx.val / 2 ^ j.val) ^^^ 1) := by
  rw [xmssAuthPath, authPathVector_get, xmssNode_eq_merkleRoot]

end SLHDSA.XmssConformance
