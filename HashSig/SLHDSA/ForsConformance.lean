/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module

public import HashSig.SLHDSA.Fors
public import HashSig.SLHDSA.Position
public import HashSig.SLHDSA.XmssConformance

/-!
# Typed FORS conformance interface

This module exposes the FIPS 205 Algorithm 16 message-index decoder and global tree coordinates
as bounded values, without introducing another FORS signing or recovery implementation.  It also
records the exact FORS address grammar consumed by the concrete SHA2 and SHAKE boundaries.

`round3ForsIdxLSB` is deliberately isolated as a historical incompatibility canary.  It models the
least-significant-bit-first extraction used by round-3 SPHINCS+ and is not used by the FIPS
construction.

## References

- NIST FIPS 205, §8 (Algorithms 14–17)
- NIST FIPS 205, Algorithm 4 (`base_2b`, most-significant bits first)
- NIST FIPS 205, Appendix A (FORS index extraction clarification)
-/

@[expose] public section

namespace SLHDSA.ForsConformance

/-- The exact byte extent passed from `DigestParts.md` to FIPS FORS. -/
abbrev ForsDigest (p : Params) := Bytes p.digestBytes

/-- An index of one of the `k` FORS trees. -/
abbrev TreeIndex (p : Params) := Fin p.k

/-- A leaf index within one height-`a` FORS tree. -/
abbrev LeafIndex (p : Params) := Fin p.t

/-- A bounded node coordinate in one of the `k` FORS trees.  Height zero denotes a leaf and
height `a` denotes that tree's root. -/
structure NodePosition (p : Params) where
  tree : TreeIndex p
  height : Fin (p.a + 1)
  index : Fin (2 ^ (p.a - height.val))

/-- Global node coordinate stored in the FORS tree-address word at a typed position. -/
def NodePosition.globalIndex {p : Params} (pos : NodePosition p) : Fin (p.k * p.t) :=
  ⟨pos.tree.val * 2 ^ (p.a - pos.height.val) + pos.index.val, by
    have hheight : pos.height.val ≤ p.a := by omega
    have hscale : 0 < 2 ^ (p.a - pos.height.val) := by positivity
    have hlocal :
        pos.tree.val * 2 ^ (p.a - pos.height.val) + pos.index.val <
          p.k * 2 ^ (p.a - pos.height.val) := by
      nlinarith [pos.tree.isLt, pos.index.isLt]
    have hpow : 2 ^ (p.a - pos.height.val) ≤ 2 ^ p.a :=
      Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.sub_le p.a pos.height.val)
    exact lt_of_lt_of_le hlocal (by
      simpa [Params.t] using Nat.mul_le_mul_left p.k hpow)⟩

@[simp] theorem NodePosition.globalIndex_val {p : Params} (pos : NodePosition p) :
    pos.globalIndex.val =
      pos.tree.val * 2 ^ (p.a - pos.height.val) + pos.index.val := rfl

/-- Algorithm 16's `k` most-significant-bit-first indices, with both dimensions intrinsic. -/
def decodeIndices (p : Params) (md : ForsDigest p) : Vector (LeafIndex p) p.k :=
  Vector.ofFn fun i => ⟨forsIdx p md.toList i.val, by
    simpa [Params.t] using forsIdx_lt p md.toList i.val⟩

@[simp] theorem decodeIndices_get_val (p : Params) (md : ForsDigest p)
    (i : TreeIndex p) :
    (decodeIndices p md)[i.val].val = forsIdx p md.toList i.val := by
  simp [decodeIndices]

/-- The typed decoder satisfies the Algorithm 4 MSB-first arithmetic characterization: index
`i` is the `i`-th `a`-bit digit from the top of the big-endian digest value. The digest always
carries enough bits because `digestBytes = ⌈k·a/8⌉`. -/
theorem decodeIndices_get_bigEndian (p : Params) (md : ForsDigest p)
    (i : TreeIndex p) :
    (decodeIndices p md)[i.val].val =
      toInt md.toList /
        2 ^ (8 * p.digestBytes - p.a * (i.val + 1)) % 2 ^ p.a := by
  have hmd : md.toList.length = p.digestBytes := by simp
  have hlen : p.k * p.a ≤ 8 * md.toList.length := by
    rw [hmd]
    have hdb : p.digestBytes = (p.k * p.a + 7) / 8 := rfl
    omega
  rw [decodeIndices_get_val]
  unfold forsIdx
  rw [base2b_bigEndian md.toList p.a p.k hlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
  simp [hmd]

/-- Global leaf coordinate used by Algorithms 15–17: tree offset plus the local leaf. -/
def globalLeafIndex (p : Params) (tree : TreeIndex p) (leaf : LeafIndex p) :
    Fin (p.k * p.t) :=
  ⟨tree.val * p.t + leaf.val, by
    have ht : 0 < p.t := by simp [Params.t]
    nlinarith [tree.isLt, leaf.isLt]⟩

@[simp] theorem globalLeafIndex_val (p : Params) (tree : TreeIndex p)
    (leaf : LeafIndex p) :
    (globalLeafIndex p tree leaf).val = tree.val * 2 ^ p.a + leaf.val := by
  simp [globalLeafIndex, Params.t]

/-- The exact global coordinate used by canonical signing and recovery is the decoded coordinate. -/
@[simp] theorem globalLeafIndex_decode_val (p : Params) (md : ForsDigest p)
    (tree : TreeIndex p) :
    (globalLeafIndex p tree (decodeIndices p md)[tree.val]).val =
      tree.val * 2 ^ p.a + forsIdx p md.toList tree.val := by
  simp

/-- Consume the authoritative digest decomposition directly; no resizing or defaulting occurs. -/
def decodeDigestParts {p : Params} (parts : DigestParts p) :
    Vector (LeafIndex p) p.k :=
  decodeIndices p parts.md

@[simp] theorem decodeDigestParts_get_val {p : Params} (parts : DigestParts p)
    (tree : TreeIndex p) :
    (decodeDigestParts parts)[tree.val].val = forsIdx p parts.md.toList tree.val := by
  simp [decodeDigestParts]

/-- Algorithm 16's authentication entry is the exact sibling subtree of the digest-selected
global leaf.  The statement specializes the canonical intrinsic path; no alternate path engine is
introduced. -/
@[simp] theorem intrinsicAuthPath_decode_get {Y : Type} (p : Params)
    (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (md : ForsDigest p) (tree : TreeIndex p) (j : Fin p.a) :
    (PerfectMerkleTree.intrinsicAuthPath leaf nodeHash
      (globalLeafIndex p tree (decodeIndices p md)[tree.val]).val p.a)[j.val] =
      PerfectMerkleTree.merkleRoot leaf nodeHash j.val
        (PerfectMerkleTree.sibling
          ((globalLeafIndex p tree (decodeIndices p md)[tree.val]).val / 2 ^ j.val)) := by
  let idx := (globalLeafIndex p tree (decodeIndices p md)[tree.val]).val
  change (PerfectMerkleTree.intrinsicAuthPath leaf nodeHash idx p.a)[j.val] =
    PerfectMerkleTree.merkleRoot leaf nodeHash j.val
      (PerfectMerkleTree.sibling (idx / 2 ^ j.val))
  have hlist := PerfectMerkleTree.intrinsicAuthPath_toList leaf nodeHash idx p.a
  have hget := congrArg (fun xs => xs.getD j.val (leaf 0)) hlist
  have hv :
      j.val < (PerfectMerkleTree.intrinsicAuthPath leaf nodeHash idx p.a).toList.length := by
    simp
  have hp : j.val < (PerfectMerkleTree.authPath leaf nodeHash idx p.a).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv] at hget
  simp only [Option.getD_some] at hget
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp] at hget
  simp only [Option.getD_some] at hget
  rw [Vector.getElem_toList hv] at hget
  exact hget.trans
    (XmssConformance.authPath_getElem_eq_merkleRoot _ _ _ _ _ j.isLt)

/-- Honest signing consumes the typed decoder's exact global coordinate; the signature remains the
canonical intrinsic `ForsTreeSigCore` with no adapter or competing representation. -/
@[simp] theorem forsSign_get_eq_decoded {p : Params} (prims : Primitives p)
    (md : ForsDigest p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (tree : TreeIndex p) :
    (forsSign prims md.toList sk pk adrs)[tree.val] =
      ⟨forsSkGenCore prims.core sk pk adrs
          (globalLeafIndex p tree (decodeIndices p md)[tree.val]).val,
        PerfectMerkleTree.intrinsicAuthPath (forsLeaf prims sk pk adrs)
          (forsNodeHash prims pk adrs)
          (globalLeafIndex p tree (decodeIndices p md)[tree.val]).val p.a⟩ := by
  rw [forsSign_eq_ofFn]
  simp

/-- One historical round-3 LSB-first bit, counted from the first byte's least-significant bit. -/
def round3BitLSB (md : List Byte) (offset : ℕ) : ℕ :=
  ((md.getD (offset / 8) 0).toNat / 2 ^ (offset % 8)) % 2

/-- Historical round-3 LSB-first FORS extraction, retained only for a discriminating canary. -/
def round3ForsIdxLSB (p : Params) (md : List Byte) (i : ℕ) : ℕ :=
  (List.range p.a).foldl
    (fun acc j => acc + round3BitLSB md (i * p.a + j) * 2 ^ j) 0

/-! ## Canonical FORS address grammar -/

@[simp] theorem forsSkAdrs_layer (adrs : Adrs) (t : ℕ) :
    (forsSkAdrs adrs t).layer = adrs.layer := rfl

@[simp] theorem forsSkAdrs_tree (adrs : Adrs) (t : ℕ) :
    (forsSkAdrs adrs t).tree = adrs.tree := rfl

@[simp] theorem forsSkAdrs_type (adrs : Adrs) (t : ℕ) :
    (forsSkAdrs adrs t).type = AddrType.forsPrf.toCode := rfl

@[simp] theorem forsSkAdrs_word1 (adrs : Adrs) (t : ℕ) :
    (forsSkAdrs adrs t).word1 = adrs.getKeyPairAddress := rfl

@[simp] theorem forsSkAdrs_word2 (adrs : Adrs) (t : ℕ) :
    (forsSkAdrs adrs t).word2 = 0 := rfl

@[simp] theorem forsSkAdrs_word3 (adrs : Adrs) (t : ℕ) :
    (forsSkAdrs adrs t).word3 = t := rfl

@[simp] theorem forsNodeAdrs_layer (adrs : Adrs) (z t : ℕ) :
    (forsNodeAdrs adrs z t).layer = adrs.layer := rfl

@[simp] theorem forsNodeAdrs_tree (adrs : Adrs) (z t : ℕ) :
    (forsNodeAdrs adrs z t).tree = adrs.tree := rfl

@[simp] theorem forsNodeAdrs_type (adrs : Adrs) (z t : ℕ) :
    (forsNodeAdrs adrs z t).type = AddrType.forsTree.toCode := rfl

@[simp] theorem forsNodeAdrs_word1 (adrs : Adrs) (z t : ℕ) :
    (forsNodeAdrs adrs z t).word1 = adrs.getKeyPairAddress := rfl

@[simp] theorem forsNodeAdrs_word2 (adrs : Adrs) (z t : ℕ) :
    (forsNodeAdrs adrs z t).word2 = z := rfl

@[simp] theorem forsNodeAdrs_word3 (adrs : Adrs) (z t : ℕ) :
    (forsNodeAdrs adrs z t).word3 = t := rfl

@[simp] theorem forsPkAdrs_layer (adrs : Adrs) :
    (forsPkAdrs adrs).layer = adrs.layer := rfl

@[simp] theorem forsPkAdrs_tree (adrs : Adrs) :
    (forsPkAdrs adrs).tree = adrs.tree := rfl

@[simp] theorem forsPkAdrs_type (adrs : Adrs) :
    (forsPkAdrs adrs).type = AddrType.forsRoots.toCode := rfl

@[simp] theorem forsPkAdrs_word1 (adrs : Adrs) :
    (forsPkAdrs adrs).word1 = adrs.getKeyPairAddress := rfl

@[simp] theorem forsPkAdrs_word2 (adrs : Adrs) : (forsPkAdrs adrs).word2 = 0 := rfl

@[simp] theorem forsPkAdrs_word3 (adrs : Adrs) : (forsPkAdrs adrs).word3 = 0 := rfl

/-- FORS secret derivation preserves the outer address, type and key-pair coordinate and stores
the exact global leaf in the final word. -/
theorem forsSkAdrs_isCanonical (adrs : Adrs) (t : ℕ)
    (hbase : adrs.isCanonical = true) (ht : Adrs.Fits 4 t = true) :
    (forsSkAdrs adrs t).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, hword1, _hword2, _hword3⟩
  simp [forsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.setTreeIndex, Adrs.getKeyPairAddress, Adrs.isCanonical,
    hlayer, htree, hword1, ht]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- FORS node construction stores exact height/global node index and clears no live coordinate. -/
theorem forsNodeAdrs_isCanonical (adrs : Adrs) (z t : ℕ)
    (hbase : adrs.isCanonical = true) (hz : Adrs.Fits 4 z = true)
    (ht : Adrs.Fits 4 t = true) :
    (forsNodeAdrs adrs z t).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, hword1, _hword2, _hword3⟩
  simp [forsNodeAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.getKeyPairAddress,
    Adrs.isCanonical, hlayer, htree, hword1, hz, ht]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- FORS root compression preserves the outer/key-pair coordinate and clears words two/three. -/
theorem forsPkAdrs_isCanonical (adrs : Adrs) (hbase : adrs.isCanonical = true) :
    (forsPkAdrs adrs).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, hword1, _hword2, _hword3⟩
  simp [forsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.getKeyPairAddress, Adrs.isCanonical, hlayer, htree, hword1]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- SHAKE's full 32-byte address encoding is exact for a canonical reachable secret address. -/
theorem forsSkAdrs_fromVector_toVector (adrs : Adrs) (t : ℕ)
    (hbase : adrs.isCanonical = true) (ht : Adrs.Fits 4 t = true) :
    Adrs.fromVector (forsSkAdrs adrs t).toVector = forsSkAdrs adrs t :=
  Adrs.fromVector_toVector_of_isCanonical _ (forsSkAdrs_isCanonical adrs t hbase ht)

/-- SHAKE's full 32-byte address encoding is exact for a canonical reachable tree node. -/
theorem forsNodeAdrs_fromVector_toVector (adrs : Adrs) (z t : ℕ)
    (hbase : adrs.isCanonical = true) (hz : Adrs.Fits 4 z = true)
    (ht : Adrs.Fits 4 t = true) :
    Adrs.fromVector (forsNodeAdrs adrs z t).toVector = forsNodeAdrs adrs z t :=
  Adrs.fromVector_toVector_of_isCanonical _
    (forsNodeAdrs_isCanonical adrs z t hbase hz ht)

/-- SHAKE's full 32-byte address encoding is exact for canonical FORS root compression. -/
theorem forsPkAdrs_fromVector_toVector (adrs : Adrs) (hbase : adrs.isCanonical = true) :
    Adrs.fromVector (forsPkAdrs adrs).toVector = forsPkAdrs adrs :=
  Adrs.fromVector_toVector_of_isCanonical _ (forsPkAdrs_isCanonical adrs hbase)

end SLHDSA.ForsConformance
