/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Address
public import HashSig.SLHDSA.Encoding

/-!
# SLH-DSA digest and hypertree positions

This module owns the positional data shared by FIPS 205 message-digest parsing, FORS, and the
hypertree. `DigestParts` preserves all three outputs of the `H_msg` split. `LayerPosition` records
the exact layer, reachable tree, and leaf bounds for validated parameters and implements the
low-bits/high-bits transition between hypertree layers.

## References

- NIST FIPS 205, Section 4.1 and Algorithms 19–20 (message-digest decomposition)
- NIST FIPS 205, Algorithms 12–13 (hypertree layer recurrence)
-/

@[expose] public section

namespace SLHDSA

/-! ## Exact message-digest decomposition -/

/-- The FORS-message byte slice at the start of an `H_msg` digest. -/
def digestMdBytes (p : Params) (digest : Bytes p.m) : Bytes p.digestBytes :=
  (digest.extract 0 p.digestBytes).cast (by
    simp [Params.m]
    omega)

/-- The byte slice encoding the lowest-layer tree index. -/
def digestTreeBytes (p : Params) (digest : Bytes p.m) : Bytes p.treeIdxBytes :=
  (digest.extract p.digestBytes (p.digestBytes + p.treeIdxBytes)).cast (by
    simp [Params.m])

/-- The final byte slice encoding the lowest-layer leaf index. -/
def digestLeafBytes (p : Params) (digest : Bytes p.m) : Bytes p.leafIdxBytes :=
  (digest.extract (p.digestBytes + p.treeIdxBytes)
    (p.digestBytes + p.treeIdxBytes + p.leafIdxBytes)).cast (by
      simp [Params.m])

/-- The three outputs parsed from an SLH-DSA `H_msg` digest.

The two indices are reduced to their FIPS-prescribed bit widths. Their bounds are intrinsic, so
later algorithms cannot accidentally use high padding bits from the byte-aligned digest. -/
structure DigestParts (p : Params) where
  /-- The message passed to FORS. -/
  md : Bytes p.digestBytes
  /-- The tree at hypertree layer zero. -/
  idxTree : Fin (2 ^ (p.h - p.hp))
  /-- The leaf within that tree. -/
  idxLeaf : Fin (2 ^ p.hp)
deriving Repr, DecidableEq

/-- Split an `H_msg` digest into `md`, `idxTree`, and `idxLeaf` as prescribed by FIPS 205. -/
def splitDigest (p : Params) (digest : Bytes p.m) : DigestParts p where
  md := digestMdBytes p digest
  idxTree := ⟨toInt (digestTreeBytes p digest).toList % 2 ^ (p.h - p.hp),
    Nat.mod_lt _ (by positivity)⟩
  idxLeaf := ⟨toInt (digestLeafBytes p digest).toList % 2 ^ p.hp,
    Nat.mod_lt _ (by positivity)⟩

@[simp]
theorem digestMdBytes_toList (p : Params) (digest : Bytes p.m) :
    (digestMdBytes p digest).toList = digest.toList.take p.digestBytes := by
  simp [digestMdBytes, Vector.toList_cast, Vector.toList_extract]

@[simp]
theorem digestTreeBytes_toList (p : Params) (digest : Bytes p.m) :
    (digestTreeBytes p digest).toList =
      (digest.toList.drop p.digestBytes).take p.treeIdxBytes := by
  simp [digestTreeBytes, Vector.toList_cast, Vector.toList_extract]

@[simp]
theorem digestLeafBytes_toList (p : Params) (digest : Bytes p.m) :
    (digestLeafBytes p digest).toList =
      (digest.toList.drop (p.digestBytes + p.treeIdxBytes)).take p.leafIdxBytes := by
  simp [digestLeafBytes, Vector.toList_cast, Vector.toList_extract]

@[simp]
theorem splitDigest_md_toList (p : Params) (digest : Bytes p.m) :
    (splitDigest p digest).md.toList = digest.toList.take p.digestBytes := by
  simp [splitDigest]

@[simp]
theorem splitDigest_idxTree_val (p : Params) (digest : Bytes p.m) :
    (splitDigest p digest).idxTree.val =
      toInt ((digest.toList.drop p.digestBytes).take p.treeIdxBytes) % 2 ^ (p.h - p.hp) := by
  simp [splitDigest]

@[simp]
theorem splitDigest_idxLeaf_val (p : Params) (digest : Bytes p.m) :
    (splitDigest p digest).idxLeaf.val =
      toInt ((digest.toList.drop (p.digestBytes + p.treeIdxBytes)).take p.leafIdxBytes) %
        2 ^ p.hp := by
  simp [splitDigest]

/-- For a valid one-layer parameter set, the digest's tree index is the unique element of
`Fin 1`. -/
theorem DigestParts.idxTree_eq_zero_of_d_eq_one {p : Params} (hp : p.Valid) (hd : p.d = 1)
    (parts : DigestParts p) : parts.idxTree.val = 0 := by
  have hh : p.h = p.hp := by
    rw [hp.h_eq_layers, hd]
    simp
  have hexp : p.h - p.hp = 0 := by omega
  have hbound : 2 ^ (p.h - p.hp) = 1 := by simp [hexp]
  have hlt : parts.idxTree.val < 1 := lt_of_lt_of_eq parts.idxTree.isLt hbound
  omega

/-! ## Layer-indexed hypertree positions -/

/-- Remaining tree-index bits at a hypertree layer.

The normalized form `(d - (layer + 1)) * h'` avoids repeated transports through
`h = d * h'` while retaining the exact FIPS reachability bound. -/
def layerTreeHeight (p : ValidatedParams) (layer : ℕ) : ℕ :=
  (p.params.d - (layer + 1)) * p.params.hp

/-- A reachable tree and leaf at one layer of a validated SLH-DSA hypertree. -/
structure LayerPosition (p : ValidatedParams) where
  /-- Layer number, starting at zero. -/
  layer : Fin p.params.d
  /-- Tree index reachable at this layer. -/
  tree : Fin (2 ^ layerTreeHeight p layer.val)
  /-- Leaf index within the layer's XMSS tree. -/
  leaf : Fin (2 ^ p.params.hp)
deriving Repr, DecidableEq

namespace LayerPosition

/-- The layer-zero position parsed from an `H_msg` digest. -/
def initial (p : ValidatedParams) (parts : DigestParts p.params) : LayerPosition p where
  layer := ⟨0, p.valid.d_pos⟩
  tree := ⟨parts.idxTree.val, by
    simpa [layerTreeHeight, p.valid.h_eq_layers, Nat.sub_mul] using parts.idxTree.isLt⟩
  leaf := parts.idxLeaf

/-- Advance one hypertree layer: low `h'` bits select the next leaf and the remaining high bits
select the next tree. -/
def next {p : ValidatedParams} (pos : LayerPosition p)
    (hnext : pos.layer.val + 1 < p.params.d) : LayerPosition p where
  layer := ⟨pos.layer.val + 1, hnext⟩
  tree := ⟨pos.tree.val / 2 ^ p.params.hp, by
    have hlevels :
        p.params.d - (pos.layer.val + 1) =
          p.params.d - (pos.layer.val + 2) + 1 := by
      omega
    have hexp :
        layerTreeHeight p pos.layer.val =
          p.params.hp + layerTreeHeight p (pos.layer.val + 1) := by
      unfold layerTreeHeight
      rw [hlevels, Nat.add_mul]
      simp only [one_mul, Nat.add_comm]
      congr 2
      omega
    apply Nat.div_lt_of_lt_mul
    calc
      pos.tree.val < 2 ^ layerTreeHeight p pos.layer.val := pos.tree.isLt
      _ = 2 ^ p.params.hp * 2 ^ layerTreeHeight p (pos.layer.val + 1) := by
        rw [hexp, pow_add]⟩
  leaf := ⟨pos.tree.val % 2 ^ p.params.hp, Nat.mod_lt _ (by positivity)⟩

/-- Build the position at a natural-number layer together with the fact that the resulting
position has exactly that layer. This internal dependent result makes every trajectory step use
`next`, so `atLayer` cannot drift from the FIPS layer recurrence. -/
def atWithLayer (p : ValidatedParams) (parts : DigestParts p.params) :
    (j : ℕ) → j < p.params.d → { pos : LayerPosition p // pos.layer.val = j }
  | 0, _ => ⟨initial p parts, rfl⟩
  | j + 1, hj =>
      let previous := atWithLayer p parts j (by omega)
      let current := previous.val.next (by simpa [previous.property] using hj)
      ⟨current, by
        change previous.val.layer.val + 1 = j + 1
        rw [previous.property]⟩

/-- The hypertree position at an arbitrary valid layer.

The construction follows the same low-bits/high-bits recurrence as repeated calls to `next`, but
accepts a `Fin d` layer directly, giving a total random-access view of the trajectory that the
layer-by-layer algorithms walk with `initial` and `next`. -/
def atLayer (p : ValidatedParams) (parts : DigestParts p.params)
    (j : Fin p.params.d) : LayerPosition p :=
  (atWithLayer p parts j.val j.isLt).val

@[simp]
theorem atLayer_layer_val (p : ValidatedParams) (parts : DigestParts p.params)
    (j : Fin p.params.d) : (atLayer p parts j).layer.val = j.val :=
  (atWithLayer p parts j.val j.isLt).property

/-- The total trajectory starts at the digest-derived layer-zero position. -/
@[simp]
theorem atLayer_zero_eq_initial (p : ValidatedParams) (parts : DigestParts p.params) :
    atLayer p parts ⟨0, p.valid.d_pos⟩ = initial p parts := by
  rfl

/-- Advancing the total trajectory by one layer agrees with the primitive `next` transition. -/
theorem atLayer_succ_eq_next (p : ValidatedParams) (parts : DigestParts p.params)
    (j : Fin p.params.d) (hnext : j.val + 1 < p.params.d) :
    atLayer p parts ⟨j.val + 1, hnext⟩ =
      (atLayer p parts j).next (by simpa using hnext) := by
  simp [atLayer, atWithLayer]

@[simp]
theorem initial_layer_val (p : ValidatedParams) (parts : DigestParts p.params) :
    (initial p parts).layer.val = 0 := rfl

@[simp]
theorem initial_tree_val (p : ValidatedParams) (parts : DigestParts p.params) :
    (initial p parts).tree.val = parts.idxTree.val := rfl

@[simp]
theorem initial_leaf_val (p : ValidatedParams) (parts : DigestParts p.params) :
    (initial p parts).leaf.val = parts.idxLeaf.val := rfl

@[simp]
theorem next_layer_val {p : ValidatedParams} (pos : LayerPosition p)
    (hnext : pos.layer.val + 1 < p.params.d) :
    (pos.next hnext).layer.val = pos.layer.val + 1 := rfl

@[simp]
theorem next_tree_val {p : ValidatedParams} (pos : LayerPosition p)
    (hnext : pos.layer.val + 1 < p.params.d) :
    (pos.next hnext).tree.val = pos.tree.val / 2 ^ p.params.hp := rfl

@[simp]
theorem next_leaf_val {p : ValidatedParams} (pos : LayerPosition p)
    (hnext : pos.layer.val + 1 < p.params.d) :
    (pos.next hnext).leaf.val = pos.tree.val % 2 ^ p.params.hp := rfl

/-- The reachable tree index at the final layer is zero. -/
theorem tree_eq_zero_of_isFinal {p : ValidatedParams} (pos : LayerPosition p)
    (hfinal : pos.layer.val + 1 = p.params.d) : pos.tree.val = 0 := by
  have hrem : p.params.d - (pos.layer.val + 1) = 0 := by omega
  have hheight : layerTreeHeight p pos.layer.val = 0 := by
    simp [layerTreeHeight, hrem]
  have hbound : 2 ^ layerTreeHeight p pos.layer.val = 1 := by simp [hheight]
  have hlt : pos.tree.val < 1 := lt_of_lt_of_eq pos.tree.isLt hbound
  omega

/-- The layer and tree fields of the base hash address for this position. Type-dependent words
remain zero until the component algorithm selects its address type. -/
def toAdrs {p : ValidatedParams} (pos : LayerPosition p) : Adrs :=
  (Adrs.zero.setLayerAddress pos.layer.val).setTreeAddress pos.tree.val

@[simp]
theorem toAdrs_layer {p : ValidatedParams} (pos : LayerPosition p) :
    pos.toAdrs.layer = pos.layer.val := rfl

@[simp]
theorem toAdrs_tree {p : ValidatedParams} (pos : LayerPosition p) :
    pos.toAdrs.tree = pos.tree.val := rfl

end LayerPosition

namespace DigestParts

/-- The FIPS Algorithm 19 FORS address, carrying both digest-derived indices. -/
def forsAdrs {p : Params} (parts : DigestParts p) : Adrs :=
  ((Adrs.zero.setTreeAddress parts.idxTree.val).setTypeAndClear .forsTree).setKeyPairAddress
    parts.idxLeaf.val

@[simp]
theorem forsAdrs_layer {p : Params} (parts : DigestParts p) : parts.forsAdrs.layer = 0 := rfl

@[simp]
theorem forsAdrs_tree {p : Params} (parts : DigestParts p) :
    parts.forsAdrs.tree = parts.idxTree.val := rfl

@[simp]
theorem forsAdrs_type {p : Params} (parts : DigestParts p) :
    parts.forsAdrs.type = AddrType.forsTree.toCode := rfl

@[simp]
theorem forsAdrs_keyPair {p : Params} (parts : DigestParts p) :
    parts.forsAdrs.getKeyPairAddress = parts.idxLeaf.val := rfl

end DigestParts

end SLHDSA
