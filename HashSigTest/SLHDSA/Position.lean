/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Position

/-!
# SLH-DSA digest and position canaries

Mutation-sensitive checks for digest byte boundaries, high-bit truncation, hypertree transitions,
and address propagation. The expected values are independent of the implementation theorems.
-/

public section

namespace SLHDSA.PositionTest

open FipsParameterSet

/-! ## Total trajectories at small boundary depths -/

/-- A minimal valid one-layer profile, with no tree-index bits in its digest. -/
def oneLayerParams : Params :=
  { n := 1, h := 4, d := 1, hp := 4, a := 8, k := 1, lgw := 1 }

def oneLayerValidated : ValidatedParams := ⟨oneLayerParams, by decide⟩

def oneLayerDigest : Bytes oneLayerParams.m :=
  Vector.ofFn fun i => ([0xa5, 0xfe] : List Byte).getD i.val 0

def oneLayerPosition : LayerPosition oneLayerValidated :=
  LayerPosition.atLayer oneLayerValidated (splitDigest oneLayerParams oneLayerDigest)
    ⟨0, by decide⟩

/-- At `d = 1`, arbitrary-layer access is definitionally the unique initial position. -/
example : oneLayerPosition =
    LayerPosition.initial oneLayerValidated (splitDigest oneLayerParams oneLayerDigest) := by
  rfl

/-- A two-layer boundary profile, where the only transition must reach the final tree. -/
def twoLayerParams : Params :=
  { n := 1, h := 8, d := 2, hp := 4, a := 8, k := 1, lgw := 1 }

def twoLayerValidated : ValidatedParams := ⟨twoLayerParams, by decide⟩

def twoLayerDigest : Bytes twoLayerParams.m :=
  Vector.ofFn fun i => ([0xa5, 0xab, 0xfe] : List Byte).getD i.val 0

def twoLayerPosition0 : LayerPosition twoLayerValidated :=
  LayerPosition.atLayer twoLayerValidated (splitDigest twoLayerParams twoLayerDigest)
    ⟨0, by decide⟩

def twoLayerPosition1 : LayerPosition twoLayerValidated :=
  LayerPosition.atLayer twoLayerValidated (splitDigest twoLayerParams twoLayerDigest)
    ⟨1, by decide⟩

/-- The two-layer trajectory starts at the digest-derived initial position. -/
example : twoLayerPosition0 =
    LayerPosition.initial twoLayerValidated (splitDigest twoLayerParams twoLayerDigest) := by
  rfl

/-- The indexed two-layer trajectory agrees with one explicit recurrence step. -/
example : twoLayerPosition1 = twoLayerPosition0.next (by decide) := by
  exact LayerPosition.atLayer_succ_eq_next twoLayerValidated
    (splitDigest twoLayerParams twoLayerDigest) ⟨0, by decide⟩ (by decide)

/-- A small valid three-layer profile with one digest byte for each parsed component. -/
def threeLayerParams : Params :=
  { n := 1, h := 12, d := 3, hp := 4, a := 8, k := 1, lgw := 1 }

/-- The three-layer profile bundled with its arithmetic validity proof. -/
def threeLayerValidated : ValidatedParams := ⟨threeLayerParams, by decide⟩

/-- Digest bytes chosen so every parsed component and both masked high-bit boundaries differ. -/
def threeLayerDigest : Bytes threeLayerParams.m :=
  Vector.ofFn fun i => ([0xa5, 0xab, 0xfe] : List Byte).getD i.val 0

/-- The exact typed result of parsing `a5 || ab || fe`: the final nibble masks `fe` to `e`. -/
theorem threeLayerSplit :
    let parts := splitDigest threeLayerParams threeLayerDigest
    (parts.md.toList, parts.idxTree.val, parts.idxLeaf.val) = ([0xa5], 171, 14) := by
  simp only [splitDigest_md_toList, splitDigest_idxTree_val, splitDigest_idxLeaf_val]
  simp [threeLayerParams, threeLayerDigest, Params.digestBytes, Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn, Fin.foldr,
    Fin.foldr.loop]

theorem threeLayerTree :
    (splitDigest threeLayerParams threeLayerDigest).idxTree.val = 171 := by
  exact congrArg (fun result => result.2.1) threeLayerSplit

theorem threeLayerLeaf :
    (splitDigest threeLayerParams threeLayerDigest).idxLeaf.val = 14 := by
  exact congrArg (fun result => result.2.2) threeLayerSplit

/-- The FORS address carries the digest-derived tree and leaf, not one-layer zero defaults. -/
example : (splitDigest threeLayerParams threeLayerDigest).forsAdrs =
    { layer := 0, tree := 171, type := 3, word1 := 14, word2 := 0, word3 := 0 } := by
  unfold DigestParts.forsAdrs
  rw [show (splitDigest threeLayerParams threeLayerDigest).idxTree.val = 171 from threeLayerTree]
  rw [show (splitDigest threeLayerParams threeLayerDigest).idxLeaf.val = 14 from threeLayerLeaf]
  rfl

/-- Layer zero receives the digest's tree and leaf without swapping them. -/
def position0 : LayerPosition threeLayerValidated :=
  LayerPosition.initial threeLayerValidated (splitDigest threeLayerParams threeLayerDigest)

theorem position0Values :
    [position0.layer.val, position0.tree.val, position0.leaf.val] = [0, 171, 14] := by
  change [0, (splitDigest threeLayerParams threeLayerDigest).idxTree.val,
    (splitDigest threeLayerParams threeLayerDigest).idxLeaf.val] = [0, 171, 14]
  rw [threeLayerTree, threeLayerLeaf]

theorem position0Layer : position0.layer.val = 0 :=
  congrArg (fun xs => xs[0]!) position0Values

theorem position0Tree : position0.tree.val = 171 :=
  congrArg (fun xs => xs[1]!) position0Values

/-- The first real transition sends low four tree bits to the leaf and high bits to the tree. -/
def position1 : LayerPosition threeLayerValidated := position0.next (by decide)

theorem position1Layer : position1.layer.val = 1 := by
  change position0.layer.val + 1 = 1
  rw [position0Layer]

theorem position1Tree : position1.tree.val = 10 := by
  change position0.tree.val / 2 ^ threeLayerValidated.params.hp = 10
  rw [position0Tree]
  norm_num [threeLayerValidated, threeLayerParams]

theorem position1Leaf : position1.leaf.val = 11 := by
  change position0.tree.val % 2 ^ threeLayerValidated.params.hp = 11
  rw [position0Tree]
  norm_num [threeLayerValidated, threeLayerParams]

theorem position1Values :
    [position1.layer.val, position1.tree.val, position1.leaf.val] = [1, 10, 11] := by
  simpa only [List.cons.injEq, List.nil_eq, and_true] using
    And.intro position1Layer (And.intro position1Tree position1Leaf)

example : position1.toAdrs =
    { layer := 1, tree := 10, type := 0, word1 := 0, word2 := 0, word3 := 0 } := by
  unfold LayerPosition.toAdrs
  rw [show position1.tree.val = 10 from position1Tree]
  rw [show position1.layer.val = 1 from position1Layer]
  rfl

/-- The second transition reaches the final layer with tree zero and the prior tree as leaf. -/
def position2 : LayerPosition threeLayerValidated := position1.next (by decide)

theorem position2Layer : position2.layer.val = 2 := by
  change position1.layer.val + 1 = 2
  rw [position1Layer]

theorem position2Tree : position2.tree.val = 0 := by
  change position1.tree.val / 2 ^ threeLayerValidated.params.hp = 0
  rw [position1Tree]
  norm_num [threeLayerValidated, threeLayerParams]

theorem position2Leaf : position2.leaf.val = 10 := by
  change position1.tree.val % 2 ^ threeLayerValidated.params.hp = 10
  rw [position1Tree]
  norm_num [threeLayerValidated, threeLayerParams]

theorem position2Values :
    [position2.layer.val, position2.tree.val, position2.leaf.val] = [2, 0, 10] := by
  simpa only [List.cons.injEq, List.nil_eq, and_true] using
    And.intro position2Layer (And.intro position2Tree position2Leaf)

example : position2.tree.val = 0 := position2Tree

/-- Direct arbitrary-layer access reproduces the final position of a nontrivial three-layer
chain, so the indexed API cannot silently reverse or skip a transition. -/
example : LayerPosition.atLayer threeLayerValidated
    (splitDigest threeLayerParams threeLayerDigest) ⟨2, by decide⟩ = position2 := by
  rfl

/-- Increasing digest bytes make every slice boundary and big-endian conversion observable. -/
def increasingDigest (p : Params) : Bytes p.m :=
  Vector.ofFn fun i => UInt8.ofNat i.val

/-- Summary of exact `md` extent and the two parsed indices for a named FIPS parameter set. -/
def digestSummary (ps : FipsParameterSet) : List ℕ :=
  let p := ps.params
  let parts := splitDigest p (increasingDigest p)
  [parts.md.toList.length,
    (parts.md.toList.getD (p.digestBytes - 1) 0).toNat,
    parts.idxTree.val,
    parts.idxLeaf.val]

/-- All six numerical shapes, in both families, use the exact byte offsets and bit masks. -/
theorem allDigestSummaries : all.map digestSummary =
  [[21, 20, 5935262955280923, 29], [25, 24, 1808788007904223008, 1],
    [30, 29, 8478472156619556, 294], [33, 32, 2387509390608836392, 1],
    [39, 38, 11021681357958189, 46], [40, 39, 2893890600475373103, 0],
    [21, 20, 5935262955280923, 29], [25, 24, 1808788007904223008, 1],
    [30, 29, 8478472156619556, 294], [33, 32, 2387509390608836392, 1],
    [39, 38, 11021681357958189, 46], [40, 39, 2893890600475373103, 0]] := by
  simp only [all, List.map_cons, List.map_nil, digestSummary, splitDigest_md_toList,
    splitDigest_idxTree_val, splitDigest_idxLeaf_val]
  norm_num [increasingDigest, FipsParameterSet.params, Params.digestBytes, Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn, Fin.foldr,
    Fin.foldr.loop]

/-! ## Named FIPS hypertree trajectories -/

/-- The layer-zero position obtained from a named FIPS parameter set's increasing-byte digest. -/
private def fipsInitialPosition (ps : FipsParameterSet) : LayerPosition ps.validatedParams :=
  LayerPosition.initial ps.validatedParams (splitDigest ps.params (increasingDigest ps.params))

@[simp]
private theorem fipsInitialPosition_layer (ps : FipsParameterSet) :
    (fipsInitialPosition ps).layer.val = 0 := rfl

@[simp]
private theorem fipsInitialPosition_tree (ps : FipsParameterSet) :
    (fipsInitialPosition ps).tree.val =
      (splitDigest ps.params (increasingDigest ps.params)).idxTree.val := rfl

@[simp]
private theorem fipsInitialPosition_leaf (ps : FipsParameterSet) :
    (fipsInitialPosition ps).leaf.val =
      (splitDigest ps.params (increasingDigest ps.params)).idxLeaf.val := rfl

/-- The first FIPS layer transition, which exists for every named parameter set. -/
private def fipsFirstPosition (ps : FipsParameterSet) : LayerPosition ps.validatedParams :=
  (fipsInitialPosition ps).next (by cases ps <;> decide)

/-- Initial and first-transition position fields followed by their independently projected address
layer and tree. -/
private def fipsFirstTransitionSummary (ps : FipsParameterSet) : List ℕ :=
  let initial := fipsInitialPosition ps
  let next := fipsFirstPosition ps
  [initial.layer.val, initial.tree.val, initial.leaf.val,
    initial.toAdrs.layer, initial.toAdrs.tree,
    next.layer.val, next.tree.val, next.leaf.val,
    next.toAdrs.layer, next.toAdrs.tree]

@[simp]
private theorem fipsFirstTransitionSummary_eq (ps : FipsParameterSet) :
    fipsFirstTransitionSummary ps =
      let parts := splitDigest ps.params (increasingDigest ps.params)
      [0, parts.idxTree.val, parts.idxLeaf.val, 0, parts.idxTree.val,
        1, parts.idxTree.val / 2 ^ ps.params.hp,
        parts.idxTree.val % 2 ^ ps.params.hp,
        1, parts.idxTree.val / 2 ^ ps.params.hp] := by
  rfl

/-- Every approved small/fast shape and both hash families follow the first FIPS transition and
propagate the resulting layer and tree into the address. -/
example : all.map fipsFirstTransitionSummary =
  [[0, 5935262955280923, 29, 0, 5935262955280923,
      1, 11592310459533, 27, 1, 11592310459533],
    [0, 1808788007904223008, 1, 0, 1808788007904223008,
      1, 226098500988027876, 0, 1, 226098500988027876],
    [0, 8478472156619556, 294, 0, 8478472156619556,
      1, 16559515930897, 292, 1, 16559515930897],
    [0, 2387509390608836392, 1, 0, 2387509390608836392,
      1, 298438673826104549, 0, 1, 298438673826104549],
    [0, 11021681357958189, 46, 0, 11021681357958189,
      1, 43053442804524, 45, 1, 43053442804524],
    [0, 2893890600475373103, 0, 0, 2893890600475373103,
      1, 180868162529710818, 15, 1, 180868162529710818],
    [0, 5935262955280923, 29, 0, 5935262955280923,
      1, 11592310459533, 27, 1, 11592310459533],
    [0, 1808788007904223008, 1, 0, 1808788007904223008,
      1, 226098500988027876, 0, 1, 226098500988027876],
    [0, 8478472156619556, 294, 0, 8478472156619556,
      1, 16559515930897, 292, 1, 16559515930897],
    [0, 2387509390608836392, 1, 0, 2387509390608836392,
      1, 298438673826104549, 0, 1, 298438673826104549],
    [0, 11021681357958189, 46, 0, 11021681357958189,
      1, 43053442804524, 45, 1, 43053442804524],
    [0, 2893890600475373103, 0, 0, 2893890600475373103,
      1, 180868162529710818, 15, 1, 180868162529710818]] := by
  simp only [all, List.map_cons, List.map_nil, fipsFirstTransitionSummary_eq,
    splitDigest_idxTree_val, splitDigest_idxLeaf_val]
  norm_num [increasingDigest, FipsParameterSet.params, Params.digestBytes, Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn, Fin.foldr,
    Fin.foldr.loop]

/-- Compact layer/tree/leaf view used to pin a complete named FIPS trajectory. -/
private def positionSummary {p : ValidatedParams} (pos : LayerPosition p) : List ℕ :=
  [pos.layer.val, pos.tree.val, pos.leaf.val]

private def sha2_128sPosition0 :
    LayerPosition (.SLHDSA_SHA2_128s : FipsParameterSet).validatedParams :=
  fipsInitialPosition .SLHDSA_SHA2_128s

private def sha2_128sPosition1 := sha2_128sPosition0.next (by decide)
private def sha2_128sPosition2 := sha2_128sPosition1.next (by decide)
private def sha2_128sPosition3 := sha2_128sPosition2.next (by decide)
private def sha2_128sPosition4 := sha2_128sPosition3.next (by decide)
private def sha2_128sPosition5 := sha2_128sPosition4.next (by decide)
private def sha2_128sPosition6 := sha2_128sPosition5.next (by decide)

@[simp]
private theorem sha2_128s_hp :
    (.SLHDSA_SHA2_128s : FipsParameterSet).validatedParams.params.hp = 9 := rfl

/-- A full seven-layer approved small trajectory reaches the final zero tree without changing
layer order or swapping the high- and low-bit components. -/
example :
    [sha2_128sPosition0, sha2_128sPosition1, sha2_128sPosition2, sha2_128sPosition3,
      sha2_128sPosition4, sha2_128sPosition5, sha2_128sPosition6].map positionSummary =
    [[0, 5935262955280923, 29], [1, 11592310459533, 27], [2, 22641231366, 141],
      [3, 44221155, 6], [4, 86369, 227], [5, 168, 353], [6, 0, 168]] := by
  simp only [List.map_cons, List.map_nil, positionSummary, sha2_128sPosition6,
    sha2_128sPosition5, sha2_128sPosition4, sha2_128sPosition3, sha2_128sPosition2,
    sha2_128sPosition1, sha2_128sPosition0, LayerPosition.next_layer_val,
    LayerPosition.next_tree_val, LayerPosition.next_leaf_val, fipsInitialPosition_layer,
    fipsInitialPosition_tree, fipsInitialPosition_leaf, splitDigest_idxTree_val,
    splitDigest_idxLeaf_val, sha2_128s_hp]
  norm_num [increasingDigest, FipsParameterSet.validatedParams, FipsParameterSet.params,
    Params.digestBytes, Params.treeIdxBytes, Params.leafIdxBytes, Params.m, toInt,
    Vector.toList_ofFn, List.ofFn, Fin.foldr, Fin.foldr.loop]

/-- An all-ones digest reaches the maximum tree and leaf after discarding byte-alignment padding. -/
def truncationBoundaryCorrect (ps : FipsParameterSet) : Bool :=
  let p := ps.params
  let digest : Bytes p.m := Vector.replicate p.m 0xff
  let parts := splitDigest p digest
  parts.idxTree.val == 2 ^ (p.h - p.hp) - 1 &&
    parts.idxLeaf.val == 2 ^ p.hp - 1

example : all.all truncationBoundaryCorrect = true := by decide

/-- The one-layer limited profile has an empty tree-index slice and therefore tree zero. -/
example :
    let digest : Bytes slhdsaSha2_128_24.m := Vector.replicate slhdsaSha2_128_24.m 0xff
    (splitDigest slhdsaSha2_128_24 digest).idxTree.val = 0 := by
  decide

end SLHDSA.PositionTest
