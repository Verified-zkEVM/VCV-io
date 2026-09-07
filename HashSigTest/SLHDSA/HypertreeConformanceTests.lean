/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Concrete.Hypertree
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.HypertreeConformance

/-!
# Hypertree conformance and construction tests

Discriminating one-, two-, and three-layer trajectories and a small arbitrary-depth construction
exercise the FIPS 205 hypertree boundary. Cheap structural checks cover every approved profile;
bounded SHA2-128f and SHAKE-128f runs exercise the general sign/recover/root path.  These are
derived construction regressions, not KAT, ACVP, or security reduction evidence.
-/

@[expose] public section

namespace SLHDSA.HypertreeConformanceTests

open Concrete GeneralHypertree HypertreeConformance

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"hypertree conformance check failed: {label}")

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

/-! ## Discriminating trajectory fixtures -/

def oneLayerParams : Params :=
  { n := 1, h := 4, d := 1, hp := 4, a := 8, k := 1, lgw := 1 }

def oneLayerValidated : ValidatedParams := ⟨oneLayerParams, by decide⟩

def oneLayerDigest : Bytes oneLayerValidated.params.m :=
  #v[0xa5, 0xfe]

@[simp] theorem oneLayerDigest_toList : oneLayerDigest.toList = [0xa5, 0xfe] := by rfl

def oneLayerParts : DigestParts oneLayerValidated.params :=
  splitDigest oneLayerValidated.params oneLayerDigest

theorem oneLayerPartsTree : oneLayerParts.idxTree.val = 0 := by
  simp only [oneLayerParts, splitDigest_idxTree_val]
  norm_num [oneLayerValidated, oneLayerParams, oneLayerDigest_toList, Params.digestBytes,
    Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn,
    Fin.foldr, Fin.foldr.loop]

theorem oneLayerPartsLeaf : oneLayerParts.idxLeaf.val = 14 := by
  simp only [oneLayerParts, splitDigest_idxLeaf_val]
  norm_num [oneLayerValidated, oneLayerParams, oneLayerDigest_toList, Params.digestBytes,
    Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn,
    Fin.foldr, Fin.foldr.loop]
  all_goals decide

example :
    (trace oneLayerValidated oneLayerParts).get
        ⟨0, by decide⟩ = [0, 0, 14, 0, 0] := by
  simpa [oneLayerPartsTree, oneLayerPartsLeaf] using
    trace_zero oneLayerValidated oneLayerParts

def twoLayerParams : Params :=
  { n := 1, h := 8, d := 2, hp := 4, a := 8, k := 1, lgw := 1 }

def twoLayerValidated : ValidatedParams := ⟨twoLayerParams, by decide⟩

def twoLayerDigest : Bytes twoLayerValidated.params.m :=
  #v[0xa5, 0xab, 0xfe]

@[simp] theorem twoLayerDigest_toList :
    twoLayerDigest.toList = [0xa5, 0xab, 0xfe] := by rfl

def twoLayerParts : DigestParts twoLayerValidated.params :=
  splitDigest twoLayerValidated.params twoLayerDigest

theorem twoLayerPartsTree : twoLayerParts.idxTree.val = 11 := by
  simp only [twoLayerParts, splitDigest_idxTree_val]
  norm_num [twoLayerValidated, twoLayerParams, twoLayerDigest_toList, Params.digestBytes,
    Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn,
    Fin.foldr, Fin.foldr.loop]
  all_goals decide

theorem twoLayerPartsLeaf : twoLayerParts.idxLeaf.val = 14 := by
  simp only [twoLayerParts, splitDigest_idxLeaf_val]
  norm_num [twoLayerValidated, twoLayerParams, twoLayerDigest_toList, Params.digestBytes,
    Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn,
    Fin.foldr, Fin.foldr.loop]
  all_goals decide

example :
    (trace twoLayerValidated twoLayerParts).get
        ⟨0, by decide⟩ = [0, 11, 14, 0, 11] := by
  simpa [twoLayerPartsTree, twoLayerPartsLeaf] using
    trace_zero twoLayerValidated twoLayerParts

example :
    (trace twoLayerValidated twoLayerParts).get
        ⟨1, by decide⟩ = [1, 0, 11, 1, 0] := by
  have htree :
      (LayerPosition.atLayer twoLayerValidated twoLayerParts ⟨0, by decide⟩).tree.val = 11 := by
    rw [LayerPosition.atLayer_zero_eq_initial]
    exact twoLayerPartsTree
  have h := trace_succ twoLayerValidated twoLayerParts ⟨0, by decide⟩ (by decide)
  norm_num [twoLayerValidated, twoLayerParams, htree] at h
  simpa only [trace_get] using h

def threeLayerParams : Params :=
  { n := 1, h := 12, d := 3, hp := 4, a := 8, k := 1, lgw := 1 }

def threeLayerValidated : ValidatedParams := ⟨threeLayerParams, by decide⟩

def threeLayerDigest : Bytes threeLayerValidated.params.m :=
  #v[0xa5, 0xab, 0xfe]

@[simp] theorem threeLayerDigest_toList :
    threeLayerDigest.toList = [0xa5, 0xab, 0xfe] := by rfl

def threeLayerParts : DigestParts threeLayerValidated.params :=
  splitDigest threeLayerValidated.params threeLayerDigest

theorem threeLayerPartsTree : threeLayerParts.idxTree.val = 171 := by
  simp only [threeLayerParts, splitDigest_idxTree_val]
  norm_num [threeLayerValidated, threeLayerParams, threeLayerDigest_toList, Params.digestBytes,
    Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn,
    Fin.foldr, Fin.foldr.loop]
  all_goals decide

theorem threeLayerPartsLeaf : threeLayerParts.idxLeaf.val = 14 := by
  simp only [threeLayerParts, splitDigest_idxLeaf_val]
  norm_num [threeLayerValidated, threeLayerParams, threeLayerDigest_toList, Params.digestBytes,
    Params.treeIdxBytes,
    Params.leafIdxBytes, Params.m, toInt, Vector.toList_ofFn, List.ofFn,
    Fin.foldr, Fin.foldr.loop]
  all_goals decide

/-- The three-layer canary pins both quotient/remainder transitions and every propagated base
address. -/
theorem threeLayerTrace :
    (trace threeLayerValidated threeLayerParts).get
        ⟨0, by decide⟩ = [0, 171, 14, 0, 171] ∧
    (trace threeLayerValidated threeLayerParts).get
        ⟨1, by decide⟩ = [1, 10, 11, 1, 10] ∧
    (trace threeLayerValidated threeLayerParts).get
        ⟨2, by decide⟩ = [2, 0, 10, 2, 0] := by
  have htree0 :
      (LayerPosition.atLayer threeLayerValidated threeLayerParts ⟨0, by decide⟩).tree.val =
        171 := by
    rw [LayerPosition.atLayer_zero_eq_initial]
    exact threeLayerPartsTree
  have htree1 :
      (LayerPosition.atLayer threeLayerValidated threeLayerParts ⟨1, by decide⟩).tree.val =
        10 := by
    rw [LayerPosition.atLayer_succ_eq_next threeLayerValidated threeLayerParts
      ⟨0, by decide⟩ (by decide)]
    change
      (LayerPosition.atLayer threeLayerValidated threeLayerParts
        ⟨0, by decide⟩).tree.val / 2 ^ threeLayerValidated.params.hp = 10
    rw [htree0]
    norm_num [threeLayerValidated, threeLayerParams]
  constructor
  · simpa [threeLayerPartsTree, threeLayerPartsLeaf] using
      trace_zero threeLayerValidated threeLayerParts
  constructor
  · have h := trace_succ threeLayerValidated threeLayerParts ⟨0, by decide⟩ (by decide)
    norm_num [threeLayerValidated, threeLayerParams, htree0] at h
    simpa only [trace_get] using h
  · have h := trace_succ threeLayerValidated threeLayerParts ⟨1, by decide⟩ (by decide)
    norm_num [threeLayerValidated, threeLayerParams, htree1] at h
    simpa only [trace_get] using h

/-! ## Small executable arbitrary-depth construction -/

def toyParams : Params :=
  { n := 1, h := 6, d := 3, hp := 2, a := 2, k := 2, lgw := 1 }

def toyValidated : ValidatedParams := ⟨toyParams, by decide⟩

@[reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := List Adrs
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ adrs => [adrs]
  PRFmsg := fun _ _ _ => []
  yToBytes := fun _ => Vector.replicate 1 0
  Thash := fun _ adrs children => adrs :: children.flatten
  Hmsg := fun _ _ _ _ => Vector.replicate toyParams.m 0

def toyParts : DigestParts toyParams :=
  splitDigest toyParams (Vector.replicate toyParams.m 0)

def exerciseToy : IO Unit := do
  let sig := sign toyValidated toyPrimitives [] () () toyParts
  ensure "toy: intrinsic three-layer signature" (sig.toList.length == 3)
  let recovered := pkFromSig toyValidated toyPrimitives [] sig () toyParts
  let generated := root toyValidated toyPrimitives () ()
  ensure "toy: d=3 sign/recover/root" (decide (recovered = generated))
  ensure "toy: d=3 verification"
    (verify toyValidated toyPrimitives [] sig () toyParts generated)
  let (pk, sk) := GeneralScheme.keygenInternal toyValidated toyPrimitives () () ()
  let schemeSig := GeneralScheme.signInternal toyValidated toyPrimitives [0x53, 0x38] sk []
  ensure "toy: arbitrary-depth internal sign/verify"
    (GeneralScheme.verifyInternal toyValidated toyPrimitives [0x53, 0x38] schemeSig pk)

/-! ## All-approved structural and address checks -/

def checkApprovedProfile (set : FipsParameterSet) : IO Unit := do
  let p := set.params
  let vp := set.validatedParams
  let parts := splitDigest p (fixedBytes p.m 11)
  let positions := trajectory vp parts
  ensure s!"{set.name}: exact trajectory width" (positions.toList.length == p.d)
  for j in List.finRange p.d do
    let pos := LayerPosition.atLayer vp parts j
    ensure s!"{set.name}: layer {j.val} exact layer field" (pos.layer.val == j.val)
    ensure s!"{set.name}: layer {j.val} address layer" (pos.toAdrs.layer == j.val)
    ensure s!"{set.name}: layer {j.val} address tree" (pos.toAdrs.tree == pos.tree.val)
    ensure s!"{set.name}: layer {j.val} SHA2 base acceptance"
      (Sha2Address.ofAdrs pos.toAdrs).isOk
    ensure s!"{set.name}: layer {j.val} SHAKE base roundtrip"
      (decide (Adrs.fromVector pos.toAdrs.toVector = pos.toAdrs))
    ensure s!"{set.name}: layer {j.val} selected WOTS leaf acceptance"
      (Sha2Address.ofAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val)).isOk
    for z in List.finRange (p.hp + 1) do
      ensure s!"{set.name}: layer {j.val} node {z.val}/0 acceptance"
        (Sha2Address.ofAdrs (xmssNodeAdrs pos.toAdrs z.val 0)).isOk
    if hnext : j.val + 1 < p.d then
      let next := LayerPosition.atLayer vp parts ⟨j.val + 1, hnext⟩
      ensure s!"{set.name}: layer {j.val} quotient transition"
        (next.tree.val == pos.tree.val / 2 ^ p.hp)
      ensure s!"{set.name}: layer {j.val} remainder transition"
        (next.leaf.val == pos.tree.val % 2 ^ p.hp)
    if _hfinal : j.val + 1 = p.d then
      ensure s!"{set.name}: final tree zero" (pos.tree.val == 0)

/-! ## Bounded approved concrete construction -/

def exerciseBundle (set : FipsParameterSet) (prims : Primitives set.params)
    (parts : DigestParts set.params)
    (msg : prims.Y) (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed) : IO Unit := do
  let sig := sign set.validatedParams prims msg skSeed pkSeed parts
  ensure s!"{set.name}: intrinsic hypertree width" (sig.toList.length == set.params.d)
  let recovered := pkFromSig set.validatedParams prims msg sig pkSeed parts
  let generated := root set.validatedParams prims skSeed pkSeed
  ensure s!"{set.name}: sign/recover/root"
    (prims.core.yToBytes recovered == prims.core.yToBytes generated)

def exerciseSelectedConcrete : IO Unit := do
  let sha2Set := FipsParameterSet.SLHDSA_SHA2_128f
  let sha2 := Concrete.approvedPrimitives sha2Set
  let sha2Parts := splitDigest sha2Set.params (fixedBytes sha2Set.params.m 11)
  exerciseBundle sha2Set sha2 sha2Parts
    (fixedBytes 16 3) (fixedBytes 16 1) (fixedBytes 16 2)
  let shakeSet := FipsParameterSet.SLHDSA_SHAKE_128f
  let shake := Concrete.approvedPrimitives shakeSet
  let shakeParts := splitDigest shakeSet.params (fixedBytes shakeSet.params.m 11)
  exerciseBundle shakeSet shake shakeParts
    (fixedBytes 16 3) (fixedBytes 16 1) (fixedBytes 16 2)

def main : IO Unit := do
  exerciseToy
  for set in FipsParameterSet.all do
    checkApprovedProfile set
  exerciseSelectedConcrete
  IO.println "SLH-DSA hypertree conformance tests: PASS \
    (d=1/2/3 boundaries; 12-profile trajectories/addresses; SHA2/SHAKE-128f d=22)"

end SLHDSA.HypertreeConformanceTests

def main : IO Unit := SLHDSA.HypertreeConformanceTests.main
