/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Bolton Bailey
-/

module

public import HashSig.SLHDSA.Concrete.Xmss

/-!
# Concrete XMSS construction tests

An address-sensitive height-two toy tree exhausts every leaf/internal position and both climb
parities.  Bounded end-to-end tests additionally exercise selected FIPS `approvedPrimitives`
bundles.  These are derived construction regressions, not XMSS KAT or ACVP evidence.
-/

@[expose] public section

namespace SLHDSA.XmssConstructionTests

open Concrete XmssConformance

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"XMSS construction check failed: {label}")

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

def baseAdrs : Adrs :=
  ((Adrs.zero.setLayerAddress 1).setTreeAddress 2).setKeyPairAddress 3

/-! ## Address-sensitive height-two toy tree -/

def toyParams : Params :=
  { n := 1, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 1 }

/-- Toy nodes are complete address traces. Each hash prepends its own address to the child
traces. -/
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

def toyMsg : toyPrimitives.Y := []

def isType (ty : AddrType) (adrs : Adrs) : Bool :=
  AddrType.ofCode adrs.type == some ty

def toyExpectedTreeAddresses : List Adrs :=
  [xmssNodeAdrs baseAdrs 2 0, xmssNodeAdrs baseAdrs 1 0, xmssNodeAdrs baseAdrs 1 1]

def toyExpectedLeafAddresses : List Adrs :=
  (List.range 4).map fun i => wotsPkAdrs (wotsLeafAdrs baseAdrs i)

def toyExpectedAuth (idx : ℕ) : List toyPrimitives.Y :=
  match idx with
  | 0 => [xmssNode toyPrimitives () () baseAdrs 0 1,
      xmssNode toyPrimitives () () baseAdrs 1 1]
  | 1 => [xmssNode toyPrimitives () () baseAdrs 0 0,
      xmssNode toyPrimitives () () baseAdrs 1 1]
  | 2 => [xmssNode toyPrimitives () () baseAdrs 0 3,
      xmssNode toyPrimitives () () baseAdrs 1 0]
  | 3 => [xmssNode toyPrimitives () () baseAdrs 0 2,
      xmssNode toyPrimitives () () baseAdrs 1 0]
  | _ => []

def exerciseToy : IO Unit := do
  let root := xmssRoot toyPrimitives () () baseAdrs
  ensure "toy: exact three TREE address trace"
    (decide (root.filter (isType .tree) = toyExpectedTreeAddresses))
  ensure "toy: exact four leaf WOTS_PK address trace"
    (decide (root.filter (isType .wotsPk) = toyExpectedLeafAddresses))
  ensure "toy: four leaves plus three internal nodes"
    (toyExpectedLeafAddresses.length + toyExpectedTreeAddresses.length == 7)
  for idx in List.finRange (2 ^ toyParams.hp) do
    let sig := xmssSignBounded toyPrimitives toyMsg () () baseAdrs idx
    ensure s!"toy: exact auth entries at leaf {idx.val}"
      (decide (sig.auth.toList = toyExpectedAuth idx.val))
    let recovered := xmssPkFromSigBounded toyPrimitives idx sig toyMsg () baseAdrs
    ensure s!"toy: sign/recover/root at leaf {idx.val}" (decide (recovered = root))

/-! ## Approved concrete bundles and complete reachable address sets -/

def checkReachableAddresses (set : FipsParameterSet) : IO Unit := do
  ensure s!"{set.name}: base SHA2 address" (Sha2Address.ofAdrs baseAdrs).isOk
  for idx in List.range (2 ^ set.params.hp) do
    let leafAdrs := wotsLeafAdrs baseAdrs idx
    ensure s!"{set.name}: leaf {idx} SHA2 acceptance" (Sha2Address.ofAdrs leafAdrs).isOk
    ensure s!"{set.name}: leaf {idx} full-address roundtrip"
      (decide (Adrs.fromVector leafAdrs.toVector = leafAdrs))
  for z0 in List.range set.params.hp do
    let z := z0 + 1
    for t in List.range (2 ^ (set.params.hp - z)) do
      let nodeAdrs := xmssNodeAdrs baseAdrs z t
      ensure s!"{set.name}: node {z}/{t} SHA2 acceptance"
        (Sha2Address.ofAdrs nodeAdrs).isOk
      ensure s!"{set.name}: node {z}/{t} full-address roundtrip"
        (decide (Adrs.fromVector nodeAdrs.toVector = nodeAdrs))

def exerciseBundle {p : Params} (name : String) (prims : Primitives p)
    (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed) (msg : prims.Y)
    (idx : LeafIndex p) : IO Unit := do
  let sig := xmssSignBounded prims msg skSeed pkSeed baseAdrs idx
  ensure s!"{name}: intrinsic auth width" (sig.auth.toList.length == p.hp)
  let recovered := xmssPkFromSigBounded prims idx sig msg pkSeed baseAdrs
  let root := xmssRoot prims skSeed pkSeed baseAdrs
  ensure s!"{name}: bounded sign/recover/root at {idx.val}"
    (prims.core.yToBytes recovered == prims.core.yToBytes root)

def exerciseSelectedConcrete : IO Unit := do
  let sha2 := Concrete.approvedPrimitives .SLHDSA_SHA2_128f
  exerciseBundle FipsParameterSet.SLHDSA_SHA2_128f.name sha2
    (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3) ⟨0, by decide⟩
  exerciseBundle FipsParameterSet.SLHDSA_SHA2_128f.name sha2
    (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3) ⟨7, by decide⟩
  let shake := Concrete.approvedPrimitives .SLHDSA_SHAKE_128f
  exerciseBundle FipsParameterSet.SLHDSA_SHAKE_128f.name shake
    (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3) ⟨0, by decide⟩
  exerciseBundle FipsParameterSet.SLHDSA_SHAKE_128f.name shake
    (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3) ⟨7, by decide⟩
  let sha2_192 := Concrete.approvedPrimitives .SLHDSA_SHA2_192f
  exerciseBundle FipsParameterSet.SLHDSA_SHA2_192f.name sha2_192
    (fixedBytes 24 1) (fixedBytes 24 2) (fixedBytes 24 3) ⟨0, by decide⟩
  exerciseBundle FipsParameterSet.SLHDSA_SHA2_192f.name sha2_192
    (fixedBytes 24 1) (fixedBytes 24 2) (fixedBytes 24 3) ⟨7, by decide⟩

def main : IO Unit := do
  exerciseToy
  for set in FipsParameterSet.all do
    checkReachableAddresses set
  exerciseSelectedConcrete
  IO.println "SLH-DSA S06 XMSS construction tests: PASS \
    (height-2 exhaustive; 12-profile addresses; SHA2/SHAKE 128f and SHA2-192f indices 0/7)"

end SLHDSA.XmssConstructionTests

def main : IO Unit := SLHDSA.XmssConstructionTests.main
