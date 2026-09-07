/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module

public import HashSig.SLHDSA.Concrete.Fors

/-!
# FORS conformance and construction tests

Discriminating extraction fixtures pin FIPS 205's MSB-first Algorithm 4 interpretation separately
from the digest key-selection mask and the historical round-3 LSB-first rule.  A tiny height-two
model exhausts every one-byte digest.  Cheap checks cover decoded/addressed coordinates for all
twelve approved profiles, while SHA2-128f and SHAKE-128f exercise the concrete sign/recover/keygen
path.  These are derived construction regressions, not ACVP or authoritative KAT evidence.
-/

@[expose] public section

namespace SLHDSA.ForsConstructionTests

open Concrete ForsConformance

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"FORS construction check failed: {label}")

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

/-! ## Discriminating FIPS/round-3 extraction fixtures -/

def extractionParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 6, k := 2, lgw := 1 }

/-- The historical round-3 LSB rule sees the same first byte as the integer `18`. -/
example : round3ForsIdxLSB extractionParams [18, 16] 0 = 18 := by decide

/-- FIPS's MSB-first first index on `[18,16]` is `4`, so the historical rule is incompatible. -/
example : forsIdx extractionParams [18, 16] 0 = 4 := by decide

/-- On `[0x12,0x34]`, the second six-bit FIPS index crosses the byte boundary and is `35`. -/
example : forsIdx extractionParams [0x12, 0x34] 1 = 35 := by decide

def extractionDigest : ForsDigest extractionParams := #v[0x12, 0x34]

/-- The typed decoder agrees at the byte-boundary fixture, anchoring the arithmetic
characterization `decodeIndices_get_bigEndian` at concrete cross-byte values `4` and `35`. -/
example : (decodeIndices extractionParams extractionDigest)[0].val = 4 ∧
    (decodeIndices extractionParams extractionDigest)[1].val = 35 := by
  have h0 := decodeIndices_get_bigEndian extractionParams extractionDigest ⟨0, by decide⟩
  have h1 := decodeIndices_get_bigEndian extractionParams extractionDigest ⟨1, by decide⟩
  norm_num [extractionParams, extractionDigest, toInt] at h0 h1
  exact ⟨h0, h1⟩

example : round3ForsIdxLSB extractionParams [18, 16] 0 ≠
    forsIdx extractionParams [18, 16] 0 := by decide

/-- The LSB-first rule also disagrees on the byte-crossing second index, so the discrimination
does not depend on the non-crossing case alone. -/
example : round3ForsIdxLSB extractionParams [0x12, 0x34] 1 ≠
    forsIdx extractionParams [0x12, 0x34] 1 := by decide

def keySelectionParams : Params :=
  { n := 1, h := 4, d := 1, hp := 4, a := 6, k := 2, lgw := 1 }

/-- Key selection is a separate low-bit mask: the final byte `0xfe` selects leaf `14`. -/
example : (splitDigest keySelectionParams (#v[0, 0, 0xfe])).idxLeaf.val = 14 := by decide

def offsetParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 2, k := 2, lgw := 1 }

/-- In height-two trees, tree one/local leaf two has exact global coordinate `1*4+2=6`. -/
example : (globalLeafIndex offsetParams ⟨1, by decide⟩ ⟨2, by decide⟩).val = 6 := by decide

/-! ## Exhaustive tiny construction -/

def toyParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 2, k := 2, lgw := 1 }

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

def baseAdrs : Adrs :=
  ((Adrs.zero.setTreeAddress 2).setTypeAndClear .forsTree).setKeyPairAddress 3

def exerciseToy : IO Unit := do
  let generated := forsPkGen toyPrimitives () () baseAdrs
  for x in List.range 256 do
    let md : ForsDigest toyParams := Vector.ofFn fun _ => UInt8.ofNat x
    let indices := decodeIndices toyParams md
    ensure s!"toy digest {x}: two intrinsic indices" (indices.toList.length == toyParams.k)
    for tree in List.finRange toyParams.k do
      ensure s!"toy digest {x}/tree {tree.val}: typed decoder matches canonical FORS"
        (indices[tree.val].val == forsIdx toyParams md.toList tree.val)
    let sig := forsSign toyPrimitives md.toList () () baseAdrs
    ensure s!"toy digest {x}: intrinsic tree count" (sig.toList.length == toyParams.k)
    for tree in List.finRange toyParams.k do
      ensure s!"toy digest {x}/tree {tree.val}: intrinsic auth width"
        ((sig[tree.val]).auth.toList.length == toyParams.a)
    let recovered := forsPkFromSig toyPrimitives sig md.toList () baseAdrs
    ensure s!"toy digest {x}: sign/recover/keygen" (decide (recovered = generated))

/-! ## All-approved-profile digest/address checks -/

def checkAddress (set : FipsParameterSet) (label : String) (adrs : Adrs) : IO Unit := do
  ensure s!"{set.name}: {label}: canonical" adrs.isCanonical
  ensure s!"{set.name}: {label}: checked SHA2 acceptance" (Sha2Address.ofAdrs adrs).isOk
  ensure s!"{set.name}: {label}: full-address roundtrip"
    (decide (Adrs.fromVector adrs.toVector = adrs))

/-- Enumerate only the one digest's selected leaf and sibling path in each FORS tree.  The kernel
theorems cover every typed coordinate; this cheap loop deliberately does not enumerate the global
security target ledger. -/
def checkApprovedProfile (set : FipsParameterSet) : IO Unit := do
  let p := set.params
  let digest : Bytes p.m := fixedBytes p.m 11
  let parts := splitDigest p digest
  let indices := decodeDigestParts parts
  ensure s!"{set.name}: digest carries all k*a normative index bits"
    (p.k * p.a ≤ 8 * parts.md.toList.length)
  ensure s!"{set.name}: exact decoded tree count" (indices.toList.length == p.k)
  checkAddress set "digest-derived FORS base" parts.forsAdrs
  checkAddress set "FORS public-key compression" (forsPkAdrs parts.forsAdrs)
  for tree in List.finRange p.k do
    let leaf := indices[tree.val]
    let global := tree.val * p.t + leaf.val
    checkAddress set s!"tree {tree.val} secret {global}" (forsSkAdrs parts.forsAdrs global)
    checkAddress set s!"tree {tree.val} selected leaf {global}"
      (forsNodeAdrs parts.forsAdrs 0 global)
    for level in List.finRange p.a do
      let sibling := PerfectMerkleTree.sibling (leaf.val / 2 ^ level.val)
      let siblingGlobal := tree.val * 2 ^ (p.a - level.val) + sibling
      checkAddress set s!"tree {tree.val} auth {level.val}/{siblingGlobal}"
        (forsNodeAdrs parts.forsAdrs level.val siblingGlobal)
    checkAddress set s!"tree {tree.val} root" (forsNodeAdrs parts.forsAdrs p.a tree.val)

/-! ## Bounded concrete construction -/

def exerciseBundle {p : Params} (name : String) (prims : Primitives p)
    (md : ForsDigest p) (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed)
    (adrs : Adrs) : IO Unit := do
  let sig := forsSign prims md.toList skSeed pkSeed adrs
  ensure s!"{name}: intrinsic FORS tree count" (sig.toList.length == p.k)
  for tree in List.finRange p.k do
    ensure s!"{name}: intrinsic auth width at tree {tree.val}"
      ((sig[tree.val]).auth.toList.length == p.a)
  let recovered := forsPkFromSig prims sig md.toList pkSeed adrs
  let generated := forsPkGen prims skSeed pkSeed adrs
  ensure s!"{name}: forsSign -> forsPkFromSig = forsPkGen"
    (prims.core.yToBytes recovered == prims.core.yToBytes generated)

def exerciseSelectedConcrete : IO Unit := do
  let sha2Set := FipsParameterSet.SLHDSA_SHA2_128f
  let sha2Digest : Bytes sha2Set.params.m := fixedBytes sha2Set.params.m 11
  let sha2Parts := splitDigest sha2Set.params sha2Digest
  let sha2 := approvedPrimitives sha2Set
  exerciseBundle sha2Set.name sha2 sha2Parts.md
    (fixedBytes 16 1) (fixedBytes 16 2) sha2Parts.forsAdrs
  let shakeSet := FipsParameterSet.SLHDSA_SHAKE_128f
  let shakeDigest : Bytes shakeSet.params.m := fixedBytes shakeSet.params.m 11
  let shakeParts := splitDigest shakeSet.params shakeDigest
  let shake := approvedPrimitives shakeSet
  exerciseBundle shakeSet.name shake shakeParts.md
    (fixedBytes 16 1) (fixedBytes 16 2) shakeParts.forsAdrs

def main : IO Unit := do
  exerciseToy
  for set in FipsParameterSet.all do
    checkApprovedProfile set
  exerciseSelectedConcrete
  IO.println "SLH-DSA S07 FORS construction tests: PASS \
    (FIPS extraction; 256 toy digests; 12-profile addresses; SHA2/SHAKE 128f)"

end SLHDSA.ForsConstructionTests

def main : IO Unit := SLHDSA.ForsConstructionTests.main
