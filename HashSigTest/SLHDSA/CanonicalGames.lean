/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Security.CanonicalGames

/-!
# SLH-DSA canonical-game canaries

Checks that the canonical component games carry the target caps, sampling distributions, and
attacked members they are meant to, on the SHA-2 primitive bundle at a small validated profile and
on the twelve FIPS 205 parameter sets.

The `example`s pin, across the module boundary, the definitional facts a reduction relies on: each
problem's `numTargets` is the role's `targetCount`, the two `F` games sample uniformly, and the
standalone FORS-`F` DSPR and TCR problems are the ones the OpenPRE reduction attacks.  The
executable checks, at run time, the target caps of the small profile against hand-computed
constants, the FIPS-set caps against the closed forms, and the `H_msg` ITSR index map on a fixed
digest against its hand-decoded leaves.
-/

public section

namespace SLHDSA.CanonicalGamesTest

open Security Security.CanonicalGames Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"canonical-game check failed: {label}")

/-! ## Small validated profile -/

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

/-- The SHA-2 bundle at byte width one. -/
abbrev prims : Primitives twoLayerParams := sha2Primitives twoLayerParams

instance : SampleableType prims.PkSeed := inferInstanceAs (SampleableType (Bytes 1))
instance : SampleableType prims.Y := inferInstanceAs (SampleableType (Bytes 1))

/-- A fixed two-layer digest: `md = 0xa5`, `idx_tree = 0x02 & 0b11 = 2`, `idx_leaf = 0x01`. -/
def twoLayerDigest : Bytes twoLayerParams.m :=
  Vector.ofFn fun i => ([0xa5, 0x02, 0x01] : List Byte).getD i.val 0

/-! ## Definitional pins -/

example : (forsFOpenPreProblem prims).numTargets = targetCount twoLayerParams .forsF := rfl
example : (forsFDsprProblem prims).numTargets = targetCount twoLayerParams .forsF := rfl
example : (forsFTcrProblem prims).numTargets = targetCount twoLayerParams .forsF := rfl
example : (forsHTcrCProblem prims).numTargets = targetCount twoLayerParams .forsH := rfl
example : (forsTlTcrCProblem prims).numTargets = targetCount twoLayerParams .forsTl := rfl
example : (wotsFUdCProblem prims).numTargets = targetCount twoLayerParams .wotsFUd := rfl
example : (wotsFTcrCProblem prims).numTargets = targetCount twoLayerParams .wotsFTcr := rfl
example : (wotsFPreCProblem prims).numTargets = targetCount twoLayerParams .wotsFPre := rfl
example : (wotsTlTcrCProblem prims).numTargets = targetCount twoLayerParams .wotsTl := rfl
example : (xmssHTcrCProblem prims).numTargets = targetCount twoLayerParams .xmssH := rfl

example : (forsHTcrCProblem prims).numTargets = 96 := by decide
example : (wotsFTcrCProblem prims).numTargets = 1280 := by decide

example : (forsFOpenPreProblem prims).HasUniformInputs := rfl
example : (wotsFUdCProblem prims).HasUniformInputs := rfl
example : (wotsFUdCProblem prims).HasUniformOutputs := rfl

example : forsFDsprProblem prims = (forsFOpenPreProblem prims).toDSPR := rfl
example : forsFTcrProblem prims = (forsFOpenPreProblem prims).toTCR := rfl

example : (forsHTcrCProblem prims).thColl = prims.thashCollection := rfl
example : (wotsFUdCProblem prims).th = prims.fHash := rfl

/-- FIPS 205 SLH-DSA-SHA2-128s: `h = 63`, `k = 14`, `a = 12`. -/
example : targetCount FipsParameterSet.SLHDSA_SHA2_128s.params .forsTl = 2 ^ 63 := by decide
example : targetCount FipsParameterSet.SLHDSA_SHA2_128s.params .forsF = 2 ^ 63 * 14 * 2 ^ 12 := by
  decide

/-- FIPS 205 SLH-DSA-SHAKE-256f: `h = 68`, `k = 35`, `a = 9`. -/
example : targetCount FipsParameterSet.SLHDSA_SHAKE_256f.params .forsH =
    2 ^ 68 * 35 * (2 ^ 9 - 1) := by decide

/-! ## Run-time checks -/

/-- The small profile's caps against hand-computed constants
(`2^4 * 2 * 4`, `2^4 * 2 * 3`, `2^4`, `20 * 4`, `20 * 4 * 16`, `20 * 4`, `4 + 16`, `5 * 3`). -/
def checkTwoLayerCaps : IO Unit := do
  ensure "two-layer: forsF OpenPRE cap = 128" ((forsFOpenPreProblem prims).numTargets == 128)
  ensure "two-layer: forsF DSPR cap = 128" ((forsFDsprProblem prims).numTargets == 128)
  ensure "two-layer: forsF TCR cap = 128" ((forsFTcrProblem prims).numTargets == 128)
  ensure "two-layer: forsH TCR cap = 96" ((forsHTcrCProblem prims).numTargets == 96)
  ensure "two-layer: forsTl TCR cap = 16" ((forsTlTcrCProblem prims).numTargets == 16)
  ensure "two-layer: wotsF UD cap = 80" ((wotsFUdCProblem prims).numTargets == 80)
  ensure "two-layer: wotsF TCR cap = 1280" ((wotsFTcrCProblem prims).numTargets == 1280)
  ensure "two-layer: wotsF PRE cap = 80" ((wotsFPreCProblem prims).numTargets == 80)
  ensure "two-layer: wotsTl TCR cap = 20" ((wotsTlTcrCProblem prims).numTargets == 20)
  ensure "two-layer: xmssH TCR cap = 15" ((xmssHTcrCProblem prims).numTargets == 15)

/-- The twelve FIPS parameter sets. -/
def fipsSets : List FipsParameterSet :=
  [.SLHDSA_SHA2_128s, .SLHDSA_SHA2_128f, .SLHDSA_SHA2_192s, .SLHDSA_SHA2_192f,
    .SLHDSA_SHA2_256s, .SLHDSA_SHA2_256f, .SLHDSA_SHAKE_128s, .SLHDSA_SHAKE_128f,
    .SLHDSA_SHAKE_192s, .SLHDSA_SHAKE_192f, .SLHDSA_SHAKE_256s, .SLHDSA_SHAKE_256f]

/-- On every FIPS set the three FORS caps are the closed forms in `h`, `k`, and `a`, the XMSS cap
is the hypertree's internal-node count `2 ^ h - 1`, and the WOTS+ caps are `2 ^ h` instances times
`len` (times `w` for the target-collision role) plus the upper layers. -/
def checkFipsCaps : IO Unit := do
  for set in fipsSets do
    let p := set.params
    let name := repr set
    let leaves := 2 ^ p.h
    ensure s!"{name}: forsF = 2^h * k * 2^a" (targetCount p .forsF == leaves * p.k * 2 ^ p.a)
    ensure s!"{name}: forsH = 2^h * k * (2^a - 1)"
      (targetCount p .forsH == leaves * p.k * (2 ^ p.a - 1))
    ensure s!"{name}: forsTl = 2^h" (targetCount p .forsTl == leaves)
    ensure s!"{name}: xmssH = 2^h - 1" (targetCount p .xmssH == leaves - 1)
    ensure s!"{name}: wotsTl exceeds the bottom-layer instance count"
      (targetCount p .wotsTl > leaves)
    ensure s!"{name}: wotsFUd = wotsTl * len"
      (targetCount p .wotsFUd == targetCount p .wotsTl * p.len)
    ensure s!"{name}: wotsFPre = wotsFUd" (targetCount p .wotsFPre == targetCount p .wotsFUd)
    ensure s!"{name}: wotsFTcr = wotsFUd * w"
      (targetCount p .wotsFTcr == targetCount p .wotsFUd * p.w)
  ensure "SHA2-128s: forsTl = 2^63" (targetCount FipsParameterSet.SLHDSA_SHA2_128s.params .forsTl
    == 9223372036854775808)
  ensure "SHA2-128s: wotsTl = sum of seven layers"
    (targetCount FipsParameterSet.SLHDSA_SHA2_128s.params .wotsTl ==
      (List.range 7).foldl (fun acc i => acc + 2 ^ (9 * (i + 1))) 0)

/-- A semantic index of the small profile from its four coordinates. -/
def mkIndex (t l i f : ℕ) (ht : t < 2 ^ (twoLayerParams.h - twoLayerParams.hp) := by decide)
    (hl : l < 2 ^ twoLayerParams.hp := by decide) (hi : i < twoLayerParams.k := by decide)
    (hf : f < 2 ^ twoLayerParams.a := by decide) : HmsgIndex twoLayerParams :=
  ⟨⟨t, ht⟩, ⟨l, hl⟩, ⟨i, hi⟩, ⟨f, hf⟩⟩

/-- The ITSR index map on two fixed digests.  `md = 0xa5 = 0b10100101` has base-4 digits `2, 2`
and its instance is tree `2`, leaf `1`; `md = 0x1b = 0b00011011` has base-4 digits `0, 1` and its
instance is tree `3`, leaf `0`. -/
def checkHmsgIndices : IO Unit := do
  let indices := (hmsgItsrProblem prims).indices twoLayerDigest
  ensure "two-layer: k = 2 indices" (indices.length == twoLayerParams.k)
  ensure "two-layer: 0xa5 decodes to leaves 2 and 2 at tree 2, leaf 1"
    (indices == [mkIndex 2 1 0 2, mkIndex 2 1 1 2])
  ensure "two-layer: the two indices are distinct" indices.Nodup
  let otherDigest : Bytes twoLayerParams.m :=
    Vector.ofFn fun i => ([0x1b, 0x03, 0x00] : List Byte).getD i.val 0
  let other := (hmsgItsrProblem prims).indices otherDigest
  ensure "two-layer: 0x1b decodes to leaves 0 and 1 at tree 3, leaf 0"
    (other == [mkIndex 3 0 0 0, mkIndex 3 0 1 1])
  ensure "two-layer: the two digests share no index" (indices.all fun i => !other.contains i)

/-- The ITSR keyed family hashes with the bundle's own `H_msg`. -/
def checkHmsgHash : IO Unit := do
  let r : prims.Y := Vector.ofFn fun _ => (0x11 : Byte)
  let pkSeed : prims.PkSeed := Vector.ofFn fun _ => (0x22 : Byte)
  let pkRoot : prims.Y := Vector.ofFn fun _ => (0x33 : Byte)
  let request : List Byte := [0x44, 0x55]
  let viaGame := (hmsgItsrProblem prims).khf.hash r ⟨pkSeed, pkRoot, request⟩
  ensure "two-layer: the ITSR hash is Hmsg" (viaGame == prims.Hmsg r pkSeed pkRoot request)
  ensure "two-layer: a different request changes the digest"
    (viaGame != prims.Hmsg r pkSeed pkRoot [0x44, 0x56])

def main : IO Unit := do
  checkTwoLayerCaps
  checkFipsCaps
  checkHmsgIndices
  checkHmsgHash
  IO.println "SLH-DSA canonical-game tests: PASS \
    (small-profile and FIPS target caps, H_msg ITSR index map and keyed hash)"

end SLHDSA.CanonicalGamesTest

def main : IO Unit := SLHDSA.CanonicalGamesTest.main
