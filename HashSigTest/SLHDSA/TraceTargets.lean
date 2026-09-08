/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Security.TraceTargets

/-!
# SLH-DSA WOTS+ trace-target canaries

Executable checks for the union construction-address ledger and for the WOTS+ trace theorems, run
at the values rather than through the theorems, on two small validated profiles whose ledgers can
be enumerated completely at run time.

The union ledger is checked to have the length of its six components and no duplicate address, and
near-miss addresses (the unexecuted hash step `w - 1`, a secret-key derivation type code, a chain
past `len`) are checked to be absent.  A deliberately out-of-bounds one-step `chainM` execution
also checks that the logged `w - 1` tweak is rejected by the encoded ledger.  The trace canary runs
`wotsPkGenM`, `wotsSignM`, and `wotsPkFromSigM` at a reachable position under
`QueryImpl.withLogging` of the SHA-2 and SHAKE primitive bundles' canonical `PublicHash.impl`
handler, and checks that every logged `thash` query (an `F` or `T_len` call) carries a tweak from
`encodeTargets` of the union ledger, that the log has exactly the length the total query bound
predicts, and that the exact set of tweaks each run logs is the one the WOTS+ address helpers name
for that instance.  The recovered public key is compared with the generated one so that the
logged programs are the WOTS+ programs and not a stub.  These canaries concern the complete WOTS+
step ledger; they do not model the partial target selection or game hops of the UD reduction.
-/

public section

namespace SLHDSA.TraceTargetsTest

open OracleComp OracleSpec Security Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"trace-target check failed: {label}")

/-! ## Small validated profiles -/

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

/-- One layer of height two, one FORS tree of height one, `w = 256`, `len = 2`. -/
def oneLayerParams : Params :=
  { n := 1, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 8 }

def oneLayer : ValidatedParams := ⟨oneLayerParams, by decide⟩

/-- A fixed two-layer digest: `md = 0xa5`, `idx_tree = 0x2 & 0b11 = 2`, `idx_leaf = 0x1`. -/
def twoLayerDigest : Bytes twoLayerParams.m :=
  Vector.ofFn fun i => ([0xa5, 0x02, 0x01] : List Byte).getD i.val 0

/-- A fixed one-layer digest: `md = 0x5a`, `idx_leaf = 0x03`. -/
def oneLayerDigest : Bytes oneLayerParams.m :=
  Vector.ofFn fun i => ([0x5a, 0x03] : List Byte).getD i.val 0

def twoLayerPosition : LayerPosition twoLayer :=
  LayerPosition.initial twoLayer (splitDigest twoLayerParams twoLayerDigest)

def oneLayerPosition : LayerPosition oneLayer :=
  LayerPosition.initial oneLayer (splitDigest oneLayerParams oneLayerDigest)

/-! ## The union ledger -/

def roleLengthSum (vp : ValidatedParams) : ℕ :=
  (forsLeafAddresses vp).length + (forsTreeAddresses vp).length +
    (forsRootAddresses vp).length + (wotsStepAddresses vp).length +
    (wotsPkAddresses vp).length + (xmssNodeAddresses vp).length

/-- The union has the length of its six components, no duplicate, and every role member; the
hand-computed totals are `128 + 96 + 16 + 1200 + 20 + 15` and `8 + 4 + 4 + 2040 + 4 + 3`. -/
def checkUnionLedger (profile : String) (vp : ValidatedParams) (expected : ℕ) : IO Unit := do
  let union := constructionAddresses vp
  ensure s!"{profile}: union length is the sum of the six ledgers"
    (union.length == roleLengthSum vp)
  ensure s!"{profile}: union length is the hand-computed total" (union.length == expected)
  ensure s!"{profile}: no duplicate address in the union" (decide union.Nodup)
  for ledger in [forsLeafAddresses vp, forsTreeAddresses vp, forsRootAddresses vp,
      wotsStepAddresses vp, wotsPkAddresses vp, xmssNodeAddresses vp] do
    ensure s!"{profile}: every role address is in the union"
      (ledger.all fun a => union.contains a)

/-- Structurally near addresses that no WOTS+ program at a reachable position hashes. -/
def checkNearMisses (profile : String) (vp : ValidatedParams) (pos : LayerPosition vp) :
    IO Unit := do
  let union := constructionAddresses vp
  let base := wotsInstanceAdrs pos
  let w := vp.params.w
  let len := vp.params.len
  ensure s!"{profile}: the last executed step w - 2 of chain 0 is a target"
    (union.contains ((wotsChainAdrs base 0).setHashAddress (w - 2)))
  ensure s!"{profile}: hash step w - 1 is not a target"
    (!union.contains ((wotsChainAdrs base 0).setHashAddress (w - 1)))
  ensure s!"{profile}: a chain index equal to len is not a target"
    (!union.contains ((wotsChainAdrs base len).setHashAddress 0))
  ensure s!"{profile}: the WOTS+ PRF secret-key address is not a hash target"
    (!union.contains (wotsSkAdrs base 0))
  ensure s!"{profile}: the public-key compression address is a target"
    (union.contains (wotsPkAdrs base))
  let wrongType := (base.setTypeAndClear .forsPrf).setKeyPairAddress base.getKeyPairAddress
  ensure s!"{profile}: the same position at the FORS PRF type code is not a target"
    (!union.contains wrongType)

/-! ## Logged WOTS+ executions -/

/-- Run a public-hash program under the bundle's canonical handler with logging. -/
def loggedRun {p : Params} (prims : Primitives p) {α : Type}
    (program : OracleComp (publicHashSpec prims.core) α) :
    α × QueryLog (publicHashSpec prims.core) :=
  (simulateQ (PublicHash.impl prims).withLogging program).run.run

/-- The tweak of a logged `thash` entry; `H_msg` has none. -/
def entryKey {p : Params} (prims : Primitives p)
    (entry : (q : (publicHashSpec prims.core).Domain) × (publicHashSpec prims.core).Range q) :
    Option prims.AdrsKey :=
  match entry.1 with
  | .thash _ adrsKey _ => some adrsKey
  | .hmsg _ _ _ _ => none

/-- No two entries of `ks` are equal under `keyEq`. -/
def distinctUnder {α : Type} (keyEq : α → α → Bool) : List α → Bool
  | [] => true
  | k :: ks => !ks.any (keyEq k) && distinctUnder keyEq ks

/-- Every logged entry is a `thash` query whose tweak lies in `encoded`, and the multiset of logged
tweaks is exactly `expected`: the expected list is checked pairwise distinct under `keyEq`, the log
has its length, and the two are mutually contained. -/
def checkLog {p : Params} (prims : Primitives p) (keyEq : prims.AdrsKey → prims.AdrsKey → Bool)
    (label : String) (log : QueryLog (publicHashSpec prims.core))
    (encoded expected : List prims.AdrsKey) : IO Unit := do
  let keys := log.filterMap (entryKey prims)
  let mem (k : prims.AdrsKey) (ks : List prims.AdrsKey) : Bool := ks.any (keyEq k)
  ensure s!"{label}: the expected tweaks are pairwise distinct" (distinctUnder keyEq expected)
  ensure s!"{label}: every logged query is a thash query" (keys.length == log.length)
  ensure s!"{label}: the log has the predicted length" (log.length == expected.length)
  ensure s!"{label}: every logged tweak is in the encoded union ledger"
    (keys.all fun k => mem k encoded)
  ensure s!"{label}: every expected tweak was logged" (expected.all fun k => mem k keys)
  ensure s!"{label}: every logged tweak was expected" (keys.all fun k => mem k expected)

/-- Execute the first step outside the WOTS+ chain domain and confirm that its concrete logged
tweak is absent from the encoded construction ledger.  This is a mutation canary for the strict
upper bound in `chainM_queriesWithinConstructionTargets`, not a valid WOTS+ execution. -/
def checkRejectedChainStep (vp : ValidatedParams) (label : String)
    (prims : Primitives vp.params)
    (keyEq : prims.AdrsKey → prims.AdrsKey → Bool) (pkSeed : prims.PkSeed)
    (x : prims.Y) (pos : LayerPosition vp) : IO Unit := do
  let p := vp.params
  let base := wotsInstanceAdrs pos
  let badAdrs := (wotsChainAdrs base 0).setHashAddress (p.w - 1)
  let (_, log) := loggedRun prims
    (chainM prims.core pkSeed (wotsChainAdrs base 0) x (p.w - 1) 1 :
      OracleComp (publicHashSpec prims.core) prims.Y)
  let keys := log.filterMap (entryKey prims)
  let badKey := prims.adrsToKey badAdrs
  let encoded := encodeTargets prims (constructionAddresses vp)
  ensure s!"{label}: the out-of-bounds chain logs exactly one thash query"
    (log.length == 1 && keys.length == 1)
  ensure s!"{label}: the out-of-bounds chain logs the w - 1 tweak"
    (keys.all fun k => keyEq k badKey)
  ensure s!"{label}: the logged w - 1 tweak is rejected by the encoded ledger"
    (keys.all fun k => !encoded.any (keyEq k))

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

/-- Run the three WOTS+ programs at `pos` under `prims` and compare their logs with the tweaks the
WOTS+ address helpers name for that instance: the `len * (w - 1)` executed steps and the
public-key compression for generation, the `sum chainSteps` steps for signing, and the
complementary steps plus the compression for recovery. -/
def exerciseBundle (vp : ValidatedParams) (label : String) (prims : Primitives vp.params)
    (keyEq : prims.AdrsKey → prims.AdrsKey → Bool) (skSeed : prims.SkSeed)
    (pkSeed : prims.PkSeed) (msg : prims.Y) (pos : LayerPosition vp) : IO Unit := do
  let p := vp.params
  let base := wotsInstanceAdrs pos
  let encoded := encodeTargets prims (constructionAddresses vp)
  let stepKeys (lo hi : ℕ → ℕ) : List prims.AdrsKey :=
    (List.range p.len).flatMap fun i =>
      (List.range (hi i - lo i)).map fun j =>
        prims.adrsToKey ((wotsChainAdrs base i).setHashAddress (lo i + j))
  let pkKey := prims.adrsToKey (wotsPkAdrs base)
  let steps := fun i => chainStepsCore prims.core msg i
  let (generated, genLog) := loggedRun prims
    (wotsPkGenM prims.core skSeed pkSeed base : OracleComp (publicHashSpec prims.core) prims.Y)
  checkLog prims keyEq s!"{label} wotsPkGenM" genLog encoded
    (stepKeys (fun _ => 0) (fun _ => p.w - 1) ++ [pkKey])
  ensure s!"{label} wotsPkGenM: log length is len * (w - 1) + 1"
    (genLog.length == p.len * (p.w - 1) + 1)
  let (signature, signLog) := loggedRun prims
    (wotsSignM prims.core msg skSeed pkSeed base :
      OracleComp (publicHashSpec prims.core) (WotsSig p prims.core))
  checkLog prims keyEq s!"{label} wotsSignM" signLog encoded (stepKeys (fun _ => 0) steps)
  ensure s!"{label} wotsSignM: the signing log is non-empty" (signLog.length > 0)
  let (recovered, recoverLog) := loggedRun prims
    (wotsPkFromSigM prims.core signature msg pkSeed base :
      OracleComp (publicHashSpec prims.core) prims.Y)
  checkLog prims keyEq s!"{label} wotsPkFromSigM" recoverLog encoded
    (stepKeys steps (fun _ => p.w - 1) ++ [pkKey])
  ensure s!"{label}: signing and recovery together execute every step once"
    (signLog.length + recoverLog.length == genLog.length)
  ensure s!"{label}: wotsSignM -> wotsPkFromSigM = wotsPkGenM"
    (prims.core.yToBytes recovered == prims.core.yToBytes generated)

/-- The approved bundles' encoded tweaks are byte vectors of the two encoders' widths; instance
search does not see through the bundle projection, so the comparisons are named explicitly. -/
def sha2KeyEq (p : Params) : (sha2Primitives p).AdrsKey → (sha2Primitives p).AdrsKey → Bool :=
  fun a b : Bytes 22 => a == b

def shakeKeyEq (p : Params) :
    (shakePrimitives p).AdrsKey → (shakePrimitives p).AdrsKey → Bool :=
  fun a b : Bytes 32 => a == b

def checkTwoLayerTraces : IO Unit := do
  checkRejectedChainStep twoLayer "two-layer SHA-2" (sha2Primitives twoLayerParams)
    (sha2KeyEq _) (fixedBytes 1 2) (fixedBytes 1 3) twoLayerPosition
  checkRejectedChainStep twoLayer "two-layer SHAKE" (shakePrimitives twoLayerParams)
    (shakeKeyEq _) (fixedBytes 1 2) (fixedBytes 1 3) twoLayerPosition
  exerciseBundle twoLayer "two-layer SHA-2" (sha2Primitives twoLayerParams) (sha2KeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 2) (fixedBytes 1 3) twoLayerPosition
  exerciseBundle twoLayer "two-layer SHAKE" (shakePrimitives twoLayerParams) (shakeKeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 2) (fixedBytes 1 3) twoLayerPosition
  exerciseBundle twoLayer "two-layer SHA-2, top layer" (sha2Primitives twoLayerParams)
    (sha2KeyEq _) (fixedBytes 1 4) (fixedBytes 1 5) (fixedBytes 1 6)
    (twoLayerPosition.next (by decide))

def checkOneLayerTraces : IO Unit := do
  checkRejectedChainStep oneLayer "one-layer SHA-2" (sha2Primitives oneLayerParams)
    (sha2KeyEq _) (fixedBytes 1 2) (fixedBytes 1 3) oneLayerPosition
  checkRejectedChainStep oneLayer "one-layer SHAKE" (shakePrimitives oneLayerParams)
    (shakeKeyEq _) (fixedBytes 1 2) (fixedBytes 1 3) oneLayerPosition
  exerciseBundle oneLayer "one-layer SHA-2" (sha2Primitives oneLayerParams) (sha2KeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 2) (fixedBytes 1 3) oneLayerPosition
  exerciseBundle oneLayer "one-layer SHAKE" (shakePrimitives oneLayerParams) (shakeKeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 2) (fixedBytes 1 3) oneLayerPosition

def main : IO Unit := do
  checkUnionLedger "two-layer" twoLayer 1475
  checkUnionLedger "one-layer" oneLayer 2063
  checkNearMisses "two-layer" twoLayer twoLayerPosition
  checkNearMisses "one-layer" oneLayer oneLayerPosition
  checkTwoLayerTraces
  checkOneLayerTraces
  IO.println "SLH-DSA WOTS+ trace-target tests: PASS \
    (two small profiles; union ledger size and distinctness, near misses, rejected boundary \
    chains, logged WOTS+ executions under SHA-2 and SHAKE handlers)"

end SLHDSA.TraceTargetsTest

def main : IO Unit := SLHDSA.TraceTargetsTest.main
