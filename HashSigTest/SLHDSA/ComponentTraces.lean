/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Security.ComponentTraces

/-!
# SLH-DSA component trace-target canaries

Executable checks for the FORS, XMSS, hypertree, and internal scheme trace theorems of
`HashSig.SLHDSA.Security.ComponentTraces`, run at the values rather than through the theorems, on
two small validated profiles whose ledgers can be enumerated completely at run time.

Each FORS and XMSS program is run under `QueryImpl.withLogging` of the SHA-2 and SHAKE primitive
bundles' canonical `PublicHash.impl` handler, at the FORS address derived from one fixed digest and
at the layer positions on that digest's hypertree trajectory.  The log is checked to contain only
`thash` queries whose tweaks lie in `encodeTargets` of the union ledger, to hit exactly the tweak
set the FIPS 205 algorithm visits (all leaves and internal nodes for root generation, the sibling
subtrees and the signing chain steps for signing, and the revealed leaf, its ancestors, and the
recovery chain steps for recovery), and to have the length the total query bounds predict: exactly
for the FORS programs and XMSS root generation, and jointly for XMSS signing and recovery, whose
individual lengths depend on the message.  Recovered roots are compared with generated ones so the
logged programs are the real ones.  The internal scheme programs are run end to end: key generation
logs exactly the top-layer tree, signing and verification log one `H_msg` query and otherwise only
ledger tweaks within their query bounds, and verification accepts.
-/

public section

namespace SLHDSA.ComponentTracesTest

open OracleComp OracleSpec Security Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"component-trace check failed: {label}")

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

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

/-! ## Logged executions -/

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

/-- A scheme-level log has exactly one `H_msg` entry, every other entry is a `thash` query whose
tweak lies in `encoded`, and the log stays within `bound`. -/
def checkSchemeLog {p : Params} (prims : Primitives p)
    (keyEq : prims.AdrsKey → prims.AdrsKey → Bool) (label : String)
    (log : QueryLog (publicHashSpec prims.core)) (encoded : List prims.AdrsKey) (bound : ℕ) :
    IO Unit := do
  let keys := log.filterMap (entryKey prims)
  ensure s!"{label}: exactly one H_msg query" (keys.length + 1 == log.length)
  ensure s!"{label}: every thash tweak is in the encoded union ledger"
    (keys.all fun k => encoded.any (keyEq k))
  ensure s!"{label}: the log is non-empty" (log.length > 0)
  ensure s!"{label}: the log is within the total query bound" (log.length ≤ bound)

/-! ## Expected tweak sets -/

/-- The chain steps `[lo i, hi i)` of every WOTS+ chain at the instance `base`. -/
def wotsStepKeys {p : Params} (prims : Primitives p) (base : Adrs) (lo hi : ℕ → ℕ) :
    List prims.AdrsKey :=
  (List.range p.len).flatMap fun i =>
    (List.range (hi i - lo i)).map fun j =>
      prims.adrsToKey ((wotsChainAdrs base i).setHashAddress (lo i + j))

/-- The tweaks of WOTS+ public-key generation at `base`: every executed step and the compression. -/
def wotsPkGenKeys {p : Params} (prims : Primitives p) (base : Adrs) : List prims.AdrsKey :=
  wotsStepKeys prims base (fun _ => 0) (fun _ => p.w - 1) ++ [prims.adrsToKey (wotsPkAdrs base)]

/-- The global leaf indices of FORS tree `tree`. -/
def forsLeafIndices (p : Params) (tree : ℕ) : List ℕ :=
  (List.range (2 ^ p.a)).map fun j => tree * 2 ^ p.a + j

/-- The `(height, global index)` coordinates of the internal nodes of FORS tree `tree`. -/
def forsNodeCoords (p : Params) (tree : ℕ) : List (ℕ × ℕ) :=
  (List.range p.a).flatMap fun h' =>
    (List.range (2 ^ (p.a - (h' + 1)))).map fun j => (h' + 1, tree * 2 ^ (p.a - (h' + 1)) + j)

/-- The tweaks of FORS public-key generation: every leaf and internal node of every tree, then the
root compression. -/
def forsPkGenKeys {p : Params} (prims : Primitives p) (adrs : Adrs) : List prims.AdrsKey :=
  ((List.range p.k).flatMap fun tree =>
    (forsLeafIndices p tree).map (fun i => prims.adrsToKey (forsNodeAdrs adrs 0 i)) ++
      (forsNodeCoords p tree).map (fun hj => prims.adrsToKey (forsNodeAdrs adrs hj.1 hj.2))) ++
    [prims.adrsToKey (forsPkAdrs adrs)]

/-- The tweaks of FORS signing: in every tree, every leaf except the selected one and every
internal node off the selected leaf's path. -/
def forsSignKeys {p : Params} (prims : Primitives p) (md : List Byte) (adrs : Adrs) :
    List prims.AdrsKey :=
  (List.range p.k).flatMap fun tree =>
    let selected := tree * 2 ^ p.a + forsIdx p md tree
    ((forsLeafIndices p tree).filter (· != selected)).map
        (fun i => prims.adrsToKey (forsNodeAdrs adrs 0 i)) ++
      ((forsNodeCoords p tree).filter (fun hj => hj.2 != selected / 2 ^ hj.1)).map
        (fun hj => prims.adrsToKey (forsNodeAdrs adrs hj.1 hj.2))

/-- The tweaks of FORS public-key recovery: in every tree, the revealed leaf and its ancestors,
then the root compression. -/
def forsPkFromSigKeys {p : Params} (prims : Primitives p) (md : List Byte) (adrs : Adrs) :
    List prims.AdrsKey :=
  ((List.range p.k).flatMap fun tree =>
    let selected := tree * 2 ^ p.a + forsIdx p md tree
    prims.adrsToKey (forsNodeAdrs adrs 0 selected) ::
      (List.range p.a).map fun h' =>
        prims.adrsToKey (forsNodeAdrs adrs (h' + 1) (selected / 2 ^ (h' + 1)))) ++
    [prims.adrsToKey (forsPkAdrs adrs)]

/-- The `(height, index)` coordinates of the internal nodes of a height-`hp` XMSS tree. -/
def xmssNodeCoords (p : Params) : List (ℕ × ℕ) :=
  (List.range p.hp).flatMap fun h' =>
    (List.range (2 ^ (p.hp - (h' + 1)))).map fun j => (h' + 1, j)

/-- The tweaks of an XMSS root: WOTS+ public-key generation at every leaf and `H` at every
internal node. -/
def xmssRootKeys {p : Params} (prims : Primitives p) (adrs : Adrs) : List prims.AdrsKey :=
  ((List.range (2 ^ p.hp)).flatMap fun t => wotsPkGenKeys prims (wotsLeafAdrs adrs t)) ++
    (xmssNodeCoords p).map fun hj => prims.adrsToKey (xmssNodeAdrs adrs hj.1 hj.2)

/-- The tweaks of XMSS signing at leaf `idx`: WOTS+ public-key generation at every other leaf, `H`
at every internal node off the path of `idx`, and the WOTS+ signing steps at `idx`. -/
def xmssSignKeys {p : Params} (prims : Primitives p) (msg : prims.Y) (adrs : Adrs) (idx : ℕ) :
    List prims.AdrsKey :=
  ((List.range (2 ^ p.hp)).filter (· != idx)).flatMap
      (fun t => wotsPkGenKeys prims (wotsLeafAdrs adrs t)) ++
    ((xmssNodeCoords p).filter (fun hj => hj.2 != idx / 2 ^ hj.1)).map
      (fun hj => prims.adrsToKey (xmssNodeAdrs adrs hj.1 hj.2)) ++
    wotsStepKeys prims (wotsLeafAdrs adrs idx) (fun _ => 0)
      (fun i => chainStepsCore prims.core msg i)

/-- The tweaks of XMSS root recovery at leaf `idx`: the WOTS+ recovery steps and compression at
`idx`, then `H` at each ancestor of `idx`. -/
def xmssPkFromSigKeys {p : Params} (prims : Primitives p) (msg : prims.Y) (adrs : Adrs)
    (idx : ℕ) : List prims.AdrsKey :=
  wotsStepKeys prims (wotsLeafAdrs adrs idx) (fun i => chainStepsCore prims.core msg i)
      (fun _ => p.w - 1) ++
    [prims.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx))] ++
    (List.range p.hp).map fun h' =>
      prims.adrsToKey (xmssNodeAdrs adrs (h' + 1) (idx / 2 ^ (h' + 1)))

/-! ## FORS, XMSS, and scheme executions -/

/-- Run the three FORS programs at the digest-derived address and compare their logs with the
tweak sets above and their lengths with the FORS total query bounds. -/
def exerciseFors (vp : ValidatedParams) (label : String) (prims : Primitives vp.params)
    (keyEq : prims.AdrsKey → prims.AdrsKey → Bool) (skSeed : prims.SkSeed)
    (pkSeed : prims.PkSeed) (parts : DigestParts vp.params) : IO Unit := do
  let p := vp.params
  let encoded := encodeTargets prims (constructionAddresses vp)
  let md := parts.md.toList
  let adrs := parts.forsAdrs
  let (generated, genLog) := loggedRun prims
    (forsPkGenM prims.core skSeed pkSeed adrs : OracleComp (publicHashSpec prims.core) prims.Y)
  checkLog prims keyEq s!"{label} forsPkGenM" genLog encoded (forsPkGenKeys prims adrs)
  ensure s!"{label} forsPkGenM: log length is k * (2^a + (2^a - 1)) + 1"
    (genLog.length == p.k * (2 ^ p.a + (2 ^ p.a - 1)) + 1)
  let (signature, signLog) := loggedRun prims
    (forsSignM prims.core md skSeed pkSeed adrs :
      OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core))
  checkLog prims keyEq s!"{label} forsSignM" signLog encoded (forsSignKeys prims md adrs)
  ensure s!"{label} forsSignM: log length is k * ((2^a - 1) + (2^a - a - 1))"
    (signLog.length == p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1)))
  let (recovered, recoverLog) := loggedRun prims
    (forsPkFromSigM prims.core signature md pkSeed adrs :
      OracleComp (publicHashSpec prims.core) prims.Y)
  checkLog prims keyEq s!"{label} forsPkFromSigM" recoverLog encoded
    (forsPkFromSigKeys prims md adrs)
  ensure s!"{label} forsPkFromSigM: log length is k * (a + 1) + 1"
    (recoverLog.length == p.k * (p.a + 1) + 1)
  ensure s!"{label}: forsSignM -> forsPkFromSigM = forsPkGenM"
    (prims.core.yToBytes recovered == prims.core.yToBytes generated)

/-- Run the XMSS root, signing, and recovery programs at a reachable position and compare their
logs with the tweak sets above; signing and recovery together execute every WOTS+ step of the
position's leaf once and visit every internal node of its tree once. -/
def exerciseXmss (vp : ValidatedParams) (label : String) (prims : Primitives vp.params)
    (keyEq : prims.AdrsKey → prims.AdrsKey → Bool) (skSeed : prims.SkSeed)
    (pkSeed : prims.PkSeed) (msg : prims.Y) (pos : LayerPosition vp) : IO Unit := do
  let p := vp.params
  let encoded := encodeTargets prims (constructionAddresses vp)
  let adrs := pos.toAdrs
  let idx := pos.leaf.val
  let (root, rootLog) := loggedRun prims
    (xmssRootM prims.core skSeed pkSeed adrs : OracleComp (publicHashSpec prims.core) prims.Y)
  checkLog prims keyEq s!"{label} xmssRootM" rootLog encoded (xmssRootKeys prims adrs)
  ensure s!"{label} xmssRootM: log length is xmssNodeQueryBound p hp"
    (rootLog.length == xmssNodeQueryBound p p.hp)
  let (signature, signLog) := loggedRun prims
    (xmssSignM prims.core msg skSeed pkSeed adrs idx :
      OracleComp (publicHashSpec prims.core) (XmssSig p prims.core))
  checkLog prims keyEq s!"{label} xmssSignM" signLog encoded (xmssSignKeys prims msg adrs idx)
  ensure s!"{label} xmssSignM: the signing log is non-empty" (signLog.length > 0)
  let (recovered, recoverLog) := loggedRun prims
    (xmssPkFromSigM prims.core idx signature msg pkSeed adrs :
      OracleComp (publicHashSpec prims.core) prims.Y)
  checkLog prims keyEq s!"{label} xmssPkFromSigM" recoverLog encoded
    (xmssPkFromSigKeys prims msg adrs idx)
  ensure s!"{label}: signing and recovery together cost the auth path, one full WOTS+ key, and hp"
    (signLog.length + recoverLog.length ==
      xmssAuthPathQueryBound p p.hp + (p.len * (p.w - 1) + 1) + p.hp)
  ensure s!"{label}: xmssSignM -> xmssPkFromSigM = xmssRootM"
    (prims.core.yToBytes recovered == prims.core.yToBytes root)

/-- Run internal key generation, signing, and verification: key generation logs exactly the
top-layer tree, the other two log one `H_msg` and ledger tweaks within their bounds, and the
signature verifies. -/
def exerciseScheme (vp : ValidatedParams) (label : String) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (keyEq : prims.AdrsKey → prims.AdrsKey → Bool)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y)
    (message : List Byte) : IO Unit := do
  let p := vp.params
  let encoded := encodeTargets prims (constructionAddresses vp)
  let (keys, keygenLog) := loggedRun prims
    (GeneralScheme.keygenInternalM vp prims.core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec prims.core) (PublicKeyCore prims.core × SecretKeyCore prims.core))
  checkLog prims keyEq s!"{label} keygenInternalM" keygenLog encoded
    (xmssRootKeys prims (GeneralHypertree.layerAdrs (p.d - 1) 0))
  ensure s!"{label} keygenInternalM: log length is keygenInternalQueryBound"
    (keygenLog.length == GeneralScheme.keygenInternalQueryBound p)
  let (signature, signLog) := loggedRun prims
    (GeneralScheme.signInternalM vp prims.core message keys.2 addrnd :
      OracleComp (publicHashSpec prims.core) (GeneralScheme.SignatureCore vp prims.core))
  checkSchemeLog prims keyEq s!"{label} signInternalM" signLog encoded
    (GeneralScheme.signInternalQueryBound p)
  let (verdict, verifyLog) := loggedRun prims
    (GeneralScheme.verifyInternalM vp prims.core message signature keys.1 :
      OracleComp (publicHashSpec prims.core) Bool)
  checkSchemeLog prims keyEq s!"{label} verifyInternalM" verifyLog encoded
    (GeneralScheme.verifyInternalQueryBound p)
  ensure s!"{label}: verifyInternalM accepts signInternalM" verdict

/-- The approved bundles' encoded tweaks are byte vectors of the two encoders' widths; instance
search does not see through the bundle projection, so the comparisons are named explicitly. -/
def sha2KeyEq (p : Params) : (sha2Primitives p).AdrsKey → (sha2Primitives p).AdrsKey → Bool :=
  fun a b : Bytes 22 => a == b

def shakeKeyEq (p : Params) :
    (shakePrimitives p).AdrsKey → (shakePrimitives p).AdrsKey → Bool :=
  fun a b : Bytes 32 => a == b

instance (p : Params) : DecidableEq (sha2Primitives p).Y :=
  inferInstanceAs (DecidableEq (Bytes p.n))

instance (p : Params) : DecidableEq (shakePrimitives p).Y :=
  inferInstanceAs (DecidableEq (Bytes p.n))

/-- Every check of one profile under one bundle: FORS at the digest address, XMSS at each listed
position, and the scheme end to end. -/
def exerciseBundle (vp : ValidatedParams) (label : String) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (keyEq : prims.AdrsKey → prims.AdrsKey → Bool)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (msg addrnd : prims.Y)
    (digest : Bytes vp.params.m) (positions : List (String × LayerPosition vp)) : IO Unit := do
  exerciseFors vp label prims keyEq skSeed pkSeed (splitDigest vp.params digest)
  for (posLabel, pos) in positions do
    exerciseXmss vp s!"{label}, {posLabel}" prims keyEq skSeed pkSeed msg pos
  exerciseScheme vp label prims keyEq skSeed skPrf pkSeed addrnd [0x01, 0x02, 0x03]

def checkTwoLayer : IO Unit := do
  let positions := [("layer 0", twoLayerPosition), ("layer 1", twoLayerPosition.next (by decide))]
  exerciseBundle twoLayer "two-layer SHA-2" (sha2Primitives twoLayerParams) (sha2KeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 4) (fixedBytes 1 2) (fixedBytes 1 3) (fixedBytes 1 5)
    twoLayerDigest positions
  exerciseBundle twoLayer "two-layer SHAKE" (shakePrimitives twoLayerParams) (shakeKeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 4) (fixedBytes 1 2) (fixedBytes 1 3) (fixedBytes 1 5)
    twoLayerDigest positions

def checkOneLayer : IO Unit := do
  let positions := [("layer 0", oneLayerPosition)]
  exerciseBundle oneLayer "one-layer SHA-2" (sha2Primitives oneLayerParams) (sha2KeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 4) (fixedBytes 1 2) (fixedBytes 1 3) (fixedBytes 1 5)
    oneLayerDigest positions
  exerciseBundle oneLayer "one-layer SHAKE" (shakePrimitives oneLayerParams) (shakeKeyEq _)
    (fixedBytes 1 1) (fixedBytes 1 4) (fixedBytes 1 2) (fixedBytes 1 3) (fixedBytes 1 5)
    oneLayerDigest positions

def main : IO Unit := do
  checkTwoLayer
  checkOneLayer
  IO.println "SLH-DSA component trace-target tests: PASS \
    (two small profiles; logged FORS, XMSS, and internal scheme executions under SHA-2 and \
    SHAKE handlers against the encoded union ledger and the expected tweak sets)"

end SLHDSA.ComponentTracesTest

def main : IO Unit := SLHDSA.ComponentTracesTest.main
