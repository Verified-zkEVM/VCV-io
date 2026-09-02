/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ReachableTargets

/-!
# SLH-DSA reachable-target ledger canaries

Executable, mutation-sensitive checks for the security target ledgers over small validated
parameter profiles whose ledgers can be enumerated completely at run time.  The expected sizes are
hand-computed constants, not the `targetCount` formulas, so a wrong ledger and a wrong formula
cannot cancel.  The checks also pin the exact address content of the ledgers: the addresses the
construction actually hashes for a fixed digest are members, and near-miss addresses (wrong type,
wrong height, hash step `w - 1`, out-of-range tree) are not.  Cross-role ledgers are checked to
be pairwise disjoint on these profiles.
-/

@[expose] public section

namespace SLHDSA.ReachableTargetsTest

open Security

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"reachable-target ledger check failed: {label}")

/-! ## Small validated profiles -/

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

/-- One layer of height two, one FORS tree of height one, `w = 256`, `len = 2`. -/
def oneLayerParams : Params :=
  { n := 1, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 8 }

def oneLayer : ValidatedParams := ⟨oneLayerParams, by decide⟩

example : twoLayerParams.len = 4 := by decide
example : twoLayerParams.w = 16 := by decide
example : oneLayerParams.len = 2 := by decide
example : oneLayerParams.w = 256 := by decide

/-! ## Hand-computed ledger sizes -/

/-- Every role's ledger length, as a hand-computed constant for the two-layer profile.  Layer zero
holds `2^2 = 4` trees and layer one holds one, so there are `5` XMSS trees and `20` WOTS+
instances; the `16` bottom leaves each host `k = 2` FORS trees with `4` leaves and `3` internal
nodes. -/
def checkTwoLayerSizes : IO Unit := do
  ensure "two-layer: 5 XMSS trees" ((allXmssTrees twoLayer).length == 5)
  ensure "two-layer: 20 WOTS+ instances" ((allWotsInstances twoLayer).length == 20)
  ensure "two-layer: 16 bottom positions" ((allBottomPositions twoLayer).length == 16)
  ensure "two-layer: 128 FORS leaves" ((forsLeafAddresses twoLayer).length == 128)
  ensure "two-layer: 96 FORS internal nodes" ((forsTreeAddresses twoLayer).length == 96)
  ensure "two-layer: 16 FORS roots" ((forsRootAddresses twoLayer).length == 16)
  ensure "two-layer: 15 XMSS internal nodes" ((xmssNodeAddresses twoLayer).length == 15)
  ensure "two-layer: 20 WOTS+ base addresses" ((wotsInstanceAddresses twoLayer).length == 20)
  ensure "two-layer: 80 WOTS+ chains" ((allWotsChains twoLayer).length == 80)
  ensure "two-layer: 1200 executed WOTS+ steps" ((wotsStepAddresses twoLayer).length == 1200)
  ensure "two-layer: 20 WOTS+ public keys" ((wotsPkAddresses twoLayer).length == 20)
  ensure "two-layer: 80 selected UD steps"
    ((selectedWotsAddresses twoLayer fun _ => firstWotsStep twoLayer).length == 80)
  ensure "two-layer: optional PRE selection drops zero-digit chains"
    ((optionalWotsAddresses twoLayer fun coord =>
      if coord.2.val = 0 then none else some (firstWotsStep twoLayer)).length == 60)

/-- The one-layer profile has a single XMSS tree with `4` leaves and `w - 1 = 255` steps per
chain. -/
def checkOneLayerSizes : IO Unit := do
  ensure "one-layer: 1 XMSS tree" ((allXmssTrees oneLayer).length == 1)
  ensure "one-layer: 4 WOTS+ instances" ((allWotsInstances oneLayer).length == 4)
  ensure "one-layer: 4 bottom positions" ((allBottomPositions oneLayer).length == 4)
  ensure "one-layer: 8 FORS leaves" ((forsLeafAddresses oneLayer).length == 8)
  ensure "one-layer: 4 FORS internal nodes" ((forsTreeAddresses oneLayer).length == 4)
  ensure "one-layer: 4 FORS roots" ((forsRootAddresses oneLayer).length == 4)
  ensure "one-layer: 3 XMSS internal nodes" ((xmssNodeAddresses oneLayer).length == 3)
  ensure "one-layer: 2040 executed WOTS+ steps" ((wotsStepAddresses oneLayer).length == 2040)
  ensure "one-layer: 4 WOTS+ public keys" ((wotsPkAddresses oneLayer).length == 4)

/-- The formula layer agrees with the same hand-computed constants. -/
def checkTargetCounts : IO Unit := do
  ensure "two-layer: xmssTreeCount = 5" (xmssTreeCount twoLayerParams == 5)
  ensure "two-layer: wotsInstanceCount = 20" (wotsInstanceCount twoLayerParams == 20)
  ensure "two-layer: targetCount forsF = 128" (targetCount twoLayerParams .forsF == 128)
  ensure "two-layer: targetCount forsH = 96" (targetCount twoLayerParams .forsH == 96)
  ensure "two-layer: targetCount forsTl = 16" (targetCount twoLayerParams .forsTl == 16)
  ensure "two-layer: targetCount wotsFUd = 80" (targetCount twoLayerParams .wotsFUd == 80)
  ensure "two-layer: targetCount wotsFTcr = 1280" (targetCount twoLayerParams .wotsFTcr == 1280)
  ensure "two-layer: targetCount wotsFPre = 80" (targetCount twoLayerParams .wotsFPre == 80)
  ensure "two-layer: targetCount wotsTl = 20" (targetCount twoLayerParams .wotsTl == 20)
  ensure "two-layer: targetCount xmssH = 15" (targetCount twoLayerParams .xmssH == 15)
  ensure "one-layer: xmssTreeCount = 1" (xmssTreeCount oneLayerParams == 1)
  ensure "one-layer: wotsInstanceCount = 4" (wotsInstanceCount oneLayerParams == 4)
  ensure "one-layer: targetCount wotsFTcr = 2048" (targetCount oneLayerParams .wotsFTcr == 2048)

/-! ## Run-time distinctness and cross-role separation -/

def checkNodup (label : String) (addresses : List Adrs) : IO Unit :=
  ensure s!"{label}: no duplicate address" (decide addresses.Nodup)

def checkDisjoint (label : String) (left right : List Adrs) : IO Unit :=
  ensure s!"{label}: disjoint" (!left.any fun a => right.contains a)

def roleLedgers (vp : ValidatedParams) : List (String × List Adrs) :=
  [("FORS leaves", forsLeafAddresses vp),
   ("FORS internal nodes", forsTreeAddresses vp),
   ("FORS roots", forsRootAddresses vp),
   ("XMSS internal nodes", xmssNodeAddresses vp),
   ("WOTS+ steps", wotsStepAddresses vp),
   ("WOTS+ public keys", wotsPkAddresses vp)]

def checkLedgerFamily (profile : String) (vp : ValidatedParams) : IO Unit := do
  let ledgers := roleLedgers vp
  for (label, addresses) in ledgers do
    checkNodup s!"{profile} {label}" addresses
    ensure s!"{profile} {label}: every address is canonical"
      (addresses.all fun a => a.isCanonical)
  for (leftLabel, left) in ledgers do
    for (rightLabel, right) in ledgers do
      if leftLabel != rightLabel then
        checkDisjoint s!"{profile} {leftLabel} vs {rightLabel}" left right
  checkNodup s!"{profile} WOTS+ base addresses" (wotsInstanceAddresses vp)
  -- A WOTS+ base address is an instance identifier, not a separate hash target: it coincides
  -- with the first executed step of chain zero, so it lies inside the step ledger.
  ensure s!"{profile} WOTS+ base addresses are the chain-zero step-zero targets"
    ((wotsInstanceAddresses vp).all fun a => (wotsStepAddresses vp).contains a)

/-! ## Pinned address content -/

/-- A fixed two-layer digest: `md = 0xa5`, `idx_tree = 0x2 & 0b11 = 2`, `idx_leaf = 0x1`. -/
def twoLayerDigest : Bytes twoLayerParams.m :=
  Vector.ofFn fun i => ([0xa5, 0x02, 0x01] : List Byte).getD i.val 0

def twoLayerParts : DigestParts twoLayerParams := splitDigest twoLayerParams twoLayerDigest

/-- The FORS and hypertree addresses that Algorithms 18--20 hash for the fixed digest are members
of the ledgers, and structurally near addresses are not. -/
def checkTwoLayerContent : IO Unit := do
  ensure "two-layer digest: idx_tree = 2" (twoLayerParts.idxTree.val == 2)
  ensure "two-layer digest: idx_leaf = 1" (twoLayerParts.idxLeaf.val == 1)
  let forsBase := twoLayerParts.forsAdrs
  let bottom := BottomPosition.ofDigestParts twoLayer twoLayerParts
  ensure "typed bottom position reproduces Algorithm 19's FORS address"
    (bottom.forsAdrs == forsBase)
  -- FORS leaf `(tree 1, leaf 3)` sits at global index `1 * 4 + 3 = 7`, height `0`.
  ensure "FORS leaf (1, 3) is a leaf target"
    ((forsLeafAddresses twoLayer).contains (forsNodeAdrs forsBase 0 7))
  ensure "FORS leaf index 8 exceeds k * t and is not a leaf target"
    (!(forsLeafAddresses twoLayer).contains (forsNodeAdrs forsBase 0 8))
  ensure "FORS leaf is not an internal-node target"
    (!(forsTreeAddresses twoLayer).contains (forsNodeAdrs forsBase 0 7))
  -- FORS internal node at height `1`, index `3` (tree `1`, node `1`) and the root of tree `1`.
  ensure "FORS internal node (height 1, index 3) is a tree target"
    ((forsTreeAddresses twoLayer).contains (forsNodeAdrs forsBase 1 3))
  ensure "FORS root (height 2, index 1) is a tree target"
    ((forsTreeAddresses twoLayer).contains (forsNodeAdrs forsBase 2 1))
  ensure "FORS height 3 exceeds a and is not a tree target"
    (!(forsTreeAddresses twoLayer).contains (forsNodeAdrs forsBase 3 0))
  ensure "FORS index 2 at height 2 exceeds k and is not a tree target"
    (!(forsTreeAddresses twoLayer).contains (forsNodeAdrs forsBase 2 2))
  ensure "FORS root compression address is a root target"
    ((forsRootAddresses twoLayer).contains (forsPkAdrs forsBase))
  -- The layer-zero XMSS tree `2` and its WOTS+ leaf `1` used by the signature.
  let pos0 := LayerPosition.initial twoLayer twoLayerParts
  ensure "initial position is tree 2, leaf 1 at layer 0"
    (pos0.layer.val == 0 && pos0.tree.val == 2 && pos0.leaf.val == 1)
  let wotsBase := wotsInstanceAdrs pos0
  ensure "WOTS+ base address is a listed instance"
    ((wotsInstanceAddresses twoLayer).contains wotsBase)
  ensure "WOTS+ base address matches the XMSS leaf address"
    (wotsBase == wotsLeafAdrs pos0.toAdrs 1)
  ensure "WOTS+ chain 3 step 14 is an executed-step target"
    ((wotsStepAddresses twoLayer).contains ((wotsChainAdrs wotsBase 3).setHashAddress 14))
  ensure "WOTS+ chain 3 step 15 = w - 1 is never executed"
    (!(wotsStepAddresses twoLayer).contains ((wotsChainAdrs wotsBase 3).setHashAddress 15))
  ensure "WOTS+ chain 4 exceeds len and is not a step target"
    (!(wotsStepAddresses twoLayer).contains ((wotsChainAdrs wotsBase 4).setHashAddress 0))
  ensure "WOTS+ public-key compression address is a listed target"
    ((wotsPkAddresses twoLayer).contains (wotsPkAdrs wotsBase))
  ensure "XMSS node (height 1, index 1) of layer-zero tree 2 is a target"
    ((xmssNodeAddresses twoLayer).contains (xmssNodeAdrs pos0.toAdrs 1 1))
  ensure "XMSS root (height 2, index 0) of layer-zero tree 2 is a target"
    ((xmssNodeAddresses twoLayer).contains (xmssNodeAdrs pos0.toAdrs 2 0))
  ensure "XMSS height 0 is a leaf, not an internal-node target"
    (!(xmssNodeAddresses twoLayer).contains (xmssNodeAdrs pos0.toAdrs 0 1))
  -- The layer-one position: the single top tree, leaf `idx_tree = 2`.
  let pos1 := pos0.next (by decide)
  ensure "next position is tree 0, leaf 2 at layer 1"
    (pos1.layer.val == 1 && pos1.tree.val == 0 && pos1.leaf.val == 2)
  ensure "top-layer WOTS+ base address is a listed instance"
    ((wotsInstanceAddresses twoLayer).contains (wotsInstanceAdrs pos1))
  ensure "top-layer XMSS root is a target"
    ((xmssNodeAddresses twoLayer).contains (xmssNodeAdrs pos1.toAdrs 2 0))
  ensure "a second tree at the top layer is unreachable"
    (!(xmssNodeAddresses twoLayer).contains
      (xmssNodeAdrs ((Adrs.zero.setLayerAddress 1).setTreeAddress 1) 2 0))
  ensure "layer 2 does not exist"
    (!(xmssNodeAddresses twoLayer).contains
      (xmssNodeAdrs ((Adrs.zero.setLayerAddress 2).setTreeAddress 0) 1 0))

/-! ## Kernel-checked counts -/

example : xmssTreeCount twoLayerParams = 5 := by decide
example : wotsInstanceCount twoLayerParams = 20 := by decide
example : targetCount twoLayerParams .xmssH = 2 ^ twoLayerParams.h - 1 := by decide
example : xmssTreeCount oneLayerParams = 1 := by decide
example : (perfectInternalCoords 3).length = 7 := by decide
example : (perfectInternalCoords 2) = [(1, 0), (1, 1), (2, 0)] := by decide

def main : IO Unit := do
  checkTargetCounts
  checkTwoLayerSizes
  checkOneLayerSizes
  checkLedgerFamily "two-layer" twoLayer
  checkLedgerFamily "one-layer" oneLayer
  checkTwoLayerContent
  IO.println "SLH-DSA reachable-target ledger tests: PASS \
    (two small profiles; sizes, distinctness, cross-role disjointness, pinned content)"

end SLHDSA.ReachableTargetsTest

def main : IO Unit := SLHDSA.ReachableTargetsTest.main
