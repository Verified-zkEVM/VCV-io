/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.EncodedTargets

/-!
# SLH-DSA encoded target-ledger canaries

Executable checks that the concrete address encoders keep the reachable target ledgers
duplicate-free, run at the values rather than through the theorems: `Sha2Address.ofAdrs` is applied
to every ledger entry and the encoded key lists are compared for duplicates at both key widths.

Two further groups pin the negative direction, because the ledgers of a small profile keep every
field far below its encoded width and so exercise no boundary on their own.  `checkFieldBoundaries`
walks the SHA-2 layer and tree fields across their exact limits.  `checkFallbackAliasing` shows what
each encoder does past its domain: SHA-2 returns the all-zero key, which is the genuine key of the
all-zero WOTS-hash address rather than a sentinel, and SHAKE truncates each field to its width, so
two addresses differing only above a width collide silently.

One group is kernel-checked rather than run: a parameter set whose hypertree is too tall for
SHA-2's compressed tree field separates the two conditions theorems.  It satisfies the canonical
bounds, provably fails the approved ones, the SHAKE conditions hold for it, and the SHA-2
conditions are refutable.
-/

public section

namespace SLHDSA.EncodedTargetsTest

open Security Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"encoded target-ledger check failed: {label}")

/-! ## The encoders each bundle installs -/

theorem adrsToKey_sha2 (p : Params) (a : Adrs) :
    (sha2Primitives p).adrsToKey a = sha2AdrsKey a := rfl

theorem adrsToKey_shake (p : Params) (a : Adrs) :
    (shakePrimitives p).adrsToKey a = Adrs.toVector a := rfl

/-! ## Profiles -/

/-- Two layers of height two, two FORS trees of height two. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

/-- One layer of height two, one FORS tree of height one, with the widest Winternitz base. -/
def oneLayerParams : Params :=
  { n := 1, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 8 }

def oneLayer : ValidatedParams := ⟨oneLayerParams, by decide⟩

example : twoLayerParams.len = 4 := by decide
example : twoLayerParams.w = 16 := by decide
example : twoLayerParams.t = 4 := by decide
example : oneLayerParams.len = 2 := by decide
example : oneLayerParams.w = 256 := by decide
example : oneLayerParams.t = 2 := by decide

example : ApprovedAddressBounds twoLayerParams :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

example : ApprovedAddressBounds oneLayerParams :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-! ### A profile SHA-2's compressed layout cannot hold

The two encoders need different amounts of the parameter set, and this profile separates them: its
hypertree carries ninety tree-index bits, which the canonical twelve-byte tree word holds and the
compressed eight-byte one does not. -/

def deepParams : Params := { n := 16, h := 99, d := 11, hp := 9, a := 12, k := 14, lgw := 4 }

def deep : ValidatedParams := ⟨deepParams, by decide⟩

theorem deepCanonicalBounds : CanonicalAddressBounds deepParams :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

example : (deepParams.d - 1) * deepParams.hp = 90 := by decide
example : deepParams.len = 35 := by decide
example : deepParams.w = 16 := by decide
example : deepParams.t = 4096 := by decide
example : layerTreeHeight deep 0 = 90 := by decide

example : ¬ ApprovedAddressBounds deepParams := fun hb => absurd hb.treeBits_le (by decide)

/-- The SHAKE conditions cover it. -/
example : EncodedTargetLedgerConditions deep (shakePrimitives deepParams) :=
  shakeEncodedTargetLedgerConditions deep deepCanonicalBounds

/-- The SHA-2 conditions are not merely unavailable for it, they are false.  Two distinct
layer-zero trees whose indices exceed the compressed eight-byte field are both listed XMSS
internal-node targets, and both compress to the all-zero key. -/
theorem deep_sha2_conditions_false :
    ¬ EncodedTargetLedgerConditions deep (sha2Primitives deep.params) := by
  intro hconditions
  have hbound : ∀ t : ℕ, t < 2 ^ 64 + 2 → t < 2 ^ layerTreeHeight deep 0 := by
    intro t ht
    have hle : (2 : ℕ) ^ 64 + 2 ≤ 2 ^ layerTreeHeight deep 0 := by
      rw [show layerTreeHeight deep 0 = 90 from by decide]
      norm_num
    omega
  let c₁ : LayerTreeCoord deep :=
    ⟨⟨0, by decide⟩, ⟨2 ^ 64, hbound _ (by norm_num)⟩⟩
  let c₂ : LayerTreeCoord deep :=
    ⟨⟨0, by decide⟩, ⟨2 ^ 64 + 1, hbound _ (by norm_num)⟩⟩
  have hz : (0 : ℕ) < 1 := by norm_num
  have hzh : (1 : ℕ) ≤ deepParams.hp := by decide
  have hidx : (0 : ℕ) < 2 ^ (deepParams.hp - 1) := Nat.two_pow_pos _
  have hm₁ := mem_xmssNodeAddresses deep c₁ hz hzh hidx
  have hm₂ := mem_xmssNodeAddresses deep c₂ hz hzh hidx
  have hinj := (encodeTargets_nodup_iff_injOn (sha2Primitives deepParams)
    (xmssNodeAddresses deep) (xmssNodeAddresses_nodup deep)).1 hconditions.xmssH
  have hzero : ∀ a : Adrs, Adrs.Fits 8 a.tree = false → sha2AdrsKey a = zeroBytes 22 := by
    intro a ha
    unfold sha2AdrsKey Adrs.compressSha2Checked
    by_cases h1 : a.isCanonical = false
    · simp [h1]
    · by_cases h2 : Adrs.Fits 1 a.layer = false
      · simp [h1, h2]
      · simp [h1, h2, ha]
  have htree₁ : (xmssNodeAdrs c₁.toAdrs 1 0).tree = 2 ^ 64 := rfl
  have htree₂ : (xmssNodeAdrs c₂.toAdrs 1 0).tree = 2 ^ 64 + 1 := rfl
  have heq : xmssNodeAdrs c₁.toAdrs 1 0 = xmssNodeAdrs c₂.toAdrs 1 0 := by
    refine hinj _ hm₁ _ hm₂ ?_
    rw [adrsToKey_sha2, adrsToKey_sha2, hzero _ (by rw [htree₁]; decide),
      hzero _ (by rw [htree₂]; decide)]
  have hcontra := congrArg Adrs.tree heq
  rw [htree₁, htree₂] at hcontra
  omega

/-- Every ledger of a profile, including the two roles whose ledger depends on a reduction's own
selection. -/
def ledgers (vp : ValidatedParams) : List (String × List Adrs) :=
  [("FORS leaves", forsLeafAddresses vp),
   ("FORS internal nodes", forsTreeAddresses vp),
   ("FORS roots", forsRootAddresses vp),
   ("XMSS internal nodes", xmssNodeAddresses vp),
   ("WOTS+ steps", wotsStepAddresses vp),
   ("WOTS+ public keys", wotsPkAddresses vp),
   ("WOTS+ selected steps", selectedWotsAddresses vp fun _ => firstWotsStep vp),
   ("WOTS+ optional steps",
     optionalWotsAddresses vp fun coord =>
       if coord.2.val = 0 then none else some (firstWotsStep vp))]

/-! ## The two encoders at their concrete key widths -/

def sha2Keys (addresses : List Adrs) : List (Bytes 22) := addresses.map sha2AdrsKey

def shakeKeys (addresses : List Adrs) : List (Bytes 32) := addresses.map Adrs.toVector


example (p : Params) (addresses : List Adrs) :
    encodeTargets (sha2Primitives p) addresses = sha2Keys addresses := rfl

example (p : Params) (addresses : List Adrs) :
    encodeTargets (shakePrimitives p) addresses = shakeKeys addresses := rfl

/-! ## Ledger checks -/

/-- The runtime predicate below is exactly the `Sha2Domain` the obligations are stated over. -/
example (a : Adrs) : Sha2Domain a ↔ (Sha2Address.ofAdrs a).toOption.isSome = true :=
  sha2Domain_iff_ofAdrs_isSome

/-- Every ledger address passes the checked SHA-2 compression boundary, so none of them is encoded
through the zero fallback, and only the genuinely all-zero address carries the all-zero key. -/
def checkSha2Domain (profile : String) (vp : ValidatedParams) : IO Unit := do
  for (label, addresses) in ledgers vp do
    ensure s!"{profile} {label}: every address is accepted by the checked SHA-2 boundary"
      (addresses.all fun a => (Sha2Address.ofAdrs a).toOption.isSome)
    ensure s!"{profile} {label}: only the all-zero address carries the all-zero key"
      (addresses.all fun a => a = Adrs.zero || sha2AdrsKey a != zeroBytes 22)

/-- Encoded tweaks stay distinct under both approved encoders. -/
def checkEncodedNodup (profile : String) (vp : ValidatedParams) : IO Unit := do
  for (label, addresses) in ledgers vp do
    ensure s!"{profile} {label}: SHA-2 encoded tweaks are distinct"
      (decide (sha2Keys addresses).Nodup)
    ensure s!"{profile} {label}: SHAKE encoded tweaks are distinct"
      (decide (shakeKeys addresses).Nodup)

/-! ## Encoder boundaries -/

def wotsAt (layer tree keyPair : ℕ) : Adrs :=
  (((Adrs.zero.setLayerAddress layer).setTreeAddress tree).setTypeAndClear
    .wotsHash).setKeyPairAddress keyPair

def wotsStepAt (chain step : ℕ) : Adrs :=
  ((wotsAt 0 0 0).setChainAddress chain).setHashAddress step

/-- Each address word accepts exactly its documented width: the compressed one-byte layer and
eight-byte tree that SHA-2 imposes, and the four-byte key-pair, chain, and hash-address words the
canonical layout imposes.  A small profile's ledgers stay far below every one of these limits, so
the boundary is exercised here directly. -/
def checkFieldBoundaries : IO Unit := do
  ensure "SHA-2 accepts the largest one-byte layer"
    (Sha2Address.ofAdrs (wotsAt 255 0 0)).toOption.isSome
  ensure "a two-byte layer is still canonical, so only the compressed width can reject it"
    (wotsAt 256 0 0).isCanonical
  ensure "SHA-2 rejects a two-byte layer"
    (Sha2Address.ofAdrs (wotsAt 256 0 0)).toOption.isNone
  ensure "SHA-2 accepts the largest eight-byte tree"
    (Sha2Address.ofAdrs (wotsAt 0 (2 ^ 64 - 1) 0)).toOption.isSome
  ensure "a nine-byte tree is still canonical, so only the compressed width can reject it"
    (wotsAt 0 (2 ^ 64) 0).isCanonical
  ensure "SHA-2 rejects a nine-byte tree"
    (Sha2Address.ofAdrs (wotsAt 0 (2 ^ 64) 0)).toOption.isNone
  ensure "the canonical layout accepts the largest four-byte key-pair word"
    (wotsAt 0 0 (2 ^ 32 - 1)).isCanonical
  ensure "the canonical layout rejects a five-byte key-pair word"
    (!(wotsAt 0 0 (2 ^ 32)).isCanonical)
  ensure "SHA-2 accepts the largest key-pair word its canonical layout allows"
    (Sha2Address.ofAdrs (wotsAt 0 0 (2 ^ 32 - 1))).toOption.isSome
  ensure "the canonical layout accepts the largest four-byte chain word"
    (wotsStepAt (2 ^ 32 - 1) 0).isCanonical
  ensure "the canonical layout rejects a five-byte chain word"
    (!(wotsStepAt (2 ^ 32) 0).isCanonical)
  ensure "the canonical layout accepts the largest four-byte hash-address word"
    (wotsStepAt 0 (2 ^ 32 - 1)).isCanonical
  ensure "the canonical layout rejects a five-byte hash-address word"
    (!(wotsStepAt 0 (2 ^ 32)).isCanonical)

/-- Past its domain each encoder collapses distinct addresses onto one key. -/
def checkFallbackAliasing : IO Unit := do
  let wideTree := wotsAt 0 (2 ^ 64) 0
  ensure "an over-wide tree index is rejected by the checked SHA-2 boundary"
    (Sha2Address.ofAdrs wideTree).toOption.isNone
  ensure "SHA-2 maps it to the all-zero key"
    (sha2AdrsKey wideTree == zeroBytes 22)
  ensure "which is the genuine key of the all-zero WOTS-hash address"
    (sha2AdrsKey Adrs.zero == zeroBytes 22)
  ensure "so SHA-2 does not separate the two"
    (wideTree != Adrs.zero && sha2AdrsKey wideTree == sha2AdrsKey Adrs.zero)
  let overWideTree := wotsAt 0 (2 ^ 96) 0
  ensure "an over-wide tree index is not canonical"
    (!overWideTree.isCanonical)
  ensure "and SHAKE truncates it onto the all-zero address"
    (Adrs.toVector overWideTree == Adrs.toVector Adrs.zero)
  let overWideKeyPair := wotsAt 0 0 (2 ^ 32)
  ensure "an over-wide key-pair word is not canonical"
    (!overWideKeyPair.isCanonical)
  ensure "and SHAKE truncates it onto the all-zero address too"
    (Adrs.toVector overWideKeyPair == Adrs.toVector Adrs.zero)
  ensure "so canonicality is what SHAKE's injectivity rests on"
    (overWideTree != overWideKeyPair &&
      Adrs.toVector overWideTree == Adrs.toVector overWideKeyPair)

def main : IO Unit := do
  checkSha2Domain "two-layer" twoLayer
  checkEncodedNodup "two-layer" twoLayer
  checkSha2Domain "one-layer" oneLayer
  checkEncodedNodup "one-layer" oneLayer
  checkFieldBoundaries
  checkFallbackAliasing
  IO.println "SLH-DSA encoded target-ledger tests: PASS \
    (two profiles, eight ledgers each; SHA-2 and SHAKE distinctness; five field boundaries; \
    both encoders' out-of-domain aliasing)"

end SLHDSA.EncodedTargetsTest

def main : IO Unit := SLHDSA.EncodedTargetsTest.main
