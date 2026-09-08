/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.EncodedTargets
public import HashSig.SLHDSA.Security.WotsWitnesses

/-!
# SLH-DSA WOTS+ witness canaries

Executable checks that the WOTS+ witness extractor really produces witnesses, and that what it
produces really satisfies the collision or preimage equation — evaluated at the values, not
restated from the theorems.

No collision is exhibitable under an approved instantiation, so the extraction canaries run over a
toy primitive bundle whose `Thash` collapses its input (`F x = x >>> 1` on a one-byte node type).
The witness lemmas are stated for an arbitrary `Primitives` bundle, so this is in scope; it is a
falsifiability fixture, not a claim about any approved profile.  Over that bundle the checks build
an honest WOTS+ signature, three forgeries that all recover the honest public key, and confirm
that the extractor returns the `F`-collision, the `F`-preimage, and the `T_len` second preimage
respectively, each satisfying its equation by evaluation.  Two negative canaries close the other
direction: signing the same message twice yields no witness at all, and a forgery whose recovered
public key differs yields a `T_len` witness that fails its own validity check — which is exactly
why `findWotsWitness_sound` carries the public-key hypothesis.

The `example`s pin the theorem statements at that bundle and at approved profiles.  The last group
is kernel-checked rather than run: on a profile whose layer-zero tree indices overflow SHA-2's
compressed eight-byte tree field, two distinct listed chain-step targets encode to the same
all-zero key, so `wotsStepAdrsKey_injective`'s `EncodedTargetLedgerConditions` hypothesis is
load-bearing rather than decorative.
-/

public section

namespace SLHDSA.WotsWitnessesTest

open Security Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"WOTS+ witness check failed: {label}")

/-! ## The toy bundle

One byte per node, `w = 4`, six chains.  `Thash` exclusive-ors its inputs and shifts the result
right by one bit, so `F x = x >>> 1`, `chain x i s = x >>> s`, and both `F` and `T_len` collide
readily. -/

-- Exposed: the toy fixture's arithmetic has to reduce inside the exposed bundle below and inside
-- the `decide` pins, so the parameter record, the secret table, and the bundle are exposed as a
-- group.  Nothing outside this executable consumes them.
@[expose] def toyParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 1, k := 1, lgw := 2 }

theorem toyValid : toyParams.Valid := by decide

example : toyParams.w = 4 := by decide
example : toyParams.len1 = 4 := by decide
example : toyParams.len2 = 2 := by decide
example : toyParams.len = 6 := by decide

/-- The per-chain secret values the toy `PRF` hands out, indexed by the chain address. -/
@[expose] def toySecret : ℕ → UInt8
  | 0 => 2
  | 1 => 7
  | 2 => 19
  | 3 => 33
  | 4 => 100
  | _ => 42

@[expose, reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bytes 1
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ adrs => Vector.replicate 1 (toySecret adrs.word2)
  PRFmsg := fun _ _ _ => Vector.replicate 1 0
  yToBytes := id
  Thash := fun _ _ children =>
    Vector.replicate 1 ((children.foldl (fun acc y => acc ^^^ y[0]) 0) >>> 1)
  Hmsg := fun _ _ _ _ => Vector.replicate toyParams.m 0

instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

/-- The toy node encoding is the identity, so the bundle is byte coherent. -/
theorem toyByteLaws : toyPrimitives.core.ByteLaws := ⟨fun _ _ h => h⟩

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

def baseAdrs : Adrs :=
  ((Adrs.zero.setTreeAddress 0).setTypeAndClear .wotsHash).setKeyPairAddress 0

/-! ## The two messages

`0x00` is the forged message and `0x40` the honestly signed one.  Their chain-length vectors are
`[0,0,0,0,3,0]` and `[1,0,0,0,2,3]`, so chains `0` and `5` have a strictly smaller forged step
count and are the two the extractor can act on. -/

def forgedMsg : toyPrimitives.Y := node 0x00
def honestMsg : toyPrimitives.Y := node 0x40

example : chainLengthsCore toyPrimitives.core forgedMsg = [0, 0, 0, 0, 3, 0] := by decide
example : chainLengthsCore toyPrimitives.core honestMsg = [1, 0, 0, 0, 2, 3] := by decide
theorem forgedMsg_ne_honestMsg : forgedMsg ≠ honestMsg := fun h =>
  absurd (congrArg (fun v : toyPrimitives.Y => v.toList) h) (by decide)

/-! ## Honest and forged signatures -/

def honestSig : WotsSig toyParams toyPrimitives.core :=
  wotsSign toyPrimitives honestMsg () () baseAdrs

def honestTops : Vector toyPrimitives.Y toyParams.len :=
  wotsPkGenTops toyPrimitives () () baseAdrs

/-- Rebuild a signature on `forgedMsg` from the honest chain ends: chain `i` starts at the honest
top shifted back up by the `w - 1 - a` steps the recovery will apply, so recovery returns exactly
the honest top.  `tweak` perturbs chain zero's top, which is how the `T_len` scenarios are built.
-/
def forgery (tweak : UInt8) : WotsSig toyParams toyPrimitives.core :=
  Vector.ofFn fun i : Fin toyParams.len =>
    let a := chainStepsCore toyPrimitives.core forgedMsg i.val
    let top := byteOf honestTops[i.val]
    node (((if i.val = 0 then top ^^^ tweak else top)) <<< (UInt8.ofNat (toyParams.w - 1 - a)))

/-- The untweaked forgery, whose recovered chain ends are exactly the honest ones. -/
def chainForgery : WotsSig toyParams toyPrimitives.core := forgery 0

/-- A forgery whose chain-zero end differs from the honest one in its lowest bit only.  `T_len`
exclusive-ors its inputs and shifts right, so the two chain-end vectors still compress equally. -/
def tlForgery : WotsSig toyParams toyPrimitives.core := forgery 1

/-- A forgery whose chain-zero end differs in bit one, which survives the shift: this one does not
recover the honest public key at all. -/
def badForgery : WotsSig toyParams toyPrimitives.core := forgery 2

/-! ## Witness validity, evaluated

`witnessHolds` re-evaluates the equation each constructor asserts.  It is deliberately a separate
computation from `WotsWitness.Valid`: the checks below run it on the extractor's actual output. -/

def witnessHolds : WotsWitness toyParams toyPrimitives → Bool
  | .tlCollision recovered =>
      (recovered != honestTops) &&
        (toyPrimitives.Tl () (wotsPkAdrs baseAdrs) recovered.toList ==
          toyPrimitives.Tl () (wotsPkAdrs baseAdrs) honestTops.toList)
  | .fPreimage i step value =>
      decide (step < toyParams.w - 1) &&
        (toyPrimitives.F () ((wotsChainAdrs baseAdrs i.val).setHashAddress step) value ==
          honestSig[i.val])
  | .fCollision i step value target =>
      decide (step < toyParams.w - 1) && (value != target) &&
        (toyPrimitives.F () ((wotsChainAdrs baseAdrs i.val).setHashAddress step) value ==
          toyPrimitives.F () ((wotsChainAdrs baseAdrs i.val).setHashAddress step) target)

/-- A tag naming which constructor the extractor returned, so a canary can pin the branch. -/
def witnessTag : Option (WotsWitness toyParams toyPrimitives) → String
  | none => "none"
  | some (.tlCollision _) => "tlCollision"
  | some (.fPreimage i step _) => s!"fPreimage {i.val} {step}"
  | some (.fCollision i step _ _) => s!"fCollision {i.val} {step}"

def extract (sig : WotsSig toyParams toyPrimitives.core) (msg : toyPrimitives.Y) :
    Option (WotsWitness toyParams toyPrimitives) :=
  findWotsWitness toyPrimitives sig msg honestSig honestMsg () baseAdrs

/-! ## Positive canaries -/

/-- Chain zero: the honest secret is `2`, so advancing the forged chain to the honest digit `1`
gives `0` where the honest signature reveals `1`.  The two are distinct and share their `F` image
at hash address one, which is the collision the extractor returns. -/
def checkChainCollision : IO Unit := do
  let witness := findWotsChainWitness toyPrimitives chainForgery forgedMsg honestSig honestMsg ()
    baseAdrs ⟨0, by decide⟩
  ensure "chain 0 yields an F-collision at hash address 1"
    (witnessTag witness == "fCollision 0 1")
  match witness with
  | none => ensure "chain 0 yields a witness" false
  | some w =>
      ensure "the chain-0 collision satisfies its equation" (witnessHolds w)
      match w with
      | .fCollision _ _ value target =>
          ensure "the chain-0 collision is between the expected values"
            ((byteOf value == 0) && (byteOf target == 1))
      | _ => ensure "the chain-0 witness is a collision" false

/-- Chain five: the honest digit is `3 = w - 1`, so the forged chain advanced to it lands exactly
on the honest revealed value, giving an `F`-preimage at hash address two. -/
def checkChainPreimage : IO Unit := do
  let witness := findWotsChainWitness toyPrimitives chainForgery forgedMsg honestSig honestMsg ()
    baseAdrs ⟨5, by decide⟩
  ensure "chain 5 yields an F-preimage at hash address 2"
    (witnessTag witness == "fPreimage 5 2")
  match witness with
  | none => ensure "chain 5 yields a witness" false
  | some w =>
      ensure "the chain-5 preimage satisfies its equation" (witnessHolds w)
      match w with
      | .fPreimage _ _ value =>
          ensure "the chain-5 preimage is the expected value" (byteOf value == 10)
      | _ => ensure "the chain-5 witness is a preimage" false

/-- The chains whose forged step count is not strictly smaller yield nothing: chains one to three
have equal step counts, chain four has a strictly larger one. -/
def checkChainNoWitness : IO Unit := do
  let indices : List (Fin toyParams.len) :=
    [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
  for i in indices do
    let witness := findWotsChainWitness toyPrimitives chainForgery forgedMsg honestSig honestMsg ()
      baseAdrs i
    ensure s!"chain {i.val} yields no witness" (witnessTag witness == "none")

/-- The whole-instance extractor scans the chains in order, so it returns chain zero's collision.
The forgery recovers the honest public key, so the witness is sound. -/
def checkInstanceCollision : IO Unit := do
  ensure "the chain forgery recovers the honest public key"
    (wotsPkFromSig toyPrimitives chainForgery forgedMsg () baseAdrs ==
      wotsPkGen toyPrimitives () () baseAdrs)
  ensure "the chain forgery recovers the honest chain ends"
    (wotsPkFromSigTops toyPrimitives chainForgery forgedMsg () baseAdrs == honestTops)
  let witness := extract chainForgery forgedMsg
  ensure "the instance extractor returns chain 0's collision"
    (witnessTag witness == "fCollision 0 1")
  match witness with
  | none => ensure "the instance extractor returns a witness" false
  | some w => ensure "the instance collision satisfies its equation" (witnessHolds w)

/-- Perturbing chain zero's end in its lowest bit changes the recovered chain ends but not their
`T_len` image, so the extractor returns the `T_len` second preimage. -/
def checkInstanceTlCollision : IO Unit := do
  ensure "the T_len forgery recovers the honest public key"
    (wotsPkFromSig toyPrimitives tlForgery forgedMsg () baseAdrs ==
      wotsPkGen toyPrimitives () () baseAdrs)
  ensure "the T_len forgery recovers different chain ends"
    (wotsPkFromSigTops toyPrimitives tlForgery forgedMsg () baseAdrs != honestTops)
  let witness := extract tlForgery forgedMsg
  ensure "the instance extractor returns a T_len second preimage"
    (witnessTag witness == "tlCollision")
  match witness with
  | none => ensure "the T_len extractor returns a witness" false
  | some w => ensure "the T_len second preimage satisfies its equation" (witnessHolds w)

/-- `F` on the toy bundle is a one-bit right shift at every address and every node value. -/
def checkToyF : IO Unit := do
  ensure "F is a one-bit right shift on every node"
    ((List.range 256).all fun x =>
      toyPrimitives.F () (wotsChainAdrs baseAdrs 0) (node (UInt8.ofNat x)) ==
        node (UInt8.ofNat x >>> 1))

/-! ## Negative canaries -/

/-- Signing the same message twice gives no index with a strictly smaller step count, and the
chain ends agree, so the search returns nothing. -/
def checkNoWitnessOnHonestPair : IO Unit := do
  ensure "an honest signature against itself yields no witness"
    (witnessTag (extract honestSig honestMsg) == "none")

/-- Perturbing chain zero's end in bit one survives the `T_len` shift, so the forgery does not
recover the honest public key.  The extractor still returns a `T_len` witness — it only compares
chain ends — but that witness fails its own equation.  This is why `findWotsWitness_sound` carries
the public-key hypothesis. -/
def checkMalformedTlForgery : IO Unit := do
  ensure "the malformed forgery does not recover the honest public key"
    (wotsPkFromSig toyPrimitives badForgery forgedMsg () baseAdrs !=
      wotsPkGen toyPrimitives () () baseAdrs)
  let witness := extract badForgery forgedMsg
  ensure "the malformed forgery still produces a T_len witness"
    (witnessTag witness == "tlCollision")
  match witness with
  | none => ensure "the malformed forgery produces a witness" false
  | some w =>
      ensure "the malformed T_len witness fails its own equation" (!witnessHolds w)

/-- `witnessHolds` itself has to be able to fail.  A fabricated collision whose two values have
different `F` images, a fabricated preimage of the wrong value, and a genuine collision moved to a
hash address at or above `w - 1` are all rejected. -/
def checkFabricatedWitnesses : IO Unit := do
  ensure "a fabricated collision with different F images is rejected"
    (!witnessHolds (.fCollision ⟨0, by decide⟩ 1 (node 0) (node 3)))
  ensure "a fabricated preimage of the wrong value is rejected"
    (!witnessHolds (.fPreimage ⟨5, by decide⟩ 2 (node 0)))
  ensure "a collision at hash address w - 1 is rejected"
    (!witnessHolds (.fCollision ⟨0, by decide⟩ (toyParams.w - 1) (node 0) (node 1)))
  ensure "the genuine chain-zero collision is still accepted"
    (witnessHolds (.fCollision ⟨0, by decide⟩ 1 (node 0) (node 1)))

/-! ## Statement pins at the toy bundle -/

/-- A hypothesis-shape pin for `wotsPkFromSigTops_cases`: the validity and byte-coherence
arguments are discharged by the toy fixture, and the conclusion is weakened here to its index
component. -/
example (sig sig' : WotsSig toyParams toyPrimitives.core) (msg msg' : toyPrimitives.Y)
    (hne : msg ≠ msg')
    (htops : wotsPkFromSigTops toyPrimitives sig msg () baseAdrs =
      wotsPkFromSigTops toyPrimitives sig' msg' () baseAdrs) :
    ∃ i : Fin toyParams.len,
      chainStepsCore toyPrimitives.core msg i.val <
        chainStepsCore toyPrimitives.core msg' i.val :=
  let ⟨i, hi, _⟩ :=
    wotsPkFromSigTops_cases toyValid toyPrimitives toyByteLaws sig sig' msg msg' () baseAdrs hne
      htops
  ⟨i, hi⟩

example (sig : WotsSig toyParams toyPrimitives.core) (msg msg' : toyPrimitives.Y)
    (hne : msg ≠ msg') :
    (findWotsWitness toyPrimitives sig msg honestSig msg' () baseAdrs).isSome :=
  findWotsWitness_isSome toyValid toyPrimitives toyByteLaws sig msg honestSig msg' () baseAdrs hne

/-- The same at the exact data the run-time checks use, so that the extractor's success on the
chain forgery is a theorem and not only an observation. -/
example :
    (findWotsWitness toyPrimitives chainForgery forgedMsg honestSig honestMsg ()
      baseAdrs).isSome :=
  findWotsWitness_isSome toyValid toyPrimitives toyByteLaws chainForgery forgedMsg honestSig
    honestMsg () baseAdrs forgedMsg_ne_honestMsg

example (sig sig' : WotsSig toyParams toyPrimitives.core) (msg msg' : toyPrimitives.Y)
    (hpk : wotsPkFromSig toyPrimitives sig msg () baseAdrs =
      wotsPkFromSig toyPrimitives sig' msg' () baseAdrs)
    (w : WotsWitness toyParams toyPrimitives)
    (hw : findWotsWitness toyPrimitives sig msg sig' msg' () baseAdrs = some w) :
    w.Valid () baseAdrs (wotsPkFromSigTops toyPrimitives sig' msg' () baseAdrs) sig' :=
  findWotsWitness_sound toyPrimitives sig msg sig' msg' () baseAdrs hpk hw

/-! ## Ledger pins on approved profiles -/

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

theorem twoLayerApprovedAddressBounds : ApprovedAddressBounds twoLayerParams :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- Every chain-step address a witness can name at a reachable instance is a listed `wotsFTcr`
target. -/
example (pos : LayerPosition twoLayer) (i : Fin twoLayerParams.len) {t : ℕ}
    (ht : t < twoLayerParams.w - 1) :
    (wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress t ∈ wotsStepAddresses twoLayer :=
  mem_wotsStepAddresses_of_lt pos i ht

/-- The `T_len` witness address at a reachable instance is a listed `wotsTl` target. -/
example (pos : LayerPosition twoLayer) :
    wotsPkAdrs (wotsInstanceAdrs pos) ∈ wotsPkAddresses twoLayer :=
  mem_wotsPkAddresses twoLayer pos

/-- Under the SHA-2 encoder at an approved-bounds profile, distinct chain-step coordinates carry
distinct encoded tweaks. -/
example : Function.Injective fun coord : WotsChainCoord twoLayer × Fin (twoLayerParams.w - 1) =>
    (sha2Primitives twoLayerParams).adrsToKey (wotsStepAdrs coord.1 coord.2) :=
  wotsStepAdrsKey_injective
    (sha2EncodedTargetLedgerConditions twoLayer twoLayerApprovedAddressBounds)

/-- The same for the `T_len` compression addresses, under the SHAKE encoder. -/
example : Function.Injective fun pos : LayerPosition twoLayer =>
    (shakePrimitives twoLayerParams).adrsToKey (wotsPkAdrs (wotsInstanceAdrs pos)) :=
  wotsPkAdrsKey_injective (shakeEncodedTargetLedgerConditions twoLayer
    twoLayerApprovedAddressBounds.toCanonicalAddressBounds)

/-! ## The encoded-distinctness hypothesis is load-bearing

`Concrete.sha2AdrsKey` sends every address outside its checked domain to the all-zero key, which is
the genuine key of the all-zero WOTS-hash address rather than a sentinel.  On a profile whose
layer-zero tree indices overflow the compressed eight-byte tree field, two distinct listed
chain-step targets therefore share a tweak, and `wotsStepAdrsKey_injective` is false without its
`EncodedTargetLedgerConditions` argument. -/

-- Exposed: the aliasing pin below evaluates the SHA-2 key map at concrete addresses of this
-- profile, so its arithmetic has to reduce.
@[expose] def deepParams : Params :=
  { n := 16, h := 99, d := 11, hp := 9, a := 12, k := 14, lgw := 4 }

@[expose] def deep : ValidatedParams := ⟨deepParams, by decide⟩

/-- The SHA-2 bundle's tweak map is the compressed `ADRSc` key map. -/
theorem adrsToKey_sha2 (p : Params) (a : Adrs) :
    (sha2Primitives p).adrsToKey a = sha2AdrsKey a := rfl

example : layerTreeHeight deep 0 = 90 := by decide
example : deep.params.len = 35 := by decide
example : deep.params.w - 1 = 15 := by decide

/-- Past the checked domain the SHA-2 key map returns the all-zero key. -/
theorem sha2AdrsKey_eq_zero_of_tree_overflow (a : Adrs) (ha : Adrs.Fits 8 a.tree = false) :
    sha2AdrsKey a = zeroBytes 22 := by
  unfold sha2AdrsKey Adrs.compressSha2Checked
  by_cases h1 : a.isCanonical = false
  · simp [h1]
  · by_cases h2 : Adrs.Fits 1 a.layer = false
    · simp [h1, h2]
    · simp [h1, h2, ha]

theorem deep_tree_bound (t : ℕ) (ht : t < 2 ^ 64 + 2) : t < 2 ^ layerTreeHeight deep 0 := by
  have hle : (2 : ℕ) ^ 64 + 2 ≤ 2 ^ layerTreeHeight deep 0 := by
    rw [show layerTreeHeight deep 0 = 90 from by decide]
    norm_num
  omega

/-- A layer-zero position of the `deep` profile at a tree index the compressed field cannot
hold. -/
@[expose] def deepPos (t : ℕ) (ht : t < 2 ^ 64 + 2) : LayerPosition deep :=
  ⟨⟨0, by decide⟩, ⟨t, deep_tree_bound t ht⟩, ⟨0, Nat.two_pow_pos _⟩⟩

@[expose] def deepCoord (t : ℕ) (ht : t < 2 ^ 64 + 2) :
    WotsChainCoord deep × Fin (deep.params.w - 1) :=
  ((deepPos t ht, ⟨0, by decide⟩), ⟨0, by decide⟩)

theorem deepCoord_tree (t : ℕ) (ht : t < 2 ^ 64 + 2) :
    (wotsStepAdrs (deepCoord t ht).1 (deepCoord t ht).2).tree = t := rfl

/-- Two distinct listed chain-step targets of the `deep` profile carry the same encoded SHA-2
tweak, namely the all-zero key: their layer-zero tree indices exceed the compressed eight-byte
tree field, and the checked compression falls back to that key rather than to a sentinel. -/
theorem deep_wotsStep_sha2_alias :
    ∃ c₁ c₂ : WotsChainCoord deep × Fin (deep.params.w - 1),
      wotsStepAdrs c₁.1 c₁.2 ∈ wotsStepAddresses deep ∧
        wotsStepAdrs c₂.1 c₂.2 ∈ wotsStepAddresses deep ∧
        c₁ ≠ c₂ ∧
        (sha2Primitives deep.params).adrsToKey (wotsStepAdrs c₁.1 c₁.2) =
          (sha2Primitives deep.params).adrsToKey (wotsStepAdrs c₂.1 c₂.2) := by
  refine ⟨deepCoord (2 ^ 64) (by norm_num), deepCoord (2 ^ 64 + 1) (by norm_num),
    mem_wotsStepAddresses deep _ _, mem_wotsStepAddresses deep _ _, ?_, ?_⟩
  · intro h
    have h₁ := deepCoord_tree (2 ^ 64) (by norm_num)
    have h₂ := deepCoord_tree (2 ^ 64 + 1) (by norm_num)
    rw [h] at h₁
    omega
  · have hfits : ∀ t : ℕ, 2 ^ 64 ≤ t → ∀ ht : t < 2 ^ 64 + 2,
        Adrs.Fits 8 (wotsStepAdrs (deepCoord t ht).1 (deepCoord t ht).2).tree = false := by
      intro t hle ht
      rw [deepCoord_tree, Adrs.Fits, decide_eq_false_iff_not, not_lt]
      norm_num
      omega
    rw [adrsToKey_sha2, adrsToKey_sha2,
      sha2AdrsKey_eq_zero_of_tree_overflow _ (hfits (2 ^ 64) (le_refl _) _),
      sha2AdrsKey_eq_zero_of_tree_overflow _ (hfits (2 ^ 64 + 1) (by norm_num) _)]

/-- Consequently `wotsStepAdrsKey_injective` is false for the SHA-2 bundle at this profile: its
`EncodedTargetLedgerConditions` hypothesis is load-bearing. -/
theorem deep_wotsStep_sha2_not_injective :
    ¬ Function.Injective fun coord : WotsChainCoord deep × Fin (deep.params.w - 1) =>
        (sha2Primitives deep.params).adrsToKey (wotsStepAdrs coord.1 coord.2) := by
  intro hinj
  obtain ⟨c₁, c₂, _, _, hne, hkey⟩ := deep_wotsStep_sha2_alias
  exact hne (hinj hkey)

def main : IO Unit := do
  checkToyF
  checkChainCollision
  checkChainPreimage
  checkChainNoWitness
  checkInstanceCollision
  checkInstanceTlCollision
  checkNoWitnessOnHonestPair
  checkMalformedTlForgery
  checkFabricatedWitnesses
  IO.println "SLH-DSA WOTS+ witness tests: PASS \
    (chain collision and preimage extraction, T_len second preimage, \
     the empty, malformed-input, and fabricated-witness canaries)"

end SLHDSA.WotsWitnessesTest

def main : IO Unit := SLHDSA.WotsWitnessesTest.main
