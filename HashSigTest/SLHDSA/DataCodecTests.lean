/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Quang Dao
-/

module
public import HashSig

/-!
# Structured SLH-DSA wire-codec regression tests

These tests exercise the canonical key and signature codecs at depth one, depth two, and all
twelve approved FIPS 205 parameter sets, instantiated over the identity byte carrier `byteCore`
rather than a concrete hash suite. Every structured signature boundary receives a marker:
`R`, each FORS secret and authentication node, every WOTS chain value, and every XMSS
authentication node. Short and long inputs are rejected before semantic decoding.

An end-to-end exercise over the real approved primitives then keygens, signs, encodes,
decodes, and verifies at SLH-DSA-SHA2-128f and SLH-DSA-SHAKE-128f through
`Concrete.approvedWireCodec`, checking the exact FIPS byte widths of the resulting wires.
-/

public section

namespace SLHDSA.DataCodecTests

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"SLH-DSA structured codec check failed: {label}")

def zeroBytes (n : ℕ) : Bytes n := Vector.replicate n 0

def markerBytes (n tag : ℕ) : Bytes n :=
  ⟨(toByte tag n).toArray, by simp [toByte]⟩

/-- A proof-only primitive context whose semantic carriers are exactly the FIPS byte carriers.
The hash operations are irrelevant to codec tests and return zero nodes. -/
@[expose] def byteCore (p : Params) : CorePrimitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Unit
  adrsToKey := fun _ => ()
  PRF := fun _ _ _ => zeroBytes p.n
  PRFmsg := fun _ _ _ => zeroBytes p.n
  yToBytes := fun y => y

@[expose] def byteCodec (p : Params) : CoreWireCodec p (byteCore p) where
  pkSeed := WireCodec.bytes p.n
  skSeed := WireCodec.bytes p.n
  skPrf := WireCodec.bytes p.n
  y := WireCodec.bytes p.n
  y_toBytes := fun _ => rfl

def zeroPublicKey (p : Params) : PublicKeyCore (byteCore p) :=
  ⟨zeroBytes p.n, zeroBytes p.n⟩

def zeroSecretKey (p : Params) : SecretKeyCore (byteCore p) :=
  ⟨zeroBytes p.n, zeroBytes p.n, zeroBytes p.n, zeroBytes p.n⟩

def forsSecretTag (p : Params) (tree : ℕ) : ℕ :=
  2 + tree * (1 + p.a)

def forsAuthTag (p : Params) (tree node : ℕ) : ℕ :=
  forsSecretTag p tree + 1 + node

def wotsTag (p : Params) (layer chain : ℕ) : ℕ :=
  2 + p.k * (1 + p.a) + layer * (p.len + p.hp) + chain

def xmssAuthTag (p : Params) (layer node : ℕ) : ℕ :=
  2 + p.k * (1 + p.a) + layer * (p.len + p.hp) + p.len + node

/-- A signature whose node-sized blocks expose their precise semantic position on the wire. -/
def markedSignature (p : Params) : SignatureCore p (byteCore p) :=
  ⟨markerBytes p.n 1,
    Vector.ofFn fun tree =>
      ⟨markerBytes p.n (forsSecretTag p tree.val),
        Vector.ofFn fun node => markerBytes p.n (forsAuthTag p tree.val node.val)⟩,
    Vector.ofFn fun layer =>
      ⟨Vector.ofFn fun chain => markerBytes p.n (wotsTag p layer.val chain.val),
        Vector.ofFn fun node => markerBytes p.n (xmssAuthTag p layer.val node.val)⟩⟩

def ensureMarker (label : String) (raw : List Byte) (width offset tag : ℕ) : IO Unit :=
  ensure label ((raw.drop offset).take width == (markerBytes width tag).toList)

def checkRoundTrip {α : Type} {width : ℕ} (label : String) (codec : WireCodec α width)
    (value : α) : IO Unit := do
  let raw := codec.encode value
  ensure s!"{label}: exact encoded length" (raw.length == width)
  match codec.decode raw with
  | .error error => throw (IO.userError s!"{label}: encoded value rejected: {repr error}")
  | .ok decoded => ensure s!"{label}: decode then canonical encode" (codec.encode decoded == raw)
  ensure s!"{label}: reject short"
    (match codec.decode (raw.drop 1) with
     | .error error => error == .invalidLength width (width - 1)
     | .ok _ => false)
  ensure s!"{label}: reject long"
    (match codec.decode (0 :: raw) with
     | .error error => error == .invalidLength width (width + 1)
     | .ok _ => false)

def checkSignatureBoundaries (label : String) (vp : ValidatedParams) : IO Unit := do
  let p := vp.params
  let atomic := byteCodec p
  let signature := markedSignature p
  let raw := encodeSignature vp atomic signature
  checkRoundTrip s!"{label}: signature" (signatureCodec vp atomic) signature
  ensureMarker s!"{label}: R" raw p.n (WireLayout.randomnessOffset p) 1
  for tree in List.range p.k do
    ensureMarker s!"{label}: FORS[{tree}].sk" raw
      p.n (WireLayout.forsSecretOffset p tree) (forsSecretTag p tree)
    for node in List.range p.a do
      ensureMarker s!"{label}: FORS[{tree}].auth[{node}]" raw
        p.n (WireLayout.forsAuthOffset p tree node) (forsAuthTag p tree node)
  for layer in List.range p.d do
    for chain in List.range p.len do
      ensureMarker s!"{label}: HT[{layer}].WOTS[{chain}]" raw
        p.n (WireLayout.wotsOffset p layer chain) (wotsTag p layer chain)
    for node in List.range p.hp do
      ensureMarker s!"{label}: HT[{layer}].auth[{node}]" raw
        p.n (WireLayout.xmssAuthOffset p layer node) (xmssAuthTag p layer node)

def checkKeyCodecs (label : String) (p : Params) : IO Unit := do
  let atomic := byteCodec p
  checkRoundTrip s!"{label}: public key" (publicKeyCodec atomic) (zeroPublicKey p)
  checkRoundTrip s!"{label}: secret key" (secretKeyCodec atomic) (zeroSecretKey p)
  let pk : PublicKeyCore (byteCore p) := ⟨markerBytes p.n 1, markerBytes p.n 2⟩
  let pkRaw := encodePublicKey atomic pk
  ensureMarker s!"{label}: PK.seed" pkRaw p.n 0 1
  ensureMarker s!"{label}: PK.root" pkRaw p.n p.n 2
  let sk : SecretKeyCore (byteCore p) :=
    ⟨markerBytes p.n 1, markerBytes p.n 2, markerBytes p.n 3, markerBytes p.n 4⟩
  let skRaw := encodeSecretKey atomic sk
  ensureMarker s!"{label}: SK.seed" skRaw p.n 0 1
  ensureMarker s!"{label}: SK.prf" skRaw p.n p.n 2
  ensureMarker s!"{label}: SK PK.seed" skRaw p.n (2 * p.n) 3
  ensureMarker s!"{label}: SK PK.root" skRaw p.n (3 * p.n) 4

def d1Params : Params :=
  { n := 1, h := 2, d := 1, hp := 2, a := 2, k := 2, lgw := 1 }

def d2Params : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 1 }

def d1 : ValidatedParams := ⟨d1Params, by decide⟩

def d2 : ValidatedParams := ⟨d2Params, by decide⟩

structure ExpectedRow where
  name : String
  n : ℕ
  d : ℕ
  hp : ℕ
  a : ℕ
  k : ℕ
  len : ℕ
  pk : ℕ
  sk : ℕ
  signature : ℕ
deriving Repr, BEq

def expectedRows : List ExpectedRow :=
  [⟨"SLH-DSA-SHA2-128s", 16, 7, 9, 12, 14, 35, 32, 64, 7856⟩,
   ⟨"SLH-DSA-SHA2-128f", 16, 22, 3, 6, 33, 35, 32, 64, 17088⟩,
   ⟨"SLH-DSA-SHA2-192s", 24, 7, 9, 14, 17, 51, 48, 96, 16224⟩,
   ⟨"SLH-DSA-SHA2-192f", 24, 22, 3, 8, 33, 51, 48, 96, 35664⟩,
   ⟨"SLH-DSA-SHA2-256s", 32, 8, 8, 14, 22, 67, 64, 128, 29792⟩,
   ⟨"SLH-DSA-SHA2-256f", 32, 17, 4, 9, 35, 67, 64, 128, 49856⟩,
   ⟨"SLH-DSA-SHAKE-128s", 16, 7, 9, 12, 14, 35, 32, 64, 7856⟩,
   ⟨"SLH-DSA-SHAKE-128f", 16, 22, 3, 6, 33, 35, 32, 64, 17088⟩,
   ⟨"SLH-DSA-SHAKE-192s", 24, 7, 9, 14, 17, 51, 48, 96, 16224⟩,
   ⟨"SLH-DSA-SHAKE-192f", 24, 22, 3, 8, 33, 51, 48, 96, 35664⟩,
   ⟨"SLH-DSA-SHAKE-256s", 32, 8, 8, 14, 22, 67, 64, 128, 29792⟩,
   ⟨"SLH-DSA-SHAKE-256f", 32, 17, 4, 9, 35, 67, 64, 128, 49856⟩]

def observedRows : List ExpectedRow := FipsParameterSet.all.map fun set =>
  let p := set.params
  ⟨set.name, p.n, p.d, p.hp, p.a, p.k, p.len,
    p.publicKeyBytes, p.secretKeyBytes, p.signatureBytes⟩

def testAllFipsSets : IO Unit := do
  ensure "all twelve independent FIPS width rows" (observedRows == expectedRows)
  for set in FipsParameterSet.all do
    let vp := set.validatedParams
    checkKeyCodecs set.name vp.params
    checkSignatureBoundaries set.name vp

/-! ## End-to-end over the real approved primitives

Honest keygen / sign / encode / decode / verify at the fast 128-bit profiles of both hash
families, driving the general scheme over `Concrete.approvedPrimitives` and crossing the byte
boundary through `Concrete.encodeApprovedSignature` / `Concrete.decodeApprovedSignature`. -/

instance : DecidableEq (Concrete.approvedPrimitives .SLHDSA_SHA2_128f).Y :=
  inferInstanceAs (DecidableEq (Bytes 16))

instance : DecidableEq (Concrete.approvedPrimitives .SLHDSA_SHAKE_128f).Y :=
  inferInstanceAs (DecidableEq (Bytes 16))

def seedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

def endToEndMessage : List Byte :=
  "FIPS 205 wire".toUTF8.toList

def checkApprovedEndToEnd (set : FipsParameterSet)
    [DecidableEq (Concrete.approvedPrimitives set).Y]
    (skSeed : (Concrete.approvedPrimitives set).SkSeed)
    (skPrf : (Concrete.approvedPrimitives set).SkPrf)
    (pkSeed : (Concrete.approvedPrimitives set).PkSeed)
    (addrnd : (Concrete.approvedPrimitives set).Y) : IO Unit := do
  let vp := set.validatedParams
  let prims := Concrete.approvedPrimitives set
  let (pk, sk) := GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed
  let sig := GeneralScheme.signInternal vp prims endToEndMessage sk addrnd
  ensure s!"{set.name}: honest signature verifies before the byte boundary"
    (GeneralScheme.verifyInternal vp prims endToEndMessage sig pk)
  let raw := Concrete.encodeApprovedSignature set sig
  ensure s!"{set.name}: exact FIPS signature width" (raw.length == set.params.signatureBytes)
  match Concrete.decodeApprovedSignature set raw with
  | .error error =>
      throw (IO.userError s!"{set.name}: honest wire signature rejected: {repr error}")
  | .ok decoded =>
      ensure s!"{set.name}: decoded wire signature verifies"
        (GeneralScheme.verifyInternal vp prims endToEndMessage decoded pk)
  ensure s!"{set.name}: tampered wire signature rejected as non-exact"
    (match Concrete.decodeApprovedSignature set (0 :: raw) with
     | .error _ => true
     | .ok _ => false)
  let flipped := raw.set 0 (raw.headD 0 ^^^ 0x01)
  ensure s!"{set.name}: same-length corrupted wire decodes but fails verification"
    (match Concrete.decodeApprovedSignature set flipped with
     | .error _ => false
     | .ok corrupted =>
         !(GeneralScheme.verifyInternal vp prims endToEndMessage corrupted pk))
  let pkRaw := Concrete.encodeApprovedPublicKey set pk
  ensure s!"{set.name}: exact FIPS public-key width"
    (pkRaw.length == set.params.publicKeyBytes)
  match Concrete.decodeApprovedPublicKey set pkRaw with
  | .error error =>
      throw (IO.userError s!"{set.name}: honest wire public key rejected: {repr error}")
  | .ok decodedPk =>
      ensure s!"{set.name}: signature verifies under the decoded wire public key"
        (GeneralScheme.verifyInternal vp prims endToEndMessage sig decodedPk)
  let skRaw := Concrete.encodeApprovedSecretKey set sk
  ensure s!"{set.name}: exact FIPS secret-key width"
    (skRaw.length == set.params.secretKeyBytes)
  match Concrete.decodeApprovedSecretKey set skRaw with
  | .error error =>
      throw (IO.userError s!"{set.name}: honest wire secret key rejected: {repr error}")
  | .ok decodedSk =>
      ensure s!"{set.name}: decoded secret key re-encodes canonically"
        (Concrete.encodeApprovedSecretKey set decodedSk == skRaw)
  IO.println s!"{set.name}: end-to-end keygen/sign/encode/decode/verify PASS \
    ({raw.length} signature bytes)"

def testApprovedEndToEnd : IO Unit := do
  checkApprovedEndToEnd .SLHDSA_SHA2_128f
    (seedBytes 16 1) (seedBytes 16 2) (seedBytes 16 3) (seedBytes 16 4)
  checkApprovedEndToEnd .SLHDSA_SHAKE_128f
    (seedBytes 16 1) (seedBytes 16 2) (seedBytes 16 3) (seedBytes 16 4)

def run : IO Unit := do
  checkKeyCodecs "d=1 canary" d1.params
  checkSignatureBoundaries "d=1 canary" d1
  checkKeyCodecs "d=2 canary" d2.params
  checkSignatureBoundaries "d=2 canary" d2
  testAllFipsSets
  testApprovedEndToEnd
  IO.println "SLH-DSA structured wire codecs: PASS \
    (d=1, d=2, all 12 FIPS sets, SHA2/SHAKE-128f end-to-end)"

end SLHDSA.DataCodecTests

def main : IO Unit := SLHDSA.DataCodecTests.run
