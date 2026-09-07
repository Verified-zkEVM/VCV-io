/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Concrete.Prehash

/-!
# SLH-DSA external-interface canaries

Direct boundary examples that distinguish the pure and pre-hash domains, context placement,
DER-OID placement, digest placement, and the required 255/256-byte rejection boundary. The
executable suite also pins the FIPS 205 Algorithm 19 line 2 deterministic randomizer
(`opt_rand = PK.seed`) across all twelve approved profiles and runs end-to-end
keygen→sign→verify round trips through the pinned deterministic external entry points for one
SHA2 and one SHAKE profile, including tamper, wrong-message, and verify-side overlong-context
rejections.
-/

public section

namespace SLHDSA.ExternalTest

open SLHDSA.External
open SLHDSA.Concrete.Prehash

def failingDescriptor : PrehashDescriptor where
  oidDer := [0x06, 0x01, 0x2a]
  outputLength := 2
  digest := fun _ => .error (.digestLengthMismatch 2 0)

def fixedDescriptor : PrehashDescriptor where
  oidDer := [0x06, 0x01, 0x2a]
  outputLength := 2
  digest := fun _ => .ok #v[0xaa, 0xbb]

structure ExpectedAlgorithm where
  algorithm : Algorithm
  name : String
  oidDer : List Byte
  outputLength : ℕ

def expectedAlgorithms : List ExpectedAlgorithm :=
  [⟨.sha2_224, "SHA2-224", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04], 28⟩,
   ⟨.sha2_256, "SHA2-256", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01], 32⟩,
   ⟨.sha2_384, "SHA2-384", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02], 48⟩,
   ⟨.sha2_512, "SHA2-512", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03], 64⟩,
   ⟨.sha2_512_224, "SHA2-512/224",
     [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x05], 28⟩,
   ⟨.sha2_512_256, "SHA2-512/256",
     [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x06], 32⟩,
   ⟨.sha3_224, "SHA3-224", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x07], 28⟩,
   ⟨.sha3_256, "SHA3-256", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x08], 32⟩,
   ⟨.sha3_384, "SHA3-384", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x09], 48⟩,
   ⟨.sha3_512, "SHA3-512", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0a], 64⟩,
   ⟨.shake128, "SHAKE-128", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b], 32⟩,
   ⟨.shake256, "SHAKE-256", [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c], 64⟩]

/-! A seeded canary pins the FIPS Algorithm 21 `(SK, PK)` adapter over the canonical internal
`(PK, SK)` convenience order. A regression that removes the swap changes both the type and value. -/
example (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    keygenWithSeeds vp prims skSeed skPrf pkSeed =
      let (pk, sk) := GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed
      (sk, pk) := by
  rfl

/-- Rejects a wrong pure domain byte or a missing empty-context length byte. -/
example : encodePureMessage [] [0xcc] = .ok [0x00, 0x00, 0xcc] := by
  decide

set_option maxRecDepth 2048 in
/-- The largest permitted context is accepted and contributes exactly 257 prefix bytes. -/
example : (encodePureMessage (List.replicate 255 0x7f) []).map List.length = .ok 257 := by
  decide

set_option maxRecDepth 2048 in
/-- The first forbidden context length is rejected with its observed size. -/
example : encodePureMessage (List.replicate 256 0x7f) [] = .error (.contextTooLong 256) := by
  decide

set_option maxRecDepth 2048 in
/-- Algorithm 23 rejects the context before evaluating even a failing pre-hash descriptor. -/
example : encodePrehashMessageWithDescriptor failingDescriptor
    (List.replicate 256 0x7f) [] = .error (.contextTooLong 256) := by
  decide

set_option maxRecDepth 2048 in
/-- The largest permitted pre-hash context remains accepted. -/
example : (encodePrehashMessageWithDescriptor fixedDescriptor
    (List.replicate 255 0x7f) []).map List.length = .ok 262 := by
  decide

set_option maxRecDepth 2048 in
/-- Context rejection also precedes the concrete strength-policy check. -/
example : SLHDSA.Concrete.Prehash.encodeMessage
    FipsParameterSet.SLHDSA_SHA2_256s.params .sha2_256 (List.replicate 256 0x7f) [] =
    .error (.contextTooLong 256) := by
  decide

/-- A category-5 parameter rejects the category-1 SHA-256 pre-hash before signing. -/
example : SLHDSA.Concrete.Prehash.encodeMessage
    FipsParameterSet.SLHDSA_SHA2_256s.params .sha2_256 [] [] =
    .error (.prehashTooWeak 32 32) := by
  decide

/-- Exact digest conversion fails closed rather than padding a short engine result. -/
example : digestBytesExact 2 (ByteArray.mk #[0xaa]) =
    .error (.digestLengthMismatch 2 1) := by
  decide

private def hexValue (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else 0

private def parseHex (hex : String) : ByteArray := Id.run do
  let chars := hex.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:chars.size / 2] do
    out := out.push (hexValue chars[2 * i]! <<< 4 ||| hexValue chars[2 * i + 1]!)
  return out

private def expectedAbc : Algorithm → String
  | .sha2_224 => "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
  | .sha2_256 => "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  | .sha2_384 =>
      "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed\
      8086072ba1e7cc2358baeca134c825a7"
  | .sha2_512 =>
      "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
      2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  | .sha2_512_224 => "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa"
  | .sha2_512_256 => "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23"
  | .sha3_224 => "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf"
  | .sha3_256 => "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
  | .sha3_384 =>
      "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b\
      298d88cea927ac7f539f1edf228376d25"
  | .sha3_512 =>
      "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e\
      10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
  | .shake128 => "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
  | .shake256 =>
      "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739\
      d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4"

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"SLH-DSA external-interface check failed: {label}")

/-! ## FIPS deterministic-variant pinning and pinned external round trips -/

private def testBytes (n offset : ℕ) : SLHDSA.Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (i.val * 7 + offset)

private def flip16 (bytes : SLHDSA.Bytes 16) : SLHDSA.Bytes 16 :=
  bytes.set 0 (bytes[0] ^^^ 0x01)

private def checkPin (set : FipsParameterSet)
    (seed : (SLHDSA.Concrete.approvedPrimitives set).PkSeed)
    (expected : SLHDSA.Bytes set.params.n) : Bool :=
  ((SLHDSA.Concrete.approvedPrimitives set).yToBytes
    (SLHDSA.Concrete.approvedRandomizerOfPkSeed set seed)).toList == expected.toList

/-- FIPS 205 Algorithm 19 line 2: the pinned deterministic randomizer's byte encoding is
exactly the `PK.seed` bytes, exercised through the set-level dispatch for each profile. -/
private def pinnedRandomizerAgrees : FipsParameterSet → Bool
  | .SLHDSA_SHA2_128s => checkPin .SLHDSA_SHA2_128s (testBytes 16 5) (testBytes 16 5)
  | .SLHDSA_SHA2_128f => checkPin .SLHDSA_SHA2_128f (testBytes 16 6) (testBytes 16 6)
  | .SLHDSA_SHA2_192s => checkPin .SLHDSA_SHA2_192s (testBytes 24 7) (testBytes 24 7)
  | .SLHDSA_SHA2_192f => checkPin .SLHDSA_SHA2_192f (testBytes 24 8) (testBytes 24 8)
  | .SLHDSA_SHA2_256s => checkPin .SLHDSA_SHA2_256s (testBytes 32 9) (testBytes 32 9)
  | .SLHDSA_SHA2_256f => checkPin .SLHDSA_SHA2_256f (testBytes 32 10) (testBytes 32 10)
  | .SLHDSA_SHAKE_128s => checkPin .SLHDSA_SHAKE_128s (testBytes 16 11) (testBytes 16 11)
  | .SLHDSA_SHAKE_128f => checkPin .SLHDSA_SHAKE_128f (testBytes 16 12) (testBytes 16 12)
  | .SLHDSA_SHAKE_192s => checkPin .SLHDSA_SHAKE_192s (testBytes 24 13) (testBytes 24 13)
  | .SLHDSA_SHAKE_192f => checkPin .SLHDSA_SHAKE_192f (testBytes 24 14) (testBytes 24 14)
  | .SLHDSA_SHAKE_256s => checkPin .SLHDSA_SHAKE_256s (testBytes 32 15) (testBytes 32 15)
  | .SLHDSA_SHAKE_256f => checkPin .SLHDSA_SHAKE_256f (testBytes 32 16) (testBytes 32 16)

/-- End-to-end keygen→sign→verify through the pinned deterministic external entry points
(pure Algorithm 22 and checked pre-hash Algorithm 23), with tampered-signature,
wrong-message, and verify-side overlong-context rejections. -/
private def roundTrip (label : String) (set : FipsParameterSet)
    (inst : DecidableEq (SLHDSA.Concrete.approvedPrimitives set).Y)
    (skSeed : (SLHDSA.Concrete.approvedPrimitives set).SkSeed)
    (skPrf : (SLHDSA.Concrete.approvedPrimitives set).SkPrf)
    (pkSeed : (SLHDSA.Concrete.approvedPrimitives set).PkSeed)
    (algorithm : Algorithm)
    (tamper : GeneralScheme.SignatureCore set.validatedParams
        (SLHDSA.Concrete.approvedPrimitives set).core →
      GeneralScheme.SignatureCore set.validatedParams
        (SLHDSA.Concrete.approvedPrimitives set).core) : IO Unit := do
  let vp := set.validatedParams
  let prims := SLHDSA.Concrete.approvedPrimitives set
  let message : List Byte := [0x4d, 0x53, 0x47]
  let wrongMessage : List Byte := [0x4d, 0x53, 0x58]
  let context : List Byte := [0xc0, 0xff]
  let longContext : List Byte := List.replicate 256 0x00
  let (sk, pk) := keygenWithSeeds vp prims skSeed skPrf pkSeed
  let pureSig ← match SLHDSA.Concrete.signPureDeterministicApproved set message context sk with
    | .error error => throw (IO.userError s!"{label}: pure pinned signing failed: {repr error}")
    | .ok signature => pure signature
  ensure s!"{label}: pure pinned sign/verify round trip"
    (@verifyPure vp prims inst message pureSig context pk)
  ensure s!"{label}: pure tampered-signature reject"
    (!(@verifyPure vp prims inst message (tamper pureSig) context pk))
  ensure s!"{label}: pure wrong-message reject"
    (!(@verifyPure vp prims inst wrongMessage pureSig context pk))
  ensure s!"{label}: pure overlong-context verify reject"
    (!(@verifyPure vp prims inst message pureSig longContext pk))
  let preSig ← match SLHDSA.Concrete.Prehash.signDeterministicApproved set algorithm
      message context sk with
    | .error error =>
        throw (IO.userError s!"{label}: prehash pinned signing failed: {repr error}")
    | .ok signature => pure signature
  ensure s!"{label}: prehash pinned sign/verify round trip"
    (@SLHDSA.Concrete.Prehash.verify vp prims inst algorithm message preSig context pk)
  ensure s!"{label}: prehash tampered-signature reject"
    (!(@SLHDSA.Concrete.Prehash.verify vp prims inst algorithm message
      (tamper preSig) context pk))
  ensure s!"{label}: prehash wrong-message reject"
    (!(@SLHDSA.Concrete.Prehash.verify vp prims inst algorithm wrongMessage preSig context pk))
  ensure s!"{label}: prehash overlong-context verify reject"
    (!(@SLHDSA.Concrete.Prehash.verify vp prims inst algorithm message preSig longContext pk))

private def checkDigest (label : String) (algorithm : Algorithm)
    (message : List Byte) (expected : String) : IO Unit := do
  match algorithm.digest message with
  | .error error => throw (IO.userError s!"{label}: unexpected digest error {repr error}")
  | .ok digest =>
      ensure label (ByteArray.mk digest.toArray == parseHex expected)

/-- Executable FIPS 180-4/FIPS 202 canaries for all twelve ACVP pre-hash choices, including
their exact DER OIDs and digest widths. -/
def run : IO Unit := do
  ensure "complete independent prehash menu"
    (SLHDSA.Concrete.Prehash.all == expectedAlgorithms.map (·.algorithm))
  ensure "prehash menu has no duplicates"
    (SLHDSA.Concrete.Prehash.all.eraseDups == SLHDSA.Concrete.Prehash.all)
  ensure "unknown prehash name rejected" (Algorithm.ofName? "SHA2-999" == none)
  ensure "prehash names are case-sensitive" (Algorithm.ofName? "sha2-256" == none)
  ensure "prehash names reject trailing bytes" (Algorithm.ofName? "SHA2-256 " == none)
  let encoded ← match SLHDSA.Concrete.Prehash.encodeMessage
      FipsParameterSet.SLHDSA_SHA2_128s.params
      .sha2_256 [0x10, 0x11] [0xff] with
    | .error error => throw (IO.userError s!"prehash encoding failed: {repr error}")
    | .ok value => pure value
  ensure "domain/context/OID order"
    (encoded.take 15 == [0x01, 0x02, 0x10, 0x11, 0x06, 0x09, 0x60, 0x86,
      0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01])
  ensure "digest placement"
    (ByteArray.mk (encoded.drop 15).toArray ==
      parseHex "a8100ae6aa1940d0b663bb31cd466142ebbdbd5187131b92d93818987832eb89")
  ensure "pure/prehash domain separation"
    (encodePureMessage [] [] !=
      SLHDSA.Concrete.Prehash.encodeMessage
        FipsParameterSet.SLHDSA_SHA2_128s.params .sha2_256 [] [])
  for row in expectedAlgorithms do
    let algorithm := row.algorithm
    ensure s!"{row.name}: exact ACVP name" (algorithm.name == row.name)
    ensure s!"{row.name}: exact parser binding" (Algorithm.ofName? row.name == some algorithm)
    ensure s!"{row.name}: complete DER OID" (algorithm.oidDer == row.oidDer)
    ensure s!"{row.name}: exact output width" (algorithm.outputLength == row.outputLength)
    checkDigest s!"{row.name}: abc digest" algorithm [0x61, 0x62, 0x63]
      (expectedAbc algorithm)
  ensure "SHA2-224 is below category 1"
    (!Algorithm.sha2_224.validFor FipsParameterSet.SLHDSA_SHA2_128s.params)
  ensure "SHA2-256 reaches category 1"
    (Algorithm.sha2_256.validFor FipsParameterSet.SLHDSA_SHA2_128s.params)
  ensure "SHA2-256 is below category 3"
    (!Algorithm.sha2_256.validFor FipsParameterSet.SLHDSA_SHA2_192s.params)
  ensure "SHA2-384 reaches category 3"
    (Algorithm.sha2_384.validFor FipsParameterSet.SLHDSA_SHA2_192s.params)
  ensure "SHA2-384 is below category 5"
    (!Algorithm.sha2_384.validFor FipsParameterSet.SLHDSA_SHA2_256s.params)
  ensure "SHA2-512 reaches category 5"
    (Algorithm.sha2_512.validFor FipsParameterSet.SLHDSA_SHA2_256s.params)
  ensure "SHAKE128 reaches category 1"
    (Algorithm.shake128.validFor FipsParameterSet.SLHDSA_SHAKE_128s.params)
  ensure "SHAKE128 is below category 3"
    (!Algorithm.shake128.validFor FipsParameterSet.SLHDSA_SHAKE_192s.params)
  ensure "SHAKE256 reaches category 5"
    (Algorithm.shake256.validFor FipsParameterSet.SLHDSA_SHAKE_256s.params)
  checkDigest "SHA3-224 exact-rate padding" .sha3_224 (List.replicate 144 0x61)
    "f9019111996dcf160e284e320fd6d8825cabcd41a5ffdc4c5e9d64b6"
  checkDigest "SHA3-384 exact-rate padding" .sha3_384 (List.replicate 104 0x61)
    "3a4f3b6284e571238884e95655e8c8a60e068e4059a9734abc08823a900d1615\
    92860243f00619ae699a29092ed91a16"
  checkDigest "SHA3-512 exact-rate padding" .sha3_512 (List.replicate 72 0x61)
    "a8ae722a78e10cbbc413886c02eb5b369a03f6560084aff566bd597bb7ad8c1c\
    cd86e81296852359bf2faddb5153c0a7445722987875e74287adac21adebe952"
  checkDigest "SHAKE128 exact-rate padding" .shake128 (List.replicate 168 0x61)
    "c22e11586c22b713bde373fce93314d76829de2c21d940a28eb659b8dec953a2"
  for set in FipsParameterSet.all do
    ensure s!"{set.name}: pinned deterministic randomizer equals PK.seed bytes"
      (pinnedRandomizerAgrees set)
  roundTrip "SLH-DSA-SHA2-128f" .SLHDSA_SHA2_128f
    (inferInstanceAs (DecidableEq (SLHDSA.Bytes 16))) (testBytes 16 1) (testBytes 16 2)
    (testBytes 16 3) .sha2_256 (fun sig => { sig with randomness := flip16 sig.randomness })
  roundTrip "SLH-DSA-SHAKE-128f" .SLHDSA_SHAKE_128f
    (inferInstanceAs (DecidableEq (SLHDSA.Bytes 16))) (testBytes 16 1) (testBytes 16 2)
    (testBytes 16 3) .shake128 (fun sig => { sig with randomness := flip16 sig.randomness })
  IO.println "SLH-DSA external-interface tests: PASS (12 bound OIDs/digests; strength/context; \
    12 pinned opt_rand = PK.seed profiles; SHA2-128f and SHAKE-128f pinned round trips)"

end SLHDSA.ExternalTest

def main : IO Unit := SLHDSA.ExternalTest.run
