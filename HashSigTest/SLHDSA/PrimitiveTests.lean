/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import Lean.Data.Json.Parser

/-!
# S04 SHA2, SHAKE, and SLH-DSA primitive tests

Runtime checks for the pinned NIST SHA-2, HMAC, and SHAKE examples, derived RFC 8017 MGF1
regressions, the SHA2 rejecting address boundary, and exact FIPS 205 Section 11 grammar
fingerprints for all twelve approved profiles. See `PrimitiveVectors/vectors.json` for exact
source hashes, case identifiers, evidence classification, and expected bytes.
-/

public section

namespace SLHDSA.PrimitiveTests

open SLHDSA.Concrete
open SLHDSA.Concrete.Sha2
open SLHDSA.Concrete.Keccak

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

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"S04 primitive check failed: {label}")

private def checkHex (label : String) (actual : ByteArray) (expected : String) : IO Unit :=
  ensure label (actual == parseHex expected)

private abbrev JsonObject := Std.TreeMap.Raw String Lean.Json compare

private def jsonField (label : String) (object : JsonObject) (key : String) :
    Except String Lean.Json :=
  match object.get? key with
  | some value => .ok value
  | none => .error s!"{label}: missing field {key}"

private def projectionOutput (root : Lean.Json) (id : String) : Except String String := do
  let rootObject ← root.getObj?
  let vectorsObject ← (← jsonField "root" rootObject "vectors").getObj?
  let shakeCases ← (← jsonField "vectors" vectorsObject "shake256").getArr?
  for value in shakeCases do
    let object ← value.getObj?
    if let some idValue := object.get? "id" then
      if (← idValue.getStr?) = id then
        return ← (← jsonField id object "output").getStr?
  throw s!"SHAKE projection case absent: {id}"

private def shakeEmpty272Expected : String :=
  "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4dd\
    d8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be141e96616fb13957\
    692cc7edd0b45ae3dc07223c8e92937bef84bc0eab862853349ec75546f58fb7c2775c38\
    462c5010d846c185c15111e595522a6bcd16cf86f3d122109e3b1fdd943b6aec468a2d6\
    21a7c06c6a957c62b54dafc3be87567d677231395f6147293b68ceab7a9e0c58d864e8e\
    fde4e1b9a46cbe854713672f5caaae314ed9083dab4b099f8e300f01b8650f1f4b1d8f\
    cf3f3cb53fb8e9eb2ea203bdc970f50ae55428a91f7f53ac266b28419c3778a15fd248\
    d339ede785fb7f5a1aaa96d313eacc890936c173cdcd0f"

private def shakeA61In135Expected : String :=
  "55b991ece1e567b6e7c2c714444dd201cd51f4f3832d08e1d26bebc63e07a3d7"

private def shakeA61In136Expected : String :=
  "8fcc5a08f0a1f6827c9cf64ee8d16e0443106359ca6c8efd230759256f44996a"

private def shakeA61In137Expected : String :=
  "a44e1a438dad6273d540be65ee26386c59588efb09139dc086385d2db0c25782"

private def testProjection : IO Unit := do
  let source ← IO.FS.readFile "HashSigTest/SLHDSA/PrimitiveVectors/vectors.json"
  checkHex "primitive projection byte pin" (sha256 source.toUTF8)
    "a2d86492e31ca719827b780f5b3f9ef0ef4a59694c478f9f58c8567389bba570"
  let root ← match Lean.Json.parse source with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"primitive projection JSON rejected: {error}")
  let check (id expected : String) : IO Unit :=
    match projectionOutput root id with
    | .ok projected => ensure s!"projection/runtime agreement {id}" (projected == expected)
    | .error error => throw (IO.userError error)
  check "shake256-empty-out272" shakeEmpty272Expected
  check "shake256-a61-in135-out32" shakeA61In135Expected
  check "shake256-a61-in136-out32" shakeA61In136Expected
  check "shake256-a61-in137-out32" shakeA61In137Expected

private def sequence (start count : ℕ) : ByteArray :=
  ByteArray.mk ((List.range count).map fun i => (start + i).toUInt8).toArray

private def sequenceBytes (start count : ℕ) : Bytes count :=
  Vector.ofFn fun i : Fin count => (start + i.val).toUInt8

def testSha2 : IO Unit := do
  checkHex "SHA-224 abc" (sha224 "abc".toUTF8)
    "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
  checkHex "SHA-224 55-byte padding neighbor"
    (sha224 (ByteArray.mk (Array.replicate 55 0x61)))
    "fb0bd626a70c28541dfa781bb5cc4d7d7f56622a58f01a0b1ddd646f"
  checkHex "SHA-224 56-byte padding neighbor"
    (sha224 (ByteArray.mk (Array.replicate 56 0x61)))
    "d40854fc9caf172067136f2e29e1380b14626bf6f0dd06779f820dcd"
  checkHex "SHA-256 empty" (sha256 ByteArray.empty)
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  checkHex "SHA-256 55-byte padding neighbor"
    (sha256 (parseHex
      "3ebfb06db8c38d5ba037f1363e118550aad94606e26835a01af05078533cc25f2f39573c\
        04b632f62f68c294ab31f2a3e2a1a0d8c2be51"))
    "6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4"
  checkHex "SHA-256 56-byte padding neighbor"
    (sha256 (parseHex
      "2d52447d1244d2ebc28650e7b05654bad35b3a68eedc7f8515306b496d75f3e73385dd1\
        b002625024b81a02f2fd6dffb6e6d561cb7d0bd7a"))
    "cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360"
  checkHex "SHA-256 64-byte message"
    (sha256 (parseHex
      "5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547\
        208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509"))
    "42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa"
  checkHex "SHA-512 empty" (sha512 ByteArray.empty)
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c\
      5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
  checkHex "SHA-512 111-byte padding neighbor"
    (sha512 (parseHex
      "324533e685f1852e358eea8ea8b81c288b3f3beb1f2bc2b8d3fdbac318382e3d7120de3\
        0c9c237aa0a34831deb1e5e060a7969cd3a9742ec1e64b354f7eb290cba1c681c66cc7ea9\
        94fdf5614f604d1a2718aab581c1c94931b1387e4b7dc73635bf3a7301174075fa70a9227\
        d85d3"))
    "3b26c5170729d0814153becb95f1b65cd42f9a6d0649d914e4f69d938b5e9dc041cd0f5c\
      8da0b484d7c7bc7b1bdefb08fe8b1bfedc81109345bc9e9a399feedf"
  checkHex "SHA-512 112-byte padding neighbor"
    (sha512 (parseHex
      "518985977ee21d2bf622a20567124fcbf11c72df805365835ab3c041f4a9cd8a0ad63c9d\
        ee1018aa21a9fa3720f47dc48006f1aa3dba544950f87e627f369bc2793ede21223274492c\
        ceb77be7eea50e5a509059929a16d33a9f54796cde5770c74bd3ecc25318503f1a419764\
        07aff2"))
    "c00926a374cde55b8fbd77f50da1363da19744d3f464e07ce31794c5a61b6f9c85689fa\
      1cfe136553527fd876be91673c2cac2dd157b2defea360851b6d92cf4"
  checkHex "SHA-512 128-byte message"
    (sha512 (parseHex
      "fd2203e467574e834ab07c9097ae164532f24be1eb5d88f1af7748ceff0d2c67a21f4e40\
        97f9d3bb4e9fbf97186e0db6db0100230a52b453d421f8ab9c9a6043aa3295ea20d2f06a\
        2f37470d8a99075f1b8a8336f6228cf08b5942fc1fb4299c7d2480e8e82bce175540bdfa\
        d7752bc95b577f229515394f3ae5cec870a4b2f8"))
    "a21b1077d52b27ac545af63b32746c6e3c51cb0cb9f281eb9f3580a6d4996d5c9917d2\
      a6e484627a9d5a06fa1b25327a9d710e027387fc3e07d7c4d14c6086cc"
  checkHex "SHA-384 abc" (sha384 "abc".toUTF8)
    "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed\
      8086072ba1e7cc2358baeca134c825a7"
  checkHex "SHA-384 111-byte padding neighbor"
    (sha384 (ByteArray.mk (Array.replicate 111 0x61)))
    "3c37955051cb5c3026f94d551d5b5e2ac38d572ae4e07172085fed81f8466b8f\
      90dc23a8ffcdea0b8d8e58e8fdacc80a"
  checkHex "SHA-384 112-byte padding neighbor"
    (sha384 (ByteArray.mk (Array.replicate 112 0x61)))
    "187d4e07cb306103c69967bf544d0dfbe9042577599c73c330abc0cb64c61236\
      d5ed565ee19119d8c31779a38f791fcd"
  checkHex "SHA-512/224 abc" (sha512_224 "abc".toUTF8)
    "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa"
  checkHex "SHA-512/224 111-byte padding neighbor"
    (sha512_224 (ByteArray.mk (Array.replicate 111 0x61)))
    "3ebe1b48e8c66acb9ae014db95b4bec93de7e9572bff41cf566bd7d0"
  checkHex "SHA-512/224 112-byte padding neighbor"
    (sha512_224 (ByteArray.mk (Array.replicate 112 0x61)))
    "79b41fef2a0439d2705724a67615f7bcbcd2bf5664a7774b80818eb6"
  checkHex "SHA-512/256 abc" (sha512_256 "abc".toUTF8)
    "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23"
  checkHex "SHA-512/256 111-byte padding neighbor"
    (sha512_256 (ByteArray.mk (Array.replicate 111 0x61)))
    "0239e429f98d0ed61ee8e2a7c30afe98c1c3a80ce5dff62a107e9c538f7632ce"
  checkHex "SHA-512/256 112-byte padding neighbor"
    (sha512_256 (ByteArray.mk (Array.replicate 112 0x61)))
    "9216b5303edb66504570bee90e48ea5beaa5e9fe9f760bbd3e0460559fc005f6"
  ensure "SHA-256 length lower bound" (sha256InputLengthValid (2 ^ 61 - 1))
  ensure "SHA-256 length rejection boundary" (!sha256InputLengthValid (2 ^ 61))
  ensure "SHA-512 length lower bound" (sha512InputLengthValid (2 ^ 125 - 1))
  ensure "SHA-512 length rejection boundary" (!sha512InputLengthValid (2 ^ 125))

def testHmacAndMgf : IO Unit := do
  checkHex "HMAC-SHA-256 short key"
    (hmacSha256 (sequence 0 32) "Sample message for keylen<blocklen".toUTF8)
    "a28cf43130ee696a98f14a37678b56bcfcbdd9e5cf69717fecf5480f0ebdf790"
  checkHex "HMAC-SHA-256 hash-then-pad long key"
    (hmacSha256 (sequence 0 100) "Sample message for keylen=blocklen".toUTF8)
    "bdccb6c72ddeadb500ae768386cb38cc41c63dbb0878ddb9c7a38a431b78378d"
  checkHex "HMAC-SHA-512 short key"
    (hmacSha512 (sequence 0 64) "Sample message for keylen<blocklen".toUTF8)
    "fd44c18bda0bb0a6ce0e82b031bf2818f6539bd56ec00bdc10a8a2d730b3634de2545d63\
      9b0f2cf710d0692c72a1896f1f211c2b922d1a96c392e07e7ea9fedc"
  checkHex "HMAC-SHA-512 hash-then-pad long key"
    (hmacSha512 (sequence 0 200) "Sample message for keylen=blocklen".toUTF8)
    "d93ec8d2de1ad2a9957cb9b83f14e76ad6b5e0cce285079a127d3b14bccb7aa7286d4ac0\
      d4ce64215f2bc9e6870b33d97438be4aaa20cda5c5a912b48b8e27f3"
  ensure "MGF1-SHA-256 zero output" (mgf1Sha256 "abc".toUTF8 0 == ByteArray.empty)
  checkHex "MGF1-SHA-256 counter/truncation"
    (mgf1Sha256 "abc".toUTF8 33)
    "cf2db1ac9867debdf8ce91f99f141e5544bf26ca36b3fd4f8e4035eec42cab0d46"
  ensure "MGF1-SHA-512 zero output" (mgf1Sha512 "abc".toUTF8 0 == ByteArray.empty)
  checkHex "MGF1-SHA-512 counter/truncation"
    (mgf1Sha512 "abc".toUTF8 65)
    "7231a01ead7829a9af72bc1022b1021d69302e97d7888bf7e06e00dee9826108b5a092e9e\
      ca7623bde11f0486e3d47c64e78754d9277e6d689557a75b6be7a8bf7"
  ensure "MGF1-SHA-256 rejects counter wrap"
    (mgf1Sha256Checked ByteArray.empty (mgf1Sha256Maximum + 1) ==
      .error (.maskTooLong "MGF1-SHA-256" (mgf1Sha256Maximum + 1) mgf1Sha256Maximum))
  ensure "MGF1-SHA-512 rejects counter wrap"
    (mgf1Sha512Checked ByteArray.empty (mgf1Sha512Maximum + 1) ==
      .error (.maskTooLong "MGF1-SHA-512" (mgf1Sha512Maximum + 1) mgf1Sha512Maximum))

def testShake : IO Unit := do
  checkHex "SHA3-224 abc" (sha3_224 "abc".toUTF8)
    "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf"
  checkHex "SHA3-224 exact-rate padding"
    (sha3_224 (ByteArray.mk (Array.replicate 144 0x61)))
    "f9019111996dcf160e284e320fd6d8825cabcd41a5ffdc4c5e9d64b6"
  checkHex "SHA3-384 abc" (sha3_384 "abc".toUTF8)
    "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b\
      298d88cea927ac7f539f1edf228376d25"
  checkHex "SHA3-384 exact-rate padding"
    (sha3_384 (ByteArray.mk (Array.replicate 104 0x61)))
    "3a4f3b6284e571238884e95655e8c8a60e068e4059a9734abc08823a900d1615\
      92860243f00619ae699a29092ed91a16"
  checkHex "SHA3-512 abc" (sha3_512 "abc".toUTF8)
    "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e\
      10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
  checkHex "SHA3-512 exact-rate padding"
    (sha3_512 (ByteArray.mk (Array.replicate 72 0x61)))
    "a8ae722a78e10cbbc413886c02eb5b369a03f6560084aff566bd597bb7ad8c1c\
      cd86e81296852359bf2faddb5153c0a7445722987875e74287adac21adebe952"
  checkHex "SHAKE128 abc 32" (shake128 "abc".toUTF8 32)
    "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
  checkHex "SHAKE128 exact-rate padding"
    (shake128 (ByteArray.mk (Array.replicate 168 0x61)) 32)
    "c22e11586c22b713bde373fce93314d76829de2c21d940a28eb659b8dec953a2"
  checkHex "SHAKE128 multi-block squeeze 200" (shake128 ByteArray.empty 200)
    "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef263cb1eea\
      988004b93103cfb0aeefd2a686e01fa4a58e8a3639ca8a1e3f9ae57e235b8cc873c23d\
      c62b8d260169afa2f75ab916a58d974918835d25e6a435085b2badfd6dfaac359a5efbb\
      7bcc4b59d538df9a04302e10c8bc1cbf1a0b3a5120ea17cda7cfad765f5623474d368c\
      cca8af0007cd9f5e4c849f167a580b14aabdefaee7eef47cb0fca9767be1fda69419dfb\
      927e9df07348b196691abaeb580b32def58538b8d23f877"
  checkHex "SHAKE256 empty 32"
    (shake256 ByteArray.empty 32)
    "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
  let empty137 :=
    "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4dd\
      d8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be141e96616fb13957\
      692cc7edd0b45ae3dc07223c8e92937bef84bc0eab862853349ec75546f58fb7c2775c38\
      462c5010d846c185c15111e595522a6bcd16cf86f3d122109e3b1fdd94"
  checkHex "SHAKE256 squeeze 135" (shake256 ByteArray.empty 135)
    (empty137.take (2 * 135)).toString
  checkHex "SHAKE256 squeeze 136" (shake256 ByteArray.empty 136)
    (empty137.take (2 * 136)).toString
  checkHex "SHAKE256 squeeze 137 rate crossing" (shake256 ByteArray.empty 137) empty137
  checkHex "SHAKE256 squeeze 272 two blocks" (shake256 ByteArray.empty 272)
    shakeEmpty272Expected
  checkHex "SHAKE256 1600-bit absorb"
    (shake256 (ByteArray.mk (Array.replicate 200 0xa3)) 64)
    "cd8a920ed141aa0407a22d59288652e9d9f1a7ee0c1e7c1ca699424da84a904d2d700caae\
      7396ece96604440577da4f3aa22aeb8857f961c4cd8e06f0ae6610b"
  checkHex "SHAKE256 absorb 135"
    (shake256 (ByteArray.mk (Array.replicate 135 0x61)) 32)
    shakeA61In135Expected
  checkHex "SHAKE256 absorb 136"
    (shake256 (ByteArray.mk (Array.replicate 136 0x61)) 32)
    shakeA61In136Expected
  checkHex "SHAKE256 absorb 137"
    (shake256 (ByteArray.mk (Array.replicate 137 0x61)) 32)
    shakeA61In137Expected
  ensure "SHAKE domain differs from SHA3" (shake256 ByteArray.empty 32 != sha3_256 ByteArray.empty)
  ensure "SHAKE domain differs from Ethereum Keccak"
    (shake256 ByteArray.empty 32 != keccak256 ByteArray.empty)

private def profileAddress : Adrs :=
  { layer := 7, tree := 0x0102030405060708, type := AddrType.forsTree.toCode,
    word1 := 1, word2 := 2, word3 := 3 }

private def profileExpected : FipsParameterSet → String
  | .SLHDSA_SHA2_128s => "126bdad7c0379199d768a61d767412a505785bfe348f013e97720384938e661e"
  | .SLHDSA_SHAKE_128s => "8c5c29c4ecfd8be0f2ab778a4d869846d3861b6a6639e6c54e9be8c66334bf3e"
  | .SLHDSA_SHA2_128f => "a70faae3a69a68a6dec37a659dc1c48baf005f868eb2a58a6dcb00a25f927bed"
  | .SLHDSA_SHAKE_128f => "d7d0222381c39e6ade4aa762907e9b31eda867b7a0428deafa12a7e20e220718"
  | .SLHDSA_SHA2_192s => "ad1bbec52bed4cb9ba363f500a484e75aa34412aef409ae6384bd0657622ac88"
  | .SLHDSA_SHAKE_192s => "1c6edf520ce447cef2b03cb676177efb882425d2489ea0f7f1ff3544c4da2a30"
  | .SLHDSA_SHA2_192f => "4bf0c27c23b639d49a0334550af4eba4f27db1a22add231f8579b2d3c79a95e5"
  | .SLHDSA_SHAKE_192f => "010573b253a885bcea685fb26c9b5aa7be0dec697412a3d6bb427fdf75f90cdc"
  | .SLHDSA_SHA2_256s => "412034667c7f084546c39cd6ee7b1426cf32705cff083e8dc41a2bb157aac89f"
  | .SLHDSA_SHAKE_256s => "5b7baf6c7e135155a66636c6670b55a68a1b54981cd903d265599f1af1780256"
  | .SLHDSA_SHA2_256f => "9352f0249a322a2a1397fcfd1cfca97200d1aefba55a083587cf42988e72c73b"
  | .SLHDSA_SHAKE_256f => "56217933da0de7175fed5d132c030717eea4cc9d9b827ae3e234bce79a0973d8"

private def profileOutputsWith (p : Params)
    (f : Bytes p.n → Adrs → Bytes p.n → Bytes p.n)
    (h : Bytes p.n → Adrs → Bytes p.n → Bytes p.n → Bytes p.n)
    (tlHash : Bytes p.n → Adrs → List (Bytes p.n) → Bytes p.n)
    (prf : Bytes p.n → Bytes p.n → Adrs → Bytes p.n)
    (prfMsg : Bytes p.n → Bytes p.n → List Byte → Bytes p.n)
    (hMsg : Bytes p.n → Bytes p.n → Bytes p.n → List Byte → Bytes p.m) : ByteArray :=
  let pkSeed := sequenceBytes 0 p.n
  let skSeed := sequenceBytes 0x20 p.n
  let pkRoot := sequenceBytes 0x40 p.n
  let randomizer := sequenceBytes 0x60 p.n
  let optRand := sequenceBytes 0x80 p.n
  let left := sequenceBytes 0xc0 p.n
  let right := sequenceBytes 0xe0 p.n
  let tl := [sequenceBytes 0xc0 p.n, sequenceBytes 0xd0 p.n, sequenceBytes 0xe0 p.n]
  let message : List Byte := [0xde, 0xad, 0xbe, 0xef, 0, 1]
  let append (out : ByteArray) (value : Bytes p.n) := out ++ bytesToByteArray value
  append (append (append (append (append ByteArray.empty
    (f pkSeed profileAddress left))
    (h pkSeed profileAddress left right))
    (tlHash pkSeed profileAddress tl))
    (prf pkSeed skSeed profileAddress))
    (prfMsg skSeed optRand message) ++
    bytesToByteArray (hMsg randomizer pkSeed pkRoot message)

/-- Exercise the six operations through the exact bundle exported for each approved profile.
Keeping this selector exhaustive makes a mutation in either the family dispatch or any bundle
field observable in the profile fingerprint. The fingerprints were generated with independent
tooling (a from-spec Python implementation of §11) but by the same authorship pipeline, so
they guard against implementation drift rather than a shared misreading of the standard;
reference-implementation ACVP cross-checks are the KAT slice's responsibility. -/
private def profileOutputs : FipsParameterSet → ByteArray
  | .SLHDSA_SHA2_128s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_128s)
      (approvedPrimitives .SLHDSA_SHA2_128s).F (approvedPrimitives .SLHDSA_SHA2_128s).H
      (approvedPrimitives .SLHDSA_SHA2_128s).Tl (approvedPrimitives .SLHDSA_SHA2_128s).PRF
      (approvedPrimitives .SLHDSA_SHA2_128s).PRFmsg (approvedPrimitives .SLHDSA_SHA2_128s).Hmsg
  | .SLHDSA_SHAKE_128s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_128s)
      (approvedPrimitives .SLHDSA_SHAKE_128s).F (approvedPrimitives .SLHDSA_SHAKE_128s).H
      (approvedPrimitives .SLHDSA_SHAKE_128s).Tl (approvedPrimitives .SLHDSA_SHAKE_128s).PRF
      (approvedPrimitives .SLHDSA_SHAKE_128s).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_128s).Hmsg
  | .SLHDSA_SHA2_128f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_128f)
      (approvedPrimitives .SLHDSA_SHA2_128f).F (approvedPrimitives .SLHDSA_SHA2_128f).H
      (approvedPrimitives .SLHDSA_SHA2_128f).Tl (approvedPrimitives .SLHDSA_SHA2_128f).PRF
      (approvedPrimitives .SLHDSA_SHA2_128f).PRFmsg (approvedPrimitives .SLHDSA_SHA2_128f).Hmsg
  | .SLHDSA_SHAKE_128f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_128f)
      (approvedPrimitives .SLHDSA_SHAKE_128f).F (approvedPrimitives .SLHDSA_SHAKE_128f).H
      (approvedPrimitives .SLHDSA_SHAKE_128f).Tl (approvedPrimitives .SLHDSA_SHAKE_128f).PRF
      (approvedPrimitives .SLHDSA_SHAKE_128f).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_128f).Hmsg
  | .SLHDSA_SHA2_192s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_192s)
      (approvedPrimitives .SLHDSA_SHA2_192s).F (approvedPrimitives .SLHDSA_SHA2_192s).H
      (approvedPrimitives .SLHDSA_SHA2_192s).Tl (approvedPrimitives .SLHDSA_SHA2_192s).PRF
      (approvedPrimitives .SLHDSA_SHA2_192s).PRFmsg (approvedPrimitives .SLHDSA_SHA2_192s).Hmsg
  | .SLHDSA_SHAKE_192s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_192s)
      (approvedPrimitives .SLHDSA_SHAKE_192s).F (approvedPrimitives .SLHDSA_SHAKE_192s).H
      (approvedPrimitives .SLHDSA_SHAKE_192s).Tl (approvedPrimitives .SLHDSA_SHAKE_192s).PRF
      (approvedPrimitives .SLHDSA_SHAKE_192s).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_192s).Hmsg
  | .SLHDSA_SHA2_192f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_192f)
      (approvedPrimitives .SLHDSA_SHA2_192f).F (approvedPrimitives .SLHDSA_SHA2_192f).H
      (approvedPrimitives .SLHDSA_SHA2_192f).Tl (approvedPrimitives .SLHDSA_SHA2_192f).PRF
      (approvedPrimitives .SLHDSA_SHA2_192f).PRFmsg (approvedPrimitives .SLHDSA_SHA2_192f).Hmsg
  | .SLHDSA_SHAKE_192f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_192f)
      (approvedPrimitives .SLHDSA_SHAKE_192f).F (approvedPrimitives .SLHDSA_SHAKE_192f).H
      (approvedPrimitives .SLHDSA_SHAKE_192f).Tl (approvedPrimitives .SLHDSA_SHAKE_192f).PRF
      (approvedPrimitives .SLHDSA_SHAKE_192f).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_192f).Hmsg
  | .SLHDSA_SHA2_256s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_256s)
      (approvedPrimitives .SLHDSA_SHA2_256s).F (approvedPrimitives .SLHDSA_SHA2_256s).H
      (approvedPrimitives .SLHDSA_SHA2_256s).Tl (approvedPrimitives .SLHDSA_SHA2_256s).PRF
      (approvedPrimitives .SLHDSA_SHA2_256s).PRFmsg (approvedPrimitives .SLHDSA_SHA2_256s).Hmsg
  | .SLHDSA_SHAKE_256s => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_256s)
      (approvedPrimitives .SLHDSA_SHAKE_256s).F (approvedPrimitives .SLHDSA_SHAKE_256s).H
      (approvedPrimitives .SLHDSA_SHAKE_256s).Tl (approvedPrimitives .SLHDSA_SHAKE_256s).PRF
      (approvedPrimitives .SLHDSA_SHAKE_256s).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_256s).Hmsg
  | .SLHDSA_SHA2_256f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHA2_256f)
      (approvedPrimitives .SLHDSA_SHA2_256f).F (approvedPrimitives .SLHDSA_SHA2_256f).H
      (approvedPrimitives .SLHDSA_SHA2_256f).Tl (approvedPrimitives .SLHDSA_SHA2_256f).PRF
      (approvedPrimitives .SLHDSA_SHA2_256f).PRFmsg (approvedPrimitives .SLHDSA_SHA2_256f).Hmsg
  | .SLHDSA_SHAKE_256f => profileOutputsWith (FipsParameterSet.params .SLHDSA_SHAKE_256f)
      (approvedPrimitives .SLHDSA_SHAKE_256f).F (approvedPrimitives .SLHDSA_SHAKE_256f).H
      (approvedPrimitives .SLHDSA_SHAKE_256f).Tl (approvedPrimitives .SLHDSA_SHAKE_256f).PRF
      (approvedPrimitives .SLHDSA_SHAKE_256f).PRFmsg (approvedPrimitives .SLHDSA_SHAKE_256f).Hmsg

def testAddressAndProfiles : IO Unit := do
  ensure "fixed-width primitive projection rejects short input"
    (byteArrayPrefixChecked (ByteArray.mk #[0xaa]) 2 == .error (.invalidLength 2 1))
  ensure "profile address canonical" profileAddress.isCanonical
  match Sha2Address.ofAdrs profileAddress with
  | .error _ => throw (IO.userError "S04 primitive check failed: valid SHA2 address rejected")
  | .ok checked =>
      ensure "checked and concrete ADRSc agree"
        (checked.bytes.toList == profileAddress.compressSha2)
  let wideLayer := { profileAddress with layer := 256 }
  ensure "SHA2 adapter rejects wide layer"
    (match Sha2Address.ofAdrs wideLayer with
     | .error error => error == .outOfRange 1 256
     | .ok _ => false)
  let wideTree := { profileAddress with tree := 256 ^ 8 }
  ensure "SHA2 adapter rejects wide tree"
    (match Sha2Address.ofAdrs wideTree with
     | .error error => error == .outOfRange 8 (256 ^ 8)
     | .ok _ => false)
  let noncanonical := { profileAddress with type := AddrType.wotsPk.toCode, word2 := 1 }
  ensure "SHA2 adapter rejects noncanonical layout"
    (match Sha2Address.ofAdrs noncanonical with
     | .error error => error == .noncanonicalAddress
     | .ok _ => false)
  for set in FipsParameterSet.all do
    let outputs := profileOutputs set
    ensure s!"six output widths {set.name}"
      (outputs.size == 5 * set.params.n + set.params.m)
    checkHex s!"six exact grammars {set.name}" (sha256 outputs) (profileExpected set)

def run : IO Unit := do
  testProjection
  testSha2
  testHmacAndMgf
  testShake
  testAddressAndProfiles
  IO.println "SLH-DSA S04 primitive tests: PASS (SHA2/SHAKE vectors; 12 profile grammars)"

end SLHDSA.PrimitiveTests

def main : IO Unit := SLHDSA.PrimitiveTests.run
