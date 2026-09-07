/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Encoding

/-!
# Pure-Lean SHA-2 with MGF1 and HMAC

Executable, FFI-free SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256 over
`ByteArray`, together with the SHA-256 and SHA-512 variants of
MGF1 (RFC 8017 B.2.1) and HMAC (FIPS 198-1). The SLH-DSA SHA2 instantiations select these
functions exactly as prescribed by FIPS 205 Sections 11.2.1 and 11.2.2.

Arithmetic is `UInt32`, `UInt64`, and `UInt8`, with the required wrapping semantics; words and
length fields are big-endian.

## References

- FIPS 180-4 (SHA-256 and SHA-512), FIPS 198-1 (HMAC), RFC 8017 §B.2.1 (MGF1)
-/

@[expose] public section


namespace SLHDSA.Concrete.Sha2

/-- The eight SHA-256 initial hash values `H₀…H₇`. -/
def iv : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The eight SHA-224 initial hash values. -/
def iv224 : Array UInt32 :=
  #[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
    0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

/-- The 64 SHA-256 round constants `K₀…K₆₃`. -/
def k : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Right rotation of a 32-bit word. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- `Ch(x,y,z) = (x∧y) ⊕ (¬x∧z)`. -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x,y,z) = (x∧y) ⊕ (x∧z) ⊕ (y∧z)`. -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀(x)`. -/
def bsig0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
/-- `Σ₁(x)`. -/
def bsig1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
/-- `σ₀(x)`. -/
def ssig0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
/-- `σ₁(x)`. -/
def ssig1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Big-endian 4-byte serialization of a 32-bit word. -/
def u32be (x : UInt32) : ByteArray :=
  ByteArray.mk #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- Big-endian 8-byte serialization of a 64-bit word. -/
def u64be (x : UInt64) : ByteArray :=
  ByteArray.mk #[(x >>> 56).toUInt8, (x >>> 48).toUInt8, (x >>> 40).toUInt8, (x >>> 32).toUInt8,
    (x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- SHA-256 padding (FIPS 180-4 §5.1.1): append `0x80`, zero-pad, then the 64-bit big-endian
bit length, to a multiple of 64 bytes. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let bitLen : UInt64 := (len.toUInt64) * 8
  let mut out := msg.push 0x80
  let zeros := (56 + 64 - (len + 1) % 64) % 64
  for _ in [0:zeros] do
    out := out.push 0
  return out ++ u64be bitLen

/-- Process one 64-byte block at offset `base`, updating the 8-word state `st`. -/
def compress (st : Array UInt32) (m : ByteArray) (base : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for t in [0:16] do
    let o := base + t * 4
    let word : UInt32 :=
      (m[o]!).toUInt32 <<< 24 ||| (m[o + 1]!).toUInt32 <<< 16 |||
        (m[o + 2]!).toUInt32 <<< 8 ||| (m[o + 3]!).toUInt32
    w := w.set! t word
  for t in [16:64] do
    w := w.set! t (ssig1 (w[t - 2]!) + w[t - 7]! + ssig0 (w[t - 15]!) + w[t - 16]!)
  let mut a := st[0]!
  let mut b := st[1]!
  let mut c := st[2]!
  let mut d := st[3]!
  let mut e := st[4]!
  let mut f := st[5]!
  let mut g := st[6]!
  let mut h := st[7]!
  for t in [0:64] do
    let t1 := h + bsig1 e + ch e f g + k[t]! + w[t]!
    let t2 := bsig0 a + maj a b c
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d,
    st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Serialize the eight-word SHA-224/SHA-256 state to exactly 32 bytes. -/
def stateBytes32 (st : Array UInt32) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin 32 => (u32be st[i.val / 4]!)[i.val % 4]!)

@[simp] theorem stateBytes32_size (st : Array UInt32) : (stateBytes32 st).size = 32 := by
  change (Array.ofFn fun i : Fin 32 => (u32be st[i.val / 4]!)[i.val % 4]!).size = 32
  exact Array.size_ofFn

/-- Run the SHA-256 compression function from a selected initial state and serialize `outLen`
digest bytes. This is the common FIPS 180-4 engine for SHA-224 and SHA-256. -/
def sha256Family (initial : Array UInt32) (outLen : ℕ) (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st := initial
  for b in [0:padded.size / 64] do
    st := compress st padded (b * 64)
  return (stateBytes32 st).extract 0 outLen

/-- SHA-224 of a byte string (28-byte digest). -/
def sha224 (msg : ByteArray) : ByteArray := sha256Family iv224 28 msg

/-- SHA-256 of a byte string (32-byte digest). -/
def sha256 (msg : ByteArray) : ByteArray := sha256Family iv 32 msg

@[simp] theorem sha224_size (msg : ByteArray) : (sha224 msg).size = 28 := by
  simp [sha224, sha256Family]

@[simp] theorem sha256_size (msg : ByteArray) : (sha256 msg).size = 32 := by
  simp [sha256, sha256Family]

/-- MGF1 with SHA-256 (RFC 8017 §B.2.1): expand `seed` to `outLen` bytes. -/
def mgf1 (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 31) / 32
  for ctr in [0:blocks] do
    out := out ++ sha256 (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

/-- Zero-pad (or hash-then-pad) a key to the 64-byte SHA-256 block. -/
def hmacKey0 (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 64 then sha256 key else key
  let mut out := k
  for _ in [0:64 - k.size] do
    out := out.push 0
  return out

/-- XOR every byte of a 64-byte block with a constant. -/
def xorConst (block : ByteArray) (c : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:block.size] do
    out := out.push (block[i]! ^^^ c)
  return out

/-- HMAC-SHA256 (FIPS 198-1) of `msg` under `key`. -/
def hmacSha256 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0 key
  sha256 (xorConst k0 0x5c ++ sha256 (xorConst k0 0x36 ++ msg))

/-! ## SHA-512 -/

/-- The eight SHA-512 initial hash values `H₀…H₇`. -/
def iv512 : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The eight SHA-384 initial hash values. -/
def iv384 : Array UInt64 :=
  #[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- The eight SHA-512/224 initial hash values. -/
def iv512_224 : Array UInt64 :=
  #[0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
    0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1]

/-- The eight SHA-512/256 initial hash values. -/
def iv512_256 : Array UInt64 :=
  #[0x22312194fc2bf72c, 0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
    0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2]

/-- The 80 SHA-512 round constants. -/
def k512 : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- Right rotation of a 64-bit word. -/
def rotr64 (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- SHA-512 `Ch`. -/
def ch64 (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)

/-- SHA-512 `Maj`. -/
def maj64 (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- SHA-512 `Σ₀`. -/
def bsig0_64 (x : UInt64) : UInt64 := rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39

/-- SHA-512 `Σ₁`. -/
def bsig1_64 (x : UInt64) : UInt64 := rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41

/-- SHA-512 `σ₀`. -/
def ssig0_64 (x : UInt64) : UInt64 := rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)

/-- SHA-512 `σ₁`. -/
def ssig1_64 (x : UInt64) : UInt64 := rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

/-- SHA-512 padding: `1`, zeroes, and a 128-bit big-endian bit length. -/
def pad512 (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut out := msg.push 0x80
  let zeros := (112 + 128 - (len + 1) % 128) % 128
  for _ in [0:zeros] do
    out := out.push 0
  return out ++ ByteArray.mk (toByte (8 * len) 16).toArray

/-- Process one 128-byte SHA-512 block. -/
def compress512 (st : Array UInt64) (m : ByteArray) (base : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.replicate 80 0
  for t in [0:16] do
    let o := base + t * 8
    let word : UInt64 :=
      (m[o]!).toUInt64 <<< 56 ||| (m[o + 1]!).toUInt64 <<< 48 |||
      (m[o + 2]!).toUInt64 <<< 40 ||| (m[o + 3]!).toUInt64 <<< 32 |||
      (m[o + 4]!).toUInt64 <<< 24 ||| (m[o + 5]!).toUInt64 <<< 16 |||
      (m[o + 6]!).toUInt64 <<< 8 ||| (m[o + 7]!).toUInt64
    w := w.set! t word
  for t in [16:80] do
    w := w.set! t (ssig1_64 (w[t - 2]!) + w[t - 7]! + ssig0_64 (w[t - 15]!) + w[t - 16]!)
  let mut a := st[0]!
  let mut b := st[1]!
  let mut c := st[2]!
  let mut d := st[3]!
  let mut e := st[4]!
  let mut f := st[5]!
  let mut g := st[6]!
  let mut h := st[7]!
  for t in [0:80] do
    let t1 := h + bsig1_64 e + ch64 e f g + k512[t]! + w[t]!
    let t2 := bsig0_64 a + maj64 a b c
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d,
    st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Serialize the eight-word SHA-384/SHA-512 state to exactly 64 bytes. -/
def stateBytes64 (st : Array UInt64) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin 64 => (u64be st[i.val / 8]!)[i.val % 8]!)

@[simp] theorem stateBytes64_size (st : Array UInt64) : (stateBytes64 st).size = 64 := by
  change (Array.ofFn fun i : Fin 64 => (u64be st[i.val / 8]!)[i.val % 8]!).size = 64
  exact Array.size_ofFn

/-- Run the SHA-512 compression function from a selected initial state and serialize `outLen`
digest bytes. This is the common FIPS 180-4 engine for the SHA-384 and SHA-512 variants. -/
def sha512Family (initial : Array UInt64) (outLen : ℕ) (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad512 msg
  let mut st := initial
  for b in [0:padded.size / 128] do
    st := compress512 st padded (b * 128)
  return (stateBytes64 st).extract 0 outLen

/-- SHA-384 of a byte string (48-byte digest). -/
def sha384 (msg : ByteArray) : ByteArray := sha512Family iv384 48 msg

/-- SHA-512 of a byte string (64-byte digest). -/
def sha512 (msg : ByteArray) : ByteArray := sha512Family iv512 64 msg

/-- SHA-512/224 of a byte string (28-byte digest). -/
def sha512_224 (msg : ByteArray) : ByteArray := sha512Family iv512_224 28 msg

/-- SHA-512/256 of a byte string (32-byte digest). -/
def sha512_256 (msg : ByteArray) : ByteArray := sha512Family iv512_256 32 msg

@[simp] theorem sha384_size (msg : ByteArray) : (sha384 msg).size = 48 := by
  simp [sha384, sha512Family]

@[simp] theorem sha512_size (msg : ByteArray) : (sha512 msg).size = 64 := by
  simp [sha512, sha512Family]

@[simp] theorem sha512_224_size (msg : ByteArray) : (sha512_224 msg).size = 28 := by
  simp [sha512_224, sha512Family]

@[simp] theorem sha512_256_size (msg : ByteArray) : (sha512_256 msg).size = 32 := by
  simp [sha512_256, sha512Family]

/-- MGF1 with SHA-512. -/
def mgf1Sha512 (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 63) / 64
  for ctr in [0:blocks] do
    out := out ++ sha512 (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

/-- The explicit SHA-256 name, parallel to `mgf1Sha512`; `mgf1` remains a compatibility alias. -/
def mgf1Sha256 (seed : ByteArray) (outLen : Nat) : ByteArray := mgf1 seed outLen

/-- Zero-pad (or hash-then-pad) a key to the 128-byte SHA-512 block. -/
def hmacKey0_512 (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 128 then sha512 key else key
  let mut out := k
  for _ in [0:128 - k.size] do
    out := out.push 0
  return out

/-- HMAC-SHA-512. -/
def hmacSha512 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0_512 key
  sha512 (xorConst k0 0x5c ++ sha512 (xorConst k0 0x36 ++ msg))

/-! ## Checked standard-domain boundaries -/

/-- Rejections at the SHA-2 and MGF1 standard-domain boundary. -/
inductive InputError where
  | messageTooLong (algorithm : String) (sizeBytes maximumExclusive : ℕ)
  | maskTooLong (algorithm : String) (requested maximum : ℕ)
deriving Repr, DecidableEq

/-- SHA-256's 64-bit length field admits messages shorter than `2^61` bytes. -/
def sha256InputLengthValid (sizeBytes : ℕ) : Bool := sizeBytes < 2 ^ 61

/-- SHA-512's 128-bit length field admits messages shorter than `2^125` bytes. -/
def sha512InputLengthValid (sizeBytes : ℕ) : Bool := sizeBytes < 2 ^ 125

/-- Reject a SHA-256 input outside FIPS 180-4's 64-bit bit-length domain. -/
def sha256Checked (msg : ByteArray) : Except InputError ByteArray :=
  if sha256InputLengthValid msg.size then
    .ok (sha256 msg)
  else
    .error (.messageTooLong "SHA-256" msg.size (2 ^ 61))

/-- Reject a SHA-512 input outside FIPS 180-4's 128-bit bit-length domain. -/
def sha512Checked (msg : ByteArray) : Except InputError ByteArray :=
  if sha512InputLengthValid msg.size then
    .ok (sha512 msg)
  else
    .error (.messageTooLong "SHA-512" msg.size (2 ^ 125))

/-- RFC 8017's maximum MGF1-SHA-256 output length. -/
def mgf1Sha256Maximum : ℕ := 2 ^ 32 * 32

/-- RFC 8017's maximum MGF1-SHA-512 output length. -/
def mgf1Sha512Maximum : ℕ := 2 ^ 32 * 64

/-- MGF1-SHA-256 with the RFC 8017 counter-wrap bound checked before execution. -/
def mgf1Sha256Checked (seed : ByteArray) (outLen : ℕ) : Except InputError ByteArray :=
  if outLen ≤ mgf1Sha256Maximum then
    .ok (mgf1Sha256 seed outLen)
  else
    .error (.maskTooLong "MGF1-SHA-256" outLen mgf1Sha256Maximum)

/-- MGF1-SHA-512 with the RFC 8017 counter-wrap bound checked before execution. -/
def mgf1Sha512Checked (seed : ByteArray) (outLen : ℕ) : Except InputError ByteArray :=
  if outLen ≤ mgf1Sha512Maximum then
    .ok (mgf1Sha512 seed outLen)
  else
    .error (.maskTooLong "MGF1-SHA-512" outLen mgf1Sha512Maximum)

end SLHDSA.Concrete.Sha2
