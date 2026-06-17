/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Params

/-!
# Pure-Lean SHA-256 (FIPS 180-4) with MGF1 and HMAC

An executable, FFI-free SHA-256 over `ByteArray`, together with `MGF1-SHA256` (RFC 8017 B.2.1)
and `HMAC-SHA256` (FIPS 198-1). These are the hash primitives the SLH-DSA-SHA2-128-24 concrete
tweakable-hash instantiation (`HashSig.SLHDSA.Concrete.Instance`) is built from.

All arithmetic is `UInt32`/`UInt8` (wrapping mod `2^32`/`2^8`); words are big-endian.

## References

- FIPS 180-4 (SHA-256), FIPS 198-1 (HMAC), RFC 8017 §B.2.1 (MGF1)
-/


namespace SLHDSA.Concrete.Sha2

/-- The eight SHA-256 initial hash values `H₀…H₇`. -/
def iv : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

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

/-- SHA-256 of a byte string (32-byte digest). -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st := iv
  for b in [0:padded.size / 64] do
    st := compress st padded (b * 64)
  let mut out := ByteArray.empty
  for i in [0:8] do
    out := out ++ u32be (st[i]!)
  return out

/-- MGF1 with SHA-256 (RFC 8017 §B.2.1): expand `seed` to `outLen` bytes. -/
def mgf1 (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 31) / 32
  for ctr in [0:blocks] do
    out := out ++ sha256 (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

/-- Zero-pad (or hash-then-pad) a key to the 64-byte SHA-256 block. -/
private def hmacKey0 (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 64 then sha256 key else key
  let mut out := k
  for _ in [0:64 - k.size] do
    out := out.push 0
  return out

/-- XOR every byte of a 64-byte block with a constant. -/
private def xorConst (block : ByteArray) (c : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:block.size] do
    out := out.push (block[i]! ^^^ c)
  return out

/-- HMAC-SHA256 (FIPS 198-1) of `msg` under `key`. -/
def hmacSha256 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0 key
  sha256 (xorConst k0 0x5c ++ sha256 (xorConst k0 0x36 ++ msg))

end SLHDSA.Concrete.Sha2
