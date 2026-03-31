/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Ring

/-!
# Concrete Falcon Encoding

Executable compress/decompress for Falcon signature polynomials (Golomb-Rice style),
plus 14-bit public key encoding/decoding for `q = 12289`.

## Signature Compression (comp_encode / comp_decode)

Each coefficient `x` with `|x| ≤ 2047` is encoded as:
- 1 sign bit (0 = positive, 1 = negative)
- 7 low bits of `|x|`
- unary-coded high bits: `(|x| >> 7)` zero bits followed by a `1` bit

This is a variable-length code: small coefficients use ~9 bits, larger ones up to ~24 bits.

## Public Key Encoding

Each coefficient of `h ∈ R_q` takes exactly 14 bits (since `q = 12289 < 2^14`),
packed 4 coefficients into 7 bytes.

## References

- c-fn-dsa: `codec.c` (comp_encode, comp_decode, mqpoly_encode, mqpoly_decode)
- Falcon specification v1.2, Section 3.12 (Algorithms 17–18)
-/


namespace Falcon.Concrete

open Falcon

/-! ## Signature compression -/

/-- Compress a Falcon signature polynomial into at most `dlen` bytes. -/
def compress (n : ℕ) (s : IntPoly n) (dlen : ℕ) : Option (List UInt8) := Id.run do
  let mut acc : UInt32 := 0
  let mut accLen : UInt32 := 0
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    let x : Int := s[i]!
    if x < -2047 || x > 2047 then
      return none
    let sw : UInt32 := if x < 0 then 0xFFFFFFFF else 0
    let w : UInt32 := x.natAbs.toUInt32
    acc := (acc <<< 8) ||| ((sw &&& 0x80) ||| (w &&& 0x7F))
    accLen := accLen + 8
    let wh := (w >>> 7).toNat + 1
    acc := (acc <<< wh.toUInt32) ||| 1
    accLen := accLen + wh.toUInt32
    while accLen ≥ 8 do
      accLen := accLen - 8
      if out.size ≥ dlen then
        return none
      out := out.push (acc >>> accLen).toUInt8
  if accLen > 0 then
    if out.size ≥ dlen then
      return none
    out := out.push (acc <<< (8 - accLen)).toUInt8
  while out.size < dlen do
    out := out.push 0
  return some out.toList

/-- Decompress a Falcon signature polynomial from its compressed byte representation. -/
def decompress (n : ℕ) (d : List UInt8) (dlen : ℕ) : Option (IntPoly n) := Id.run do
  if d.length < dlen then return none
  let bytes := d.toArray
  let mut acc : UInt32 := 0
  let mut accLen : UInt32 := 0
  let mut j := 0
  let mut result : Array ℤ := Array.replicate n 0
  for i in [0:n] do
    if j ≥ dlen then return none
    acc := (acc <<< 8) ||| bytes[j]!.toUInt32
    j := j + 1
    let full := acc >>> accLen
    let t := (full >>> 7) &&& 1
    let mut m : UInt32 := full &&& 0x7F
    let mut done := false
    while !done do
      if accLen == 0 then
        if j ≥ dlen then return none
        acc := (acc <<< 8) ||| bytes[j]!.toUInt32
        j := j + 1
        accLen := 8
      accLen := accLen - 1
      if ((acc >>> accLen) &&& 1) != 0 then
        done := true
      else
        m := m + 0x80
        if m > 2047 then return none
    if m == 0 && t != 0 then return none
    let val : UInt32 := (m ^^^ (0 - t)) + t
    let signedVal : ℤ :=
      if val &&& 0x80000000 != 0 then -(((~~~val) + 1).toNat : ℤ)
      else (val.toNat : ℤ)
    result := result.set! i signedVal
  if accLen > 0 then
    if (acc &&& ((1 <<< accLen) - 1)) != 0 then
      return none
  while j < dlen do
    if bytes[j]! != 0 then return none
    j := j + 1
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

/-! ## Public key encoding (14 bits per coefficient) -/

/-- The FN-DSA public-key header byte for a given `logn`. -/
@[inline] def publicKeyHeader (logn : Nat) : UInt8 :=
  (0x00 + logn).toUInt8

/-- Encode a Falcon public key polynomial using the packed 14-bit coefficient format. -/
def pkEncode (n : ℕ) (h : Rq n) : ByteArray := Id.run do
  if n % 4 != 0 then
    panic! s!"Falcon public-key encoding requires n divisible by 4, got {n}"
  let mut out := ByteArray.empty
  let mut i := 0
  while i + 3 < n do
    let h0 := (h[i]!).val
    let h1 := (h[i+1]!).val
    let h2 := (h[i+2]!).val
    let h3 := (h[i+3]!).val
    out := out.push (h0 >>> 6).toUInt8
    out := out.push ((h0 <<< 2) ||| (h1 >>> 12)).toUInt8
    out := out.push (h1 >>> 4).toUInt8
    out := out.push ((h1 <<< 4) ||| (h2 >>> 10)).toUInt8
    out := out.push (h2 >>> 2).toUInt8
    out := out.push ((h2 <<< 6) ||| (h3 >>> 8)).toUInt8
    out := out.push h3.toUInt8
    i := i + 4
  return out

/-- Decode a Falcon public key polynomial from the packed 14-bit coefficient format. -/
def pkDecode (n : ℕ) (d : ByteArray) : Option (Rq n) := Id.run do
  if n % 4 != 0 then return none
  let needed := 7 * n / 4
  if d.size < needed then return none
  let mut result : Array Coeff := Array.replicate n 0
  let mut i := 0
  let mut j := 0
  while i + 3 < n do
    let d0 := d[j]!.toNat
    let d1 := d[j+1]!.toNat
    let d2 := d[j+2]!.toNat
    let d3 := d[j+3]!.toNat
    let d4 := d[j+4]!.toNat
    let d5 := d[j+5]!.toNat
    let d6 := d[j+6]!.toNat
    j := j + 7
    let h0 := (d0 <<< 6) ||| (d1 >>> 2)
    let h1 := ((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF
    let h2 := ((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF
    let h3 := ((d5 <<< 8) ||| d6) &&& 0x3FFF
    if h0 ≥ modulus || h1 ≥ modulus || h2 ≥ modulus || h3 ≥ modulus then
      return none
    result := result.set! i (h0 : Coeff)
    result := result.set! (i+1) (h1 : Coeff)
    result := result.set! (i+2) (h2 : Coeff)
    result := result.set! (i+3) (h3 : Coeff)
    i := i + 4
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

/-- External public-key bytes used by FN-DSA verification and raw-message hashing:
one header byte followed by the packed 14-bit coefficient encoding. -/
def publicKeyBytes (logn : Nat) {n : ℕ} (h : Rq n) : ByteArray :=
  ByteArray.mk #[publicKeyHeader logn] ++ pkEncode n h

/-! ## Full signature encoding/decoding -/

/-- Encode a Falcon signature as header, salt, and compressed `s₂` bytes. -/
def sigEncode (salt : Bytes 40) (compSig : List UInt8) (logn : ℕ) : ByteArray :=
  let header : UInt8 := (0x30 + logn).toUInt8
  let saltBA := ByteArray.mk salt.toArray
  let compBA := ByteArray.mk compSig.toArray
  ByteArray.mk #[header] ++ saltBA ++ compBA

/-- Decode a Falcon signature into its salt and compressed `s₂` bytes. -/
def sigDecode (d : ByteArray) (logn : ℕ) : Option (Bytes 40 × List UInt8) := Id.run do
  if d.size < 42 then return none
  let header := d[0]!
  if header != (0x30 + logn).toUInt8 then return none
  let salt : Bytes 40 := Vector.ofFn fun ⟨i, _⟩ => d[i + 1]!
  let comp := (d.extract 41 d.size).toList
  return some (salt, comp)

end Falcon.Concrete
