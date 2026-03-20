/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Encoding

/-!
# Concrete Encoding for ML-KEM

Pure-Lean executable implementation of the byte-encoding (FIPS 203 Algorithms 4–5) and
compression / decompression (FIPS 203 Section 4.2.1) operations.
-/

set_option autoImplicit false

namespace MLKEM.Concrete

open MLKEM

/-! ## Bit-level helpers -/

/-- Extract the `j`-th bit (LSB = 0) of a byte. -/
private def bitOf (b : UInt8) (j : Nat) : Nat :=
  ((b >>> j.toUInt8) &&& 1).toNat

/-- Pack an array of individual bits (0/1 as `Nat`) into bytes, little-endian bit order. -/
private def bitsToBytes (bits : Array Nat) : ByteArray := Id.run do
  let numBytes := bits.size / 8
  let mut out := ByteArray.empty
  for k in List.range numBytes do
    let mut byte : UInt8 := 0
    for j in List.range 8 do
      byte := byte ||| (bits.getD (8 * k + j) 0).toUInt8 <<< j.toUInt8
    out := out.push byte
  return out

/-- Unpack bytes into individual bits, little-endian bit order. -/
private def bytesToBits (bytes : ByteArray) : Array Nat := Id.run do
  let mut bits := Array.mkEmpty (bytes.size * 8)
  for k in List.range bytes.size do
    for j in List.range 8 do
        bits := bits.push (bitOf (bytes[k]!) j)
  return bits

/-! ## ByteEncode / ByteDecode (Algorithms 4–5) -/

/-- FIPS 203 Algorithm 4: encode 256 `d`-bit coefficients into `32d` bytes. -/
def byteEncode (d : Nat) (f : Rq) : ByteArray :=
  let fa := f.toArray
  let bits : Array Nat := Id.run do
    let mut b := Array.mkEmpty (256 * d)
    for i in List.range 256 do
      let mut a := (fa.getD i 0).val
      for _ in List.range d do
        b := b.push (a % 2)
        a := a / 2
    return b
  bitsToBytes bits

/-- FIPS 203 Algorithm 5: decode `32d` bytes into 256 coefficients. -/
def byteDecode (d : Nat) (bytes : ByteArray) : Rq :=
  let bits := bytesToBits bytes
  Vector.ofFn fun idx =>
    let i := idx.val
    let v := (List.range d).foldl (fun acc j =>
      acc + bits.getD (i * d + j) 0 * 2 ^ j) 0
    if d == 12 then (v % modulus : Nat) else (v : Nat)

/-- Extract a slice of a `ByteArray` as a new `ByteArray`. -/
private def sliceBA (ba : ByteArray) (offset len : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in List.range len do
    out := out.push (ba[offset + i]!)
  return out

/-- Encode a vector of `k` polynomials with 12-bit coefficients. -/
def byteEncode12Vec {k : Nat} (v : TqVec k) : ByteArray :=
  v.toArray.foldl (fun acc p => acc ++ byteEncode 12 p) ByteArray.empty

/-- Decode a byte array into a vector of `k` polynomials with 12-bit coefficients. -/
def byteDecode12Vec (k : Nat) (bytes : ByteArray) : TqVec k :=
  Vector.ofFn fun idx =>
    byteDecode 12 (sliceBA bytes (idx.val * 384) 384)

/-- Encode a vector of `k` polynomials with `d`-bit coefficients. -/
def byteEncodeVec (d : Nat) {k : Nat} (v : RqVec k) : ByteArray :=
  v.toArray.foldl (fun acc p => acc ++ byteEncode d p) ByteArray.empty

/-- Decode a byte array into a vector of `k` polynomials with `d`-bit coefficients. -/
def byteDecodeVec (d k : Nat) (bytes : ByteArray) : RqVec k :=
  Vector.ofFn fun idx =>
    let chunkSize := 32 * d
    byteDecode d (sliceBA bytes (idx.val * chunkSize) chunkSize)

/-! ## Compress / Decompress (Section 4.2.1) -/

/-- FIPS 203 Section 4.2.1: `Compress_d(x) = ⌈(2^d / q) · x⌋ mod 2^d`. -/
def compress (d : Nat) (x : Coeff) : Coeff :=
  let xn := x.val
  let shifted := (xn * (1 <<< d) + modulus / 2) / modulus
  (shifted % (1 <<< d) : Nat)

/-- FIPS 203 Section 4.2.1: `Decompress_d(y) = ⌈(q / 2^d) · y⌋`. -/
def decompress (d : Nat) (y : Coeff) : Coeff :=
  let yn := y.val
  let shifted := (yn * modulus + (1 <<< (d - 1))) / (1 <<< d)
  (shifted : Nat)

/-- Apply `Compress_d` coefficient-wise to a polynomial. -/
def compressPoly (d : Nat) (f : Rq) : Rq :=
  f.map (compress d)

/-- Apply `Decompress_d` coefficient-wise to a polynomial. -/
def decompressPoly (d : Nat) (f : Rq) : Rq :=
  f.map (decompress d)

/-- Apply `Compress_d` coordinate-wise to a polynomial vector. -/
def compressVec (d : Nat) {k : Nat} (v : RqVec k) : RqVec k :=
  v.map (compressPoly d)

/-- Apply `Decompress_d` coordinate-wise to a polynomial vector. -/
def decompressVec (d : Nat) {k : Nat} (v : RqVec k) : RqVec k :=
  v.map (decompressPoly d)

/-! ## Concrete `Encoding` instance -/

/-- Build the concrete `Encoding` instance for a given parameter set. -/
def concreteEncoding (params : Params) : Encoding params where
  EncodedTHat := ByteArray
  EncodedU := ByteArray
  EncodedV := ByteArray
  byteEncode12Vec := byteEncode12Vec
  byteDecode12Vec := byteDecode12Vec params.k
  byteDecode12Vec_byteEncode12Vec := by intro _; sorry
  compressDU := compressVec params.du
  decompressDU := decompressVec params.du
  byteEncodeDUVec := byteEncodeVec params.du
  byteDecodeDUVec := byteDecodeVec params.du params.k
  compressDV := compressPoly params.dv
  decompressDV := decompressPoly params.dv
  byteEncodeDV := byteEncode params.dv
  byteDecodeDV := byteDecode params.dv
  compress1 := compressPoly 1
  decompress1 := decompressPoly 1
  byteEncode1 := fun f =>
    let ba := byteEncode 1 f
    Vector.ofFn fun ⟨i, _⟩ => ba[i]!
  byteDecode1 := fun msg =>
    byteDecode 1 (ByteArray.mk msg.toArray)

end MLKEM.Concrete
