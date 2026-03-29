/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Primitives
import Examples.ML_DSA.Concrete.Rounding
import Mathlib.Data.List.OfFn

/-!
# Concrete Byte Encoding for ML-DSA

Concrete FIPS 204 byte packing for ML-DSA public keys, secret keys, signatures, and the
auxiliary `w1` commitment encoding.

This file deliberately exposes standalone `ByteArray` codecs instead of forcing them
immediately into the abstract `Encoding.Laws` surface. The concrete ML-DSA carriers
(`High = Rq`, `Power2High = Rq`, `Hint = Vector Bool ringDegree`) admit values outside the
FIPS-valid compressed ranges, while the standardized encodings are only injective on the
well-formed subset actually produced by the concrete primitives.
-/

set_option autoImplicit false

namespace ML_DSA.Concrete

open ML_DSA

/-! ## Basic byte helpers -/

def vectorToByteArray {n : Nat} (v : Bytes n) : ByteArray :=
  ByteArray.mk v.toArray

def byteArrayToVector (ba : ByteArray) (offset : Nat) (n : Nat) : Vector Byte n :=
  Vector.ofFn fun i => (ba[offset + i.val]?).getD 0

def sliceByteArray (ba : ByteArray) (offset len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn fun i : Fin len => (ba[offset + i.val]?).getD 0

def byteArrayToList (ba : ByteArray) : List Byte :=
  ba.data.toList

def concatByteArrays (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) (ByteArray.mk #[])

private def bitOf (b : UInt8) (j : Nat) : Nat :=
  ((b >>> j.toUInt8) &&& 1).toNat

private def packByte (bits : Fin 8 → Nat) : UInt8 :=
  (Nat.ofDigits 2 (List.ofFn bits)).toUInt8

def getByteD (bytes : ByteArray) (i : Nat) : UInt8 :=
  (bytes[i]?).getD 0

private def bitsToBytes (bits : Array Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn fun idx : Fin ((bits.size + 7) / 8) =>
    packByte fun j => bits.getD (8 * idx.val + j.val) 0

private def bytesToBits (bytes : ByteArray) : Array Nat :=
  Array.ofFn fun idx : Fin (bytes.size * 8) =>
    bitOf (getByteD bytes (idx.val / 8)) (idx.val % 8)

/-- Bit width for `SimpleBitPack`, where coefficients lie in `[0, b]`. -/
def simpleWidth (b : Nat) : Nat := Nat.log2 b + 1

/-- Bit width for `BitPack`, where coefficients lie in `[a, b]`. -/
def rangeWidth (a b : ℤ) : Nat := Nat.log2 (Int.toNat (b - a)) + 1

private def packNatArray (vals : Array Nat) (width : Nat) : ByteArray :=
  let bits : Array Nat := Id.run do
    let mut acc : Array Nat := Array.mkEmpty (vals.size * width)
    for i in [0:vals.size] do
      let v := vals.getD i 0
      for bit in [0:width] do
        acc := acc.push ((v / 2 ^ bit) % 2)
    return acc
  bitsToBytes bits

private def unpackNatArray (count width : Nat) (bytes : ByteArray) : Array Nat :=
  let bits := bytesToBits bytes
  Array.ofFn fun idx : Fin count =>
    Nat.ofDigits 2 <| List.ofFn fun j : Fin width => bits.getD (idx.val * width + j.val) 0

/-- FIPS 204 Algorithm 16 on a single polynomial. -/
def simpleBitPackPoly (f : Rq) (b : Nat) : ByteArray :=
  let width := simpleWidth b
  let vals := Array.ofFn fun i : Fin ringDegree => (f.get i).val
  packNatArray vals width

/-- FIPS 204 Algorithm 18 on a single polynomial. -/
def simpleBitUnpackPoly (bytes : ByteArray) (b : Nat) : Rq :=
  let width := simpleWidth b
  let vals := unpackNatArray ringDegree width bytes
  Vector.ofFn fun i => (vals.getD i.val 0 : Coeff)

/-- FIPS 204 Algorithm 17 on a single polynomial. Encodes the shifted values `b - coeff`. -/
def bitPackPoly (f : Rq) (a b : ℤ) : ByteArray :=
  let width := rangeWidth a b
  let vals := Array.ofFn fun i : Fin ringDegree =>
    Int.toNat (b - LatticeCrypto.centeredRepr (f.get i))
  packNatArray vals width

/-- FIPS 204 Algorithm 19 on a single polynomial. -/
def bitUnpackPoly (bytes : ByteArray) (a b : ℤ) : Rq :=
  let width := rangeWidth a b
  let vals := unpackNatArray ringDegree width bytes
  Vector.ofFn fun i => (((b - vals.getD i.val 0 : ℤ)) : Coeff)

/-! ## Polynomial codec specializations -/

def polyEtaPackedBytes (p : Params) : Nat :=
  ringDegree * rangeWidth (-(p.eta : ℤ)) p.eta / 8

def polyT1PackedBytes : Nat :=
  ringDegree * simpleWidth (2 ^ (Nat.log2 (modulus - 1) + 1 - droppedBits) - 1) / 8

def polyT0PackedBytes : Nat :=
  ringDegree * rangeWidth (-(2 ^ (droppedBits - 1) - 1 : ℤ)) (2 ^ (droppedBits - 1) : ℤ) / 8

def polyZPackedBytes (p : Params) : Nat :=
  ringDegree * rangeWidth (-(p.gamma1 : ℤ) + 1) p.gamma1 / 8

def polyW1PackedBytes (p : Params) : Nat :=
  ringDegree * simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) / 8

def polyEtaPack (p : Params) (f : Rq) : ByteArray :=
  bitPackPoly f (-(p.eta : ℤ)) p.eta

def polyEtaUnpack (p : Params) (bytes : ByteArray) : Rq :=
  bitUnpackPoly bytes (-(p.eta : ℤ)) p.eta

def polyT1Pack (f : Power2High) : ByteArray :=
  simpleBitPackPoly f (2 ^ (Nat.log2 (modulus - 1) + 1 - droppedBits) - 1)

def polyT1Unpack (bytes : ByteArray) : Power2High :=
  simpleBitUnpackPoly bytes (2 ^ (Nat.log2 (modulus - 1) + 1 - droppedBits) - 1)

def polyT0Pack (f : Rq) : ByteArray :=
  bitPackPoly f (-(2 ^ (droppedBits - 1) - 1 : ℤ)) (2 ^ (droppedBits - 1) : ℤ)

def polyT0Unpack (bytes : ByteArray) : Rq :=
  bitUnpackPoly bytes (-(2 ^ (droppedBits - 1) - 1 : ℤ)) (2 ^ (droppedBits - 1) : ℤ)

def polyZPack (p : Params) (f : Rq) : ByteArray :=
  bitPackPoly f (-(p.gamma1 : ℤ) + 1) p.gamma1

def polyZUnpack (p : Params) (bytes : ByteArray) : Rq :=
  bitUnpackPoly bytes (-(p.gamma1 : ℤ) + 1) p.gamma1

def polyW1Pack (p : Params) (f : High) : ByteArray :=
  simpleBitPackPoly f ((modulus - 1) / (2 * p.gamma2) - 1)

/-! ## Vector-level packers -/

private def packPolyVector {k : Nat} (v : Vector Rq k) (pack : Rq → ByteArray) : ByteArray :=
  concatByteArrays <| v.toList.map pack

private def unpackPolyVector (k chunkSize : Nat) (bytes : ByteArray) (unpack : ByteArray → Rq) :
    Vector Rq k :=
  Vector.ofFn fun i => unpack (sliceByteArray bytes (i.val * chunkSize) chunkSize)

/-- `w1Encode(w₁)` (Algorithm 28). -/
def w1EncodeBytes (p : Params) (w1 : Vector High p.k) : ByteArray :=
  packPolyVector w1 (polyW1Pack p)

def w1Encode (p : Params) (w1 : Vector High p.k) : List Byte :=
  byteArrayToList (w1EncodeBytes p w1)

/-! ## Key and signature encodings -/

def pkEncode (p : Params) (rho : Bytes 32) (t1 : Vector Power2High p.k) : ByteArray :=
  vectorToByteArray rho ++ packPolyVector t1 polyT1Pack

def pkDecode (p : Params) (bytes : ByteArray) : Bytes 32 × Vector Power2High p.k :=
  let rho := byteArrayToVector bytes 0 32
  let t1Bytes := sliceByteArray bytes 32 (p.k * polyT1PackedBytes)
  let t1 := unpackPolyVector p.k polyT1PackedBytes t1Bytes polyT1Unpack
  (rho, t1)

def skEncode (p : Params) (rho key : Bytes 32) (tr : Bytes 64)
    (s1 : RqVec p.l) (s2 t0 : RqVec p.k) : ByteArray :=
  vectorToByteArray rho ++
  vectorToByteArray key ++
  vectorToByteArray tr ++
  packPolyVector s1 (polyEtaPack p) ++
  packPolyVector s2 (polyEtaPack p) ++
  packPolyVector t0 polyT0Pack

def skDecode (p : Params) (bytes : ByteArray) :
    Bytes 32 × Bytes 32 × Bytes 64 × RqVec p.l × RqVec p.k × RqVec p.k :=
  let rho := byteArrayToVector bytes 0 32
  let key := byteArrayToVector bytes 32 32
  let tr := byteArrayToVector bytes 64 64
  let s1Off := 128
  let s1Len := p.l * polyEtaPackedBytes p
  let s2Off := s1Off + s1Len
  let s2Len := p.k * polyEtaPackedBytes p
  let t0Off := s2Off + s2Len
  let s1 := unpackPolyVector p.l (polyEtaPackedBytes p)
    (sliceByteArray bytes s1Off s1Len) (polyEtaUnpack p)
  let s2 := unpackPolyVector p.k (polyEtaPackedBytes p)
    (sliceByteArray bytes s2Off s2Len) (polyEtaUnpack p)
  let t0 := unpackPolyVector p.k polyT0PackedBytes
    (sliceByteArray bytes t0Off (p.k * polyT0PackedBytes)) polyT0Unpack
  (rho, key, tr, s1, s2, t0)

def hintBitPack (p : Params) (h : Vector Hint p.k) : ByteArray :=
  ByteArray.mk <| Id.run do
    let mut out : Array Byte := Array.replicate (p.omega + p.k) 0
    let mut cursor := 0
    for i in [0:p.k] do
      let hi := h.toArray.getD i (Vector.ofFn fun _ => false)
      for j in [0:ringDegree] do
        if hi.toArray.getD j false then
          if cursor < p.omega then
            out := out.set! cursor j.toUInt8
          cursor := cursor + 1
      out := out.set! (p.omega + i) cursor.toUInt8
    return out

def hintBitUnpack (p : Params) (bytes : ByteArray) : Option (Vector Hint p.k) := Id.run do
  let mut hints : Array Hint := Array.mkEmpty p.k
  let mut cursor := 0
  for i in [0:p.k] do
    let endCursor := (getByteD bytes (p.omega + i)).toNat
    if endCursor < cursor || endCursor > p.omega then
      return none
    let mut coeffs : Array Bool := Array.replicate ringDegree false
    let mut prev := 0
    for j in [cursor:endCursor] do
      let idx := (getByteD bytes j).toNat
      if idx ≥ ringDegree then
        return none
      if j > cursor && idx ≤ prev then
        return none
      coeffs := coeffs.set! idx true
      prev := idx
    hints := hints.push <| Vector.ofFn fun j => coeffs.getD j.val false
    cursor := endCursor
  for j in [cursor:p.omega] do
    if getByteD bytes j != 0 then
      return none
  return some <| Vector.ofFn fun i => hints.getD i.val (Vector.ofFn fun _ => false)

def sigEncode (p : Params) (cTilde : CommitHashBytes p) (z : RqVec p.l) (h : Vector Hint p.k) :
    ByteArray :=
  vectorToByteArray cTilde ++ packPolyVector z (polyZPack p) ++ hintBitPack p h

def sigDecode (p : Params) (bytes : ByteArray) :
    Option (CommitHashBytes p × RqVec p.l × Vector Hint p.k) :=
  let cLen := p.lambda / 4
  let zOff := cLen
  let zLen := p.l * polyZPackedBytes p
  let hOff := zOff + zLen
  let cTilde := byteArrayToVector bytes 0 cLen
  let zBytes := sliceByteArray bytes zOff zLen
  let z := unpackPolyVector p.l (polyZPackedBytes p) zBytes (polyZUnpack p)
  match hintBitUnpack p (sliceByteArray bytes hOff (p.omega + p.k)) with
  | some h => some (cTilde, z, h)
  | none => none

end ML_DSA.Concrete
