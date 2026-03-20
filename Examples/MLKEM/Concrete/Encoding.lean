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

/-- Total byte lookup with zero fallback. -/
private def getByteD (bytes : ByteArray) (i : Nat) : UInt8 :=
  (bytes[i]?).getD 0

/-- Pack an array of individual bits (0/1 as `Nat`) into bytes, little-endian bit order. -/
private def bitsToBytes (bits : Array Nat) : ByteArray := Id.run do
  let numBytes := bits.size / 8
  let mut out := ByteArray.empty
  for k in [0:numBytes] do
    let mut byte : UInt8 := 0
    for j in [0:8] do
      byte := byte ||| (bits.getD (8 * k + j) 0).toUInt8 <<< j.toUInt8
    out := out.push byte
  return out

/-- Unpack bytes into individual bits, little-endian bit order. -/
private def bytesToBits (bytes : ByteArray) : Array Nat := Id.run do
  let mut bits := Array.mkEmpty (bytes.size * 8)
  for k in [0:bytes.size] do
    for j in [0:8] do
      bits := bits.push (bitOf (bytes[k]!) j)
  return bits

/-! ## ByteEncode / ByteDecode (Algorithms 4–5) -/

/-- FIPS 203 Algorithm 4: encode 256 `d`-bit coefficients into `32d` bytes. -/
def byteEncode (d : Nat) (f : Rq) : ByteArray :=
  let fa := f.toArray
  let bits : Array Nat := Id.run do
    let mut b := Array.mkEmpty (256 * d)
    for i in [0:256] do
      let mut a := (fa.getD i 0).val
      for _ in [0:d] do
        b := b.push (a % 2)
        a := a / 2
    return b
  bitsToBytes bits

/-- FIPS 203 Algorithm 5: decode `32d` bytes into 256 coefficients. -/
def byteDecode (d : Nat) (bytes : ByteArray) : Rq :=
  let bits := bytesToBits bytes
  Vector.ofFn fun idx =>
    let i := idx.val
    let v := Id.run do
      let mut acc := 0
      for j in [0:d] do
        acc := acc + bits.getD (i * d + j) 0 * 2 ^ j
      return acc
    (v : Nat)

/-- Extract a slice of a `ByteArray` as a new `ByteArray`. -/
private def sliceBA (ba : ByteArray) (offset len : Nat) : ByteArray :=
  ba.extract offset (offset + len)

/-! ## 12-bit public-key encoding -/

local instance : NeZero modulus := by
  unfold modulus
  exact ⟨by decide⟩

/-- Encode one byte of a 12-bit-packed polynomial block. -/
private def byteEncode12PolyByte (f : Tq) (idx : Fin 384) : UInt8 :=
  let pair := idx.val / 3
  have hpair : pair < 128 := by
    omega
  have h0 : 2 * pair < ringDegree := by
    have : 2 * pair < 256 := by omega
    simpa [ringDegree] using this
  have h1 : 2 * pair + 1 < ringDegree := by
    have : 2 * pair + 1 < 256 := by omega
    simpa [ringDegree] using this
  let a := (f[(2 * pair)]'h0 : Coeff).val
  let b := (f[(2 * pair + 1)]'h1 : Coeff).val
  match idx.val % 3 with
  | 0 => a.toUInt8
  | 1 => (a / 256 + 16 * (b % 16)).toUInt8
  | _ => (b / 16).toUInt8

/-- Encode one NTT-domain polynomial by packing coefficient pairs into 3-byte blocks. -/
private def byteEncode12Poly (f : Tq) : ByteArray :=
  ByteArray.mk <| Array.ofFn (byteEncode12PolyByte f)

/-- Decode one 384-byte public-key block into an NTT-domain polynomial. -/
private def byteDecode12Poly (bytes : ByteArray) : Tq :=
  Vector.ofFn fun idx =>
    let pair := idx.val / 2
    let b0 := (getByteD bytes (3 * pair)).toNat
    let b1 := (getByteD bytes (3 * pair + 1)).toNat
    let b2 := (getByteD bytes (3 * pair + 2)).toNat
    if idx.val % 2 = 0 then
      (((b0 + 256 * (b1 % 16) : Nat) : Coeff))
    else
      (((b1 / 16 + 16 * b2 : Nat) : Coeff))

/-- Encode one byte of a concatenated 12-bit-packed vector block. -/
private def byteEncode12VecByte {k : Nat} (v : TqVec k) (idx : Fin (384 * k)) : UInt8 :=
  let poly := idx.val / 384
  let byte := idx.val % 384
  have hpoly : poly < k := by
    exact Nat.div_lt_of_lt_mul idx.isLt
  have hbyte : byte < 384 := Nat.mod_lt _ (by decide)
  byteEncode12PolyByte (v[poly]'hpoly) ⟨byte, hbyte⟩

/-- Decode one polynomial from a concatenated 12-bit-packed vector block. -/
private def byteDecode12VecPoly {k : Nat} (bytes : ByteArray) (poly : Fin k) : Tq :=
  Vector.ofFn fun idx =>
    let pair := idx.val / 2
    let base := poly.val * 384 + 3 * pair
    let b0 := (getByteD bytes base).toNat
    let b1 := (getByteD bytes (poly.val * 384 + (3 * pair + 1))).toNat
    let b2 := (getByteD bytes (poly.val * 384 + (3 * pair + 2))).toNat
    if idx.val % 2 = 0 then
      (((b0 + 256 * (b1 % 16) : Nat) : Coeff))
    else
      (((b1 / 16 + 16 * b2 : Nat) : Coeff))

private theorem decode12Pair_fst {a b : Nat} (ha : a < 4096) :
    a % 256 + 256 * ((a / 256 + 16 * (b % 16)) % 16) = a := by
  have haDiv : a / 256 < 16 := Nat.div_lt_of_lt_mul (by omega)
  calc
    a % 256 + 256 * ((a / 256 + 16 * (b % 16)) % 16)
        = a % 256 + 256 * ((a / 256) % 16) := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt haDiv]
    _ = a % 256 + 256 * (a / 256) := by
      rw [Nat.mod_eq_of_lt haDiv]
    _ = a := by
      rw [Nat.mod_add_div]

private theorem decode12Pair_snd {a b : Nat} (ha : a < 4096) :
    (a / 256 + 16 * (b % 16)) / 16 + 16 * (b / 16) = b := by
  have haDiv : a / 256 < 16 := Nat.div_lt_of_lt_mul (by omega)
  calc
    (a / 256 + 16 * (b % 16)) / 16 + 16 * (b / 16)
        = (a / 256 + (b % 16) * 16) / 16 + 16 * (b / 16) := by
            rw [Nat.mul_comm 16 (b % 16)]
    _ = (a / 256) / 16 + (b % 16) + 16 * (b / 16) := by
      rw [Nat.add_mul_div_right (a / 256) (b % 16) (by decide : 0 < 16)]
    _ = b % 16 + 16 * (b / 16) := by
      rw [Nat.div_eq_of_lt haDiv, zero_add]
    _ = b := by
      rw [Nat.mod_add_div]

private theorem getByteD_eq_getElem {bytes : ByteArray} {i : Nat} (hi : i < bytes.size) :
    getByteD bytes i = bytes[i] := by
  unfold getByteD
  simp [hi]

private theorem getByteD_byteEncode12Poly (f : Tq) {j : Nat} (hj : j < 384) :
    getByteD (byteEncode12Poly f) j = byteEncode12PolyByte f ⟨j, hj⟩ := by
  have hsizeData : j < (byteEncode12Poly f).data.size := by
    simpa [byteEncode12Poly] using hj
  have hsize : j < (byteEncode12Poly f).size := by
    simpa [ByteArray.size_data] using hsizeData
  rw [getByteD_eq_getElem hsize]
  rw [ByteArray.getElem_eq_getElem_data]
  simp [byteEncode12Poly]

/-- Encode a vector of `k` polynomials with 12-bit coefficients. -/
def byteEncode12Vec {k : Nat} (v : TqVec k) : ByteArray :=
  ByteArray.mk <| Array.ofFn (byteEncode12VecByte v)

private theorem getByteD_byteEncode12Vec {k : Nat} (v : TqVec k) {poly j : Nat}
    (hpoly : poly < k) (hj : j < 384) :
    getByteD (byteEncode12Vec v) (poly * 384 + j) =
      byteEncode12PolyByte (v[poly]'hpoly) ⟨j, hj⟩ := by
  have hidxNat : poly * 384 + j < 384 * k := by
    omega
  have hidxData : poly * 384 + j < (byteEncode12Vec v).data.size := by
    simpa [byteEncode12Vec] using hidxNat
  have hidx : poly * 384 + j < (byteEncode12Vec v).size := by
    simpa [ByteArray.size_data] using hidxData
  have hdiv : (poly * 384 + j) / 384 = poly := by
    rw [Nat.add_comm, Nat.add_mul_div_right j poly (z := 384) (by decide : 0 < 384),
      Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (poly * 384 + j) % 384 = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [getByteD_eq_getElem hidx]
  rw [ByteArray.getElem_eq_getElem_data]
  simp [byteEncode12VecByte, hdiv, hmod, byteEncode12Vec]

/-- Decode a byte array into a vector of `k` polynomials with 12-bit coefficients. -/
def byteDecode12Vec (k : Nat) (bytes : ByteArray) : TqVec k :=
  Vector.ofFn fun idx =>
    byteDecode12VecPoly bytes idx

private theorem byteDecode12Poly_byteEncode12Poly (f : Tq) :
    byteDecode12Poly (byteEncode12Poly f) = f := by
  have hfun :
      (fun idx : Fin ringDegree =>
        let pair := idx.val / 2
        let b0 := (getByteD (byteEncode12Poly f) (3 * pair)).toNat
        let b1 := (getByteD (byteEncode12Poly f) (3 * pair + 1)).toNat
        let b2 := (getByteD (byteEncode12Poly f) (3 * pair + 2)).toNat
        if idx.val % 2 = 0 then
          (((b0 + 256 * (b1 % 16) : Nat) : Coeff))
        else
          (((b1 / 16 + 16 * b2 : Nat) : Coeff)))
      = fun idx : Fin ringDegree => f[idx.val] := by
    funext idx
    let pair := idx.val / 2
    have hpair : pair < 128 := by
      dsimp [pair]
      have : idx.val < 256 := idx.isLt
      omega
    have h0 : 2 * pair < ringDegree := by
      have : 2 * pair < 256 := by omega
      simpa [ringDegree] using this
    have h1 : 2 * pair + 1 < ringDegree := by
      have : 2 * pair + 1 < 256 := by omega
      simpa [ringDegree] using this
    let a : Nat := (f[(2 * pair)]'h0 : Coeff).val
    let b : Nat := (f[(2 * pair + 1)]'h1 : Coeff).val
    have ha : a < 4096 := by
      dsimp [a]
      exact lt_trans (ZMod.val_lt _) (by decide)
    have hab : a / 256 + 16 * (b % 16) < 256 := by
      have haDiv : a / 256 < 16 := Nat.div_lt_of_lt_mul (by omega)
      have hbMod : b % 16 < 16 := Nat.mod_lt _ (by decide)
      omega
    have hbDiv : b / 16 < 256 := by
      have hb : b < 4096 := by
        exact lt_trans (ZMod.val_lt _) (by decide)
      exact Nat.div_lt_of_lt_mul hb
    have hdiv0 : (3 * pair) / 3 = pair := by omega
    have hdiv1 : (3 * pair + 1) / 3 = pair := by omega
    have hdiv2 : (3 * pair + 2) / 3 = pair := by omega
    have hmod0 : (3 * pair) % 3 = 0 := by omega
    have hmod1 : (3 * pair + 1) % 3 = 1 := by omega
    have hmod2 : (3 * pair + 2) % 3 = 2 := by omega
    have hb0 :
        (getByteD (byteEncode12Poly f) (3 * pair)).toNat = a % 256 := by
      rw [getByteD_byteEncode12Poly (f := f) (j := 3 * pair) (by omega)]
      simp [byteEncode12PolyByte, a, hdiv0, hmod0]
    have hb1 :
        (getByteD (byteEncode12Poly f) (3 * pair + 1)).toNat = a / 256 + 16 * (b % 16) := by
      rw [getByteD_byteEncode12Poly (f := f) (j := 3 * pair + 1) (by omega)]
      simp [byteEncode12PolyByte, a, b, hdiv1, hmod1, Nat.mod_eq_of_lt hab]
    have hb2 :
        (getByteD (byteEncode12Poly f) (3 * pair + 2)).toNat = b / 16 := by
      rw [getByteD_byteEncode12Poly (f := f) (j := 3 * pair + 2) (by omega)]
      simp [byteEncode12PolyByte, b, hdiv2, hmod2, Nat.mod_eq_of_lt hbDiv]
    by_cases hEven : idx.val % 2 = 0
    · have hidx : idx.val = 2 * pair := by
        dsimp [pair]
        omega
      rw [if_pos hEven]
      calc
        (((getByteD (byteEncode12Poly f) (3 * pair)).toNat +
            256 * ((getByteD (byteEncode12Poly f) (3 * pair + 1)).toNat % 16) : Nat) : Coeff)
            = (a : Coeff) := by
                rw [hb0, hb1]
                exact congrArg (fun n : Nat => (n : Coeff)) (decode12Pair_fst (a := a) (b := b) ha)
        _ = f[idx.val] := by
            have hidx' : idx = ⟨2 * pair, h0⟩ := by
              apply Fin.ext
              exact hidx
            simp [hidx', a]
    · have hmod : idx.val % 2 = 1 := by
        have hlt : idx.val % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      have hidx : idx.val = 2 * pair + 1 := by
        dsimp [pair]
        omega
      rw [if_neg hEven]
      calc
        (((getByteD (byteEncode12Poly f) (3 * pair + 1)).toNat / 16 +
            16 * (getByteD (byteEncode12Poly f) (3 * pair + 2)).toNat : Nat) : Coeff)
            = (b : Coeff) := by
                rw [hb1, hb2]
                exact congrArg (fun n : Nat => (n : Coeff)) (decode12Pair_snd (a := a) (b := b) ha)
        _ = f[idx.val] := by
            have hidx' : idx = ⟨2 * pair + 1, h1⟩ := by
              apply Fin.ext
              exact hidx
            simp [hidx', b]
  apply Vector.toArray_inj.mp
  unfold byteDecode12Poly
  rw [Vector.toArray_ofFn]
  calc
    Array.ofFn
      (fun idx : Fin ringDegree =>
        let pair := idx.val / 2
        let b0 := (getByteD (byteEncode12Poly f) (3 * pair)).toNat
        let b1 := (getByteD (byteEncode12Poly f) (3 * pair + 1)).toNat
        let b2 := (getByteD (byteEncode12Poly f) (3 * pair + 2)).toNat
        if idx.val % 2 = 0 then
          (((b0 + 256 * (b1 % 16) : Nat) : Coeff))
        else
          (((b1 / 16 + 16 * b2 : Nat) : Coeff)))
        = Array.ofFn (fun idx : Fin ringDegree => f[idx.val]) := by
            exact congrArg Array.ofFn hfun
    _ = f.toArray := by
      apply Array.ext
      · simp
      · intro i hi1 hi2
        simp

private theorem byteDecode12VecPoly_byteEncode12Vec_eq {k : Nat} (v : TqVec k) (poly : Fin k) :
    byteDecode12VecPoly (byteEncode12Vec v) poly =
      byteDecode12Poly (byteEncode12Poly (v[poly.val])) := by
  have hfun :
      (fun idx : Fin ringDegree =>
        let pair := idx.val / 2
        let base := poly.val * 384 + 3 * pair
        let b0 := (getByteD (byteEncode12Vec v) base).toNat
        let b1 := (getByteD (byteEncode12Vec v) (poly.val * 384 + (3 * pair + 1))).toNat
        let b2 := (getByteD (byteEncode12Vec v) (poly.val * 384 + (3 * pair + 2))).toNat
        if idx.val % 2 = 0 then
          (((b0 + 256 * (b1 % 16) : Nat) : Coeff))
        else
          (((b1 / 16 + 16 * b2 : Nat) : Coeff)))
      =
      (fun idx : Fin ringDegree =>
        let pair := idx.val / 2
        let b0 := (getByteD (byteEncode12Poly (v[poly.val])) (3 * pair)).toNat
        let b1 := (getByteD (byteEncode12Poly (v[poly.val])) (3 * pair + 1)).toNat
        let b2 := (getByteD (byteEncode12Poly (v[poly.val])) (3 * pair + 2)).toNat
        if idx.val % 2 = 0 then
          (((b0 + 256 * (b1 % 16) : Nat) : Coeff))
        else
          (((b1 / 16 + 16 * b2 : Nat) : Coeff))) := by
    funext idx
    let pair := idx.val / 2
    have hpair : pair < 128 := by
      dsimp [pair]
      have : idx.val < 256 := idx.isLt
      omega
    have hb0 :
        (getByteD (byteEncode12Vec v) (poly.val * 384 + 3 * pair)).toNat =
          (getByteD (byteEncode12Poly (v[poly.val])) (3 * pair)).toNat := by
      have h :
          getByteD (byteEncode12Vec v) (poly.val * 384 + 3 * pair) =
            getByteD (byteEncode12Poly (v[poly.val])) (3 * pair) := by
        rw [getByteD_byteEncode12Vec (v := v) (poly := poly.val) (j := 3 * pair)
          poly.isLt (by omega)]
        rw [getByteD_byteEncode12Poly (f := v[poly.val]) (j := 3 * pair) (by omega)]
      exact congrArg UInt8.toNat h
    have hb1 :
        (getByteD (byteEncode12Vec v) (poly.val * 384 + (3 * pair + 1))).toNat =
          (getByteD (byteEncode12Poly (v[poly.val])) (3 * pair + 1)).toNat := by
      have h :
          getByteD (byteEncode12Vec v) (poly.val * 384 + (3 * pair + 1)) =
            getByteD (byteEncode12Poly (v[poly.val])) (3 * pair + 1) := by
        rw [getByteD_byteEncode12Vec (v := v) (poly := poly.val) (j := 3 * pair + 1) poly.isLt
          (by omega)]
        rw [getByteD_byteEncode12Poly (f := v[poly.val]) (j := 3 * pair + 1) (by omega)]
      exact congrArg UInt8.toNat h
    have hb2 :
        (getByteD (byteEncode12Vec v) (poly.val * 384 + (3 * pair + 2))).toNat =
          (getByteD (byteEncode12Poly (v[poly.val])) (3 * pair + 2)).toNat := by
      have h :
          getByteD (byteEncode12Vec v) (poly.val * 384 + (3 * pair + 2)) =
            getByteD (byteEncode12Poly (v[poly.val])) (3 * pair + 2) := by
        rw [getByteD_byteEncode12Vec (v := v) (poly := poly.val) (j := 3 * pair + 2) poly.isLt
          (by omega)]
        rw [getByteD_byteEncode12Poly (f := v[poly.val]) (j := 3 * pair + 2) (by omega)]
      exact congrArg UInt8.toNat h
    dsimp [byteDecode12VecPoly, byteDecode12Poly]
    rw [hb0, hb1, hb2]
  apply Vector.toArray_inj.mp
  unfold byteDecode12VecPoly byteDecode12Poly
  rw [Vector.toArray_ofFn, Vector.toArray_ofFn]
  exact congrArg Array.ofFn hfun

private theorem byteDecode12Vec_byteEncode12Vec {k : Nat} (v : TqVec k) :
    byteDecode12Vec k (byteEncode12Vec v) = v := by
  have hfun :
      (fun idx : Fin k => byteDecode12VecPoly (byteEncode12Vec v) idx)
      = fun idx : Fin k => v[idx.val] := by
    funext idx
    rw [byteDecode12VecPoly_byteEncode12Vec_eq (v := v) (poly := idx)]
    exact byteDecode12Poly_byteEncode12Poly (f := v[idx.val])
  apply Vector.toArray_inj.mp
  unfold byteDecode12Vec
  rw [Vector.toArray_ofFn]
  calc
    Array.ofFn (fun idx : Fin k => byteDecode12VecPoly (byteEncode12Vec v) idx)
        = Array.ofFn (fun idx : Fin k => v[idx.val]) := by
            exact congrArg Array.ofFn hfun
    _ = v.toArray := by
      apply Array.ext
      · simp
      · intro i hi1 hi2
        simp

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
  byteDecode12Vec_byteEncode12Vec := byteDecode12Vec_byteEncode12Vec
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
