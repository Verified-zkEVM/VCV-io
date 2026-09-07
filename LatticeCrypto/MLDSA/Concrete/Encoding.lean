/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLDSA.Primitives
public import LatticeCrypto.MLDSA.Concrete.Rounding
public import Mathlib.Data.List.OfFn

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

public section


namespace MLDSA.Concrete

open MLDSA

/-! ## Basic byte helpers -/

/-- Convert a fixed-length byte vector to a `ByteArray`. -/
def vectorToByteArray {n : Nat} (v : Bytes n) : ByteArray :=
  ByteArray.mk v.toArray

/-- Read `n` bytes from a `ByteArray` starting at `offset`, padding with zeros if needed. -/
def byteArrayToVector (ba : ByteArray) (offset : Nat) (n : Nat) : Vector Byte n :=
  Vector.ofFn fun i => (ba[offset + i.val]?).getD 0

/-- Extract a byte slice with zero padding beyond the end of the array. -/
def sliceByteArray (ba : ByteArray) (offset len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn fun i : Fin len => (ba[offset + i.val]?).getD 0

/-- Convert a `ByteArray` to a `List Byte`. -/
def byteArrayToList (ba : ByteArray) : List Byte :=
  ba.data.toList

/-- Concatenate a list of byte-array chunks. -/
def concatByteArrays (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) (ByteArray.mk #[])

private def bitOf (b : UInt8) (j : Nat) : Nat :=
  ((b >>> j.toUInt8) &&& 1).toNat

private def packByte (bits : Fin 8 → Nat) : UInt8 :=
  (Nat.ofDigits 2 (List.ofFn bits)).toUInt8

/-- Total byte lookup with zero fallback. -/
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

private theorem bytesToBits_size (bytes : ByteArray) :
    (bytesToBits bytes).size = bytes.size * 8 := by
  simp [bytesToBits]

private theorem bytesToBits_getElem (bytes : ByteArray) (i : Nat)
    (hi : i < (bytesToBits bytes).size) :
    (bytesToBits bytes)[i]'hi = bitOf (getByteD bytes (i / 8)) (i % 8) := by
  simp only [bytesToBits, Array.getElem_ofFn]

private theorem unpackNatArray_size (count width : Nat) (bytes : ByteArray) :
    (unpackNatArray count width bytes).size = count := by
  simp [unpackNatArray]

private theorem unpackNatArray_getElem (count width : Nat) (bytes : ByteArray) (i : Nat)
    (hi : i < (unpackNatArray count width bytes).size) :
    (unpackNatArray count width bytes)[i]'hi =
      Nat.ofDigits 2 (List.ofFn fun j : Fin width =>
        (bytesToBits bytes).getD (i * width + j.val) 0) := by
  simp only [unpackNatArray, Array.getElem_ofFn]

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

/-! ## `bitUnpackPoly` decode-range bounds

The decoder writes coefficients `b - v` for `v` a `width`-bit value, so every coefficient lies in
the integer window `[b - (2^width - 1), b]`. For the FIPS-204 `z` range `[-γ₁ + 1, γ₁]` this gives a
centered infinity norm of at most `γ₁`, independent of the (opaque) SHAKE byte input. -/

/-- Each `bitOf` value is a single bit, hence `< 2`. -/
private theorem bitOf_lt_two (b : UInt8) (j : Nat) : bitOf b j < 2 := by
  unfold bitOf
  rw [UInt8.toNat_and, show (1 : UInt8).toNat = 1 from rfl, show (2 : ℕ) = 2 ^ 1 from rfl]
  exact Nat.and_lt_two_pow _ (by norm_num)

/-- Total `Array.getD` lookup with a default agrees with indexing within bounds. -/
private theorem array_getD_eq_getElem {α : Type} (a : Array α) {i : Nat}
    (fallback : α) (h : i < a.size) : a.getD i fallback = a[i] := by
  simp [Array.getD, h]

/-- Every bit produced by `bytesToBits` is `< 2`. -/
private theorem bytesToBits_getD_lt_two (bytes : ByteArray) (i : Nat) :
    (bytesToBits bytes).getD i 0 < 2 := by
  by_cases hi : i < (bytesToBits bytes).size
  · rw [array_getD_eq_getElem (a := bytesToBits bytes) (i := i) (fallback := 0) hi]
    rw [bytesToBits_getElem]
    exact bitOf_lt_two _ _
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    norm_num

/-- Each value produced by `unpackNatArray` at width `width` is `< 2 ^ width`: it is the
`ofDigits` of `width` bits, each `< 2`. -/
private theorem unpackNatArray_getD_lt (count width : Nat) (bytes : ByteArray) (i : Nat) :
    (unpackNatArray count width bytes).getD i 0 < 2 ^ width := by
  by_cases hi : i < (unpackNatArray count width bytes).size
  · rw [array_getD_eq_getElem (a := unpackNatArray count width bytes) (i := i) (fallback := 0) hi]
    rw [unpackNatArray_getElem]
    set idx : Fin count := ⟨i, by simpa [unpackNatArray_size] using hi⟩ with hidx
    calc Nat.ofDigits 2 (List.ofFn fun j : Fin width =>
            (bytesToBits bytes).getD (idx.val * width + j.val) 0)
        < 2 ^ (List.ofFn fun j : Fin width =>
            (bytesToBits bytes).getD (idx.val * width + j.val) 0).length :=
          Nat.ofDigits_lt_base_pow_length (by norm_num)
            (fun x hx => by
              rw [List.mem_ofFn] at hx
              obtain ⟨j, rfl⟩ := hx
              exact bytesToBits_getD_lt_two _ _)
      _ = 2 ^ width := by rw [List.length_ofFn]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    positivity

/-- The `i`-th coefficient of `bitUnpackPoly bytes a b` is `b - v` cast into `Coeff`, where `v` is a
`width`-bit value (`width = rangeWidth a b`); in particular `0 ≤ v < 2 ^ width`. -/
theorem bitUnpackPoly_get (bytes : ByteArray) (a b : ℤ) (i : Fin ringDegree) :
    ∃ v : ℕ, v < 2 ^ rangeWidth a b ∧
      (bitUnpackPoly bytes a b).get i = ((b - (v : ℤ) : ℤ) : Coeff) := by
  refine ⟨(unpackNatArray ringDegree (rangeWidth a b) bytes).getD i.val 0,
    unpackNatArray_getD_lt _ _ _ _, ?_⟩
  simp only [bitUnpackPoly, Vector.get_ofFn]

/-! ## `simpleBitPack` roundtrip on the valid range

`simpleBitPackPoly f b` packs each coefficient `(f.get i).val` into `width = simpleWidth b` bits;
on the valid range (`(f.get i).val < 2 ^ width`) it is inverted by `simpleBitUnpackPoly`, hence
injective there. The proof characterizes the `Id.run` double loop in `packNatArray` as the
little-endian bit list `packBitsList`, then composes the standard `bitsToBytes`/`bytesToBits` and
`Nat.ofDigits` roundtrips. -/

/-- Pure-functional model of the bits emitted by `packNatArray vals width`: for each `vals[i]`, its
`width` little-endian bits, concatenated in index order. -/
private def packBitsList (vals : Array Nat) (width : Nat) : List Nat :=
  (List.range vals.size).flatMap fun i =>
    (List.range width).map fun bit => (vals.getD i 0 / 2 ^ bit) % 2

/-- A `for`-loop over a list that appends a per-element list to the accumulator array. -/
private theorem forIn_push_flatten (l : List Nat) (g : Nat → List Nat) (a : Array Nat) :
    (Id.run do
      let mut acc : Array Nat := a
      for i in l do
        for v in g i do
          acc := acc.push v
        pure ()
      return acc) = a ++ Array.mk (l.flatMap g) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have inner : ∀ (b : Array Nat), (Id.run do
        let mut acc : Array Nat := b
        for v in g x do
          acc := acc.push v
        return acc) = b ++ Array.mk (g x) := by
      intro b
      induction g x generalizing b with
      | nil => rfl
      | cons y ys ihy =>
        have step : (Id.run do
            let mut acc : Array Nat := b
            for v in (y :: ys) do
              acc := acc.push v
            return acc) = (Id.run do
              let mut acc : Array Nat := b.push y
              for v in ys do
                acc := acc.push v
              return acc) := by
          simp only [Id.run, List.forIn_cons]; rfl
        rw [step, ihy]
        rw [show (Array.mk (y :: ys) : Array Nat) = #[y] ++ Array.mk ys from by simp,
          show b.push y = b ++ #[y] from by simp, Array.append_assoc]
    have step : (Id.run do
        let mut acc : Array Nat := a
        for i in (x :: xs) do
          for v in g i do
            acc := acc.push v
          pure ()
        return acc) = (Id.run do
          let mut acc : Array Nat := (Id.run do
            let mut acc2 : Array Nat := a
            for v in g x do
              acc2 := acc2.push v
            return acc2)
          for i in xs do
            for v in g i do
              acc := acc.push v
            pure ()
          return acc) := by
      simp only [Id.run, List.forIn_cons]; rfl
    rw [step, inner, ih, List.flatMap_cons,
      show (Array.mk (g x ++ xs.flatMap g) : Array Nat)
        = Array.mk (g x) ++ Array.mk (xs.flatMap g) from by simp, Array.append_assoc]

/-- The bytes produced by `packNatArray` are `bitsToBytes` applied to the little-endian bit list. -/
private theorem packNatArray_eq (vals : Array Nat) (width : Nat) :
    packNatArray vals width = bitsToBytes (Array.mk (packBitsList vals width)) := by
  unfold packNatArray packBitsList
  rw [show (Id.run do
        let mut acc : Array Nat := Array.mkEmpty (vals.size * width)
        for i in [0:vals.size] do
          let v := vals.getD i 0
          for bit in [0:width] do
            acc := acc.push ((v / 2 ^ bit) % 2)
        return acc)
      = (Id.run do
        let mut acc : Array Nat := Array.mkEmpty (vals.size * width)
        for i in (List.range vals.size) do
          for v in ((List.range width).map fun bit => (vals.getD i 0 / 2 ^ bit) % 2) do
            acc := acc.push v
          pure ()
        return acc) from by
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range_eq_range', List.forIn_map]]
  rw [forIn_push_flatten]
  simp [Array.mkEmpty]

/-- Length of `packBitsList`: `vals.size` chunks of `width` bits each. -/
private theorem packBitsList_length (vals : Array Nat) (width : Nat) :
    (packBitsList vals width).length = vals.size * width := by
  simp [packBitsList, List.length_flatMap, Nat.mul_comm]

/-- The `(i * width + bit)`-th bit of `packBitsList vals width` is bit `bit` of `vals[i]`. -/
private theorem getD_flatMap_const_len {α} [Inhabited α] (n width : Nat) (h : Nat → Nat → α)
    (i bit : Nat) (hi : i < n) (hbit : bit < width) :
    ((List.range n).flatMap fun i => (List.range width).map fun b => h i b).getD (i * width + bit)
      default = h i bit := by
  have hlen : ∀ k, ((List.range k).flatMap fun i =>
      (List.range width).map fun b => h i b).length = k * width := by
    intro k; simp [List.length_flatMap, Nat.mul_comm]
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hii : i < m
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; calc i * width + bit < i*width + width := by omega
                                                  _ = (i+1)*width := by ring
                                                  _ ≤ m * width := by
                                                    exact Nat.mul_le_mul_right width hii)]
      exact ih i hii
    · have him : i = m := by omega
      subst him
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp only [List.flatMap_singleton, Nat.add_sub_cancel_left]
      rw [List.getD_eq_getElem _ _ (by simp [hbit])]
      simp

private theorem packBitsList_getD (vals : Array Nat) (width i bit : Nat)
    (hi : i < vals.size) (hbit : bit < width) :
    (packBitsList vals width).getD (i * width + bit) 0 = (vals.getD i 0 / 2 ^ bit) % 2 :=
  getD_flatMap_const_len vals.size width (fun i b => (vals.getD i 0 / 2 ^ b) % 2) i bit hi hbit

/-! ## `bitsToBytes` / `bytesToBits` roundtrip helpers (size a multiple of 8) -/

private theorem bitOf_packByte_fin :
    ∀ bits : Fin 8 → Fin 2, ∀ j : Fin 8,
      bitOf (packByte fun i => (bits i).val) j.val = (bits j).val := by
  intro bits j
  let digits := List.ofFn fun i => (bits i).val
  have hdigits : ∀ x ∈ digits, x < 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (bits i).isLt
  have hvalue : Nat.ofDigits 2 digits < 2 ^ 8 := by
    simpa [digits] using Nat.ofDigits_lt_base_pow_length (by decide) hdigits
  have hj : j.val.toUInt8.toNat = j.val := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide))
  have hhead : (digits.drop j.val).head! = (bits j).val := by
    rw [List.head!_eq_getElem!, List.getElem!_eq_getElem?_getD, List.getElem?_drop]
    simp only [Nat.add_zero]
    rw [List.getElem?_eq_getElem (by simp [digits, j.isLt])]
    exact List.getElem_ofFn (by simp [j.isLt])
  unfold bitOf packByte
  simp only [UInt8.toNat_and, UInt8.toNat_shiftRight]
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hvalue, hj,
    Nat.mod_eq_of_lt j.isLt, show (1 : UInt8).toNat = 1 from rfl,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.ofDigits_div_pow_eq_ofDigits_drop j.val (by decide) digits hdigits,
    Nat.ofDigits_mod_eq_head!, hhead, Nat.mod_eq_of_lt (bits j).isLt]

private theorem bytearray_mk_getByteD {arr : Array UInt8} {i : Nat} (h : i < arr.size) :
    getByteD (ByteArray.mk arr) i = arr[i] := by
  unfold getByteD
  have hsz : i < (ByteArray.mk arr).size := by simpa [ByteArray.size] using h
  rw [getElem?_pos (ByteArray.mk arr) i hsz]; rfl

private theorem getByteD_bitsToBytes (bits : Array Nat) (b : Nat)
    (hb : b < (bits.size + 7) / 8) :
    getByteD (bitsToBytes bits) b = packByte fun j => bits.getD (8 * b + j.val) 0 := by
  unfold bitsToBytes
  rw [bytearray_mk_getByteD (by simpa using hb), Array.getElem_ofFn]

private theorem bitsToBytes_size_of_mod (bits : Array Nat) (h : bits.size % 8 = 0) :
    (bitsToBytes bits).size = bits.size / 8 := by
  simp [bitsToBytes, ByteArray.size]; omega

private theorem bytesToBits_bitsToBytes_getD {bits : Array Nat} {i : Nat}
    (hsize : bits.size % 8 = 0)
    (hbits : ∀ j, j < bits.size → bits.getD j 0 < 2)
    (hi : i < bits.size) :
    (bytesToBits (bitsToBytes bits)).getD i 0 = bits.getD i 0 := by
  have hmul : 8 * (bits.size / 8) = bits.size := by omega
  have hbsize : (bitsToBytes bits).size = bits.size / 8 := bitsToBytes_size_of_mod bits hsize
  have hilt : i < (bytesToBits (bitsToBytes bits)).size := by
    simp only [bytesToBits, Array.size_ofFn, hbsize]; omega
  rw [array_getD_eq_getElem (a := bytesToBits (bitsToBytes bits)) 0 hilt]
  rw [bytesToBits_getElem]
  have hbyte : i / 8 < (bits.size + 7) / 8 := by omega
  have hbit : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hindex : 8 * (i / 8) + i % 8 = i := by omega
  change bitOf (getByteD (bitsToBytes bits) (i / 8)) (i % 8) = bits.getD i 0
  rw [getByteD_bitsToBytes bits (i / 8) hbyte]
  have hpack := bitOf_packByte_fin
    (fun j => ⟨bits.getD (8 * (i / 8) + j.val) 0, hbits _ (by omega)⟩) ⟨i % 8, hbit⟩
  simp only at hpack
  rw [hpack, hindex]

/-! ## `Nat.ofDigits` bit-decomposition recovery -/

private theorem ofDigits_bits (v width : Nat) (hv : v < 2 ^ width) :
    Nat.ofDigits 2 (List.ofFn fun j : Fin width => (v / 2 ^ j.val) % 2) = v := by
  induction width generalizing v with
  | zero => simp only [pow_zero] at hv; interval_cases v; simp
  | succ w ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    have hbits : (fun (i : Fin w) => (v / 2 ^ (Fin.succ i).val) % 2)
        = (fun (i : Fin w) => ((v / 2) / 2 ^ i.val) % 2) := by
      funext i
      rw [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [hbits, ih (v / 2)
      (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hv; omega)]
    omega

/-! ## `simpleBitPackPoly` roundtrip and injectivity on the valid range -/

/-- Generic `unpackNatArray ∘ packNatArray` roundtrip: at any index `i < vals.size`, decoding a
`width`-bit packing recovers `vals[i]`, provided every entry fits in `width` bits and
`vals.size * width` is a multiple of 8 (so the byte packing has no relevant padding). -/
private theorem unpackNatArray_packNatArray_getD (vals : Array Nat) (width i : Nat)
    (hi : i < vals.size) (hwpos : 0 < width)
    (hmod : vals.size * width % 8 = 0)
    (hvalsbnd : ∀ j, j < vals.size → vals.getD j 0 < 2 ^ width) :
    (unpackNatArray vals.size width (packNatArray vals width)).getD i 0 = vals.getD i 0 := by
  have hbitsize : (packBitsList vals width).length = vals.size * width := packBitsList_length _ _
  have hbits_lt : ∀ j, j < (packBitsList vals width).length →
      (packBitsList vals width).getD j 0 < 2 := by
    intro j hj
    rw [hbitsize] at hj
    have hjw : j / width < vals.size := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
    have hmodw : j % width < width := Nat.mod_lt _ hwpos
    have hjeq : (j / width) * width + j % width = j := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod j width
    rw [← hjeq, packBitsList_getD vals width _ _ hjw hmodw]
    exact Nat.mod_lt _ (by norm_num)
  rw [packNatArray_eq]
  rw [array_getD_eq_getElem (a := unpackNatArray vals.size width _) 0
    (by simp [unpackNatArray, hi])]
  unfold unpackNatArray
  rw [Array.getElem_ofFn]
  have hsize_mk : (Array.mk (packBitsList vals width)).size
      = (packBitsList vals width).length := List.size_toArray
  have hgetD_mk : ∀ j, (Array.mk (packBitsList vals width)).getD j 0
      = (packBitsList vals width).getD j 0 := by
    intro j
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  have hread : (List.ofFn fun j : Fin width =>
      (bytesToBits (bitsToBytes (Array.mk (packBitsList vals width)))).getD
        ((⟨i, hi⟩ : Fin vals.size).val * width + j.val) 0)
      = List.ofFn fun j : Fin width => (vals.getD i 0 / 2 ^ j.val) % 2 := by
    apply List.ext_getElem (by simp)
    intro k hk1 _
    simp only [List.getElem_ofFn]
    have hkw : k < width := by simpa using hk1
    have hpos : i * width + k < (packBitsList vals width).length := by
      rw [hbitsize]
      calc i * width + k < i * width + width := by omega
        _ = (i + 1) * width := by ring
        _ ≤ vals.size * width := Nat.mul_le_mul_right width hi
    rw [bytesToBits_bitsToBytes_getD (i := i * width + k)
      (by rw [hsize_mk, hbitsize]; exact hmod)
      (by intro j hj; rw [hsize_mk] at hj; rw [hgetD_mk]; exact hbits_lt j hj)
      (by rw [hsize_mk]; exact hpos)]
    rw [hgetD_mk, packBitsList_getD vals width i k hi hkw]
  rw [hread, ofDigits_bits _ width (hvalsbnd i hi)]

/-- `simpleBitUnpackPoly` inverts `simpleBitPackPoly` on polynomials whose coefficients fit in
`simpleWidth b` bits: `(f.get i).val < 2 ^ simpleWidth b` for all `i`. -/
theorem simpleBitUnpackPoly_simpleBitPackPoly (f : Rq) (b : Nat)
    (hf : ∀ i : Fin ringDegree, (f.get i).val < 2 ^ simpleWidth b) :
    simpleBitUnpackPoly (simpleBitPackPoly f b) b = f := by
  have hwpos : 0 < simpleWidth b := by unfold simpleWidth; omega
  set vals : Array Nat := Array.ofFn fun i : Fin ringDegree => (f.get i).val with hvals
  have hvalsize : vals.size = ringDegree := by simp [hvals]
  have hbnd : ∀ j, j < vals.size → vals.getD j 0 < 2 ^ simpleWidth b := by
    intro j hj
    rw [hvalsize] at hj
    rw [hvals, array_getD_eq_getElem (a := Array.ofFn _) 0 (by simpa using hj)]
    simpa using hf ⟨j, hj⟩
  apply LatticeCrypto.Poly.ext_get_eq
  intro i
  simp only [simpleBitUnpackPoly, simpleBitPackPoly, ← hvals]
  rw [Vector.get_ofFn]
  have hkey := unpackNatArray_packNatArray_getD vals (simpleWidth b) i.val
    (by rw [hvalsize]; exact i.isLt) hwpos
    (by rw [hvalsize]; show ringDegree * simpleWidth b % 8 = 0;
        rw [show ringDegree = 256 from rfl]; omega) hbnd
  rw [hvalsize] at hkey
  rw [hkey]
  rw [hvals, array_getD_eq_getElem (a := Array.ofFn _) 0 (by simp [i.isLt])]
  simp

/-! ## Polynomial codec specializations -/

/-- Packed size of an `η`-bounded polynomial. -/
def polyEtaPackedBytes (p : Params) : Nat :=
  ringDegree * rangeWidth (-(p.eta : ℤ)) p.eta / 8

/-- Packed size of a `t₁` polynomial. -/
def polyT1PackedBytes : Nat :=
  ringDegree * simpleWidth (2 ^ (Nat.log2 (modulus - 1) + 1 - droppedBits) - 1) / 8

/-- Packed size of a `t₀` polynomial. -/
def polyT0PackedBytes : Nat :=
  ringDegree * rangeWidth (-(2 ^ (droppedBits - 1) - 1 : ℤ)) (2 ^ (droppedBits - 1) : ℤ) / 8

/-- Packed size of a `z` polynomial. -/
def polyZPackedBytes (p : Params) : Nat :=
  ringDegree * rangeWidth (-(p.gamma1 : ℤ) + 1) p.gamma1 / 8

/-- Packed size of a `w₁` polynomial. -/
def polyW1PackedBytes (p : Params) : Nat :=
  ringDegree * simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) / 8

/-- Encode an `η`-bounded polynomial with the FIPS 204 bit-pack format. -/
def polyEtaPack (p : Params) (f : Rq) : ByteArray :=
  bitPackPoly f (-(p.eta : ℤ)) p.eta

/-- Decode an `η`-bounded polynomial from the FIPS 204 bit-pack format. -/
def polyEtaUnpack (p : Params) (bytes : ByteArray) : Rq :=
  bitUnpackPoly bytes (-(p.eta : ℤ)) p.eta

/-- Encode a `t₁` polynomial. -/
def polyT1Pack (f : Power2High) : ByteArray :=
  simpleBitPackPoly f (2 ^ (Nat.log2 (modulus - 1) + 1 - droppedBits) - 1)

/-- Decode a `t₁` polynomial. -/
def polyT1Unpack (bytes : ByteArray) : Power2High :=
  simpleBitUnpackPoly bytes (2 ^ (Nat.log2 (modulus - 1) + 1 - droppedBits) - 1)

/-- Encode a `t₀` polynomial. -/
def polyT0Pack (f : Rq) : ByteArray :=
  bitPackPoly f (-(2 ^ (droppedBits - 1) - 1 : ℤ)) (2 ^ (droppedBits - 1) : ℤ)

/-- Decode a `t₀` polynomial. -/
def polyT0Unpack (bytes : ByteArray) : Rq :=
  bitUnpackPoly bytes (-(2 ^ (droppedBits - 1) - 1 : ℤ)) (2 ^ (droppedBits - 1) : ℤ)

/-- Encode a `z` polynomial. -/
def polyZPack (p : Params) (f : Rq) : ByteArray :=
  bitPackPoly f (-(p.gamma1 : ℤ) + 1) p.gamma1

/-- Decode a `z` polynomial. -/
def polyZUnpack (p : Params) (bytes : ByteArray) : Rq :=
  bitUnpackPoly bytes (-(p.gamma1 : ℤ) + 1) p.gamma1

/-- Encode a `w₁` polynomial. -/
def polyW1Pack (p : Params) (f : High) : ByteArray :=
  simpleBitPackPoly f ((modulus - 1) / (2 * p.gamma2) - 1)

/-! ## Vector-level packers -/

private def packPolyVector {k : Nat} (v : Vector Rq k) (pack : Rq → ByteArray) : ByteArray :=
  concatByteArrays <| v.toList.map pack

private def unpackPolyVector (k chunkSize : Nat) (bytes : ByteArray) (unpack : ByteArray → Rq) :
    Vector Rq k :=
  Vector.ofFn fun i => unpack (sliceByteArray bytes (i.val * chunkSize) chunkSize)

/-! ## Vector-level packer roundtrip on the valid range

`packPolyVector` concatenates fixed-size per-polynomial packings; `unpackPolyVector` slices them
back out. When the per-polynomial codec is a left inverse on the valid range, the vector codec is
too, hence `packPolyVector` is injective on valid vectors. -/

/-- Total `ByteArray` lookup agrees with the `toList` lookup. -/
private theorem ba_getElem?_getD (ba : ByteArray) (i : Nat) :
    ba[i]?.getD 0 = ba.data.toList[i]?.getD 0 := by
  have hlen : ba.data.toList.length = ba.size := by rw [Array.length_toList]; rfl
  by_cases h : i < ba.size
  · rw [getElem?_pos ba i h, List.getElem?_eq_getElem (by omega), Option.getD_some,
      Option.getD_some, ByteArray.getElem_eq_getElem_data]
    rfl
  · rw [getElem?_neg ba i h, List.getElem?_eq_none_iff.mpr (by omega), Option.getD_none]

/-- The size of `simpleBitPackPoly` is independent of the polynomial. -/
private theorem simpleBitPackPoly_size (f : Rq) (m : Nat) :
    (simpleBitPackPoly f m).size = (ringDegree * simpleWidth m + 7) / 8 := by
  unfold simpleBitPackPoly
  rw [packNatArray_eq]
  simp only [bitsToBytes, ByteArray.size, Array.size_ofFn, List.size_toArray, packBitsList_length]

/-- `(packPolyVector v pack).data.toList` is the concatenation of the per-element packings. -/
private theorem packPolyVector_data_toList {k : Nat} (v : Vector Rq k) (pack : Rq → ByteArray) :
    (packPolyVector v pack).data.toList
      = (v.toList.map fun f => (pack f).data.toList).flatten := by
  unfold packPolyVector concatByteArrays
  have gen : ∀ (acc : ByteArray) (l : List ByteArray),
      (l.foldl (· ++ ·) acc).data.toList
        = acc.data.toList ++ (l.map fun c => c.data.toList).flatten := by
    intro acc l
    induction l generalizing acc with
    | nil => simp
    | cons c cs ih =>
      rw [List.foldl_cons, ih (acc ++ c), ByteArray.data_append, Array.toList_append]
      simp
  rw [gen]
  simp only [List.nil_append, List.map_map]
  rfl

private theorem getElem_flatten_const {α} (chunks : List (List α)) (sz : Nat)
    (hsz : ∀ c ∈ chunks, c.length = sz)
    (i j : Nat) (hi : i < chunks.length) (hj : j < sz) :
    chunks.flatten[i * sz + j]? = (chunks[i]'hi)[j]? := by
  induction chunks generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    have hc : c.length = sz := hsz c (by simp)
    rw [List.flatten_cons]
    by_cases hii : i = 0
    · subst hii
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [List.getElem?_append_left (by omega)]; simp
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [List.getElem?_append_right (by rw [hc]; nlinarith [Nat.zero_le (i' * sz)]), hc]
      have heq : (i' + 1) * sz + j - sz = i' * sz + j := by ring_nf; omega
      rw [heq]
      simp only [List.getElem_cons_succ]
      exact ih (fun c hc => hsz c (by simp [hc])) i' (by simpa using hi)

/-- Slicing chunk `i` out of `packPolyVector` recovers the `i`-th packing, when every chunk has the
common size `chunkSize`. -/
private theorem sliceByteArray_packPolyVector {k : Nat} (v : Vector Rq k) (pack : Rq → ByteArray)
    (chunkSize : Nat) (hpack : ∀ f, (pack f).size = chunkSize) (i : Fin k) :
    sliceByteArray (packPolyVector v pack) (i.val * chunkSize) chunkSize = pack (v.get i) := by
  have hmkdata : ∀ a : Array UInt8, (ByteArray.mk a).data = a := fun _ => rfl
  apply ByteArray.ext
  apply Array.ext
  · rw [show (sliceByteArray (packPolyVector v pack) (i.val * chunkSize) chunkSize).data.size
        = chunkSize from by simp [sliceByteArray, hmkdata, Array.size_ofFn],
      show (pack (v.get i)).data.size = (pack (v.get i)).size from rfl, hpack]
  · intro j hj1 _
    have hjlt : j < chunkSize := by
      simpa only [sliceByteArray, hmkdata, Array.size_ofFn] using hj1
    simp only [sliceByteArray, hmkdata, Array.getElem_ofFn]
    rw [ba_getElem?_getD, packPolyVector_data_toList]
    rw [getElem_flatten_const (v.toList.map fun f => (pack f).data.toList) chunkSize
      (by intro c hc; simp only [List.mem_map] at hc; obtain ⟨f, _, rfl⟩ := hc
          rw [Array.length_toList, show (pack f).data.size = (pack f).size from rfl, hpack])
      i.val j (by simp [i.isLt]) hjlt]
    rw [List.getElem_map]
    have hvget : v.toList[i.val]'(by simp [i.isLt]) = v.get i := by
      simp [Vector.get]
    rw [hvget]
    rw [List.getElem?_eq_getElem (by
      rw [Array.length_toList, show (pack (v.get i)).data.size = (pack (v.get i)).size from rfl,
        hpack]; exact hjlt)]
    rw [Option.getD_some, Array.getElem_toList]

/-- `unpackPolyVector` inverts `packPolyVector` on vectors whose every component is fixed by the
per-polynomial codec roundtrip. -/
private theorem unpackPolyVector_packPolyVector {k chunkSize : Nat} (v : Vector Rq k)
    (pack : Rq → ByteArray) (unpack : ByteArray → Rq)
    (hpack : ∀ f, (pack f).size = chunkSize)
    (hroundtrip : ∀ i : Fin k, unpack (pack (v.get i)) = v.get i) :
    unpackPolyVector k chunkSize (packPolyVector v pack) unpack = v := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro i
  simp only [unpackPolyVector, Vector.get_ofFn]
  rw [sliceByteArray_packPolyVector v pack chunkSize hpack i, hroundtrip i]

/-- `w1Encode(w₁)` (Algorithm 28). -/
def w1EncodeBytes (p : Params) (w1 : Vector High p.k) : ByteArray :=
  packPolyVector w1 (polyW1Pack p)

/-- FIPS 204 `w1Encode`, returned as a byte list. -/
def w1Encode (p : Params) (w1 : Vector High p.k) : List Byte :=
  byteArrayToList (w1EncodeBytes p w1)

/-- `byteArrayToList` is injective. -/
private theorem byteArrayToList_injective : Function.Injective byteArrayToList := by
  intro a b hab
  apply ByteArray.ext
  apply Array.ext'
  simpa [byteArrayToList] using hab

/-- `w1Encode` is injective on the range of commitment vectors whose every coefficient fits in the
`w₁` packer's bit width `simpleWidth ((q-1)/(2γ₂) - 1)`. The `w₁` packer is `simpleBitPackPoly` at
that width, which is inverted by `simpleBitUnpackPoly` on this range. -/
theorem w1Encode_injOn (p : Params) :
    Set.InjOn (w1Encode p)
      { w : Vector High p.k | ∀ i : Fin p.k, ∀ c : Fin ringDegree,
          ((w.get i).get c).val < 2 ^ simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) } := by
  set m := (modulus - 1) / (2 * p.gamma2) - 1 with hm
  intro w1 hw1 w2 hw2 heq
  -- Strip `byteArrayToList`, reducing to equality of the packed `ByteArray`s.
  have hbytes : w1EncodeBytes p w1 = w1EncodeBytes p w2 :=
    byteArrayToList_injective heq
  -- Decode both sides with `unpackPolyVector` (a left inverse on the valid range).
  have hchunk : ∀ f : High, (polyW1Pack p f).size
      = (ringDegree * simpleWidth m + 7) / 8 := fun f => simpleBitPackPoly_size f m
  have hround : ∀ (w : Vector High p.k),
      (∀ i : Fin p.k, ∀ c : Fin ringDegree, ((w.get i).get c).val < 2 ^ simpleWidth m) →
      unpackPolyVector p.k ((ringDegree * simpleWidth m + 7) / 8) (w1EncodeBytes p w)
        (fun bytes => simpleBitUnpackPoly bytes m) = w := by
    intro w hw
    rw [w1EncodeBytes]
    exact unpackPolyVector_packPolyVector w (polyW1Pack p)
      (fun bytes => simpleBitUnpackPoly bytes m) hchunk
      (fun i => simpleBitUnpackPoly_simpleBitPackPoly (w.get i) m (fun c => hw i c))
  rw [← hround w1 hw1, ← hround w2 hw2, hbytes]

/-! ## Key and signature encodings -/

/-- Encode an ML-DSA public key as `ρ || t₁`. -/
def pkEncode (p : Params) (rho : Bytes 32) (t1 : Vector Power2High p.k) : ByteArray :=
  vectorToByteArray rho ++ packPolyVector t1 polyT1Pack

/-- Decode an ML-DSA public key from `ρ || t₁`. -/
def pkDecode (p : Params) (bytes : ByteArray) : Bytes 32 × Vector Power2High p.k :=
  let rho := byteArrayToVector bytes 0 32
  let t1Bytes := sliceByteArray bytes 32 (p.k * polyT1PackedBytes)
  let t1 := unpackPolyVector p.k polyT1PackedBytes t1Bytes polyT1Unpack
  (rho, t1)

/-- Encode an ML-DSA secret key as the concatenation of seeds and packed secret polynomials. -/
def skEncode (p : Params) (rho key : Bytes 32) (tr : Bytes 64)
    (s1 : RqVec p.l) (s2 t0 : RqVec p.k) : ByteArray :=
  vectorToByteArray rho ++
  vectorToByteArray key ++
  vectorToByteArray tr ++
  packPolyVector s1 (polyEtaPack p) ++
  packPolyVector s2 (polyEtaPack p) ++
  packPolyVector t0 polyT0Pack

/-- Decode an ML-DSA secret key from its concrete byte encoding. -/
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

/-- Pack the sparse hint vector into the FIPS 204 hint-byte format. -/
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

/-- Decode a sparse hint vector from the FIPS 204 hint-byte format. -/
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

/-- Encode an ML-DSA signature as `c̃ || z || h`. -/
def sigEncode (p : Params) (cTilde : CommitHashBytes p) (z : RqVec p.l) (h : Vector Hint p.k) :
    ByteArray :=
  vectorToByteArray cTilde ++ packPolyVector z (polyZPack p) ++ hintBitPack p h

/-- Decode an ML-DSA signature from `c̃ || z || h`. -/
def sigDecode (p : Params) (bytes : ByteArray) :
    Option (CommitHashBytes p × RqVec p.l × Vector Hint p.k) :=
  let cLen := p.lambda / 4
  let zLen := p.l * polyZPackedBytes p
  let hLen := p.omega + p.k
  if bytes.size ≠ cLen + zLen + hLen then
    none
  else
    let zOff := cLen
    let hOff := zOff + zLen
    let cTilde := byteArrayToVector bytes 0 cLen
    let zBytes := sliceByteArray bytes zOff zLen
    let z := unpackPolyVector p.l (polyZPackedBytes p) zBytes (polyZUnpack p)
    match hintBitUnpack p (sliceByteArray bytes hOff hLen) with
    | some h => some (cTilde, z, h)
    | none => none

end MLDSA.Concrete
