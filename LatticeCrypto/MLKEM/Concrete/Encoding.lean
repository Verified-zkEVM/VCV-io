/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Encoding
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Concrete Encoding for ML-KEM

Pure-Lean executable implementation of the byte-encoding (FIPS 203 Algorithms 4–5) and
compression / decompression (FIPS 203 Section 4.2.1) operations.
-/

namespace MLKEM.Concrete

open MLKEM

local instance : NeZero modulus := by
  unfold modulus
  exact ⟨by decide⟩

/-! ## Bit-level helpers -/

/-- Extract the `j`-th bit (LSB = 0) of a byte. -/
private def bitOf (b : UInt8) (j : Nat) : Nat :=
  ((b >>> j.toUInt8) &&& 1).toNat

/-- Pack eight little-endian bits into one byte. -/
private def packByte (bits : Fin 8 → Nat) : UInt8 :=
  (Nat.ofDigits 2 (List.ofFn bits)).toUInt8

-- These finite bit-twiddling identities are auxiliary byte-level facts.
set_option maxRecDepth 1200 in
private theorem bitOf_packByte_fin :
    ∀ bits : Fin 8 → Fin 2, ∀ j : Fin 8,
      bitOf (packByte fun i => (bits i).val) j.val = (bits j).val := by
  intro bits j; fin_cases j <;> revert bits <;> decide

private theorem bitOf_lt_two (b : UInt8) (j : Nat) : bitOf b j < 2 := by
  unfold bitOf
  rw [UInt8.toNat_and, show (1 : UInt8).toNat = 1 from rfl,
      show (2 : ℕ) = 2 ^ 1 from rfl]
  exact Nat.and_lt_two_pow _ (by norm_num)

private theorem bitOf_lt_two_fin_aux :
    ∀ n : Fin (2 ^ 8), ∀ j : Fin 8, bitOf n.val.toUInt8 j.val < 2 := by
  intro _ _; exact bitOf_lt_two _ _

private theorem bitOf_lt_two_fin (b : UInt8) (j : Fin 8) : bitOf b j.val < 2 :=
  bitOf_lt_two b j.val

private theorem packByte_bitOf_fin :
    ∀ n : Fin (2 ^ 8), packByte (fun j => bitOf n.val.toUInt8 j.val) = n.val.toUInt8 := by
  intro n; fin_cases n <;> rfl

private theorem packByte_bitOf_byte (b : UInt8) :
    packByte (fun j => bitOf b j.val) = b := by
  simpa using packByte_bitOf_fin ⟨b.toNat, UInt8.toNat_lt b⟩

private theorem array_getD_eq_getElem {α : Type} (a : Array α) {i : Nat}
    {fallback : α} (hi : i < a.size) :
    a.getD i fallback = a[i] := by
  simp [Array.getD, hi]

/-- Total byte lookup with zero fallback. -/
private def getByteD (bytes : ByteArray) (i : Nat) : UInt8 :=
  (bytes[i]?).getD 0

/-- Pack an array of individual bits (0/1 as `Nat`) into bytes, little-endian bit order. -/
private def bitsToBytes (bits : Array Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn fun idx : Fin (bits.size / 8) =>
    packByte fun j => bits.getD (8 * idx.val + j.val) 0

/-- Unpack bytes into individual bits, little-endian bit order. -/
private def bytesToBits (bytes : ByteArray) : Array Nat :=
  Array.ofFn fun idx : Fin (bytes.size * 8) =>
    let byteIdx := idx.val / 8
    let bitIdx := idx.val % 8
    have hbyte : byteIdx < bytes.size := by
      have : idx.val < 8 * bytes.size := by
        omega
      exact Nat.div_lt_of_lt_mul this
    bitOf (bytes[byteIdx]'hbyte) bitIdx

private theorem bytesToBits_bitsToBytes_getElem {bits : Array Nat} {i : Nat}
    (hsize : bits.size % 8 = 0)
    (hbits : ∀ j, j < bits.size → bits.getD j 0 < 2)
    (hi : i < bits.size) :
    (bytesToBits (bitsToBytes bits))[i]'(by
      have hmul : 8 * (bits.size / 8) = bits.size := by
        simpa [hsize] using (Nat.mod_add_div bits.size 8)
      have hsizeBitsToBytesData : (bitsToBytes bits).data.size = bits.size / 8 := by
        simp [bitsToBytes]
      have hsizeBitsToBytes : (bitsToBytes bits).size = bits.size / 8 := by
        simpa [ByteArray.size_data] using hsizeBitsToBytesData
      simpa [bytesToBits, hsizeBitsToBytes, Nat.mul_comm, hmul] using hi)
      = bits[i] := by
  have hmul : 8 * (bits.size / 8) = bits.size := by
    simpa [hsize] using (Nat.mod_add_div bits.size 8)
  let byteIdx := i / 8
  let bitIdx := i % 8
  have hbyte : byteIdx < bits.size / 8 := by
    dsimp [byteIdx]
    have : i < 8 * (bits.size / 8) := by simpa [hmul] using hi
    exact Nat.div_lt_of_lt_mul this
  have hbit : bitIdx < 8 := by
    dsimp [bitIdx]
    exact Nat.mod_lt _ (by decide)
  have hpacked :
      bitOf (packByte fun j => bits.getD (8 * byteIdx + j.val) 0) bitIdx =
        bits.getD (8 * byteIdx + bitIdx) 0 := by
    let packedBits : Fin 8 → Fin 2 := fun j =>
      ⟨bits.getD (8 * byteIdx + j.val) 0,
        hbits (8 * byteIdx + j.val) (by
          have : 8 * byteIdx + j.val < 8 * (bits.size / 8) := by
            omega
          simpa [hmul, Nat.mul_comm] using this)⟩
    have hpack :=
      bitOf_packByte_fin (bits := packedBits) (j := ⟨bitIdx, hbit⟩)
    simpa [packedBits]
      using hpack
  have hindex : 8 * byteIdx + bitIdx = i := by
    dsimp [byteIdx, bitIdx]
    simpa [Nat.add_comm] using (Nat.mod_add_div i 8)
  unfold bytesToBits bitsToBytes
  rw [Array.getElem_ofFn]
  simp only
  rw [ByteArray.getElem_eq_getElem_data]
  rw [Array.getElem_ofFn]
  rw [hpacked, hindex]
  simp [hi]

private theorem bitsToBytes_bytesToBits (bytes : ByteArray) :
    bitsToBytes (bytesToBits bytes) = bytes := by
  apply ByteArray.ext
  apply Array.ext
  · simp [bitsToBytes, bytesToBits, ByteArray.size_data]
  · intro i hi1 hi2
    have hi : i < bytes.size := by
      simpa [bitsToBytes, bytesToBits, ByteArray.size_data] using hi1
    unfold bitsToBytes
    rw [Array.getElem_ofFn]
    have hbitsEq :
        (fun j : Fin 8 => (bytesToBits bytes).getD (8 * i + j.val) 0) =
          fun j : Fin 8 => bitOf (bytes[i]'hi) j.val := by
      funext j
      have hij : 8 * i + j.val < (bytesToBits bytes).size := by
        have : 8 * i + j.val < bytes.size * 8 := by
          omega
        simpa [bytesToBits, Nat.mul_comm] using this
      rw [array_getD_eq_getElem (a := bytesToBits bytes) (i := 8 * i + j.val) (fallback := 0) hij]
      unfold bytesToBits
      rw [Array.getElem_ofFn]
      have hdiv : (8 * i + j.val) / 8 = i := by
        calc
          (8 * i + j.val) / 8 = (j.val + i * 8) / 8 := by ac_rfl
          _ = j.val / 8 + i := Nat.add_mul_div_right j.val i (by decide)
          _ = i := by simp [Nat.div_eq_of_lt j.isLt]
      have hmod : (8 * i + j.val) % 8 = j.val := by
        calc
          (8 * i + j.val) % 8 = (j.val + i * 8) % 8 := by ac_rfl
          _ = j.val % 8 := Nat.add_mul_mod_self_right j.val i 8
          _ = j.val := Nat.mod_eq_of_lt j.isLt
      simp [hdiv, hmod]
    have hpack :
        packByte (fun j => (bytesToBits bytes).getD (8 * i + j.val) 0) =
          packByte (fun j => bitOf (bytes[i]'hi) j.val) := by
      simpa using congrArg packByte hbitsEq
    rw [hpack, packByte_bitOf_byte]
    rw [ByteArray.getElem_eq_getElem_data]
    rfl

private theorem bytesToBits_getD_lt_two (bytes : ByteArray) (i : Nat) :
    (bytesToBits bytes).getD i 0 < 2 := by
  by_cases hi : i < (bytesToBits bytes).size
  · rw [array_getD_eq_getElem (a := bytesToBits bytes) (i := i) (fallback := 0) hi]
    unfold bytesToBits
    rw [Array.getElem_ofFn]
    let byteIdx := i / 8
    let bitIdx := i % 8
    have hbit : bitIdx < 8 := by
      dsimp [bitIdx]
      exact Nat.mod_lt _ (by decide)
    simpa [byteIdx, bitIdx] using
      bitOf_lt_two_fin (b := bytes[byteIdx]'(by
        dsimp [byteIdx]
        have : i < 8 * bytes.size := by simpa [bytesToBits, Nat.mul_comm] using hi
        exact Nat.div_lt_of_lt_mul this))
        (j := ⟨bitIdx, hbit⟩)
  · simp [Array.getD, hi]

private theorem ofDigits_digitsAppend_two {d n : Nat} (hn : n < 2 ^ d) :
    Nat.ofDigits 2 (Nat.digitsAppend 2 d n) = n := by
  simpa using (Nat.setInvOn_digitsAppend_ofDigits (b := 2) (by decide) d).2 hn

private theorem digitsAppend_getD_two_lt {d n bit : Nat} (hn : n < 2 ^ d) (hbit : bit < d) :
    (Nat.digitsAppend 2 d n).getD bit 0 < 2 := by
  rw [List.getD_eq_getElem _ _ (by simpa [Nat.length_digitsAppend (by decide) d hn] using hbit)]
  exact Nat.lt_of_mem_digitsAppend (by decide) d _ (List.getElem_mem _)

private theorem digitsAppend_two_one_getD_zero :
    ∀ n : Fin 2, (Nat.digitsAppend 2 1 n.val).getD 0 0 = n.val := by
  decide

private theorem digitsAppend_two_one_getD_zero_mod (n : Nat) :
    (Nat.digitsAppend 2 1 (n % 2 ^ 1)).getD 0 0 = n % 2 := by
  simpa [Nat.pow_one] using digitsAppend_two_one_getD_zero ⟨n % 2, Nat.mod_lt _ (by decide)⟩

/-! ## ByteEncode / ByteDecode (Algorithms 4–5) -/

/-- FIPS 203 Algorithm 4: encode 256 `d`-bit coefficients into `32d` bytes. -/
def byteEncode (d : Nat) (f : Rq) : ByteArray :=
  let bits : Array Nat := Array.ofFn fun idx : Fin (ringDegree * d) =>
    let coeff := idx.val / d
    let bit := idx.val % d
    have hcoeff : coeff < ringDegree := by
      by_cases hd : d = 0
      · subst hd
        have hlt0 : idx.val < 0 := by
          simpa [ringDegree] using idx.isLt
        exact False.elim (Nat.not_lt_zero _ hlt0)
      · have hdPos : 0 < d := Nat.pos_of_ne_zero hd
        have hlt : idx.val < d * ringDegree := by simpa [Nat.mul_comm] using idx.isLt
        exact Nat.div_lt_of_lt_mul hlt
    let coeffBits := Nat.digitsAppend 2 d (((f[coeff]'hcoeff : Coeff).val) % 2 ^ d)
    coeffBits.getD bit 0
  bitsToBytes bits

/-- FIPS 203 Algorithm 5: decode `32d` bytes into 256 coefficients. -/
def byteDecode (d : Nat) (bytes : ByteArray) : Rq :=
  let bits := bytesToBits bytes
  Vector.ofFn fun idx =>
    let coeffBits := List.ofFn fun j : Fin d => bits.getD (idx.val * d + j.val) 0
    ((Nat.ofDigits 2 coeffBits : Nat) : Coeff)

private theorem byteEncode_size (d : Nat) (f : Rq) :
    (byteEncode d f).size = 32 * d := by
  let bits : Array Nat := Array.ofFn fun idx : Fin (ringDegree * d) =>
    let coeff := idx.val / d
    let bit := idx.val % d
    have hcoeff : coeff < ringDegree := by
      by_cases hd : d = 0
      · subst hd
        have hlt0 : idx.val < 0 := by
          simpa [ringDegree] using idx.isLt
        exact False.elim (Nat.not_lt_zero _ hlt0)
      · have hlt : idx.val < d * ringDegree := by simpa [Nat.mul_comm] using idx.isLt
        exact Nat.div_lt_of_lt_mul hlt
    let coeffBits := Nat.digitsAppend 2 d (((f[coeff]'hcoeff : Coeff).val) % 2 ^ d)
    coeffBits.getD bit 0
  have hencode : byteEncode d f = bitsToBytes bits := by
    simp [byteEncode, bits]
  have hbitsLen : bits.size = ringDegree * d := by
    simp [bits]
  have hsizeBitsToBytesData : (bitsToBytes bits).data.size = bits.size / 8 := by
    simp [bitsToBytes]
  have hsizeBitsToBytes : (bitsToBytes bits).size = bits.size / 8 := by
    simpa [ByteArray.size_data] using hsizeBitsToBytesData
  rw [hencode, hsizeBitsToBytes, hbitsLen]
  simp [ringDegree]
  omega

private theorem byteDecode_byteEncode_of_bound {d : Nat} (hd : 0 < d) (f : Rq)
    (hbound : ∀ idx : Fin ringDegree, ((f[idx.val] : Coeff).val) < 2 ^ d) :
    byteDecode d (byteEncode d f) = f := by
  let bits : Array Nat := Array.ofFn fun idx : Fin (ringDegree * d) =>
    let coeff := idx.val / d
    let bit := idx.val % d
    have hcoeff : coeff < ringDegree := by
      have hlt : idx.val < d * ringDegree := by simpa [Nat.mul_comm] using idx.isLt
      exact Nat.div_lt_of_lt_mul hlt
    let coeffBits := Nat.digitsAppend 2 d (((f[coeff]'hcoeff : Coeff).val) % 2 ^ d)
    coeffBits.getD bit 0
  have hbitsSize : bits.size % 8 = 0 := by
    simp [bits, ringDegree]
    omega
  have hbitsBinary : ∀ j, j < bits.size → bits.getD j 0 < 2 := by
    intro j hj
    have hj' : j < ringDegree * d := by simpa [bits] using hj
    let coeff := j / d
    let bit := j % d
    have hcoeff : coeff < ringDegree := by
      have hlt : j < d * ringDegree := by simpa [Nat.mul_comm] using hj'
      exact Nat.div_lt_of_lt_mul hlt
    have hbit : bit < d := by
      dsimp [bit]
      exact Nat.mod_lt _ hd
    have hcoeffBound : ((f[coeff]'hcoeff : Coeff).val) < 2 ^ d := hbound ⟨coeff, hcoeff⟩
    rw [array_getD_eq_getElem bits hj]
    simpa [bits, coeff, bit, Nat.mod_eq_of_lt hcoeffBound]
      using digitsAppend_getD_two_lt (n := (f[coeff]'hcoeff : Coeff).val) hcoeffBound hbit
  have hbitsLen : bits.size = ringDegree * d := by
    simp [bits]
  have hroundtripBitsLen : (bytesToBits (bitsToBytes bits)).size = bits.size := by
    have hsizeBitsToBytesData : (bitsToBytes bits).data.size = bits.size / 8 := by
      simp [bitsToBytes]
    have hsizeBitsToBytes : (bitsToBytes bits).size = bits.size / 8 := by
      simpa [ByteArray.size_data] using hsizeBitsToBytesData
    have hmul : 8 * (bits.size / 8) = bits.size := by
      simpa [hbitsSize] using (Nat.mod_add_div bits.size 8)
    simp [bytesToBits, hsizeBitsToBytes, Nat.mul_comm, hmul]
  apply Vector.ext
  intro i hi
  have hcoeffBound : ((f[i]'hi : Coeff).val) < 2 ^ d := hbound ⟨i, hi⟩
  have hlenDigits : (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val)).length = d :=
    Nat.length_digitsAppend (by decide) d hcoeffBound
  have hcoeffBits :
      List.ofFn (fun j : Fin d =>
        (bytesToBits (byteEncode d f)).getD (i * d + j.val) 0)
        =
      List.ofFn (fun j : Fin d =>
        (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val))[j.val]'(by
          rw [hlenDigits]
          exact j.isLt)) := by
    apply List.ofFn_inj.mpr
    funext j
    have hij : i * d + j.val < ringDegree * d := by
      calc
        i * d + j.val < i * d + d := Nat.add_lt_add_left j.isLt _
        _ = (i + 1) * d := by rw [Nat.add_mul, one_mul]
        _ ≤ ringDegree * d := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
    have hijBits : i * d + j.val < bits.size := by
      simpa [hbitsLen] using hij
    have hbitsRoundtrip :=
      bytesToBits_bitsToBytes_getElem (bits := bits) (i := i * d + j.val)
        hbitsSize hbitsBinary hijBits
    have hcoeffDiv : (i * d + j.val) / d = i := by
      calc
        (i * d + j.val) / d = (j.val + i * d) / d := by ac_rfl
        _ = j.val / d + i := Nat.add_mul_div_right j.val i hd
        _ = i := by simp [Nat.div_eq_of_lt j.isLt]
    have hcoeffMod : (i * d + j.val) % d = j.val := by
      calc
        (i * d + j.val) % d = (j.val + i * d) % d := by ac_rfl
        _ = j.val % d := Nat.add_mul_mod_self_right j.val i d
        _ = j.val := Nat.mod_eq_of_lt j.isLt
    have hencode : byteEncode d f = bitsToBytes bits := by
      simp [byteEncode, bits]
    rw [hencode]
    have hijRound : i * d + j.val < (bytesToBits (bitsToBytes bits)).size := by
      simpa [hroundtripBitsLen] using hijBits
    have hleft :
        (bytesToBits (bitsToBytes bits)).getD (i * d + j.val) 0 =
          (bytesToBits (bitsToBytes bits))[i * d + j.val] :=
      array_getD_eq_getElem (a := bytesToBits (bitsToBytes bits)) (i := i * d + j.val)
        (fallback := 0) hijRound
    have hdigitElem :
        (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val)).getD j.val 0 =
          (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val))[j.val] :=
      List.getD_eq_getElem _ _ (by
        rw [hlenDigits]
        exact j.isLt)
    have hbitPos :
        bits[i * d + j.val] =
          (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val)).getD j.val 0 := by
      have hcoeffModLt :
          ((f[i]'hi : Coeff).val % 2 ^ d) = (f[i]'hi : Coeff).val := Nat.mod_eq_of_lt hcoeffBound
      suffices
          (Nat.digitsAppend 2 d (((f[i]'hi : Coeff).val % 2 ^ d))).getD j.val 0 =
            (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val)).getD j.val 0 by
        simpa [bits, hcoeffDiv, hcoeffMod] using this
      have hdigitsMod :
          Nat.digitsAppend 2 d (((f[i]'hi : Coeff).val % 2 ^ d)) =
            Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val) := by
        rw [hcoeffModLt]
      exact congrArg (fun l => l[j.val]?.getD 0) hdigitsMod
    rw [hleft]
    exact hbitsRoundtrip.trans hbitPos |>.trans hdigitElem
  have hdigits :
      List.ofFn (fun j : Fin d =>
        (Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val))[j.val]'(by
          rw [hlenDigits]
          exact j.isLt)) =
        Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val) := by
    simpa [hlenDigits] using
      (List.ofFn_getElem (xs := Nat.digitsAppend 2 d ((f[i]'hi : Coeff).val)))
  have hcoeffBitsInput :
      (List.ofFn fun j : Fin d => (bytesToBits (byteEncode d f))[i * d + j.val]?.getD 0) =
        List.ofFn (fun j : Fin d => (bytesToBits (byteEncode d f)).getD (i * d + j.val) 0) := by
    have hencode : byteEncode d f = bitsToBytes bits := by
      simp [byteEncode, bits]
    have hencodedBitsLen : (bytesToBits (byteEncode d f)).size = ringDegree * d := by
      rw [hencode]
      simpa [hbitsLen] using hroundtripBitsLen
    apply List.ofFn_inj.mpr
    funext j
    have hij : i * d + j.val < (bytesToBits (byteEncode d f)).size := by
      have : i * d + j.val < ringDegree * d := by
        calc
          i * d + j.val < i * d + d := Nat.add_lt_add_left j.isLt _
          _ = (i + 1) * d := by rw [Nat.add_mul, one_mul]
          _ ≤ ringDegree * d := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
      simpa [hencodedBitsLen] using this
    simp [Array.getD, hij]
  simp only [byteDecode, Array.getD_eq_getD_getElem?, Vector.getElem_ofFn]
  rw [hcoeffBitsInput]
  rw [hcoeffBits, hdigits, ofDigits_digitsAppend_two hcoeffBound]
  exact ZMod.natCast_zmod_val (f[i])

private theorem byteDecode_one_coeff (bytes : ByteArray) (idx : Fin ringDegree) :
    ((byteDecode 1 bytes).get idx : Coeff).val = (bytesToBits bytes).getD idx.val 0 := by
  have hbitMod : (bytesToBits bytes).getD idx.val 0 < modulus :=
    lt_trans (bytesToBits_getD_lt_two bytes idx.val) (by decide)
  have hcast :
      (((bytesToBits bytes).getD idx.val 0 : Nat) : Coeff).val =
        (bytesToBits bytes).getD idx.val 0 :=
    ZMod.val_cast_of_lt hbitMod
  unfold byteDecode
  simpa [Nat.ofDigits_singleton] using hcast

/-! ## 12-bit public-key encoding -/

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
  let a := (f.coeffs[(2 * pair)]'h0 : Coeff).val
  let b := (f.coeffs[(2 * pair + 1)]'h1 : Coeff).val
  match idx.val % 3 with
  | 0 => a.toUInt8
  | 1 => (a / 256 + 16 * (b % 16)).toUInt8
  | _ => (b / 16).toUInt8

/-- Encode one NTT-domain polynomial by packing coefficient pairs into 3-byte blocks. -/
private def byteEncode12Poly (f : Tq) : ByteArray :=
  ByteArray.mk <| Array.ofFn (byteEncode12PolyByte f)

/-- Decode one 384-byte public-key block into an NTT-domain polynomial. -/
private def byteDecode12Poly (bytes : ByteArray) : Tq :=
  ⟨Vector.ofFn fun idx =>
    let pair := idx.val / 2
    let b0 := (getByteD bytes (3 * pair)).toNat
    let b1 := (getByteD bytes (3 * pair + 1)).toNat
    let b2 := (getByteD bytes (3 * pair + 2)).toNat
    if idx.val % 2 = 0 then
      ((b0 + 256 * (b1 % 16) : Nat) : Coeff)
    else
      ((b1 / 16 + 16 * b2 : Nat) : Coeff)⟩

/-- Encode one byte of a concatenated 12-bit-packed vector block. -/
private def byteEncode12VecByte {k : Nat}
    (v : TqVec k) (idx : Fin (384 * k)) : UInt8 :=
  let poly := idx.val / 384
  let byte := idx.val % 384
  have hpoly : poly < k :=
    Nat.div_lt_of_lt_mul idx.isLt
  have hbyte : byte < 384 := Nat.mod_lt _ (by decide)
  byteEncode12PolyByte (v[poly]'hpoly) ⟨byte, hbyte⟩

/-- Decode one polynomial from a concatenated 12-bit-packed vector block. -/
private def byteDecode12VecPoly {k : Nat} (bytes : ByteArray) (poly : Fin k) : Tq :=
  ⟨Vector.ofFn fun idx =>
    let pair := idx.val / 2
    let base := poly.val * 384 + 3 * pair
    let b0 := (getByteD bytes base).toNat
    let b1 := (getByteD bytes (poly.val * 384 + (3 * pair + 1))).toNat
    let b2 := (getByteD bytes (poly.val * 384 + (3 * pair + 2))).toNat
    if idx.val % 2 = 0 then
      ((b0 + 256 * (b1 % 16) : Nat) : Coeff)
    else
      ((b1 / 16 + 16 * b2 : Nat) : Coeff)⟩

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

private theorem tq_getElem_eq_coeffs (f : Tq) {i : Nat} (hi : i < ringDegree) :
    f[i] = f.coeffs[i] := rfl

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
      = fun idx : Fin ringDegree => f.coeffs[idx.val] := by
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
    let a : Nat := (f.coeffs[(2 * pair)]'h0 : Coeff).val
    let b : Nat := (f.coeffs[(2 * pair + 1)]'h1 : Coeff).val
    have ha : a < 4096 := by
      dsimp [a]
      exact lt_trans (ZMod.val_lt _) (by decide)
    have hab : a / 256 + 16 * (b % 16) < 256 := by
      have haDiv : a / 256 < 16 := Nat.div_lt_of_lt_mul (by omega)
      have hbMod : b % 16 < 16 := Nat.mod_lt _ (by decide)
      omega
    have hbDiv : b / 16 < 256 := by
      have hb : b < 4096 :=
        lt_trans (ZMod.val_lt _) (by decide)
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
      rfl
    have hb1 :
        (getByteD (byteEncode12Poly f) (3 * pair + 1)).toNat = a / 256 + 16 * (b % 16) := by
      have hab' :
          ZMod.val f.coeffs[2 * pair] / 256 + 16 * (ZMod.val f.coeffs[2 * pair + 1] % 16) < 256 :=
        by simpa [a, b] using hab
      rw [getByteD_byteEncode12Poly (f := f) (j := 3 * pair + 1) (by omega)]
      simp only [byteEncode12PolyByte, a, b, hdiv1, hmod1]
      exact Nat.mod_eq_of_lt hab'
    have hb2 :
        (getByteD (byteEncode12Poly f) (3 * pair + 2)).toNat = b / 16 := by
      have hbDiv' : ZMod.val f.coeffs[2 * pair + 1] / 16 < 256 := by
        simpa [b] using hbDiv
      rw [getByteD_byteEncode12Poly (f := f) (j := 3 * pair + 2) (by omega)]
      simp only [byteEncode12PolyByte, b, hdiv2, hmod2]
      exact Nat.mod_eq_of_lt hbDiv'
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
        _ = f.coeffs[idx.val] := by
            have hidx' : idx = ⟨2 * pair, h0⟩ := by
              apply Fin.ext
              exact hidx
            simp [hidx', a]
            rfl
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
        _ = f.coeffs[idx.val] := by
            have hidx' : idx = ⟨2 * pair + 1, h1⟩ := by
              apply Fin.ext
              exact hidx
            simp [hidx', b]
            rfl
  apply LatticeCrypto.TransformPoly.ext
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
        = Array.ofFn (fun idx : Fin ringDegree => f.coeffs[idx.val]) :=
            congrArg Array.ofFn hfun
    _ = f.coeffs.toArray := by
      apply Array.ext
      · simp
      · intro i hi1 hi2
        simpa using tq_getElem_eq_coeffs (f := f) (i := i) (hi := by simpa using hi1)

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
  apply LatticeCrypto.TransformPoly.ext
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
        = Array.ofFn (fun idx : Fin k => v[idx.val]) :=
            congrArg Array.ofFn hfun
    _ = v.toArray := by
      apply Array.ext
      · simp
      · intro i hi1 hi2
        simp

/-- Encode a vector of `k` polynomials with `d`-bit coefficients. -/
def byteEncodeVec (d : Nat) {k : Nat} (v : RqVec k) : ByteArray :=
  let chunkSize := 32 * d
  ByteArray.mk <| Array.ofFn fun idx : Fin (chunkSize * k) =>
    let poly := idx.val / chunkSize
    let byte := idx.val % chunkSize
    if hd : d = 0 then
      have : False := by
        have hidx : idx.val < chunkSize * k := idx.isLt
        simp [chunkSize, hd] at hidx
      False.elim this
    else
      have hchunk : 0 < chunkSize := by
        dsimp [chunkSize]
        omega
      have hpoly : poly < k :=
        Nat.div_lt_of_lt_mul idx.isLt
      have hbyte : byte < chunkSize := Nat.mod_lt _ hchunk
      getByteD (byteEncode d (v[poly]'hpoly)) byte

/-- Decode a byte array into a vector of `k` polynomials with `d`-bit coefficients. -/
def byteDecodeVec (d k : Nat) (bytes : ByteArray) : RqVec k :=
  Vector.ofFn fun idx =>
    let chunkSize := 32 * d
    byteDecode d <| ByteArray.mk <|
      Array.ofFn fun j : Fin chunkSize =>
        getByteD bytes (idx.val * chunkSize + j.val)

private theorem getByteD_byteEncodeVec {d k : Nat} (hd : 0 < d) (v : RqVec k)
    {poly j : Nat} (hpoly : poly < k) (hj : j < 32 * d) :
    getByteD (byteEncodeVec d v) (poly * (32 * d) + j) =
      getByteD (byteEncode d (v[poly]'hpoly)) j := by
  have hchunk : 0 < 32 * d := by
    omega
  have hidxNat : poly * (32 * d) + j < (32 * d) * k := by
    calc
      poly * (32 * d) + j < poly * (32 * d) + 32 * d := Nat.add_lt_add_left hj _
      _ = (poly + 1) * (32 * d) := by rw [Nat.add_mul, one_mul]
      _ ≤ k * (32 * d) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hpoly)
      _ = (32 * d) * k := by rw [Nat.mul_comm]
  have hidxData : poly * (32 * d) + j < (byteEncodeVec d v).data.size := by
    simpa [byteEncodeVec, hd.ne] using hidxNat
  have hidx : poly * (32 * d) + j < (byteEncodeVec d v).size := by
    simpa [ByteArray.size_data] using hidxData
  have hdiv : (poly * (32 * d) + j) / (32 * d) = poly := by
    calc
      (poly * (32 * d) + j) / (32 * d) = (j + poly * (32 * d)) / (32 * d) := by ac_rfl
      _ = j / (32 * d) + poly := Nat.add_mul_div_right j poly hchunk
      _ = poly := by simp [Nat.div_eq_of_lt hj]
  have hmod : (poly * (32 * d) + j) % (32 * d) = j := by
    calc
      (poly * (32 * d) + j) % (32 * d) = (j + poly * (32 * d)) % (32 * d) := by ac_rfl
      _ = j % (32 * d) := Nat.add_mul_mod_self_right j poly (32 * d)
      _ = j := Nat.mod_eq_of_lt hj
  rw [getByteD_eq_getElem hidx]
  rw [ByteArray.getElem_eq_getElem_data]
  unfold byteEncodeVec
  split_ifs with hzero
  · exact False.elim (hd.ne' hzero)
  · simp [hzero, hdiv, hmod]

private theorem byteDecodeVec_byteEncodeVec_of_bound {d k : Nat} (hd : 0 < d) (v : RqVec k)
    (hbound : ∀ poly : Fin k, ∀ coeff : Fin ringDegree,
      (((v[poly.val]'poly.isLt)[coeff.val] : Coeff).val) < 2 ^ d) :
    byteDecodeVec d k (byteEncodeVec d v) = v := by
  apply Vector.ext
  intro i hi
  have hbytes :
      ByteArray.mk
        (Array.ofFn fun j : Fin (32 * d) =>
          getByteD (byteEncodeVec d v) (i * (32 * d) + j.val)) =
        byteEncode d (v[i]'hi) := by
    apply ByteArray.ext
    apply Array.ext
    · simp [byteEncode_size]
    · intro j hj1 hj2
      have hj : j < 32 * d := by
        simpa [byteEncode_size] using hj2
      have hjEnc : j < (byteEncode d (v[i]'hi)).size := by
        simpa [byteEncode_size] using hj
      simp only [Array.getElem_ofFn]
      rw [getByteD_byteEncodeVec (hd := hd) (v := v) (poly := i) (j := j) hi hj]
      rw [getByteD_eq_getElem hjEnc, ByteArray.getElem_eq_getElem_data]
      rfl
  simp only [byteDecodeVec, Vector.getElem_ofFn]
  rw [hbytes]
  exact byteDecode_byteEncode_of_bound hd (f := v[i]'hi) (hbound := hbound ⟨i, hi⟩)

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

private theorem compress_val_lt_pow {d : Nat} (hpow : (1 <<< d) < modulus) (x : Coeff) :
    (compress d x : Coeff).val < 2 ^ d := by
  let shifted := (x.val * (1 <<< d) + modulus / 2) / modulus
  have hpowPos : 0 < (1 <<< d) := by
    have htwo : 0 < 2 := Nat.succ_pos 1
    have hpowPos' : 0 < 2 ^ d := pow_pos htwo d
    have hmul : 0 < 1 * 2 ^ d := Nat.mul_pos (Nat.succ_pos 0) hpowPos'
    rw [Nat.shiftLeft_eq]
    exact hmul
  have hmod : shifted % (1 <<< d) < (1 <<< d) := Nat.mod_lt _ hpowPos
  have hltMod : shifted % (1 <<< d) < modulus := lt_trans hmod hpow
  have hval : (((shifted % (1 <<< d) : Nat) : Coeff)).val = shifted % (1 <<< d) :=
    ZMod.val_cast_of_lt hltMod
  calc
    (compress d x : Coeff).val = shifted % (1 <<< d) := by
      simpa [compress, shifted] using hval
    _ < (1 <<< d) := hmod
    _ = 2 ^ d := by simp [Nat.shiftLeft_eq]

private theorem compressPoly_bound {d : Nat} (hpow : (1 <<< d) < modulus) (f : Rq) :
    ∀ idx : Fin ringDegree, (((compressPoly d f)[idx.val] : Coeff).val) < 2 ^ d := by
  intro idx
  have hcoeff : (compressPoly d f)[idx.val] = compress d (f[idx.val]) := by
    unfold compressPoly
    exact Vector.getElem_map (f := compress d) (xs := f) idx.isLt
  rw [hcoeff]
  exact compress_val_lt_pow (d := d) hpow (x := f[idx.val])

private theorem compressVec_bound {d k : Nat} (hpow : (1 <<< d) < modulus) (v : RqVec k) :
    ∀ poly : Fin k, ∀ coeff : Fin ringDegree,
      (((compressVec d v)[poly.val]'poly.isLt)[coeff.val] : Coeff).val < 2 ^ d := by
  intro poly coeff
  simpa [compressVec] using compressPoly_bound (d := d) hpow (f := v[poly.val]) coeff

private def byteEncode1Msg (f : Rq) : Message :=
  let bits : Array Nat := Array.ofFn fun idx : Fin ringDegree =>
    (((f.get idx : Coeff).val) % 2)
  let ba := bitsToBytes bits
  Vector.ofFn fun ⟨i, _⟩ => ba[i]!

private def byteDecode1Msg (msg : Message) : Rq :=
  let bits := bytesToBits (ByteArray.mk msg.toArray)
  Vector.ofFn fun idx =>
    ((bits.getD idx.val 0 : Nat) : Coeff)

private theorem byteDecode1Msg_val (msg : Message) (idx : Fin ringDegree) :
    ((byteDecode1Msg msg).get idx : Coeff).val =
      (bytesToBits (ByteArray.mk msg.toArray)).getD idx.val 0 := by
  have hbitMod : (bytesToBits (ByteArray.mk msg.toArray)).getD idx.val 0 < modulus :=
    lt_trans (bytesToBits_getD_lt_two (ByteArray.mk msg.toArray) idx.val) (by decide)
  have hcast :
      ((((bytesToBits (ByteArray.mk msg.toArray)).getD idx.val 0 : Nat) : Coeff).val) =
        (bytesToBits (ByteArray.mk msg.toArray)).getD idx.val 0 :=
    ZMod.val_cast_of_lt hbitMod
  unfold byteDecode1Msg
  simpa using hcast

private theorem messageToArray_ofByteArray (ba : ByteArray) (hsize : ba.size = 32) :
    (Vector.ofFn (n := 32) (fun i => ba[i.val]!)).toArray = ba.data := by
  rw [Vector.toArray_ofFn]
  apply Array.ext
  · simpa [ByteArray.size_data] using hsize.symm
  · intro i hi1 hi2
    have hi : i < ba.size := by simpa [hsize] using hi1
    rw [Array.getElem_ofFn]
    simp [hi, ByteArray.getElem_eq_getElem_data]
    rfl

private theorem toArray_byteEncode1Msg (f : Rq) :
    (byteEncode1Msg f).toArray = (byteEncode 1 f).data := by
  let bits : Array Nat := Array.ofFn fun idx : Fin ringDegree =>
    (((f.get idx : Coeff).val) % 2)
  have hbitsEq :
      (Array.ofFn fun idx : Fin (ringDegree * 1) =>
        let coeff := idx.val / 1
        let bit := idx.val % 1
        have hcoeff : coeff < ringDegree := by
          omega
        let coeffBits := Nat.digitsAppend 2 1 (((f[coeff]'hcoeff : Coeff).val) % 2 ^ 1)
        coeffBits.getD bit 0) = bits := by
    apply Array.ext
    · simp [bits, ringDegree]
    · intro i hi1 hi2
      have hi : i < ringDegree := by
        simpa [bits, ringDegree] using hi1
      let idx : Fin ringDegree := ⟨i, hi⟩
      rw [Array.getElem_ofFn, Array.getElem_ofFn]
      simpa [bits, idx, Nat.div_one, Nat.mod_one] using
        digitsAppend_two_one_getD_zero_mod (((f.get idx : Coeff).val))
  have hencode : byteEncode 1 f = bitsToBytes bits := by
    unfold byteEncode
    simpa [Nat.mul_one] using congrArg bitsToBytes hbitsEq
  have hsize : (bitsToBytes bits).size = 32 := by
    simpa [hencode] using byteEncode_size 1 f
  unfold byteEncode1Msg
  simpa [hencode, bits] using messageToArray_ofByteArray (ba := bitsToBytes bits) hsize

private theorem byteArray_byteEncode1Msg (f : Rq) :
    ByteArray.mk (byteEncode1Msg f).toArray = byteEncode 1 f := by
  apply ByteArray.ext
  simpa using toArray_byteEncode1Msg (f := f)

private theorem byteDecode1Msg_eq_byteDecode1 (msg : Message) :
    byteDecode1Msg msg = byteDecode 1 (ByteArray.mk msg.toArray) := by
  apply Vector.ext
  intro i hi
  let idx : Fin ringDegree := ⟨i, hi⟩
  apply (ZMod.val_injective modulus)
  change (((byteDecode1Msg msg).get idx : Coeff).val) =
    (((byteDecode 1 (ByteArray.mk msg.toArray)).get idx : Coeff).val)
  calc
    (((byteDecode1Msg msg).get idx : Coeff).val)
        = (bytesToBits (ByteArray.mk msg.toArray)).getD idx.val 0 := by
            simpa [idx] using byteDecode1Msg_val (msg := msg) idx
    _ = (((byteDecode 1 (ByteArray.mk msg.toArray)).get idx : Coeff).val) := by
        symm
        simpa [idx] using byteDecode_one_coeff (ByteArray.mk msg.toArray) idx

private theorem byteEncode1Msg_byteDecode1Msg (msg : Message) :
    byteEncode1Msg (byteDecode1Msg msg) = msg := by
  let bits : Array Nat := Array.ofFn fun idx : Fin ringDegree =>
    (((byteDecode1Msg msg).get idx : Coeff).val % 2)
  have hbitsEq : bits = bytesToBits (ByteArray.mk msg.toArray) := by
    apply Array.ext
    · have hmsgSize : (ByteArray.mk msg.toArray).size = 32 := msg.size_toArray
      simp [bits, bytesToBits, hmsgSize, ringDegree]
    · intro i hi1 hi2
      have hi : i < ringDegree := by simpa [bits, ringDegree] using hi1
      let idx : Fin ringDegree := ⟨i, hi⟩
      rw [Array.getElem_ofFn]
      have hbitLt :
          (bytesToBits (ByteArray.mk msg.toArray)).getD i 0 < 2 :=
        bytesToBits_getD_lt_two (ByteArray.mk msg.toArray) i
      have hget :
          (bytesToBits (ByteArray.mk msg.toArray)).getD i 0 =
            (bytesToBits (ByteArray.mk msg.toArray))[i] :=
        array_getD_eq_getElem
          (a := bytesToBits (ByteArray.mk msg.toArray)) (i := i) (fallback := 0) hi2
      rw [byteDecode1Msg_val (msg := msg) idx, Nat.mod_eq_of_lt hbitLt, hget]
  apply Vector.toArray_inj.mp
  have hbytes : bitsToBytes bits = ByteArray.mk msg.toArray := by
    rw [hbitsEq, bitsToBytes_bytesToBits]
  have hsize : (bitsToBytes bits).size = 32 := by
    simpa [hbytes] using (show (ByteArray.mk msg.toArray).size = 32 from msg.size_toArray)
  calc
    (byteEncode1Msg (byteDecode1Msg msg)).toArray = (bitsToBytes bits).data := by
      unfold byteEncode1Msg
      simpa [bits] using messageToArray_ofByteArray (ba := bitsToBytes bits) hsize
    _ = (ByteArray.mk msg.toArray).data := by simp [hbytes]
    _ = msg.toArray := rfl

private theorem byteDecode1Msg_byteEncode1Msg_of_bound (f : Rq)
    (hbound : ∀ idx : Fin ringDegree, ((f[idx.val] : Coeff).val) < 2) :
    byteDecode1Msg (byteEncode1Msg f) = f := by
  calc
    byteDecode1Msg (byteEncode1Msg f) = byteDecode 1 (ByteArray.mk (byteEncode1Msg f).toArray) :=
      byteDecode1Msg_eq_byteDecode1 (msg := byteEncode1Msg f)
    _ = byteDecode 1 (byteEncode 1 f) := by
      rw [byteArray_byteEncode1Msg (f := f)]
    _ = f := byteDecode_byteEncode_of_bound (d := 1) (by decide) f (by simpa using hbound)

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
  byteEncode1 := byteEncode1Msg
  byteDecode1 := byteDecode1Msg

/-- Proof bundle showing that the concrete ML-KEM encoding satisfies the abstract encoding laws
under the standard bit-width side conditions. -/
theorem concreteEncodingLaws (params : Params)
    (hduPos : 0 < params.du) (hdvPos : 0 < params.dv)
    (hduPow : (1 <<< params.du) < modulus) (hdvPow : (1 <<< params.dv) < modulus) :
    (concreteEncoding params).Laws := by
  have hpow1 : (1 <<< 1) < modulus := by
    decide
  refine
    { byteDecodeDUVec_byteEncodeDUVec_compressDU := ?_
      byteDecodeDV_byteEncodeDV_compressDV := ?_
      byteEncode1_byteDecode1 := ?_
      byteDecode1_byteEncode1_compress1 := ?_ }
  · intro u
    simpa [concreteEncoding] using
      byteDecodeVec_byteEncodeVec_of_bound (d := params.du) (k := params.k) hduPos
        (v := compressVec params.du u) (hbound := compressVec_bound (d := params.du) hduPow u)
  · intro v
    simpa [concreteEncoding] using
      byteDecode_byteEncode_of_bound (d := params.dv) hdvPos
        (f := compressPoly params.dv v) (hbound := compressPoly_bound (d := params.dv) hdvPow v)
  · intro msg
    simpa [concreteEncoding] using byteEncode1Msg_byteDecode1Msg (msg := msg)
  · intro v
    simpa [concreteEncoding] using
      byteDecode1Msg_byteEncode1Msg_of_bound (f := compressPoly 1 v)
        (hbound := compressPoly_bound (d := 1) hpow1 v)

end MLKEM.Concrete
