/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.EncodingLemmas
public import HashSig.SLHDSA.WotsChecksum

/-!
# WOTS+ Checksum Byte Encoding (FIPS 205 §5.2–5.3)

The normative checksum pipeline used by WOTS+ signing and public-key recovery.  FIPS 205 first
left-shifts the checksum by the padding needed to fill its final byte, serializes it in
big-endian order with `toByte`, and only then applies `base_2b`.  The outer modulus in
`checksumShift` is essential when `len2 * lg_w` is already byte aligned.

The main equivalence theorem proves that this byte-oriented pipeline produces the mathematical
fixed-width base-`w` checksum digits used by `WotsChecksum`.

## References

- NIST FIPS 205, Algorithms 7 and 8, line 6
- NIST FIPS 205, Appendix A
-/

@[expose] public section


namespace SLHDSA.WotsEncoding

open WotsChecksum

/-- Number of meaningful bits in the fixed-width WOTS+ checksum representation. -/
def checksumBitLength (p : Params) : ℕ := p.len2 * p.lgw

/-- Number of bytes occupied by the padded WOTS+ checksum representation. -/
def checksumByteLength (p : Params) : ℕ := (checksumBitLength p + 7) / 8

/-- FIPS 205's right-padding width.  The outer modulus makes byte-aligned inputs shift by zero. -/
def checksumShift (p : Params) : ℕ := (8 - checksumBitLength p % 8) % 8

/-- The WOTS+ checksum after the FIPS 205 padding shift. -/
def shiftedChecksumValue (p : Params) (digits : List ℕ) : ℕ :=
  wotsChecksumValue p.w digits <<< checksumShift p

/-- Big-endian Algorithm 3 serialization of the shifted WOTS+ checksum. -/
def checksumBytes (p : Params) (digits : List ℕ) : List Byte :=
  toByte (shiftedChecksumValue p digits) (checksumByteLength p)

/-- Algorithm 4 decoding of the serialized checksum into exactly `len2` base-`w` digits. -/
def checksumDigits (p : Params) (digits : List ℕ) : List ℕ :=
  base2b (checksumBytes p digits) p.lgw p.len2

/-- FIPS 205's complete message-plus-checksum chain-length vector. -/
def fullDigits (p : Params) (digits : List ℕ) : List ℕ :=
  digits ++ checksumDigits p digits

private theorem ceil8_padding (k : ℕ) :
    8 * ((k + 7) / 8) = k + ((8 - k % 8) % 8) := by
  omega

/-- The chosen byte width is exactly the checksum bit width plus its FIPS padding. -/
theorem checksumByteLength_bits (p : Params) :
    8 * checksumByteLength p = checksumBitLength p + checksumShift p := by
  exact ceil8_padding (checksumBitLength p)

/-- The FIPS padding width is always smaller than one byte. -/
theorem checksumShift_lt_eight (p : Params) : checksumShift p < 8 := by
  exact Nat.mod_lt _ (by decide)

/-- The byte serialization has the fixed width prescribed by FIPS 205. -/
@[simp] theorem checksumBytes_length (p : Params) (digits : List ℕ) :
    (checksumBytes p digits).length = checksumByteLength p := by
  simp [checksumBytes]

/-- The checksum byte string is the MSB-first Algorithm 3 representation: byte `i` carries
base-256 digit `checksumByteLength p - 1 - i` of the shifted checksum value. -/
theorem checksumBytes_bigEndian (p : Params) (digits : List ℕ) :
    checksumBytes p digits =
      (List.range (checksumByteLength p)).map (fun i =>
        UInt8.ofNat (shiftedChecksumValue p digits /
          256 ^ (checksumByteLength p - 1 - i) % 256)) :=
  rfl

/-- The checksum decoder always emits exactly `len2` digits. -/
@[simp] theorem checksumDigits_length (p : Params) (digits : List ℕ) :
    (checksumDigits p digits).length = p.len2 := by
  simp [checksumDigits]

/-- Every checksum digit emitted by the byte pipeline is a genuine base-`w` digit. -/
theorem checksumDigits_lt (p : Params) (digits : List ℕ) :
    ∀ d ∈ checksumDigits p digits, d < p.w := by
  intro d hd
  simpa only [Params.w] using
    base2b_lt (checksumBytes p digits) p.lgw p.len2 d hd

/-- The full FIPS chain-length vector has the message width plus checksum width. -/
@[simp] theorem fullDigits_length (p : Params) (digits : List ℕ)
    (hlen : digits.length = p.len1) :
    (fullDigits p digits).length = p.len := by
  simp [fullDigits, hlen, Params.len]

/-- Every full FIPS digit is bounded when the message digits are bounded. -/
theorem fullDigits_lt (p : Params) (digits : List ℕ)
    (hbound : ∀ d ∈ digits, d < p.w) :
    ∀ d ∈ fullDigits p digits, d < p.w := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact hbound d hd
  · exact checksumDigits_lt p digits d hd

private theorem digitsOfBaseW_eq_range (n w len : ℕ) :
    digitsOfBaseW n w len =
      (List.range len).map (fun i => n / w ^ (len - 1 - i) % w) := by
  induction len with
  | zero => simp [digitsOfBaseW]
  | succ len ih =>
      rw [digitsOfBaseW, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, ih, List.cons.injEq]
      constructor
      · congr 2
      · apply List.map_congr_left
        intro i hi
        congr 3
        omega

private theorem shifted_fit {x b len : ℕ} (hfit : x < (2 ^ b) ^ len) :
    x * 2 ^ ((8 - (len * b) % 8) % 8) < 256 ^ ((len * b + 7) / 8) := by
  have hx : x < 2 ^ (b * len) := by
    simpa only [Nat.pow_mul] using hfit
  have hmul :
      x * 2 ^ ((8 - (len * b) % 8) % 8) <
        2 ^ (b * len) * 2 ^ ((8 - (len * b) % 8) % 8) :=
    (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ ((8 - (len * b) % 8) % 8))).2 hx
  rw [← pow_add] at hmul
  have hbits :
      b * len + ((8 - (len * b) % 8) % 8) = 8 * ((len * b + 7) / 8) := by
    rw [ceil8_padding]
    simp only [Nat.mul_comm]
  rw [hbits] at hmul
  simpa only [show 256 = 2 ^ 8 by norm_num, Nat.pow_mul] using hmul

private theorem base2b_toByte_shift_eq_digitsOfBaseW (x b len : ℕ)
    (hfit : x < (2 ^ b) ^ len) :
    base2b
        (toByte (x * 2 ^ ((8 - (len * b) % 8) % 8)) ((len * b + 7) / 8)) b len =
      digitsOfBaseW x (2 ^ b) len := by
  have hbits : len * b ≤
      8 * (toByte (x * 2 ^ ((8 - len * b % 8) % 8)) ((len * b + 7) / 8)).length := by
    rw [toByte_length]
    omega
  rw [base2b_bigEndian _ _ _ hbits, digitsOfBaseW_eq_range]
  apply List.map_congr_left
  intro i hi
  have hi' : i < len := List.mem_range.mp hi
  rw [toInt_toByte _ _ (shifted_fit hfit)]
  rw [toByte_length]
  have hexp :
      8 * ((len * b + 7) / 8) - b * (i + 1) =
        b * (len - 1 - i) + ((8 - (len * b) % 8) % 8) := by
    have hsplit : len = (len - 1 - i) + (i + 1) := by omega
    have hmul : b * len = b * (len - 1 - i) + b * (i + 1) := by
      calc
        b * len = b * ((len - 1 - i) + (i + 1)) := congrArg (b * ·) hsplit
        _ = b * (len - 1 - i) + b * (i + 1) := Nat.mul_add _ _ _
    have htotal :
        8 * ((len * b + 7) / 8) =
          b * len + ((8 - (len * b) % 8) % 8) := by
      rw [ceil8_padding]
      congr 1
      exact Nat.mul_comm len b
    rw [htotal]
    omega
  rw [hexp, pow_add]
  rw [Nat.mul_div_mul_right _ _
    (by positivity : 0 < 2 ^ ((8 - (len * b) % 8) % 8))]
  rw [Nat.pow_mul]

/-- A valid parameter set gives the mathematical checksum enough `len2` base-`w` digits. -/
theorem wotsChecksumValue_lt_pow {p : Params} (valid : p.Valid) (digits : List ℕ)
    (hlen : digits.length = p.len1) (hbound : ∀ d ∈ digits, d < p.w) :
    wotsChecksumValue p.w digits < p.w ^ p.len2 := by
  apply Nat.lt_of_le_of_lt (wotsChecksumValue_le hlen hbound)
  simpa [Params.len2, Params.w, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self
      (Nat.one_lt_two_pow (Nat.ne_of_gt valid.lgw_pos)) (p.len1 * (p.w - 1))

/-- The shifted checksum fits its prescribed byte width, so Algorithm 3 does not truncate it. -/
theorem shiftedChecksumValue_lt_pow {p : Params} (valid : p.Valid) (digits : List ℕ)
    (hlen : digits.length = p.len1) (hbound : ∀ d ∈ digits, d < p.w) :
    shiftedChecksumValue p digits < 256 ^ checksumByteLength p := by
  simpa [shiftedChecksumValue, checksumShift, checksumBitLength, checksumByteLength,
    Params.w, Nat.shiftLeft_eq, Nat.mul_comm] using
    shifted_fit (wotsChecksumValue_lt_pow valid digits hlen hbound)

/-- Kernel-checked bridge from the exact FIPS byte pipeline to the mathematical base-`w` digits. -/
theorem checksumDigits_eq_digitsOfBaseW {p : Params} (valid : p.Valid)
    (digits : List ℕ) (hlen : digits.length = p.len1)
    (hbound : ∀ d ∈ digits, d < p.w) :
    checksumDigits p digits = digitsOfBaseW (wotsChecksumValue p.w digits) p.w p.len2 := by
  simpa [checksumDigits, checksumBytes, shiftedChecksumValue, checksumShift,
    checksumBitLength, checksumByteLength, Params.w, Nat.shiftLeft_eq, Nat.mul_comm] using
    base2b_toByte_shift_eq_digitsOfBaseW
      (wotsChecksumValue p.w digits) p.lgw p.len2
      (wotsChecksumValue_lt_pow valid digits hlen hbound)

/-- Under the FIPS parameter validity obligations, the byte and mathematical full-digit views
coincide exactly. -/
theorem fullDigits_eq_wotsFullDigits {p : Params} (valid : p.Valid) (digits : List ℕ)
    (hlen : digits.length = p.len1) (hbound : ∀ d ∈ digits, d < p.w) :
    fullDigits p digits = wotsFullDigits digits p.w p.len1 p.len2 := by
  simp only [fullDigits, wotsFullDigits]
  rw [checksumDigits_eq_digitsOfBaseW valid digits hlen hbound]

end SLHDSA.WotsEncoding
