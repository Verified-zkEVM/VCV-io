/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module

public import HashSig.SLHDSA.Wots

/-!
# WOTS+ Checksum Encoding Canaries

Discriminating checks for the FIPS 205 checksum byte pipeline.  The reduced `lg_w = 2` profile
is byte aligned and therefore exercises the outer modulus in the padding formula; a historical
shift-by-eight interpretation truncates to a different digit vector.
-/

public section


namespace SLHDSA.WotsEncodingTest

open WotsChecksum WotsEncoding

def limited : Params := slhdsaSha2_128_24
def zeroDigits : List ℕ := List.replicate limited.len1 0

/-- Minimal byte-backed context used to exercise the operational WOTS digit path. -/
@[expose]
def limitedCore : CorePrimitives limited where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bytes limited.n
  AdrsKey := Unit
  adrsToKey := fun _ => ()
  PRF := fun _ _ _ => Vector.replicate limited.n 0
  PRFmsg := fun _ _ _ => Vector.replicate limited.n 0
  yToBytes := id

def zeroNode : limitedCore.Y := Vector.replicate limited.n 0

theorem byteList_eq_singleton_of_length_toInt (bytes : List Byte) (b : Byte)
    (hlen : bytes.length = 1) (hint : toInt bytes = b.toNat) : bytes = [b] := by
  cases bytes with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil =>
          have hxb : x = b := UInt8.toNat_inj.mp (by simpa [toInt] using hint)
          simp [hxb]
      | cons y ys => simp at hlen

theorem limited_zeroDigits_length : zeroDigits.length = limited.len1 := by
  simp [zeroDigits]

theorem limited_zeroDigits_lt : ∀ d ∈ zeroDigits, d < limited.w := by
  intro d hd
  have hd' := List.eq_of_mem_replicate hd
  subst d
  norm_num [limited, slhdsaSha2_128_24, LimitedParameterSet.params, Params.w]

theorem limited_checksumValue : wotsChecksumValue limited.w zeroDigits = 192 := by
  decide

theorem limited_valid : limited.Valid := by
  simpa [limited, slhdsaSha2_128_24] using
    (LimitedParameterSet.params_valid .SLHDSA_SHA2_128_24)

/-- The reduced `lg_w = 2` profile has 64 message digits and four checksum digits. -/
example : (limited.lgw, limited.len1, limited.len2, limited.w) = (2, 64, 4, 4) := by
  decide

/-- Its eight checksum bits occupy one byte and require no shift. -/
example :
    (checksumBitLength limited, checksumByteLength limited, checksumShift limited) = (8, 1, 0) :=
  by decide

/-- The all-zero message digit vector has checksum `64 * (4 - 1) = 192`. -/
example : wotsChecksumValue limited.w zeroDigits = 192 := limited_checksumValue

/-- Correct big-endian serialization is exactly the byte `c0`. -/
example : checksumBytes limited zeroDigits = [0xc0] := by
  apply byteList_eq_singleton_of_length_toInt
  · calc
      (checksumBytes limited zeroDigits).length = checksumByteLength limited :=
        checksumBytes_length limited zeroDigits
      _ = 1 := by decide
  · have hfit := shiftedChecksumValue_lt_pow
      limited_valid zeroDigits
      limited_zeroDigits_length limited_zeroDigits_lt
    have hint := toInt_toByte (shiftedChecksumValue limited zeroDigits)
      (checksumByteLength limited) hfit
    calc
      toInt (checksumBytes limited zeroDigits) = shiftedChecksumValue limited zeroDigits := by
        simpa only [checksumBytes] using hint
      _ = 192 := by
        simp only [shiftedChecksumValue, limited_checksumValue, Nat.shiftLeft_eq]
        decide

/-- Decoding `c0` at two bits per digit produces the prescribed four checksum digits. -/
example : checksumDigits limited zeroDigits = [3, 0, 0, 0] := by
  rw [checksumDigits_eq_digitsOfBaseW limited_valid zeroDigits
    limited_zeroDigits_length limited_zeroDigits_lt]
  rw [limited_checksumValue]
  have hw : limited.w = 4 := by decide
  have hlen2 : limited.len2 = 4 := by decide
  rw [hw, hlen2]
  norm_num [digitsOfBaseW]

/-- Executable WOTS chain lengths use the normative checksum byte pipeline. -/
example : chainLengthsCore limitedCore zeroNode = zeroDigits ++ [3, 0, 0, 0] := by
  rw [chainLengthsCore_eq_wotsFullDigits limited_valid]
  have hmsg : wotsMsgDigitsCore limitedCore zeroNode = zeroDigits := by
    decide
  rw [hmsg]
  rw [show wotsFullDigits zeroDigits limited.w limited.len1 limited.len2 =
      zeroDigits ++ [3, 0, 0, 0] by
    rw [wotsFullDigits, limited_checksumValue]
    have hw : limited.w = 4 := by decide
    have hlen2 : limited.len2 = 4 := by decide
    rw [hw, hlen2]
    norm_num [digitsOfBaseW]]

def historicalShiftedBytes : List Byte :=
  toByte (wotsChecksumValue limited.w zeroDigits <<< 8) (checksumByteLength limited)

def historicalShiftedDigits : List ℕ :=
  base2b historicalShiftedBytes limited.lgw limited.len2

/-- The erroneous shift-by-eight interpretation is truncated by the one-byte serialization. -/
example : historicalShiftedBytes = [0] := by
  apply byteList_eq_singleton_of_length_toInt
  · calc
      historicalShiftedBytes.length = checksumByteLength limited := by
        simp only [historicalShiftedBytes, toByte_length]
      _ = 1 := by decide
  · have hint := toInt_toByte_mod (wotsChecksumValue limited.w zeroDigits <<< 8)
      (checksumByteLength limited)
    calc
      toInt historicalShiftedBytes =
          (wotsChecksumValue limited.w zeroDigits <<< 8) %
            256 ^ checksumByteLength limited := by
        simpa only [historicalShiftedBytes] using hint
      _ = 0 := by rw [limited_checksumValue]; decide
example : historicalShiftedDigits = [0, 0, 0, 0] := by
  have hbytes : historicalShiftedBytes = [0] := by
    apply byteList_eq_singleton_of_length_toInt
    · calc
        historicalShiftedBytes.length = checksumByteLength limited := by
          simp only [historicalShiftedBytes, toByte_length]
        _ = 1 := by decide
    · have hint := toInt_toByte_mod (wotsChecksumValue limited.w zeroDigits <<< 8)
        (checksumByteLength limited)
      calc
        toInt historicalShiftedBytes =
            (wotsChecksumValue limited.w zeroDigits <<< 8) %
              256 ^ checksumByteLength limited := by
          simpa only [historicalShiftedBytes] using hint
        _ = 0 := by rw [limited_checksumValue]; decide
  change base2b historicalShiftedBytes limited.lgw limited.len2 = [0, 0, 0, 0]
  rw [hbytes]
  have hlgw : limited.lgw = 2 := by decide
  have hlen2 : limited.len2 = 4 := by decide
  rw [hlgw, hlen2]
  norm_num [base2b, toInt]
  rfl

/-- The canary discriminates the normative outer-mod shift from the historical truncation. -/
example : checksumDigits limited zeroDigits ≠ historicalShiftedDigits := by
  rw [show checksumDigits limited zeroDigits = [3, 0, 0, 0] by
    rw [checksumDigits_eq_digitsOfBaseW
      limited_valid zeroDigits
      limited_zeroDigits_length limited_zeroDigits_lt]
    rw [limited_checksumValue]
    have hw : limited.w = 4 := by decide
    have hlen2 : limited.len2 = 4 := by decide
    rw [hw, hlen2]
    norm_num [digitsOfBaseW]]
  rw [show historicalShiftedDigits = [0, 0, 0, 0] by
    have hbytes : historicalShiftedBytes = [0] := by
      apply byteList_eq_singleton_of_length_toInt
      · calc
          historicalShiftedBytes.length = checksumByteLength limited := by
            simp only [historicalShiftedBytes, toByte_length]
          _ = 1 := by decide
      · have hint := toInt_toByte_mod (wotsChecksumValue limited.w zeroDigits <<< 8)
          (checksumByteLength limited)
        calc
          toInt historicalShiftedBytes =
              (wotsChecksumValue limited.w zeroDigits <<< 8) %
                256 ^ checksumByteLength limited := by
            simpa only [historicalShiftedBytes] using hint
          _ = 0 := by rw [limited_checksumValue]; decide
    change base2b historicalShiftedBytes limited.lgw limited.len2 = [0, 0, 0, 0]
    rw [hbytes]
    have hlgw : limited.lgw = 2 := by decide
    have hlen2 : limited.len2 = 4 := by decide
    rw [hlgw, hlen2]
    norm_num [base2b, toInt]
    rfl]
  decide

/-- Every approved FIPS profile has three four-bit checksum digits, a four-bit shift, and a
two-byte serialized checksum. -/
example : FipsParameterSet.all.map (fun set =>
    let p := set.params
    (p.lgw, p.len2, checksumBitLength p, checksumShift p, checksumByteLength p)) =
    List.replicate 12 (4, 3, 12, 4, 2) := by
  decide

/-- The kernel bridge applies to the byte-aligned reduced profile, not only to approved
`lg_w = 4` profiles. -/
example :
    checksumDigits limited zeroDigits =
      digitsOfBaseW (wotsChecksumValue limited.w zeroDigits) limited.w limited.len2 := by
  apply checksumDigits_eq_digitsOfBaseW limited_valid
  · decide
  · exact limited_zeroDigits_lt

end SLHDSA.WotsEncodingTest
