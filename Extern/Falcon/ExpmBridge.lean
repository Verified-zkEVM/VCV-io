/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
import all LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPRBridge
public import LatticeCrypto.Falcon.Concrete.FPR
public import Extern.Falcon.FPRBridge
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# The fixed-point layer of Falcon's `expm_p63`

`Falcon.Concrete.FPR.expm_p63` evaluates a degree-twelve polynomial in `UInt64` fixed point and
scales the result, computing `⌊2 ^ 63 * ccs * exp (-x)⌋` for a scale factor `ccs` in `[0, 1)` and
an argument `x` in `[0, log 2)`. Its accuracy therefore splits in two:

* how faithfully the fixed-point pipeline evaluates the polynomial it is given, and
* how well that polynomial approximates `exp (-x)`.

This module is the first half. It reads each machine operation as exact arithmetic on `ℕ` and
bounds the truncation each one contributes: `mulHi64` is the high half of a `128`-bit product, and
`mtwop63` is the conversion of an `FPR` in `[0, 1)` to a `63`-bit fixed-point fraction. The second
half — certifying the coefficient table against `Real.exp` — is a numerical-certification problem
of a different character, described in `docs/agents/expm-certification.md`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR Polynomial

/-! ## The high half of a 64-bit product

`mulHi64` splits both operands into `32`-bit limbs and reassembles the carries, exactly as
`FPR.mul` does at `25` bits. The result is the top half of the `128`-bit product, and no
intermediate leaves its register. -/

private theorem toNat_and_low32 (v : UInt64) : (v &&& 0xFFFFFFFF).toNat = v.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem toNat_shiftRight_32_uint64 (v : UInt64) : (v >>> 32).toNat = v.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from by decide,
    Nat.shiftRight_eq_div_pow]

/-- Three `UInt64` additions whose exact sum fits a register agree with addition on `ℕ`. -/
private theorem toNat_add3_of_lt {x y z : UInt64}
    (h : x.toNat + y.toNat + z.toNat < 2 ^ 64) :
    (x + y + z).toNat = x.toNat + y.toNat + z.toNat := by
  have h1 : (x + y).toNat = x.toNat + y.toNat := toNat_add_of_lt_uint64 (by omega)
  rw [toNat_add_of_lt_uint64 (by omega : (x + y).toNat + z.toNat < 2 ^ 64), h1]

/-- Four `UInt64` additions whose exact sum fits a register agree with addition on `ℕ`. -/
private theorem toNat_add4_of_lt {x y z w : UInt64}
    (h : x.toNat + y.toNat + z.toNat + w.toNat < 2 ^ 64) :
    (x + y + z + w).toNat = x.toNat + y.toNat + z.toNat + w.toNat := by
  have h3 : (x + y + z).toNat = x.toNat + y.toNat + z.toNat := toNat_add3_of_lt (by omega)
  rw [toNat_add_of_lt_uint64 (by omega : (x + y + z).toNat + w.toNat < 2 ^ 64), h3]

/-- The limb identity behind `mulHi64`, as plain arithmetic on `ℕ`: the high half of the product
is the top partial product plus the carries out of the two cross terms and the middle column. -/
private theorem mulHi_limbs (aHi aLo bHi bLo : ℕ) :
    (aHi * 2 ^ 32 + aLo) * (bHi * 2 ^ 32 + bLo) / 2 ^ 64
      = aHi * bHi + (aHi * bLo) / 2 ^ 32 + (aLo * bHi) / 2 ^ 32
        + ((aLo * bLo) / 2 ^ 32 + (aHi * bLo) % 2 ^ 32 + (aLo * bHi) % 2 ^ 32) / 2 ^ 32 := by
  -- name every quotient and remainder, so the identity becomes polynomial
  obtain ⟨q1, r1, hr1, he1⟩ : ∃ q r, r < 2 ^ 32 ∧ aHi * bLo = q * 2 ^ 32 + r :=
    ⟨aHi * bLo / 2 ^ 32, aHi * bLo % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _), by omega⟩
  obtain ⟨q2, r2, hr2, he2⟩ : ∃ q r, r < 2 ^ 32 ∧ aLo * bHi = q * 2 ^ 32 + r :=
    ⟨aLo * bHi / 2 ^ 32, aLo * bHi % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _), by omega⟩
  obtain ⟨q3, r3, hr3, he3⟩ : ∃ q r, r < 2 ^ 32 ∧ aLo * bLo = q * 2 ^ 32 + r :=
    ⟨aLo * bLo / 2 ^ 32, aLo * bLo % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _), by omega⟩
  have hd1 : (aHi * bLo) / 2 ^ 32 = q1 := by omega
  have hm1 : (aHi * bLo) % 2 ^ 32 = r1 := by omega
  have hd2 : (aLo * bHi) / 2 ^ 32 = q2 := by omega
  have hm2 : (aLo * bHi) % 2 ^ 32 = r2 := by omega
  have hd3 : (aLo * bLo) / 2 ^ 32 = q3 := by omega
  rw [hd1, hm1, hd2, hm2, hd3]
  -- the product, split at bit 64
  have hexp : (aHi * 2 ^ 32 + aLo) * (bHi * 2 ^ 32 + bLo)
      = (aHi * bHi + q1 + q2) * 2 ^ 64 + ((q3 + r1 + r2) * 2 ^ 32 + r3) := by
    calc (aHi * 2 ^ 32 + aLo) * (bHi * 2 ^ 32 + bLo)
        = aHi * bHi * 2 ^ 64 + (aHi * bLo) * 2 ^ 32 + (aLo * bHi) * 2 ^ 32
          + aLo * bLo := by ring
      _ = aHi * bHi * 2 ^ 64 + (q1 * 2 ^ 32 + r1) * 2 ^ 32 + (q2 * 2 ^ 32 + r2) * 2 ^ 32
          + (q3 * 2 ^ 32 + r3) := by rw [he1, he2, he3]
      _ = (aHi * bHi + q1 + q2) * 2 ^ 64 + ((q3 + r1 + r2) * 2 ^ 32 + r3) := by ring
  rw [hexp]
  -- the low part cannot reach the next multiple of 2 ^ 64
  obtain ⟨M, s, hs, hM⟩ : ∃ M s, s < 2 ^ 32 ∧ q3 + r1 + r2 = M * 2 ^ 32 + s :=
    ⟨(q3 + r1 + r2) / 2 ^ 32, (q3 + r1 + r2) % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos _),
      by omega⟩
  have hMdiv : (q3 + r1 + r2) / 2 ^ 32 = M := by omega
  rw [hMdiv, hM]
  have hlow : (M * 2 ^ 32 + s) * 2 ^ 32 + r3 = M * 2 ^ 64 + (s * 2 ^ 32 + r3) := by ring
  rw [hlow, ← add_assoc, ← add_mul]
  have hfit : s * 2 ^ 32 + r3 < 2 ^ 64 := by nlinarith [hs, hr3]
  omega

/-- The final column of `mulHi64`, assembled. Given the exact values of the top partial product
`X`, of the two cross carries `Y` and `Z`, and of the three middle-column pieces `u`, `v`, `w`,
the column sums without leaving its register and equals the high half of `A * B`. -/
private theorem toNat_finalColumn {X Y Z u v w : UInt64} {A B : ℕ}
    (hA : A < 2 ^ 64) (hB : B < 2 ^ 64)
    (hX : X.toNat = A / 2 ^ 32 * (B / 2 ^ 32))
    (hY : Y.toNat = A / 2 ^ 32 * (B % 2 ^ 32) / 2 ^ 32)
    (hZ : Z.toNat = A % 2 ^ 32 * (B / 2 ^ 32) / 2 ^ 32)
    (hu : u.toNat = A % 2 ^ 32 * (B % 2 ^ 32) / 2 ^ 32)
    (hv : v.toNat = A / 2 ^ 32 * (B % 2 ^ 32) % 2 ^ 32)
    (hw : w.toNat = A % 2 ^ 32 * (B / 2 ^ 32) % 2 ^ 32)
    (hmid : u.toNat + v.toNat + w.toNat < 2 ^ 64) :
    (X + Y + Z + ((u + v + w) >>> 32)).toNat = A * B / 2 ^ 64 := by
  -- the middle column, as exact arithmetic, then its carry out
  have hcarry : ((u + v + w) >>> 32).toNat
      = (A % 2 ^ 32 * (B % 2 ^ 32) / 2 ^ 32 + A / 2 ^ 32 * (B % 2 ^ 32) % 2 ^ 32
        + A % 2 ^ 32 * (B / 2 ^ 32) % 2 ^ 32) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, toNat_add3_of_lt hmid, hu, hv, hw]
  -- the limb identity, with the limbs of `A` and `B` reassembled
  have key := mulHi_limbs (A / 2 ^ 32) (A % 2 ^ 32) (B / 2 ^ 32) (B % 2 ^ 32)
  rw [Nat.div_add_mod' A (2 ^ 32), Nat.div_add_mod' B (2 ^ 32)] at key
  have hlt : A * B / 2 ^ 64 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hA hB)
  have hsum : X.toNat + Y.toNat + Z.toNat + ((u + v + w) >>> 32).toNat = A * B / 2 ^ 64 := by
    rw [hX, hY, hZ, hcarry, key]
  exact (toNat_add4_of_lt (by omega)).trans hsum

/-- `mulHi64` is the high half of the exact product: `⌊a * b / 2 ^ 64⌋`. -/
private theorem toNat_mulHi64 (a b : UInt64) :
    (mulHi64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have haLo : (a &&& 0xFFFFFFFF).toNat = a.toNat % 2 ^ 32 := toNat_and_low32 a
  have hbLo : (b &&& 0xFFFFFFFF).toNat = b.toNat % 2 ^ 32 := toNat_and_low32 b
  have haHi : (a >>> 32).toNat = a.toNat / 2 ^ 32 := toNat_shiftRight_32_uint64 a
  have hbHi : (b >>> 32).toNat = b.toNat / 2 ^ 32 := toNat_shiftRight_32_uint64 b
  have hb32 : ∀ n : ℕ, n < 2 ^ 64 → n / 2 ^ 32 < 2 ^ 32 := by
    intro n hn; exact Nat.div_lt_of_lt_mul (by omega)
  -- every limb product fits a register
  have hprod : ∀ u v : UInt64, u.toNat < 2 ^ 32 → v.toNat < 2 ^ 32 →
      (u * v).toNat = u.toNat * v.toNat := by
    intro u v hu hv
    have hlt : u.toNat * v.toNat < 2 ^ 64 := by
      calc u.toNat * v.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt hu hv
        _ = 2 ^ 64 := by norm_num
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
  simp only [mulHi64]
  -- the four limbs, and the four partial products they form
  have hAH : (a >>> 32).toNat < 2 ^ 32 := by rw [haHi]; exact hb32 _ ha
  have hAL : (a &&& (0xFFFFFFFF : UInt64)).toNat < 2 ^ 32 := by rw [haLo]; omega
  have hBH : (b >>> 32).toNat < 2 ^ 32 := by rw [hbHi]; exact hb32 _ hb
  have hBL : (b &&& (0xFFFFFFFF : UInt64)).toNat < 2 ^ 32 := by rw [hbLo]; omega
  have p11 := hprod _ _ hAH hBH
  have p10 := hprod _ _ hAH hBL
  have p01 := hprod _ _ hAL hBH
  have p00 := hprod _ _ hAL hBL
  -- each partial product's high and low halves
  have s10 : (((a >>> 32) * (b &&& (0xFFFFFFFF : UInt64))) >>> 32).toNat
      = (a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, p10, haHi, hbLo]
  have s01 : (((a &&& (0xFFFFFFFF : UInt64)) * (b >>> 32)) >>> 32).toNat
      = ((a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32)) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, p01, haLo, hbHi]
  have s00 : (((a &&& (0xFFFFFFFF : UInt64)) * (b &&& (0xFFFFFFFF : UInt64))) >>> 32).toNat
      = ((a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32)) / 2 ^ 32 := by
    rw [toNat_shiftRight_32_uint64, p00, haLo, hbLo]
  have m10 : (((a >>> 32) * (b &&& (0xFFFFFFFF : UInt64))) &&& (0xFFFFFFFF : UInt64)).toNat
      = (a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)) % 2 ^ 32 := by
    rw [toNat_and_low32, p10, haHi, hbLo]
  have m01 : (((a &&& (0xFFFFFFFF : UInt64)) * (b >>> 32)) &&& (0xFFFFFFFF : UInt64)).toNat
      = ((a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32)) % 2 ^ 32 := by
    rw [toNat_and_low32, p01, haLo, hbHi]
  -- the middle column, then the final sum; neither leaves its register
  have hmidlt : ((((a &&& (0xFFFFFFFF : UInt64)) * (b &&& (0xFFFFFFFF : UInt64))) >>> 32).toNat
      + (((a >>> 32) * (b &&& (0xFFFFFFFF : UInt64))) &&& (0xFFFFFFFF : UInt64)).toNat
      + (((a &&& (0xFFFFFFFF : UInt64)) * (b >>> 32)) &&& (0xFFFFFFFF : UInt64)).toNat)
        < 2 ^ 64 := by
    have h1 : ((a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32)) / 2 ^ 32 < 2 ^ 32 := by
      refine Nat.div_lt_of_lt_mul ?_
      calc (a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32) < 2 ^ 32 * 2 ^ 32 :=
            Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
        _ = 2 ^ 32 * 2 ^ 32 := rfl
    have h2 : (a.toNat / 2 ^ 32 * (b.toNat % 2 ^ 32)) % 2 ^ 32 < 2 ^ 32 :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have h3 : ((a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32)) % 2 ^ 32 < 2 ^ 32 :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [s00, m10, m01]; omega
  -- the top partial product, then the whole final column
  have t11 : ((a >>> 32) * (b >>> 32)).toNat = a.toNat / 2 ^ 32 * (b.toNat / 2 ^ 32) := by
    rw [p11, haHi, hbHi]
  exact toNat_finalColumn ha hb t11 s10 s01 s00 m10 m01 hmidlt

/-! ## The `63`-bit fixed-point conversion

`mtwop63` converts an `FPR` in `[0, 1)` to a `63`-bit fixed-point fraction. It reassembles the
significand into bits `62..10` of a register by a shift, an implicit-bit `|||`, and a mask, and
then rescales it by a right shift whose amount saturates at `63`. Both halves are exact: the
saturation bites only for operands below `2 ^ (-64)`, where the answer is `0` on either reading. -/

/-- Setting bit `k` of a value and then truncating to `k + 1` bits keeps the low `k` bits and
forces bit `k`. -/
private theorem or_two_pow_mod_two_pow_succ (A k : ℕ) :
    (A ||| 2 ^ k) % 2 ^ (k + 1) = A % 2 ^ k + 2 ^ k := by
  rw [← or_two_pow_add_of_lt _ k (Nat.mod_lt _ (Nat.two_pow_pos _))]
  refine Nat.eq_of_testBit_eq fun j => ?_
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy j k with h | h | h
  · simp [h, show j < k + 1 by omega, show ¬ k = j by omega]
  · subst h; simp
  · simp [show ¬ j < k by omega, show ¬ j < k + 1 by omega, show ¬ k = j by omega]

/-- Masking to six bits is the identity below `64`. -/
private theorem and_63_of_lt {n : ℕ} (h : n < 64) : n &&& 63 = n := by
  rw [show (63 : ℕ) = 2 ^ 6 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

/-- A value carrying all sixteen low bits saturates the six-bit mask. -/
private theorem and_63_or_65535 (n : ℕ) : (n ||| 65535) &&& 63 = 63 := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from by norm_num,
    show (63 : ℕ) = 2 ^ 6 - 1 from by norm_num]
  refine Nat.eq_of_testBit_eq fun j => ?_
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 6
  · simp [hj, show j < 16 from by omega]
  · simp [hj]

/-- The fraction word `mtwop63` builds before shifting: the operand's significand, scaled by
`2 ^ 10`. The sign bit is shifted out and the implicit-bit `|||` overwrites the one exponent bit
that survives, so no field of the operand other than its mantissa reaches the result. -/
private theorem toNat_m_of (x : FPR) :
    ((((x <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63)).toNat
      = 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52) := by
  have hM63 : (M63 : UInt64).toNat = 2 ^ 63 - 1 := by decide
  have hbit : ((1 : UInt64) <<< 62).toNat = 2 ^ 62 := by decide
  have hshl : (x <<< (10 : UInt64)).toNat = x.toNat * 2 ^ 10 % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, show ((10 : UInt64).toNat % 64) = 10 from by decide,
      Nat.shiftLeft_eq]
  rw [UInt64.toNat_and, hM63, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_or, hbit,
    show (63 : ℕ) = 62 + 1 from rfl, or_two_pow_mod_two_pow_succ, hshl,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : (62 : ℕ) ≤ 64)),
    show (2 : ℕ) ^ 62 = 2 ^ 52 * 2 ^ 10 from by norm_num, Nat.mul_mod_mul_right]
  unfold FPR.decode
  ring

/-- The shift amount `mtwop63` derives from `e`: the true gap when it fits in six bits, and a
saturated `63` otherwise. Beyond `63` the `UInt32` subtraction `63 - e` wraps, and the top half of
the wrapped value fills all six low bits of the mask. -/
private theorem toNat_ue_of (e : UInt32) (he : e.toNat < 2 ^ 16) :
    ((e ||| ((63 - e) >>> 16)) &&& 63).toNat = min e.toNat 63 := by
  have h63 : (63 : UInt32).toNat = 63 := by decide
  have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
  rw [UInt32.toNat_and, UInt32.toNat_or, h63, UInt32.toNat_shiftRight, h16,
    Nat.shiftRight_eq_div_pow]
  rcases le_or_gt e.toNat 63 with h | h
  · have hsub : ((63 : UInt32) - e).toNat = 63 - e.toNat := by
      rw [toNat_sub_of_le_uint32 (by rw [h63]; exact h), h63]
    rw [hsub, Nat.div_eq_of_lt (show 63 - e.toNat < 2 ^ 16 by omega), Nat.or_zero,
      and_63_of_lt (by omega), min_eq_left h]
  · have hsub : ((63 : UInt32) - e).toNat = 2 ^ 32 - e.toNat + 63 := by
      rw [UInt32.toNat_sub, h63]
      exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (2 ^ 32 - e.toNat + 63) / 2 ^ 16 = 65535 :=
      Nat.div_eq_of_lt_le (by norm_num; omega) (by norm_num; omega)
    rw [hsub, hdiv, and_63_or_65535, min_eq_right h.le]

/-- The final shift of `mtwop63`, read as a division. -/
private theorem toNat_shiftRight_ue {m : UInt64} {e : UInt32} {k : ℕ} (he : e.toNat = k)
    (hk : k < 2 ^ 16) :
    (m >>> (((e ||| ((63 - e) >>> 16)) &&& 63).toUInt64)).toNat = m.toNat / 2 ^ min k 63 := by
  have hue : ((e ||| ((63 - e) >>> 16)) &&& 63).toNat = min k 63 := by
    rw [toNat_ue_of e (by omega), he]
  rw [UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, hue, Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow]

/-- The exponent word `mtwop63` forms: the true gap `1022 - ex`, with no wraparound. -/
private theorem toNat_e_of (x : FPR) (hexle : (FPR.decode x).exponent ≤ 1022) :
    ((1022 : UInt32) - ((x >>> 52).toUInt32 &&& 0x7FF)).toNat
      = 1022 - (FPR.decode x).exponent := by
  have hfield : ((x >>> 52).toUInt32 &&& 0x7FF).toNat = (FPR.decode x).exponent :=
    toNat_ex_field_of x
  have h1022 : (1022 : UInt32).toNat = 1022 := by decide
  rw [toNat_sub_of_le_uint32 (by rw [hfield, h1022]; exact hexle), hfield, h1022]

/-- `mtwop63`, read as exact arithmetic on `ℕ`: the significand scaled by `2 ^ 10`, divided by
`2 ^ (1022 - ex)` with the shift amount saturated at `63`. -/
private theorem toNat_mtwop63_aux (x : FPR) (hexle : (FPR.decode x).exponent ≤ 1022) :
    (mtwop63 x).toNat = 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52)
      / 2 ^ min (1022 - (FPR.decode x).exponent) 63 := by
  simp only [mtwop63]
  rw [toNat_shiftRight_ue (toNat_e_of x hexle) (by omega), toNat_m_of]

/-- A normal operand with nonnegative value denotes `significand * 2 ^ (ex - 1075)`: the sign bit
is clear, so the case split in `FPR.Bits.toReal` collapses. -/
private theorem toReal_eq_significand_of_nonneg (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) :
    toReal x = (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ)
      * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by
  obtain ⟨hne0, hne2047⟩ := hn
  have hsig : (FPR.decode x).significand = (FPR.decode x).mantissa + 2 ^ 52 := by
    unfold FPR.Bits.significand
    rw [if_neg hne0]
  have hkey := toReal_eq_significand_mul_two_zpow hne0 hne2047
  rw [hsig] at hkey
  change toReal x = _ at hkey
  have hpos : (0 : ℝ) < (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ) := by
    have h : 0 < (FPR.decode x).mantissa + 2 ^ 52 := by omega
    exact_mod_cast h
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) := by positivity
  by_cases hs : (FPR.decode x).sign = true
  · rw [hkey, if_pos hs] at h0
    nlinarith
  · rw [hkey, if_neg hs]
    ring

/-- An operand below `1` has biased exponent at most `1022`: with the implicit leading bit, an
exponent field of `1023` already denotes a value of at least `1`. -/
private theorem exponent_le_of_toReal_lt_one (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (h1 : toReal x < 1) : (FPR.decode x).exponent ≤ 1022 := by
  by_contra hcon
  have hc : 1022 < (FPR.decode x).exponent := by omega
  rw [toReal_eq_significand_of_nonneg x hn h0] at h1
  have hsig : (2 : ℝ) ^ (52 : ℕ) ≤ (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ) := by
    have h : (2 : ℕ) ^ 52 ≤ (FPR.decode x).mantissa + 2 ^ 52 := by omega
    exact_mod_cast h
  have hz : (2 : ℝ) ^ ((1023 : ℤ) - 1075)
      ≤ (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ ((1023 : ℤ) - 1075) := by positivity
  have hone : (2 : ℝ) ^ (52 : ℕ) * (2 : ℝ) ^ ((1023 : ℤ) - 1075) = 1 := by
    rw [show ((1023 : ℤ) - 1075) = (-52 : ℤ) from by norm_num,
      ← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  nlinarith [mul_le_mul hsig hz hzpos.le (by positivity : (0 : ℝ) ≤
    (((FPR.decode x).mantissa + 2 ^ 52 : ℕ) : ℝ))]

/-- The exact value `mtwop63` is asked for, as a quotient of naturals. -/
private theorem floor_two_pow_63_mul_toReal (x : FPR) (hn : FPR.IsNormal x)
    (h0 : 0 ≤ toReal x) (h1 : toReal x < 1) :
    ⌊(2 : ℝ) ^ 63 * toReal x⌋₊ = 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52)
      / 2 ^ (1022 - (FPR.decode x).exponent) := by
  have hexle := exponent_le_of_toReal_lt_one x hn h0 h1
  have hexz : ((1022 - (FPR.decode x).exponent : ℕ) : ℤ)
      = (1022 : ℤ) - ((FPR.decode x).exponent : ℤ) := by omega
  have hcast : ((2 ^ (1022 - (FPR.decode x).exponent) : ℕ) : ℝ)
      = (2 : ℝ) ^ ((1022 : ℤ) - ((FPR.decode x).exponent : ℤ)) := by
    rw [← hexz, zpow_natCast]
    push_cast
    ring
  have hval : (2 : ℝ) ^ 63 * toReal x
      = ((2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52) : ℕ) : ℝ)
        / ((2 ^ (1022 - (FPR.decode x).exponent) : ℕ) : ℝ) := by
    rw [toReal_eq_significand_of_nonneg x hn h0, eq_div_iff (by positivity), hcast]
    have hexp : (2 : ℝ) ^ (63 : ℕ) * (2 : ℝ) ^ (((FPR.decode x).exponent : ℤ) - 1075)
        * (2 : ℝ) ^ ((1022 : ℤ) - ((FPR.decode x).exponent : ℤ)) = (2 : ℝ) ^ (10 : ℕ) := by
      rw [← zpow_natCast (2 : ℝ) 63, ← zpow_natCast (2 : ℝ) 10,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    push_cast
    linear_combination (((FPR.decode x).mantissa : ℝ) + 2 ^ 52) * hexp
  rw [hval, Nat.floor_div_natCast, Nat.floor_natCast]

/-- On an all-ones exponent field `mtwop63` returns `0`: the exponent word `1022 - 2047` wraps,
and the wrapped value saturates the shift at `63`, which clears the whole `63`-bit fraction. -/
private theorem toNat_mtwop63_of_exponent_eq_2047 (x : FPR)
    (hex : (FPR.decode x).exponent = 2047) : (mtwop63 x).toNat = 0 := by
  have hfield : ((x >>> 52).toUInt32 &&& 0x7FF) = (2047 : UInt32) := by
    rw [← UInt32.toNat_inj, toNat_ex_field_of x, hex]
    decide
  have hman := FPR.decode_mantissa_lt x
  have hue : ((((1022 : UInt32) - (2047 : UInt32)) |||
      (((63 : UInt32) - ((1022 : UInt32) - (2047 : UInt32))) >>> (16 : UInt32)))
      &&& (63 : UInt32)) = (63 : UInt32) := by decide
  simp only [mtwop63]
  rw [hfield, hue, UInt64.toNat_shiftRight,
    show ((63 : UInt32).toUInt64.toNat % 64) = 63 from by decide,
    Nat.shiftRight_eq_div_pow, toNat_m_of]
  exact Nat.div_eq_of_lt (by omega)

/-- A subnormal operand is below `2 ^ (-1022)` in magnitude. -/
private theorem toReal_lt_of_exponent_eq_zero (x : FPR)
    (hex : (FPR.decode x).exponent = 0) : toReal x < 2 ^ (-1022 : ℤ) := by
  have hm : ((FPR.decode x).mantissa : ℝ) < 2 ^ (52 : ℕ) := by
    exact_mod_cast FPR.decode_mantissa_lt x
  have hm0 : (0 : ℝ) ≤ ((FPR.decode x).mantissa : ℝ) := Nat.cast_nonneg _
  have hkey : (2 : ℝ) ^ (52 : ℕ) * 2 ^ (-1074 : ℤ) = 2 ^ (-1022 : ℤ) := by
    rw [← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hz : (0 : ℝ) < 2 ^ (-1074 : ℤ) := by positivity
  change (FPR.decode x).toReal < _
  unfold FPR.Bits.toReal
  rw [if_pos hex]
  by_cases hs : (FPR.decode x).sign = true
  · rw [if_pos hs]; nlinarith
  · rw [if_neg hs]; nlinarith

/-- On a subnormal operand `mtwop63` returns `0`: the shift saturates at `63` there too. -/
private theorem toNat_mtwop63_of_exponent_eq_zero (x : FPR)
    (hex : (FPR.decode x).exponent = 0) : (mtwop63 x).toNat = 0 := by
  have hman := FPR.decode_mantissa_lt x
  rw [toNat_mtwop63_aux x (by omega), hex]
  exact Nat.div_eq_of_lt (by norm_num; omega)

/-- `mtwop63` converts an `FPR` in `[0, 1)` to a `63`-bit fixed-point fraction: it computes
`⌊2 ^ 63 * toReal x⌋`, exactly and with no rounding of its own. -/
private theorem toNat_mtwop63 (x : FPR)
    (h0 : 0 ≤ toReal x) (h1 : toReal x < 1) :
    (mtwop63 x).toNat = ⌊(2 : ℝ) ^ 63 * toReal x⌋₊ := by
  by_cases hn : FPR.IsNormal x
  case neg =>
    have hcases : (FPR.decode x).exponent = 0 ∨ (FPR.decode x).exponent = 2047 := by
      by_contra hc
      exact hn ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
    have hle : (2 : ℝ) ^ (-959 : ℤ) ≤ 1 := by
      simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-959 : ℤ) ≤ 0)
    rcases hcases with hex | hex
    · rw [toNat_mtwop63_of_exponent_eq_zero x hex]
      symm
      rw [Nat.floor_eq_zero]
      have ht := toReal_lt_of_exponent_eq_zero x hex
      have hb : (2 : ℝ) ^ (63 : ℕ) * 2 ^ (-1022 : ℤ) = 2 ^ (-959 : ℤ) := by
        rw [← zpow_natCast (2 : ℝ) 63, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 63]
    · rw [toNat_mtwop63_of_exponent_eq_2047 x hex]
      have hz : toReal x = 0 := by
        change (FPR.decode x).toReal = 0
        unfold FPR.Bits.toReal
        rw [if_neg (by omega : (FPR.decode x).exponent ≠ 0), if_pos hex]
      rw [hz]
      norm_num
  case pos =>
    have hexle := exponent_le_of_toReal_lt_one x hn h0 h1
    have hmanlt : (FPR.decode x).mantissa < 2 ^ 52 := FPR.decode_mantissa_lt x
    rw [floor_two_pow_63_mul_toReal x hn h0 h1, toNat_mtwop63_aux x hexle]
    rcases le_or_gt (1022 - (FPR.decode x).exponent) 63 with h | h
    · rw [min_eq_left h]
    · have hN : 2 ^ 10 * ((FPR.decode x).mantissa + 2 ^ 52) < 2 ^ 63 := by omega
      have hD : (2 : ℕ) ^ 63 ≤ 2 ^ (1022 - (FPR.decode x).exponent) :=
        Nat.pow_le_pow_right (by norm_num) h.le
      rw [min_eq_right h.le, Nat.div_eq_of_lt hN, Nat.div_eq_of_lt (lt_of_lt_of_le hN hD)]

/-! ## The Horner pipeline

`expm_p63` evaluates the FACCT coefficient table by Horner's rule in `UInt64` fixed point and then
applies a second `mtwop63` reading as a scale. Every step truncates, since `mulHi64` keeps only the
high half of a `128`-bit product. This section reads the loop as the exact real Horner recurrence
`hornerExact` on the same coefficients at the same quantised argument, and bounds the accumulated
truncation.

The bound is a fixed point of the step estimate `e ↦ ζ * e + 1`: one unit of fresh truncation per
step, on top of the incoming error scaled by the argument `ζ`, which `mtwop63` pins below `0.694`.
The same estimate also shows the `UInt64` subtraction `facctCoeffs[i] - mulHi64 z y` never wraps —
in fact `mulHi64 z y ≤ y` outright, so the wrap-freedom needs no numeric input at all. -/

/-- The fixed-point reading of `mtwop63 v <<< 1` as a real in `[0, 1)`. Both the polynomial's
argument `z` and its final scale `w` take this form. -/
private noncomputable def scaledArg (v : FPR) : ℝ := (((mtwop63 v) <<< 1).toNat : ℝ) / 2 ^ 64

/-- The `UInt64` Horner sequence that `expm_p63`'s loop computes. -/
private def hornerMachine (z : UInt64) : ℕ → UInt64
  | 0 => facctCoeffs[0]!
  | (i + 1) => facctCoeffs[i + 1]! - mulHi64 z (hornerMachine z i)

/-- The exact real Horner sequence on the same coefficients at the same quantised argument: the
value `hornerMachine` would compute if `mulHi64` did not truncate. -/
private noncomputable def hornerExact (ζ : ℝ) : ℕ → ℝ
  | 0 => ((facctCoeffs[0]!).toNat : ℝ)
  | (i + 1) => ((facctCoeffs[i + 1]!).toNat : ℝ) - ζ * hornerExact ζ i

/-- `expm_p63`'s loop, unrolled: its twelve iterations are exactly `hornerMachine`. -/
private theorem expm_p63_eq (x ccs : FPR) :
    expm_p63 x ccs = mulHi64 ((mtwop63 ccs) <<< 1) (hornerMachine ((mtwop63 x) <<< 1) 12) := by
  simp only [expm_p63, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    show ((Std.Legacy.Range.mk 1 facctCoeffs.size 1 (by decide)).size) = 12 from by decide,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, hornerMachine]
  rfl

/-- `mulHi64` never exceeds its second operand: the high half of `a * b` is at most `b`, whatever
`a` is. This alone rules out wraparound in the loop's subtraction. -/
private theorem toNat_mulHi64_le (a b : UInt64) : (mulHi64 a b).toNat ≤ b.toNat := by
  rw [toNat_mulHi64]
  calc a.toNat * b.toNat / 2 ^ 64 ≤ 2 ^ 64 * b.toNat / 2 ^ 64 :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ a.toNat_lt_size.le)
    _ = b.toNat := Nat.mul_div_cancel_left _ (by norm_num)

/-- `mulHi64 a b` is `⌊(a / 2 ^ 64) * b⌋`: the fixed-point product, truncated by less than one. -/
private theorem mulHi64_bracket (a b : UInt64) :
    ((mulHi64 a b).toNat : ℝ) ≤ (a.toNat : ℝ) / 2 ^ 64 * (b.toNat : ℝ) ∧
      (a.toNat : ℝ) / 2 ^ 64 * (b.toNat : ℝ) < ((mulHi64 a b).toNat : ℝ) + 1 := by
  have hval : (a.toNat : ℝ) / 2 ^ 64 * (b.toNat : ℝ)
      = ((a.toNat * b.toNat : ℕ) : ℝ) / ((2 ^ 64 : ℕ) : ℝ) := by push_cast; ring
  have hfl : ((mulHi64 a b).toNat : ℝ)
      = ((⌊((a.toNat * b.toNat : ℕ) : ℝ) / ((2 ^ 64 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by
    rw [Nat.floor_div_eq_div, toNat_mulHi64]
  rw [hval, hfl]
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- The coefficient table is nondecreasing, so a bound at one index carries to the next. -/
private theorem facctCoeffs_mono {i : ℕ} (hi : i < 12) :
    (facctCoeffs[i]!).toNat ≤ (facctCoeffs[i + 1]!).toNat := by
  interval_cases i <;> decide

/-- One Horner step. The `UInt64` subtraction cannot wrap, since `mulHi64 z y ≤ y ≤ c`; and the
step's own truncation costs at most `1`, on top of the incoming error scaled by `ζ`. -/
private theorem horner_step {z y c : UInt64} {Y ζ : ℝ}
    (hζ : ζ = (z.toNat : ℝ) / 2 ^ 64) (hζ1 : ζ ≤ 694 / 1000)
    (hyc : y.toNat ≤ c.toNat) (hy : |(y.toNat : ℝ) - Y| ≤ 4) :
    (c - mulHi64 z y).toNat ≤ c.toNat ∧
      |((c - mulHi64 z y).toNat : ℝ) - ((c.toNat : ℝ) - ζ * Y)| ≤ 4 := by
  have hmc : (mulHi64 z y).toNat ≤ c.toNat := le_trans (toNat_mulHi64_le z y) hyc
  have hsub : (c - mulHi64 z y).toNat = c.toNat - (mulHi64 z y).toNat :=
    toNat_sub_of_le_uint64 c _ hmc
  refine ⟨by omega, ?_⟩
  obtain ⟨hb1, hb2⟩ := mulHi64_bracket z y
  rw [← hζ] at hb1 hb2
  have hζ0 : 0 ≤ ζ := by rw [hζ]; positivity
  rw [hsub, Nat.cast_sub hmc,
    show (c.toNat : ℝ) - ((mulHi64 z y).toNat : ℝ) - ((c.toNat : ℝ) - ζ * Y)
      = ζ * Y - ((mulHi64 z y).toNat : ℝ) from by ring, abs_le]
  rw [abs_le] at hy
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hy.2 hζ0],
    by nlinarith [mul_le_mul_of_nonneg_left hy.1 hζ0]⟩

/-- The loop invariant: each iterate stays under its own coefficient — so the next subtraction
cannot wrap — and tracks the exact recurrence to within `4`. -/
private theorem hornerMachine_error {z : UInt64} {ζ : ℝ}
    (hζ : ζ = (z.toNat : ℝ) / 2 ^ 64) (hζ1 : ζ ≤ 694 / 1000) :
    ∀ i, i ≤ 12 → (hornerMachine z i).toNat ≤ (facctCoeffs[i]!).toNat ∧
      |((hornerMachine z i).toNat : ℝ) - hornerExact ζ i| ≤ 4 := by
  intro i
  induction i with
  | zero => intro _; simp [hornerMachine, hornerExact]
  | succ k ih =>
    intro hk
    obtain ⟨hle, herr⟩ := ih (by omega)
    have hstep := horner_step hζ hζ1 (le_trans hle (facctCoeffs_mono (by omega))) herr
    rw [show hornerMachine z (k + 1)
        = facctCoeffs[k + 1]! - mulHi64 z (hornerMachine z k) from rfl,
      show hornerExact ζ (k + 1)
        = ((facctCoeffs[k + 1]!).toNat : ℝ) - ζ * hornerExact ζ k from rfl]
    exact hstep

/-- `scaledArg` lands in `[0, 1]`, which is all the final scaling multiply needs of it. -/
private theorem scaledArg_nonneg (v : FPR) : 0 ≤ scaledArg v := by
  unfold scaledArg; positivity

private theorem scaledArg_le_one (v : FPR) : scaledArg v ≤ 1 := by
  unfold scaledArg
  rw [div_le_one (by norm_num)]
  exact_mod_cast ((mtwop63 v) <<< 1).toNat_lt_size.le

/-- `mtwop63 x <<< 1` reads `2 ^ 64 * toReal x` rounded down, so `scaledArg x` never exceeds
`toReal x`. -/
private theorem scaledArg_le_toReal (x : FPR) (h0 : 0 ≤ toReal x)
    (h1 : toReal x < 1) : scaledArg x ≤ toReal x := by
  have hm : (mtwop63 x).toNat = ⌊(2 : ℝ) ^ 63 * toReal x⌋₊ := toNat_mtwop63 x h0 h1
  have hlt : (mtwop63 x).toNat < 2 ^ 63 := by
    rw [hm]
    exact (Nat.floor_lt (by positivity)).mpr (by push_cast; nlinarith)
  have hsh : ((mtwop63 x) <<< 1).toNat = (mtwop63 x).toNat * 2 := by
    rw [toNat_shiftLeft_one]
    exact Nat.mod_eq_of_lt (by omega)
  have hfl : ((mtwop63 x).toNat : ℝ) ≤ (2 : ℝ) ^ 63 * toReal x := by
    rw [hm]; exact Nat.floor_le (by positivity)
  unfold scaledArg
  rw [hsh, div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 64)]
  push_cast
  nlinarith

/-- Quantisation only ever rounds the argument down, so the bound on `toReal x` carries to
`scaledArg x` — and `0.694` is the contraction factor the error induction runs on. -/
private theorem scaledArg_le_694 (x : FPR) (h0 : 0 ≤ toReal x)
    (hub : toReal x ≤ 694 / 1000) : scaledArg x ≤ 694 / 1000 :=
  le_trans (scaledArg_le_toReal x h0 (by linarith)) hub

/-- **(a)** Every Horner iterate of the fixed-point loop tracks the exact real recurrence at the
same quantised argument to within `4`. -/
private theorem hornerMachine_sub_hornerExact_le (x : FPR)
    (h0 : 0 ≤ toReal x) (hub : toReal x ≤ 694 / 1000) (i : ℕ) (hi : i ≤ 12) :
    |((hornerMachine ((mtwop63 x) <<< 1) i).toNat : ℝ) - hornerExact (scaledArg x) i| ≤ 4 :=
  (hornerMachine_error rfl (scaledArg_le_694 x h0 hub) i hi).2

/-- **(b)** The whole pipeline, including the final scaling multiply: `expm_p63 x ccs` tracks
`scaledArg ccs * hornerExact (scaledArg x) 12` to within `5`. -/
private theorem expm_p63_sub_exact_le (x ccs : FPR)
    (h0 : 0 ≤ toReal x) (hub : toReal x ≤ 694 / 1000) :
    |((expm_p63 x ccs).toNat : ℝ) - scaledArg ccs * hornerExact (scaledArg x) 12| ≤ 5 := by
  have hy := hornerMachine_sub_hornerExact_le x h0 hub 12 le_rfl
  obtain ⟨hb1, hb2⟩ := mulHi64_bracket ((mtwop63 ccs) <<< 1) (hornerMachine ((mtwop63 x) <<< 1) 12)
  rw [show (((mtwop63 ccs) <<< 1).toNat : ℝ) / 2 ^ 64 = scaledArg ccs from rfl] at hb1 hb2
  have hs0 := scaledArg_nonneg ccs
  have hs1 := scaledArg_le_one ccs
  rw [expm_p63_eq, abs_le]
  rw [abs_le] at hy
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hy.1 hs0],
    by nlinarith [mul_le_mul_of_nonneg_left hy.2 hs0]⟩

/-! ## From the quantised arguments to the true ones

The bounds above are stated at `scaledArg x` and `scaledArg ccs`, the arguments the machine
actually uses. Because `mtwop63` is exact, each differs from the operand it stands for by a pure
floor error below `2 ^ (-63)`, and transporting the bound across that gap costs a little over one
unit at each of the two places an argument enters: through the polynomial's argument, where the
Lipschitz constant is about `2 ^ 63`, and through the final scale, where the polynomial's own
magnitude is about `2 ^ 63`. -/

private theorem two_zpow_neg_63 : (2 : ℝ) ^ (-63 : ℤ) = 1 / 2 ^ (63 : ℕ) := by norm_num

/-- `scaledArg v` is exactly `⌊2 ^ 63 * toReal v⌋ / 2 ^ 63`: the shift by one cannot overflow, so
the doubling cancels one power of two against the `2 ^ 64` scale. -/
private theorem scaledArg_eq (v : FPR) (h0 : 0 ≤ toReal v)
    (h1 : toReal v < 1) :
    scaledArg v = ((⌊(2 : ℝ) ^ 63 * toReal v⌋₊ : ℕ) : ℝ) / 2 ^ 63 := by
  have hm : (mtwop63 v).toNat = ⌊(2 : ℝ) ^ 63 * toReal v⌋₊ := toNat_mtwop63 v h0 h1
  have hlt : (mtwop63 v).toNat < 2 ^ 63 := by
    rw [hm]
    exact (Nat.floor_lt (by positivity)).mpr (by push_cast; nlinarith)
  have hsh : ((mtwop63 v) <<< 1).toNat = (mtwop63 v).toNat * 2 := by
    rw [toNat_shiftLeft_one]
    exact Nat.mod_eq_of_lt (by omega)
  unfold scaledArg
  rw [hsh, hm]
  push_cast
  ring

/-- **(1)** The quantisation gap: `scaledArg v` sits within `2 ^ (-63)` below `toReal v`. -/
private theorem scaledArg_bracket (v : FPR)
    (h0 : 0 ≤ toReal v) (h1 : toReal v < 1) :
    scaledArg v ≤ toReal v ∧ toReal v < scaledArg v + (2 : ℝ) ^ (-63 : ℤ) := by
  refine ⟨scaledArg_le_toReal v h0 h1, ?_⟩
  have hfl := Nat.lt_floor_add_one ((2 : ℝ) ^ 63 * toReal v)
  rw [scaledArg_eq v h0 h1, two_zpow_neg_63,
    show ((⌊(2 : ℝ) ^ 63 * toReal v⌋₊ : ℕ) : ℝ) / 2 ^ (63 : ℕ) + 1 / 2 ^ (63 : ℕ)
      = (((⌊(2 : ℝ) ^ 63 * toReal v⌋₊ : ℕ) : ℝ) + 1) / 2 ^ (63 : ℕ) from by ring,
    lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (63 : ℕ))]
  linarith

/-- Every coefficient fits in `63` bits. -/
private theorem facctCoeffs_le {i : ℕ} (hi : i ≤ 12) : (facctCoeffs[i]!).toNat ≤ 2 ^ 63 := by
  interval_cases i <;> decide

/-- The exact Horner iterates stay in `[0, facctCoeffs[i]]`: nonnegative because the table grows
faster than the argument shrinks it, and bounded by the coefficient because the subtracted term is
nonnegative. -/
private theorem hornerExact_mem (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 694 / 1000) :
    ∀ i, i ≤ 12 → 0 ≤ hornerExact t i ∧ hornerExact t i ≤ ((facctCoeffs[i]!).toNat : ℝ) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [show hornerExact t 0 = ((facctCoeffs[0]!).toNat : ℝ) from rfl]
    exact ⟨Nat.cast_nonneg _, le_rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hlo, hhi⟩ := ih (by omega)
    have hmono : ((facctCoeffs[k]!).toNat : ℝ) ≤ ((facctCoeffs[k + 1]!).toNat : ℝ) :=
      Nat.cast_le.mpr (facctCoeffs_mono (by omega))
    have hprod : t * hornerExact t k ≤ 694 / 1000 * ((facctCoeffs[k]!).toNat : ℝ) :=
      mul_le_mul ht1 hhi hlo (by norm_num)
    have hck : (0 : ℝ) ≤ ((facctCoeffs[k]!).toNat : ℝ) := Nat.cast_nonneg _
    rw [show hornerExact t (k + 1)
      = ((facctCoeffs[k + 1]!).toNat : ℝ) - t * hornerExact t k from rfl]
    exact ⟨by linarith, by nlinarith [mul_nonneg ht0 hlo]⟩

/-- The exact Horner iterates never exceed `2 ^ 63` in magnitude. -/
private theorem hornerExact_abs_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 694 / 1000) (i : ℕ)
    (hi : i ≤ 12) : |hornerExact t i| ≤ 2 ^ 63 := by
  obtain ⟨hlo, hhi⟩ := hornerExact_mem t ht0 ht1 i hi
  rw [abs_of_nonneg hlo]
  exact le_trans hhi (by exact_mod_cast facctCoeffs_le hi)

/-- **(2)** The exact Horner sequence is Lipschitz in its argument, with constant `2 ^ 65`. The
step estimate is `d ↦ t * d + 2 ^ 63`, whose fixed point needs a constant at least
`2 ^ 63 / (1 - 0.694) ≈ 3.27 * 2 ^ 63`; `2 ^ 65` is the next power of two above that, and closes
the induction since `0.694 * 4 + 1 ≤ 4`. -/
private theorem hornerExact_lipschitz (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs1 : s ≤ 694 / 1000) (ht1 : t ≤ 694 / 1000) :
    ∀ i, i ≤ 12 → |hornerExact s i - hornerExact t i| ≤ (2 : ℝ) ^ 65 * |s - t| := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [show hornerExact s 0 = ((facctCoeffs[0]!).toNat : ℝ) from rfl,
      show hornerExact t 0 = ((facctCoeffs[0]!).toNat : ℝ) from rfl, sub_self, abs_zero]
    positivity
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hmag := hornerExact_abs_le t ht0 ht1 k (by omega)
    have hkey : hornerExact s (k + 1) - hornerExact t (k + 1)
        = (t - s) * hornerExact t k + s * (hornerExact t k - hornerExact s k) := by
      rw [show hornerExact s (k + 1)
          = ((facctCoeffs[k + 1]!).toNat : ℝ) - s * hornerExact s k from rfl,
        show hornerExact t (k + 1)
          = ((facctCoeffs[k + 1]!).toNat : ℝ) - t * hornerExact t k from rfl]
      ring
    have h1 : |(t - s) * hornerExact t k| ≤ |s - t| * 2 ^ 63 := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hmag (abs_nonneg _)
    have h2 : |s * (hornerExact t k - hornerExact s k)|
        ≤ 694 / 1000 * ((2 : ℝ) ^ 65 * |s - t|) := by
      rw [abs_mul, abs_of_nonneg hs0, abs_sub_comm]
      exact mul_le_mul hs1 ihk (abs_nonneg _) (by norm_num)
    calc |hornerExact s (k + 1) - hornerExact t (k + 1)|
        ≤ |(t - s) * hornerExact t k| + |s * (hornerExact t k - hornerExact s k)| := by
          rw [hkey]; exact abs_add_le _ _
      _ ≤ |s - t| * 2 ^ 63 + 694 / 1000 * ((2 : ℝ) ^ 65 * |s - t|) := add_le_add h1 h2
      _ ≤ (2 : ℝ) ^ 65 * |s - t| := by nlinarith [abs_nonneg (s - t)]

/-- **(3)** The whole fixed-point pipeline against the exact polynomial at the *true* operands.
The two quantisation gaps contribute `2 ^ 65 * 2 ^ (-63) = 4` through the argument and
`2 ^ (-63) * 2 ^ 63 = 1` through the scale, on top of the truncation bound `5`. -/
private theorem expm_p63_sub_trueArg_le (x ccs : FPR)
    (h0 : 0 ≤ toReal x) (hub : toReal x ≤ 694 / 1000)
    (hc0 : 0 ≤ toReal ccs) (hc1 : toReal ccs < 1) :
    |((expm_p63 x ccs).toNat : ℝ) - toReal ccs * hornerExact (toReal x) 12| ≤ 10 := by
  have hx1 : toReal x < 1 := by linarith
  have hsx := scaledArg_bracket x h0 hx1
  have hsc := scaledArg_bracket ccs hc0 hc1
  rw [two_zpow_neg_63] at hsx hsc
  have hmain := expm_p63_sub_exact_le x ccs h0 hub
  have hLip := hornerExact_lipschitz (scaledArg x) (toReal x) (scaledArg_nonneg x) h0
    (scaledArg_le_694 x h0 hub) hub 12 le_rfl
  have hmag := hornerExact_abs_le (toReal x) h0 hub 12 le_rfl
  have hdx : |scaledArg x - toReal x| ≤ 1 / 2 ^ (63 : ℕ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hsx.1])]
    linarith [hsx.2]
  have hdc : |scaledArg ccs - toReal ccs| ≤ 1 / 2 ^ (63 : ℕ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hsc.1])]
    linarith [hsc.2]
  have hHd : |hornerExact (scaledArg x) 12 - hornerExact (toReal x) 12| ≤ 4 :=
    le_trans hLip (by
      calc (2 : ℝ) ^ 65 * |scaledArg x - toReal x|
          ≤ (2 : ℝ) ^ 65 * (1 / 2 ^ (63 : ℕ)) := mul_le_mul_of_nonneg_left hdx (by positivity)
        _ = 4 := by norm_num)
  have hkey : |scaledArg ccs * hornerExact (scaledArg x) 12
      - toReal ccs * hornerExact (toReal x) 12| ≤ 5 := by
    calc |scaledArg ccs * hornerExact (scaledArg x) 12
            - toReal ccs * hornerExact (toReal x) 12|
        ≤ |scaledArg ccs * (hornerExact (scaledArg x) 12 - hornerExact (toReal x) 12)|
          + |(scaledArg ccs - toReal ccs) * hornerExact (toReal x) 12| := by
          rw [show scaledArg ccs * hornerExact (scaledArg x) 12
              - toReal ccs * hornerExact (toReal x) 12
              = scaledArg ccs * (hornerExact (scaledArg x) 12 - hornerExact (toReal x) 12)
                + (scaledArg ccs - toReal ccs) * hornerExact (toReal x) 12 from by ring]
          exact abs_add_le _ _
      _ ≤ 1 * 4 + 1 / 2 ^ (63 : ℕ) * 2 ^ 63 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (scaledArg_nonneg ccs)]
          exact add_le_add
            (mul_le_mul (scaledArg_le_one ccs) hHd (abs_nonneg _) (by norm_num))
            (mul_le_mul hdc hmag (abs_nonneg _) (by positivity))
      _ = 5 := by norm_num
  calc |((expm_p63 x ccs).toNat : ℝ) - toReal ccs * hornerExact (toReal x) 12|
      ≤ |((expm_p63 x ccs).toNat : ℝ) - scaledArg ccs * hornerExact (scaledArg x) 12|
        + |scaledArg ccs * hornerExact (scaledArg x) 12
          - toReal ccs * hornerExact (toReal x) 12| := abs_sub_le _ _ _
    _ ≤ 5 + 5 := add_le_add hmain hkey
    _ = 10 := by norm_num

/-! ## Certifying the coefficient polynomial

The remaining obligation is `sup |certQ|` over `[0, log 2)`, where `certQ` is the exact Horner
polynomial measured against a degree-18 Taylor truncation of `exp (-x)`, in units of `2 ^ (-63)`.
`facctCoeffs` is a minimax fit, so `certQ` is `O(1)` in these units while its coefficients are
`O(2 ^ 63)`: every bound that applies a triangle inequality to coefficients discards exactly the
cancellation that makes the fit good, and misses by orders of magnitude.

What survives is subdivision in a Chebyshev basis. On a subinterval parameterised by
`x = (p + q * y) / s` with `y ∈ [-1, 1]`, writing `D * certQ` as `∑ j, N j * T j y` gives
`|certQ| ≤ (∑ j, |N j|) / D` from `|T j y| ≤ 1` alone, and the cancellation is carried by the
coefficients rather than thrown away.

Two things make the certificates cheap. The interval endpoints are *dyadic*, so `s` is a power of
two and the cleared coefficients stay near 60 digits rather than the ~330 that equal subdivision
of `[0, r]` by a decimal `r` would force; and `certQ_expand` clears `18!` once, so every
per-certificate identity is a polynomial identity over `ℤ` with no division. -/

/-- Monomial form of `Chebyshev.T` at the reals, degree 0. -/
private theorem chebEval0 (y : ℝ) : (Chebyshev.T ℝ (0 : ℤ)).eval y = 1 := by
  simp [Chebyshev.T_zero]

private theorem chebEval1 (y : ℝ) : (Chebyshev.T ℝ (1 : ℤ)).eval y = y := by
  simp [Chebyshev.T_one]

private theorem chebEval2 (y : ℝ) : (Chebyshev.T ℝ (2 : ℤ)).eval y =
    (-1) + 2 * y ^ 2
    := by
  rw [show (2 : ℤ) = 0 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (0 : ℤ) + 1 = 1 from by norm_num,
    chebEval1, chebEval0]
  ring

private theorem chebEval3 (y : ℝ) : (Chebyshev.T ℝ (3 : ℤ)).eval y =
    (-3) * y + 4 * y ^ 3
    := by
  rw [show (3 : ℤ) = 1 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (1 : ℤ) + 1 = 2 from by norm_num,
    chebEval2, chebEval1]
  ring

private theorem chebEval4 (y : ℝ) : (Chebyshev.T ℝ (4 : ℤ)).eval y =
    1 + (-8) * y ^ 2 + 8 * y ^ 4
    := by
  rw [show (4 : ℤ) = 2 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (2 : ℤ) + 1 = 3 from by norm_num,
    chebEval3, chebEval2]
  ring

private theorem chebEval5 (y : ℝ) : (Chebyshev.T ℝ (5 : ℤ)).eval y =
    5 * y + (-20) * y ^ 3 + 16 * y ^ 5
    := by
  rw [show (5 : ℤ) = 3 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (3 : ℤ) + 1 = 4 from by norm_num,
    chebEval4, chebEval3]
  ring

private theorem chebEval6 (y : ℝ) : (Chebyshev.T ℝ (6 : ℤ)).eval y =
    (-1) + 18 * y ^ 2 + (-48) * y ^ 4 + 32 * y ^ 6
    := by
  rw [show (6 : ℤ) = 4 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (4 : ℤ) + 1 = 5 from by norm_num,
    chebEval5, chebEval4]
  ring

private theorem chebEval7 (y : ℝ) : (Chebyshev.T ℝ (7 : ℤ)).eval y =
    (-7) * y + 56 * y ^ 3 + (-112) * y ^ 5 + 64 * y ^ 7
    := by
  rw [show (7 : ℤ) = 5 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (5 : ℤ) + 1 = 6 from by norm_num,
    chebEval6, chebEval5]
  ring

private theorem chebEval8 (y : ℝ) : (Chebyshev.T ℝ (8 : ℤ)).eval y =
    1 + (-32) * y ^ 2 + 160 * y ^ 4 + (-256) * y ^ 6 + 128 * y ^ 8
    := by
  rw [show (8 : ℤ) = 6 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (6 : ℤ) + 1 = 7 from by norm_num,
    chebEval7, chebEval6]
  ring

private theorem chebEval9 (y : ℝ) : (Chebyshev.T ℝ (9 : ℤ)).eval y =
    9 * y + (-120) * y ^ 3 + 432 * y ^ 5 + (-576) * y ^ 7 + 256 * y ^ 9
    := by
  rw [show (9 : ℤ) = 7 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (7 : ℤ) + 1 = 8 from by norm_num,
    chebEval8, chebEval7]
  ring

private theorem chebEval10 (y : ℝ) : (Chebyshev.T ℝ (10 : ℤ)).eval y =
    (-1) + 50 * y ^ 2 + (-400) * y ^ 4 + 1120 * y ^ 6 + (-1280) * y ^ 8 + 512 * y ^ 10
    := by
  rw [show (10 : ℤ) = 8 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (8 : ℤ) + 1 = 9 from by norm_num,
    chebEval9, chebEval8]
  ring

private theorem chebEval11 (y : ℝ) : (Chebyshev.T ℝ (11 : ℤ)).eval y =
    (-11) * y + 220 * y ^ 3 + (-1232) * y ^ 5 + 2816 * y ^ 7 + (-2816) * y ^ 9 + 1024 * y ^ 11
    := by
  rw [show (11 : ℤ) = 9 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (9 : ℤ) + 1 = 10 from by norm_num,
    chebEval10, chebEval9]
  ring

private theorem chebEval12 (y : ℝ) : (Chebyshev.T ℝ (12 : ℤ)).eval y =
    1 + (-72) * y ^ 2 + 840 * y ^ 4 + (-3584) * y ^ 6 + 6912 * y ^ 8 + (-6144) * y ^ 10 + 2048 * y
      ^ 12
    := by
  rw [show (12 : ℤ) = 10 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (10 : ℤ) + 1 = 11 from by norm_num,
    chebEval11, chebEval10]
  ring

private theorem chebEval13 (y : ℝ) : (Chebyshev.T ℝ (13 : ℤ)).eval y =
    13 * y + (-364) * y ^ 3 + 2912 * y ^ 5 + (-9984) * y ^ 7 + 16640 * y ^ 9 + (-13312) * y ^ 11 +
      4096 * y ^ 13
    := by
  rw [show (13 : ℤ) = 11 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (11 : ℤ) + 1 = 12 from by norm_num,
    chebEval12, chebEval11]
  ring

private theorem chebEval14 (y : ℝ) : (Chebyshev.T ℝ (14 : ℤ)).eval y =
    (-1) + 98 * y ^ 2 + (-1568) * y ^ 4 + 9408 * y ^ 6 + (-26880) * y ^ 8 + 39424 * y ^ 10 +
      (-28672) * y ^ 12 + 8192 * y ^ 14
    := by
  rw [show (14 : ℤ) = 12 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (12 : ℤ) + 1 = 13 from by norm_num,
    chebEval13, chebEval12]
  ring

private theorem chebEval15 (y : ℝ) : (Chebyshev.T ℝ (15 : ℤ)).eval y =
    (-15) * y + 560 * y ^ 3 + (-6048) * y ^ 5 + 28800 * y ^ 7 + (-70400) * y ^ 9 + 92160 * y ^ 11
      + (-61440) * y ^ 13 + 16384 * y ^ 15
    := by
  rw [show (15 : ℤ) = 13 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (13 : ℤ) + 1 = 14 from by norm_num,
    chebEval14, chebEval13]
  ring

private theorem chebEval16 (y : ℝ) : (Chebyshev.T ℝ (16 : ℤ)).eval y =
    1 + (-128) * y ^ 2 + 2688 * y ^ 4 + (-21504) * y ^ 6 + 84480 * y ^ 8 + (-180224) * y ^ 10 +
      212992 * y ^ 12 + (-131072) * y ^ 14 + 32768 * y ^ 16
    := by
  rw [show (16 : ℤ) = 14 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (14 : ℤ) + 1 = 15 from by norm_num,
    chebEval15, chebEval14]
  ring

private theorem chebEval17 (y : ℝ) : (Chebyshev.T ℝ (17 : ℤ)).eval y =
    17 * y + (-816) * y ^ 3 + 11424 * y ^ 5 + (-71808) * y ^ 7 + 239360 * y ^ 9 + (-452608) * y ^
      11 + 487424 * y ^ 13 + (-278528) * y ^ 15 + 65536 * y ^ 17
    := by
  rw [show (17 : ℤ) = 15 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (15 : ℤ) + 1 = 16 from by norm_num,
    chebEval16, chebEval15]
  ring

private theorem chebEval18 (y : ℝ) : (Chebyshev.T ℝ (18 : ℤ)).eval y =
    (-1) + 162 * y ^ 2 + (-4320) * y ^ 4 + 44352 * y ^ 6 + (-228096) * y ^ 8 + 658944 * y ^ 10 +
      (-1118208) * y ^ 12 + 1105920 * y ^ 14 + (-589824) * y ^ 16 + 131072 * y ^ 18
    := by
  rw [show (18 : ℤ) = 16 + 2 from by norm_num, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, show (16 : ℤ) + 1 = 17 from by norm_num,
    chebEval17, chebEval16]
  ring

/-- **Chebyshev certificate.** If `D * Q` on the interval parameterised by `x = (p + q*y)/s`,
`y ∈ [-1, 1]`, expands in the Chebyshev basis with coefficients `N`, then `|Q| ≤ B` there,
provided `∑ |N j| ≤ D * B`. All the cancellation lives in the coefficients: the only analytic
input is `|T j t| ≤ 1`. -/
private theorem abs_le_of_chebCert {p q s D B : ℝ} (hq : 0 < q) (hs : 0 < s) (hD : 0 < D)
    {n : ℕ} (Q : ℝ → ℝ) (N : ℕ → ℝ)
    (hQ : ∀ y : ℝ, D * Q ((p + q * y) / s)
      = ∑ j ∈ Finset.range (n + 1), N j * (Chebyshev.T ℝ (j : ℤ)).eval y)
    (hB : ∑ j ∈ Finset.range (n + 1), |N j| ≤ D * B)
    (x : ℝ) (hx0 : (p - q) / s ≤ x) (hx1 : x ≤ (p + q) / s) :
    |Q x| ≤ B := by
  rw [div_le_iff₀ hs] at hx0
  rw [le_div_iff₀ hs] at hx1
  have hy : |(s * x - p) / q| ≤ 1 := by
    rw [abs_div, abs_of_pos hq, div_le_one hq, abs_le]
    constructor <;> linarith
  have h1 := hQ ((s * x - p) / q)
  rw [show (p + q * ((s * x - p) / q)) / s = x from by field_simp; ring] at h1
  have h2 : |D * Q x| ≤ ∑ j ∈ Finset.range (n + 1), |N j| := by
    rw [h1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    calc |N j| * |(Chebyshev.T ℝ (j : ℤ)).eval ((s * x - p) / q)| ≤ |N j| * 1 :=
          mul_le_mul_of_nonneg_left (Chebyshev.abs_eval_T_real_le_one _ hy) (abs_nonneg _)
      _ = |N j| := mul_one _
  rw [abs_mul, abs_of_pos hD] at h2
  exact le_of_mul_le_mul_left (by linarith) hD

private theorem facctVal0 : (facctCoeffs[0]!).toNat = 19127174051 := by decide
private theorem facctVal1 : (facctCoeffs[1]!).toNat = 233346759686 := by decide
private theorem facctVal2 : (facctCoeffs[2]!).toNat = 2542029181962 := by decide
private theorem facctVal3 : (facctCoeffs[3]!).toNat = 25415798087749 := by decide
private theorem facctVal4 : (facctCoeffs[4]!).toNat = 228754078003076 := by decide
private theorem facctVal5 : (facctCoeffs[5]!).toNat = 1830034511206115 := by decide
private theorem facctVal6 : (facctCoeffs[6]!).toNat = 12810238987800554 := by decide
private theorem facctVal7 : (facctCoeffs[7]!).toNat = 76861433589428176 := by decide
private theorem facctVal8 : (facctCoeffs[8]!).toNat = 384307168197152512 := by decide
private theorem facctVal9 : (facctCoeffs[9]!).toNat = 1537228672812056320 := by decide
private theorem facctVal10 : (facctCoeffs[10]!).toNat = 4611686018427565056 := by decide
private theorem facctVal11 : (facctCoeffs[11]!).toNat = 9223372036854728704 := by decide
private theorem facctVal12 : (facctCoeffs[12]!).toNat = 9223372036854775808 := by decide

/-- The degree-18 Taylor truncation of `exp (-x)`. -/
private noncomputable def taylorExpNeg (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (-x) ^ i / (i.factorial : ℝ)

/-- The certification target, in units of `2 ^ (-63)`. -/
private noncomputable def certQ (x : ℝ) : ℝ :=
  hornerExact x 12 - 2 ^ 63 * taylorExpNeg 18 x

/-- `18! * certQ` has integer coefficients. -/
private theorem certQ_expand (x : ℝ) :
    (6402373705728000 : ℝ) * certQ x = 0 + 301577411034611712000 * x + 1134193306717126656000 * x
      ^ 2 + (-18739867347641696256000) * x ^ 3 + (-32842982000626237440000) * x ^ 4 +
      326702176168714253107200 * x ^ 5 + 305549933392096365772800 * x ^ 6 +
      (-2413115680306070554214400) * x ^ 7 + (-1208665697255858877235200) * x ^ 8 +
      8596251864142770040012800 * x ^ 9 + 2017429890733951881707520 * x ^ 10 +
      (-14609216358110315699896320) * x ^ 11 + (-821012305358570167664640) * x ^ 12 +
      9483102193412606294753280 * x ^ 13 + (-677364442386614735339520) * x ^ 14 +
      45157629492440982355968 * x ^ 15 + (-2822351843277561397248) * x ^ 16 +
      166020696663385964544 * x ^ 17 + (-9223372036854775808) * x ^ 18 := by
  unfold certQ taylorExpNeg
  simp only [hornerExact, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, facctVal0,
    facctVal1, facctVal2, facctVal3, facctVal4, facctVal5, facctVal6, facctVal7, facctVal8,
    facctVal9, facctVal10, facctVal11, facctVal12]
  norm_num [Nat.factorial]
  ring

/-- The same after clearing the denominator of an affine substitution `u = v / s`. -/
private theorem certQ_shift (s u v : ℝ) (hv : s * u = v) :
    ((6402373705728000 : ℝ) * s ^ 18) * certQ u = 0 * s ^ 18 + 301577411034611712000 * s ^ 17 * v
      + 1134193306717126656000 * s ^ 16 * v ^ 2 + (-18739867347641696256000) * s ^ 15 * v ^ 3 +
      (-32842982000626237440000) * s ^ 14 * v ^ 4 + 326702176168714253107200 * s ^ 13 * v ^ 5 +
      305549933392096365772800 * s ^ 12 * v ^ 6 + (-2413115680306070554214400) * s ^ 11 * v ^ 7 +
      (-1208665697255858877235200) * s ^ 10 * v ^ 8 + 8596251864142770040012800 * s ^ 9 * v ^ 9 +
      2017429890733951881707520 * s ^ 8 * v ^ 10 + (-14609216358110315699896320) * s ^ 7 * v ^ 11
      + (-821012305358570167664640) * s ^ 6 * v ^ 12 + 9483102193412606294753280 * s ^ 5 * v ^ 13
      + (-677364442386614735339520) * s ^ 4 * v ^ 14 + 45157629492440982355968 * s ^ 3 * v ^ 15 +
      (-2822351843277561397248) * s ^ 2 * v ^ 16 + 166020696663385964544 * s ^ 1 * v ^ 17 +
      (-9223372036854775808) * v ^ 18 := by
  subst hv
  rw [show ((6402373705728000 : ℝ) * s ^ 18) * certQ u = s ^ 18 * ((6402373705728000 : ℝ) * certQ
    u) from by ring, certQ_expand u]
  ring

private def certN0 : ℕ → ℤ
  | 0 => 11881511226875854183730651234993383627649187840
  | 1 => 11645475310696677515549319626459146108734013440
  | 2 => (-419008747506919410591667375759940143546368000)
  | 3 => (-180829873027354429998784145600280879169536000)
  | 4 => 2909414929571706713745068551077661759242240
  | 5 => 759499094382365726934447714249898595450880
  | 6 => (-8313529238396370481691713960732168028160)
  | 7 => (-1346451996606859545604784226645735112704)
  | 8 => 10703486790517088849614248869955108864
  | 9 => 1155152406970669618050048975372812288
  | 10 => (-6370672649408901769145347813146624)
  | 11 => (-475568451610850344956206537244672)
  | 12 => 1556967932400366019615559516160
  | 13 => 75296752412977559323583447040
  | 14 => (-84036456362858841838190592)
  | 15 => 87537882057808162062336
  | 16 => (-85486624439304978432)
  | 17 => 78531518502273024
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert0_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((1 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN0 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((1 + 1 * y) / 32) (1 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN0, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[0, 1/16]`: `|certQ| ≤ 3045` units. -/
private theorem cert0 (x : ℝ) (hx0 : (1 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (1 + 1 : ℝ) / 32) : |certQ x| ≤ 3045 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN0 j : ℤ) : ℝ)) cert0_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN0]
      norm_num) x hx0 hx1


private def certN1 : ℕ → ℤ
  | 0 => 1700748434629298810745915522971861477460361455997068247040
  | 1 => 118251869431958618463463654269483640883335365189917736960
  | 2 => (-6825876950197671879950587371734718260488273662050304000)
  | 3 => (-119442368869078886200064471486150863259203817963520000)
  | 4 => 2972780863955619780202495813609230585659221962915840
  | 5 => 32172346111492434413910335349295108515913499934720
  | 6 => (-483080659106792093806501856398272007191983554560)
  | 7 => (-3766202582381194857762731525963794039802167296)
  | 8 => 35524046326975736809553379483007515585675264
  | 9 => 221253093349551739440746123018898077908992
  | 10 => (-1213431436399241755331226962194537119744)
  | 11 => (-6447283015301775458117910316657410048)
  | 12 => 16211955065855955132112600993628160
  | 13 => 74148859166065036701476019240960
  | 14 => (-20688854610015888439794204672)
  | 15 => 5387716311960878510505984
  | 16 => (-1315442200672324288512)
  | 17 => 301459700057112576
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert1_id (y : ℝ) :
    (544653719624375948879864004646796773222775355604992000 : ℝ) * certQ ((9 + 1 * y) / 128)
      = ∑ j ∈ Finset.range 19, ((certN1 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (544653719624375948879864004646796773222775355604992000 : ℝ) = (6402373705728000 : ℝ) *
    (128 : ℝ) ^ 18 from by norm_num,
    certQ_shift (128 : ℝ) ((9 + 1 * y) / 128) (9 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN1, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[1/16, 5/64]`: `|certQ| ≤ 3353` units. -/
private theorem cert1 (x : ℝ) (hx0 : (9 - 1 : ℝ) / 128 ≤ x)
    (hx1 : x ≤ (9 + 1 : ℝ) / 128) : |certQ x| ≤ 3353 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN1 j : ℤ) : ℝ)) cert1_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN1]
      norm_num) x hx0 hx1

private def certN2 : ℕ → ℤ
  | 0 => 1878706678022572276615977992944228233860992552052132413440
  | 1 => 58764857524110200331622122478438416887860535060846346240
  | 2 => (-7954697402209131789084607282983858254420461498159595520)
  | 3 => (-67393689185139773959984960446060296221500834148515840)
  | 4 => 3492440521876629891296859600266857714366669651968000
  | 5 => 19448432544906522655176190693957122859604744601600
  | 6 => (-571492068213085095813999977462973125332303872000)
  | 7 => (-2511899617903226241224451317537600217802604544)
  | 8 => 42549306416715319667872421962765809355849728
  | 9 => 167284967679422003868741248926754919153664
  | 10 => (-1478636328392533075453625274409043361792)
  | 11 => (-5577052628531603699494986551924883456)
  | 12 => 20037729368074891453490112164265984
  | 13 => 72999287625947667605182841094144
  | 14 => (-20368104195746439114560372736)
  | 15 => 5304180307421328517890048
  | 16 => (-1295115203754187554816)
  | 17 => 296393150476320768
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert2_id (y : ℝ) :
    (544653719624375948879864004646796773222775355604992000 : ℝ) * certQ ((11 + 1 * y) / 128)
      = ∑ j ∈ Finset.range 19, ((certN2 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (544653719624375948879864004646796773222775355604992000 : ℝ) = (6402373705728000 : ℝ) *
    (128 : ℝ) ^ 18 from by norm_num,
    certQ_shift (128 : ℝ) ((11 + 1 * y) / 128) (11 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN2, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[5/64, 3/32]`: `|certQ| ≤ 3572` units. -/
private theorem cert2 (x : ℝ) (hx0 : (11 - 1 : ℝ) / 128 ≤ x)
    (hx1 : x ≤ (11 + 1 : ℝ) / 128) : |certQ x| ≤ 3572 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN2 j : ℤ) : ℝ)) cert2_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN2]
      norm_num) x hx0 hx1

private def certN3 : ℕ → ℤ
  | 0 => 1930724774539558806202939292645103333495234368245447262208
  | 1 => (-7133062260577217941785588450475167362754245058864611328)
  | 2 => (-8417783928054258503855679972650373926426524860184264704)
  | 3 => (-9169195317032702294387051498284416759623639208296448)
  | 4 => 3739371339103863595486401294600182949987750506397696
  | 5 => 5047627815984122890214495472877955938697984606208
  | 6 => (-621941900515916549531442484481547498968101945344)
  | 7 => (-1065843230756377227958897364335592502976315392)
  | 8 => 47450484967241599161586889036965232001417216
  | 9 => 103528287236204838462886815378117868126208
  | 10 => (-1701532084446032766795015053695984336896)
  | 11 => (-4524612279732221415809940260841848832)
  | 12 => 23804190534741211397695239603879936
  | 13 => 71867538495254639725021986029568
  | 14 => (-20052327134756043093908127744)
  | 15 => 5221934205872651473256448
  | 16 => (-1275132732207544664064)
  | 17 => 291326600895528960
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert3_id (y : ℝ) :
    (544653719624375948879864004646796773222775355604992000 : ℝ) * certQ ((13 + 1 * y) / 128)
      = ∑ j ∈ Finset.range 19, ((certN3 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (544653719624375948879864004646796773222775355604992000 : ℝ) = (6402373705728000 : ℝ) *
    (128 : ℝ) ^ 18 from by norm_num,
    certQ_shift (128 : ℝ) ((13 + 1 * y) / 128) (13 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN3, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[3/32, 7/64]`: `|certQ| ≤ 3574` units. -/
private theorem cert3 (x : ℝ) (hx0 : (13 - 1 : ℝ) / 128 ≤ x)
    (hx1 : x ≤ (13 + 1 : ℝ) / 128) : |certQ x| ≤ 3574 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN3 j : ℤ) : ℝ)) cert3_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN3]
      norm_num) x hx0 hx1

private def certN4 : ℕ → ℤ
  | 0 => 1849487624338585222869350976128187089742298640989584097280
  | 1 => (-73895980453021887170703895034541439128272921926167429120)
  | 2 => (-8168150478317719201021443514291381875215300663068065792)
  | 3 => 50650333850450815903095979838859043284002706183684096
  | 4 => 3689540134814397734050960558572153510710971006451712
  | 5 => (-10062555302279869983873690692978845156929485930496)
  | 6 => (-630063205092344254760656124752575792883357974528)
  | 7 => 498700020481515426116137974762086100186955776
  | 8 => 49907581133235134321221445633744216216567808
  | 9 => 31834927540627819941391124221641401303040
  | 10 => (-1874163775037220333615373460517389598720)
  | 11 => (-3292786872727743319728185378246492160)
  | 12 => 27512258127420219640010170209140736
  | 13 => 70753335420869511804374558441472
  | 14 => (-19741446694353961269136982016)
  | 15 => 5140955957691071770656768
  | 16 => (-1255494786032395616256)
  | 17 => 286260051314737152
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert4_id (y : ℝ) :
    (544653719624375948879864004646796773222775355604992000 : ℝ) * certQ ((15 + 1 * y) / 128)
      = ∑ j ∈ Finset.range 19, ((certN4 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (544653719624375948879864004646796773222775355604992000 : ℝ) = (6402373705728000 : ℝ) *
    (128 : ℝ) ^ 18 from by norm_num,
    certQ_shift (128 : ℝ) ((15 + 1 * y) / 128) (15 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN4, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[7/64, 1/8]`: `|certQ| ≤ 3547` units. -/
private theorem cert4 (x : ℝ) (hx0 : (15 - 1 : ℝ) / 128 ≤ x)
    (hx1 : x ≤ (15 + 1 : ℝ) / 128) : |certQ x| ≤ 3547 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN4 j : ℤ) : ℝ)) cert4_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN4]
      norm_num) x hx0 hx1

private def certN5 : ℕ → ℤ
  | 0 => 15262100256548378243831099365288193872814407680
  | 1 => (-11656132631138071276520867407103963888175022080)
  | 2 => (-1046210463854208710887710923584297348620091392)
  | 3 => 160849946864107048138832986812412291379625984
  | 4 => 8393612220322916039628541686018886820954112
  | 5 => (-649263108885875406254235719188360571387904)
  | 6 => (-26915136383469860625640380334083070230528)
  | 7 => 1037046083648844110206839736066432303104
  | 8 => 41614786425789867827584198902187819008
  | 9 => (-637208178838541301017991241678192640)
  | 10 => (-30947351942264765018331985288888320)
  | 11 => 34589212839914936263632287170560
  | 12 => 8918182336796350397643736743936
  | 13 => 66449149210795307524882956288
  | 14 => (-74161978859835173860540416)
  | 15 => 77249722835154273042432
  | 16 => (-75495388665983533056)
  | 17 => 68398419340689408
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert5_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((5 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN5 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((5 + 1 * y) / 32) (5 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN5, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[1/8, 3/16]`: `|certQ| ≤ 3550` units. -/
private theorem cert5 (x : ℝ) (hx0 : (5 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (5 + 1 : ℝ) / 32) : |certQ x| ≤ 3550 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN5 j : ℤ) : ℝ)) cert5_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN5]
      norm_num) x hx0 hx1

private def certN6 : ℕ → ℤ
  | 0 => (-9454431640590317328629954898972071616369917952)
  | 1 => (-11178047505369242280247284150846433644911788032)
  | 2 => 1180306514612763448286771186401191478979198976
  | 3 => 168394515827520696208219287951445724032401408
  | 4 => (-8041956636011081756465907318456152462721024)
  | 5 => (-825817449115400571657296097382304996917248)
  | 6 => 15670117813112946536594992352510645108736
  | 7 => 1773791109215954598097920201430979837952
  | 8 => (-2003127750900897996540791333389860864)
  | 9 => (-1706507553112313455099145076393115648)
  | 10 => (-18807048474672957388729945870565376)
  | 11 => 543885566699197446040993337966592
  | 12 => 12267777391756297565539198304256
  | 13 => 62423188668305112838220808192
  | 14 => (-69669020733980996077092864)
  | 15 => 72563172917171151962112
  | 16 => (-71016558836563574784)
  | 17 => 63331869759897600
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert6_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((7 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN6 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((7 + 1 * y) / 32) (7 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN6, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[3/16, 1/4]`: `|certQ| ≤ 2775` units. -/
private theorem cert6 (x : ℝ) (hx0 : (7 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (7 + 1 : ℝ) / 32) : |certQ x| ≤ 2775 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN6 j : ℤ) : ℝ)) cert6_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN6]
      norm_num) x hx0 hx1

private def certN7 : ℕ → ℤ
  | 0 => (-18207745031304472857778231769434510040246517760)
  | 1 => 3118096791167953267493111750194298259410780160
  | 2 => 1994320424237846666563192305132182052934778880
  | 3 => (-55985012650389767535982142944758833778524160)
  | 4 => (-17067432046018053717821913414622607572992000)
  | 5 => 78417077822746801216795366801094895206400
  | 6 => 54492223885225744534232180673025671168000
  | 7 => 639203898802484507756250030250125164544
  | 8 => (-69548762380919491453182222710480044032)
  | 9 => (-1795427665177418001533357272778932224)
  | 10 => 19206715222780816928480038767034368
  | 11 => 1209041371891445290369331962576896
  | 12 => 15414429562156512410332481716224
  | 13 => 58641118077287885083735228416
  | 14 => (-65448877090696446791909376)
  | 15 => 68152243296383105236992
  | 16 => (-66882254378637459456)
  | 17 => 58265320179105792
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert7_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((9 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN7 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((9 + 1 * y) / 32) (9 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN7, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[1/4, 5/16]`: `|certQ| ≤ 2952` units. -/
private theorem cert7 (x : ℝ) (hx0 : (9 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (9 + 1 : ℝ) / 32) : |certQ x| ≤ 2952 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN7 j : ℤ) : ℝ)) cert7_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN7]
      norm_num) x hx0 hx1

private def certN8 : ℕ → ℤ
  | 0 => (-1045960243441298956639980913428016993256079360)
  | 1 => 12333287179602325623022221215317014016677642240
  | 2 => (-29830284411248630433949504602901807575859200)
  | 3 => (-244589429894079346796130061764598728700723200)
  | 4 => (-2496079661827340447804589401114149870632960)
  | 5 => 1297916262296470741984530177852898258452480
  | 6 => 33241004939289372682958095636276854128640
  | 7 => (-2354716926264124142405329854527547899904)
  | 8 => (-105472616557291183415795268465538891776)
  | 9 => 265303664350236178822234538191618048
  | 10 => 89741854379318977512906450844778496
  | 11 => 2020613469452994185331216784293888
  | 12 => 18370431788431199967827743211520
  | 13 => 55088110498980074675503104000
  | 14 => (-61485672200863089722130432)
  | 15 => 63994884349014526918656
  | 16 => (-63092475292205187072)
  | 17 => 53198770598313984
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert8_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((11 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN8 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((11 + 1 * y) / 32) (11 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN8, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[5/16, 3/8]`: `|certQ| ≤ 1724` units. -/
private theorem cert8 (x : ℝ) (hx0 : (11 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (11 + 1 : ℝ) / 32) : |certQ x| ≤ 1724 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN8 j : ℤ) : ℝ)) cert8_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN8]
      norm_num) x hx0 hx1

private def certN9 : ℕ → ℤ
  | 0 => 15002499575334500623863000135567112598735290368
  | 1 => 1791946021831128863651808400234266084671225856
  | 2 => (-2284455591620307102182323136302484305458757632)
  | 3 => (-62400100400592219169948126081017280003571712)
  | 4 => 24270898154722705256166329803212344292016128
  | 5 => 961319795686163262775402521480146618155008
  | 6 => (-72482232404446518485800805790055076462592)
  | 7 => (-4694368467071175705446994618700095553536)
  | 8 => (-7443465858180710203646446590750621696)
  | 9 => 5902736203960543677436852494185529344
  | 10 => 199043498453041513609121560321327104
  | 11 => 2969730620497655794241028042522624
  | 12 => 21147328481852435366407405830144
  | 13 => 51750190992080821441448116224
  | 14 => (-57764853312789024941801472)
  | 15 => 60069046451289811058688
  | 16 => (-59647221577266757632)
  | 17 => 48132221017522176
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert9_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((13 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN9 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((13 + 1 * y) / 32) (13 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN9, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[3/8, 7/16]`: `|certQ| ≤ 2419` units. -/
private theorem cert9 (x : ℝ) (hx0 : (13 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (13 + 1 : ℝ) / 32) : |certQ x| ≤ 2419 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN9 j : ℤ) : ℝ)) cert9_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN9]
      norm_num) x hx0 hx1

private def certN10 : ℕ → ℤ
  | 0 => 3045733579594837278268226378113414953256878080
  | 1 => (-12243384382584582092794644681933248622420295680)
  | 2 => (-491544835859818814470979366495277239859412992)
  | 3 => 343160285361851283456305258753746535725400064
  | 4 => 16370277612072047842423607416041933291651072
  | 5 => (-2124526626983183291682282520389228045533184)
  | 6 => (-162788361116429489571363964509543274119168)
  | 7 => 277890585663068470259669877987773251584
  | 8 => 382647594599966545673678423031659102208
  | 9 => 16786078749960990465092713947133378560
  | 10 => 352978380464228075012473955108782080
  | 11 => 4048058609215600064000188754165760
  | 12 => 23755957902143090639616539099136
  | 13 => 48614162526016068587354062848
  | 14 => (-54273190652208888881872896)
  | 15 => 56352679979433351708672
  | 16 => (-56546493233822171136)
  | 17 => 43065671436730368
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert10_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((15 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN10 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((15 + 1 * y) / 32) (15 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN10, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[7/16, 1/2]`: `|certQ| ≤ 2037` units. -/
private theorem cert10 (x : ℝ) (hx0 : (15 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (15 + 1 : ℝ) / 32) : |certQ x| ≤ 2037 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN10 j : ℤ) : ℝ)) cert10_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN10]
      norm_num) x hx0 hx1

private def certN11 : ℕ → ℤ
  | 0 => (-12103166892192084643578594805739842024853471232)
  | 1 => 282466456646815188063202443943614936061575168
  | 2 => 3192944074146786150323347040366142777307693056
  | 3 => 88601708285278405529860345136667110531923968
  | 4 => (-54655131642098908903781435026347254007988224)
  | 5 => (-3889622747867215707142408919507128201248768)
  | 6 => 128811045081408824206622785466805660942336
  | 7 => 25285233732921777184877042015630222426112
  | 8 => 1287138034525509438333164610097571168256
  | 9 => 34812026014140110732017686316582961152
  | 10 => 557057734251414012544543775873040384
  | 11 => 5247767287537411662683534725742592
  | 12 => 26206490682579495464875931467776
  | 13 => 45667531894202676660878180352
  | 14 => (-50998777422283854330200064)
  | 15 => 52823735309669542920192
  | 16 => (-53790290261871427584)
  | 17 => 37999121855938560
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert11_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((17 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN11 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((17 + 1 * y) / 32) (17 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN11, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[1/2, 9/16]`: `|certQ| ≤ 1985` units. -/
private theorem cert11 (x : ℝ) (hx0 : (17 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (17 + 1 : ℝ) / 32) : |certQ x| ≤ 1985 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN11 j : ℤ) : ℝ)) cert11_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN11]
      norm_num) x hx0 hx1

private def certN12 : ℕ → ℤ
  | 0 => 4632107008890280112739765702835306033619927040
  | 1 => 11983368104314706376779523458567035199799951360
  | 2 => (-2118901726655684750906263754624972926715166720)
  | 3 => (-899368153988960262254714150623830641643356160)
  | 4 => (-14620875930007981831060197997465376391168000)
  | 5 => 13675308777180567053904795096411458135654400
  | 6 => 1635224845738093636017903181883403927552000
  | 7 => 91300010998199471751611538875159930732544
  | 8 => 3000532682191409915736168851340219383808
  | 9 => 62090972931530658814741417894080413696
  | 10 => 816458781015257187598402664401993728
  | 11 => 6561499376542827746811000668553216
  | 12 => 28508464502583831828323855499264
  | 13 => 42898435627312537515564466176
  | 14 => (-47931029803601630431543296)
  | 15 => 49460162818222778744832
  | 16 => (-51378612661414526976)
  | 17 => 32932572275146752
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert12_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((19 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN12 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((19 + 1 * y) / 32) (19 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN12, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[9/16, 5/8]`: `|certQ| ≤ 2481` units. -/
private theorem cert12 (x : ℝ) (hx0 : (19 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (19 + 1 : ℝ) / 32) : |certQ x| ≤ 2481 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN12 j : ℤ) : ℝ)) cert12_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN12]
      norm_num) x hx0 hx1

private def certN13 : ℕ → ℤ
  | 0 => 252741753700702399744346223430539295525437440
  | 1 => (-12267247671118031937620047540154813840841768960)
  | 2 => 4525179346167494785719141780109255216044441600
  | 3 => 4280236175486057033331834230984777911605657600
  | 4 => 924113216654280964030111301944742980186275840
  | 5 => 96752610589185576906117337084099865692078080
  | 6 => 5920228647597078501285141960174350043709440
  | 7 => 229973657319058241322690838600559043280896
  | 8 => 5896961377095478628351674528979258179584
  | 9 => 100934061451291181503498557483235934208
  | 10 => 1136044878378710688285824233626402816
  | 11 => 7982340839693664286758799669198848
  | 12 => 30670814907806262615786525818880
  | 13 => 40295565906536688274857000960
  | 14 => (-45060686954176462687567872)
  | 15 => 46239912881317453234176
  | 16 => (-49311460432451469312)
  | 17 => 27866022694354944
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert13_id (y : ℝ) :
    (7925754756788606011539581299392692355072000 : ℝ) * certQ ((21 + 1 * y) / 32)
      = ∑ j ∈ Finset.range 19, ((certN13 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (7925754756788606011539581299392692355072000 : ℝ) = (6402373705728000 : ℝ) * (32 : ℝ) ^
    18 from by norm_num,
    certQ_shift (32 : ℝ) ((21 + 1 * y) / 32) (21 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN13, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[5/8, 11/16]`: `|certQ| ≤ 2821` units. -/
private theorem cert13 (x : ℝ) (hx0 : (21 - 1 : ℝ) / 32 ≤ x)
    (hx1 : x ≤ (21 + 1 : ℝ) / 32) : |certQ x| ≤ 2821 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN13 j : ℤ) : ℝ)) cert13_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN13]
      norm_num) x hx0 hx1

private def certN14 : ℕ → ℤ
  | 0 => 151501501959600363906838155402906506504109681824827466351378432
  | 1 => 209061276227279498532763600957325983980442139529966259500220416
  | 2 => 18880356012683973310170970215914022688152046784324527680651264
  | 3 => 640153452129703192895877181648834131465807771378775285039104
  | 4 => 11033409694886815381167252955197052488133535156162078441472
  | 5 => 111556759032503150840635409405376205899294103667252133888
  | 6 => 715988568592391484889009340784417607185836564935606272
  | 7 => 3049641717538891727225674270294618614565553420894208
  | 8 => 8806899334315740451312117033969994675795187990528
  | 9 => 17273893388722478689140489979481770573235748864
  | 10 => 22542051666584214698488570672723424817709056
  | 11 => 18508792787330134113623988631086840152064
  | 12 => 8343922952139465168430794819489497088
  | 13 => 1274667408748962640911456459030528
  | 14 => (-178295089582090680680514060288)
  | 15 => 22775198988261511133134848
  | 16 => (-3091125965351590821888)
  | 17 => 200128708441276416
  | 18 => (-70368744177664)
  | _ => 0

private theorem cert14_id (y : ℝ) :
    (142777704677212408743163069634129893319711222819715022848000 : ℝ) * certQ ((177 + 1 * y) / 256)
      = ∑ j ∈ Finset.range 19, ((certN14 j : ℤ) : ℝ) * (Chebyshev.T ℝ (j : ℤ)).eval y := by
  rw [show (142777704677212408743163069634129893319711222819715022848000 : ℝ) = (6402373705728000
    : ℝ) * (256 : ℝ) ^ 18 from by norm_num,
    certQ_shift (256 : ℝ) ((177 + 1 * y) / 256) (177 + 1 * y) (by ring)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN14, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, chebEval0, chebEval1, chebEval2, chebEval3, chebEval4, chebEval5, chebEval6,
    chebEval7, chebEval8, chebEval9, chebEval10, chebEval11, chebEval12, chebEval13, chebEval14,
    chebEval15, chebEval16, chebEval17, chebEval18]
  push_cast
  ring

/-- Certificate for `[11/16, 89/128]`: `|certQ| ≤ 2663` units. -/
private theorem cert14 (x : ℝ) (hx0 : (177 - 1 : ℝ) / 256 ≤ x)
    (hx1 : x ≤ (177 + 1 : ℝ) / 256) : |certQ x| ≤ 2663 :=
  abs_le_of_chebCert (by norm_num) (by norm_num) (by norm_num) certQ
    (fun j => ((certN14 j : ℤ) : ℝ)) cert14_id (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, certN14]
      norm_num) x hx0 hx1

/-- The fifteen certificates cover `[0, 89 / 128]`, which contains `[0, log 2)`. -/
private theorem abs_certQ_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 89 / 128) :
    |certQ t| ≤ 3574 := by
  rcases le_or_gt t (1 / 16 : ℝ) with h | h
  · exact le_trans (cert0 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (5 / 64 : ℝ) with h | h
  · exact le_trans (cert1 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (3 / 32 : ℝ) with h | h
  · exact le_trans (cert2 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (7 / 64 : ℝ) with h | h
  · exact le_trans (cert3 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (1 / 8 : ℝ) with h | h
  · exact le_trans (cert4 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (3 / 16 : ℝ) with h | h
  · exact le_trans (cert5 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (1 / 4 : ℝ) with h | h
  · exact le_trans (cert6 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (5 / 16 : ℝ) with h | h
  · exact le_trans (cert7 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (3 / 8 : ℝ) with h | h
  · exact le_trans (cert8 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (7 / 16 : ℝ) with h | h
  · exact le_trans (cert9 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (1 / 2 : ℝ) with h | h
  · exact le_trans (cert10 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (9 / 16 : ℝ) with h | h
  · exact le_trans (cert11 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (5 / 8 : ℝ) with h | h
  · exact le_trans (cert12 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  rcases le_or_gt t (11 / 16 : ℝ) with h | h
  · exact le_trans (cert13 t (by norm_num; linarith) (by norm_num; linarith))
      (by norm_num)
  exact le_trans (cert14 t (by norm_num; linarith) (by norm_num; linarith))
    (by norm_num)


/-! ## Assembly

The three error sources add in units of `2 ^ (-63)`: the fixed-point pipeline contributes `10`,
the certificates `3574`, and the Taylor truncation `80`. Their sum `3664` is under the `4096`
units that `2 ^ (-51)` allows. -/

/-- The degree-18 truncation against `Real.exp`, from `Real.exp_bound` at `n = 19`. -/
private theorem abs_taylorExpNeg_sub_exp_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |taylorExpNeg 18 t - Real.exp (-t)| ≤ 20 / 2311256907767808000 := by
  have hx : |(-t)| ≤ 1 := by rw [abs_neg, abs_of_nonneg ht0]; exact ht1
  have h := Real.exp_bound hx (n := 19) (by norm_num)
  have hp : |(-t)| ^ 19 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have heq : taylorExpNeg 18 t = ∑ m ∈ Finset.range 19, (-t) ^ m / (m.factorial : ℝ) := by
    unfold taylorExpNeg
    norm_num
  rw [heq, abs_sub_comm]
  refine le_trans h ?_
  have hc : ((Nat.succ 19 : ℕ) : ℝ) / (((Nat.factorial 19 : ℕ) : ℝ) * ((19 : ℕ) : ℝ))
      = 20 / 2311256907767808000 := by norm_num [Nat.factorial]
  rw [hc]
  nlinarith [abs_nonneg (-t)]

/-- Absolute approximation bound for the FACCT-based `expm_p63` routine, on the domain the
routine is written for: `x` in `[0, 0.694]` and `ccs` in `[0, 1)`.

The routine is documented for `x` in `[0, log 2)`, and `0.694` is the smallest constant above
`log 2` that the proof already carries — it is the contraction factor of the Horner error
induction (`scaledArg_le_694`), and the Chebyshev certificates run to `89/128 = 0.6953125`.
Stating the hypothesis at `0.694` rather than `log 2` is what lets a caller feed a *computed*
reduction. A caller that reduces modulo `log 2` by rounding a floating-point quotient obtains a
remainder that can sit a few ulps above `log 2` when the argument is near a multiple of it, so no
statement closed at `log 2` would apply to one.

Both sides of the `ccs` restriction are load-bearing. `expm_p63` reads its operands through a
fixed-point conversion that keeps `⌊2 ^ 63 * ccs⌋` in 63 bits and drops the sign bit, so the scale
factor must be a nonnegative fraction below one. At `ccs = 1` the conversion wraps to `0`, and with
it the whole product, for every `x` in range — against a true value of `Real.exp (-(toReal x))`,
never below one half. Above `1` the claim fails outright: the returned `UInt64` read at scale
`2 ^ 63` is smaller than `2`, while `toReal ccs * Real.exp (-(toReal x))` grows without bound.

The `2 ^ (-51)` is very nearly saturated, and by the approximation rather than the arithmetic
around it. Measured in units of `2 ^ (-63)`, against a budget of `4096`: the fixed-point pipeline
costs `10` (`expm_p63_sub_trueArg_le`), the Chebyshev certificates covering `[0, 89/128]` cost
`3574` (`abs_certQ_le`), and the degree-`19` Taylor truncation of `Real.exp` costs `80`. That
`3574` is where the difficulty lies: `FPR.facctCoeffs` is a minimax fit rather than a Taylor
truncation, so `P - T` carries `O(1)` coefficients while being `O(2 ^ (-51))`, and any bound
applying a triangle inequality to those coefficients discards exactly the cancellation the fit
relies on. Subdividing restores locality, which is why the bound is a family of per-interval
certificates rather than a single estimate. -/
theorem expm_p63_error (x ccs : FPR)
    (hx : 0 ≤ toReal x) (hx' : toReal x ≤ 694 / 1000)
    (hccs : 0 ≤ toReal ccs) (hccs' : toReal ccs < 1) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-(toReal x)))) ≤
    (2 : ℝ) ^ (-(51 : ℤ)) := by
  have ht89 : toReal x ≤ 89 / 128 := by linarith
  have ht1 : toReal x ≤ 1 := by linarith
  have hmain := expm_p63_sub_trueArg_le x ccs hx hx' hccs hccs'
  have hQ := abs_certQ_le (toReal x) hx ht89
  have hT := abs_taylorExpNeg_sub_exp_le (toReal x) hx ht1
  have hc : |toReal ccs| ≤ 1 := by rw [abs_of_nonneg hccs]; linarith
  have hdef : hornerExact (toReal x) 12
      = certQ (toReal x) + 2 ^ 63 * taylorExpNeg 18 (toReal x) := by
    unfold certQ; ring
  have hB : |certQ (toReal x)
      + 2 ^ 63 * (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))| ≤ 3654 := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 63)]
    nlinarith [abs_nonneg (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))]
  have key : |((expm_p63 x ccs).toNat : ℝ)
      - toReal ccs * ((2 : ℝ) ^ 63 * Real.exp (-(toReal x)))| ≤ 3664 := by
    have e1 : ((expm_p63 x ccs).toNat : ℝ)
        - toReal ccs * ((2 : ℝ) ^ 63 * Real.exp (-(toReal x)))
        = (((expm_p63 x ccs).toNat : ℝ) - toReal ccs * hornerExact (toReal x) 12)
          + toReal ccs * (certQ (toReal x)
            + 2 ^ 63 * (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))) := by
      rw [hdef]; ring
    rw [e1]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    nlinarith [abs_nonneg (certQ (toReal x)
      + 2 ^ 63 * (taylorExpNeg 18 (toReal x) - Real.exp (-(toReal x)))), abs_nonneg (toReal ccs)]
  have hscale : (((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63
      - toReal ccs * Real.exp (-(toReal x))
      = (((expm_p63 x ccs).toNat : ℝ)
        - toReal ccs * ((2 : ℝ) ^ 63 * Real.exp (-(toReal x)))) / (2 : ℝ) ^ 63 := by
    field_simp
  rw [hscale, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 63),
    div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 63)]
  refine le_trans key ?_
  norm_num

/-- The bit pattern of the binary64 value `0.5`. -/
private def half : FPR := (0x3FE0000000000000 : UInt64)

private theorem decode_half : FPR.decode half = ⟨false, 1022, 0⟩ := by
  unfold FPR.decode half; decide

private theorem toReal_half : toReal half = 0.5 := by
  unfold toReal toRealBits
  rw [decode_half]
  norm_num [FPR.Bits.toReal]

/-- `expm_p63_error` is not vacuous: `x = 0`, `ccs = 0.5` meets all four side conditions. Note
`FPR.zero` is *not* a normal operand, so the bound genuinely covers the zero-exponent case. -/
example : 0 ≤ toReal FPR.zero ∧ toReal FPR.zero ≤ 694 / 1000 ∧
    0 ≤ toReal half ∧ toReal half < 1 := by
  refine ⟨by rw [toReal_zero], by rw [toReal_zero]; norm_num,
    by rw [toReal_half]; norm_num, by rw [toReal_half]; norm_num⟩

/-! ## Sign-blindness

`expm_p63` reaches its argument only through `mtwop63`, which reads the significand and the
exponent field and never the sign bit. The routine therefore computes `exp (-|x|)`, not
`exp (-x)`, and the two agree only on the nonnegative domain `expm_p63_error` is stated for.
That is what makes the sign of the reduced argument a correctness question for the caller
rather than a matter of taste: a caller reducing modulo `log 2` must round its quotient toward
negative infinity, since rounding to nearest leaves the remainder below zero for roughly half of
all arguments, where this routine reads it as `exp (|r|)`. -/

/-- `mtwop63` discards the sign bit: the shift by `10` carries it out of the word, and the
exponent mask keeps only bits `52` through `62`. -/
private theorem mtwop63_neg (x : FPR) : mtwop63 (FPR.neg x) = mtwop63 x := by
  have hm : ((((FPR.neg x) <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63)
      = (((x <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63) := by
    rw [← UInt64.toNat_inj, toNat_m_of, toNat_m_of, decode_neg_mantissa]
  have he : (((FPR.neg x) >>> 52).toUInt32 &&& (0x7FF : UInt32))
      = ((x >>> 52).toUInt32 &&& (0x7FF : UInt32)) := by
    rw [← UInt32.toNat_inj, toNat_ex_field_of, toNat_ex_field_of, decode_neg_exponent]
  simp only [mtwop63]
  rw [hm, he]

/-- `expm_p63` is invariant under negating its argument. -/
theorem expm_p63_neg (x ccs : FPR) : FPR.expm_p63 (FPR.neg x) ccs = FPR.expm_p63 x ccs := by
  simp only [FPR.expm_p63, mtwop63_neg]

/-- `expm_p63_error` on the whole symmetric domain: the routine approximates `exp (-|x|)`.

This is the form a caller wants when the argument is *computed* rather than assumed nonnegative,
since it separates the approximation question from the sign question. Note that it is not an
extension of `expm_p63_error` to negative arguments in the naive sense — on `toReal x < 0` the
value approximated is `Real.exp (-|toReal x|)`, which is `Real.exp (toReal x)`, the reciprocal of
what an unwary reader of `expm_p63` might expect. -/
theorem expm_p63_error_abs (x ccs : FPR)
    (hx : |toReal x| ≤ 694 / 1000)
    (hccs : 0 ≤ toReal ccs) (hccs' : toReal ccs < 1) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-|toReal x|))) ≤ (2 : ℝ) ^ (-(51 : ℤ)) := by
  rcases le_or_gt 0 (toReal x) with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    exact expm_p63_error x ccs h hx hccs hccs'
  · have hneg : toReal (FPR.neg x) = -toReal x := toReal_neg x
    have h0 : 0 ≤ toReal (FPR.neg x) := by rw [hneg]; linarith
    have habs : |toReal x| = toReal (FPR.neg x) := by
      rw [hneg, abs_of_neg h]
    rw [habs, ← expm_p63_neg x ccs]
    exact expm_p63_error _ ccs h0 (by rw [← habs]; exact hx) hccs hccs'

end Falcon.Concrete.FPRBridge
