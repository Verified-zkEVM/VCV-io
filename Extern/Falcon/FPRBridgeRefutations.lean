/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
import all LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Concrete.FPR
import all Extern.Falcon.FPRBridge
public import Extern.Falcon.FPRBridge
import all Extern.Falcon.ExpmBridge
public import Extern.Falcon.ExpmBridge

/-!
# Why the FPR error bounds carry domain hypotheses

`Extern/Falcon/FPRBridge.lean` states each per-operation error bound on operands in
`FPR.IsNormalOrZero` whose exact result lies in `FPR.InNormalMagnitudeRange`, and
`Extern/Falcon/ExpmBridge.lean` states `expm_p63_error` for `ccs` in `[0, 1)`. This file is the
evidence that those hypotheses are necessary rather than defensive: it refutes each bound read
without them, at an explicit `UInt64` input, in the kernel.

Each refutation has the same shape, and none of them needs a numeric estimate. Dropping the
restriction lets the routine return a value at or below zero while the exact result is strictly
positive, and `not_error_of_sign_flip` turns that into a violated relative-error bound directly:
the absolute error is then at least the whole exact value, which no `ε < 1` multiple of it can
cover. The three ways it happens here are all real behaviours of the kernels:

* **Overflow past the finite range.** `FPR.add` reaches the non-finite exponent, which this
  denotation sends to `0`; `FPR.mul` wraps straight past it into a small *negative* value.
* **Underflow into the subnormal band.** Two ordinary normals whose exact difference is
  subnormal are mis-rounded by `FPR.add`'s alignment step into a large negative value — which is
  why the hypothesis restricts the *exact result* and not only the operands.
* **Subnormal operands discarded.** `FPR.div`'s flush guard fires on a zero exponent field, so a
  subnormal numerator is dropped and the quotient returns `+0`.

`expm_p63` fails differently again: its `ccs` is read through a 63-bit fixed-point conversion
that wraps at `1`.

The two closure statements at the end are why the operand domain is `FPR.IsNormalOrZero` rather
than `FPR.IsNormal`.

Nothing here is imported by the bounds themselves — this module is downstream of them, so it
cannot weaken anything it refutes.
-/

set_option maxRecDepth 40000

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## The shared argument

A returned value at or below zero cannot be within any relative epsilon below one of a positive
exact result: the absolute error is at least the exact result itself. -/

/-- A nonpositive computed value violates every relative-error bound with `ε < 1` against a
positive exact value. -/
private theorem not_error_of_sign_flip {computed exact : ℝ} (hx : 0 < exact)
    (hc : computed ≤ 0) : ¬ (|computed - exact| ≤ (2 : ℝ) ^ (-(52 : ℤ)) * |exact|) := by
  intro h
  rw [abs_of_pos hx, abs_of_nonpos (by linarith : computed - exact ≤ 0)] at h
  have heps : (2 : ℝ) ^ (-(52 : ℤ)) < 1 := by
    rw [show (2 : ℝ) ^ (-(52 : ℤ)) = ((2 : ℝ) ^ (52 : ℕ))⁻¹ from by rw [zpow_neg]; norm_num]
    rw [inv_lt_one_iff₀]
    right
    norm_num
  nlinarith

/-! ## The operands

Three bit patterns drive every counterexample: the largest finite magnitude, the smallest normal
magnitude, and its next representable neighbour. -/

/-- The largest finite binary64 magnitude, `(2 - 2 ^ (-52)) * 2 ^ 1023`. -/
private def maxFinite : FPR := (0x7FEFFFFFFFFFFFFF : UInt64)

/-- The smallest positive *normal* binary64 magnitude, `2 ^ (-1022)`. -/
private def minNormal : FPR := (0x0010000000000000 : UInt64)

/-- The representable neighbour just above `minNormal`; their exact difference is subnormal. -/
private def minNormalSucc : FPR := (0x0010000000000001 : UInt64)

private theorem toReal_maxFinite : toReal maxFinite = FPR.maxFiniteReal := by
  unfold toReal toRealBits FPR.maxFiniteReal
  rw [show FPR.decode maxFinite = ⟨false, 2046, 2 ^ 52 - 1⟩ from by
    unfold FPR.decode maxFinite; decide]
  unfold FPR.Bits.toReal
  norm_num

private theorem toReal_minNormal : toReal minNormal = (2 : ℝ) ^ (-(1022 : ℤ)) := by
  unfold toReal toRealBits
  rw [show FPR.decode minNormal = ⟨false, 1, 0⟩ from by unfold FPR.decode minNormal; decide]
  unfold FPR.Bits.toReal
  norm_num

-- Binary64's own exponent range reaches `2 ^ (-1074)` at the subnormal scale, well past
-- the default evaluation threshold of `256`. Raised here so the numeric tactics evaluate
-- the format's constants instead of declining to; it is not a suppressed diagnostic.
set_option exponentiation.threshold 1100 in
private theorem toReal_minNormalSucc :
    toReal minNormalSucc = (2 : ℝ) ^ (-(1022 : ℤ)) + (2 : ℝ) ^ (-(1074 : ℤ)) := by
  unfold toReal toRealBits
  rw [show FPR.decode minNormalSucc = ⟨false, 1, 1⟩ from by
    unfold FPR.decode minNormalSucc; decide]
  unfold FPR.Bits.toReal
  rw [show (-(1074 : ℤ)) = (-(1022 : ℤ)) + (-(52 : ℤ)) from by norm_num,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

private theorem maxFiniteReal_pos : 0 < FPR.maxFiniteReal := by
  unfold FPR.maxFiniteReal
  have h : (2 : ℝ) ^ (-(52 : ℤ)) < 1 := by
    rw [show (2 : ℝ) ^ (-(52 : ℤ)) = ((2 : ℝ) ^ (52 : ℕ))⁻¹ from by rw [zpow_neg]; norm_num]
    rw [inv_lt_one_iff₀]; right; norm_num
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1023 : ℤ) := zpow_pos (by norm_num) _
  exact mul_pos (by linarith) h2

/-! ## Overflow refutes the four arithmetic bounds

At the top of the finite range every one of `add`, `mul` and `div` returns a value whose sign is
unrelated to the exact result — `add` reaches the non-finite exponent, which this denotation sends
to `0`, and `mul` and `div` wrap straight past it into small *negative* finite values. -/

/-- `add_error` is false without its hypotheses: two largest-finite normals overflow the exponent
field, and the non-finite encoding they land on denotes `0`. -/
theorem not_add_error_unrestricted :
    ¬ ∀ (a b : FPR), |toReal (FPR.add a b) - (toReal a + toReal b)| ≤
      (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a + toReal b| := by
  intro h
  refine not_error_of_sign_flip (computed := toReal (FPR.add maxFinite maxFinite))
    (exact := toReal maxFinite + toReal maxFinite) ?_ ?_ (h maxFinite maxFinite)
  · rw [toReal_maxFinite]; linarith [maxFiniteReal_pos]
  · rw [show FPR.add maxFinite maxFinite = (0x7FFFFFFFFFFFFFFF : UInt64) from by decide]
    unfold toReal toRealBits
    rw [show FPR.decode (0x7FFFFFFFFFFFFFFF : UInt64) = ⟨false, 2047, 2 ^ 52 - 1⟩ from by
      unfold FPR.decode; decide]
    unfold FPR.Bits.toReal
    norm_num

/-- `mul_error` is false without its hypotheses: the product of two largest-finite normals wraps
to a small *negative* finite value. -/
theorem not_mul_error_unrestricted :
    ¬ ∀ (a b : FPR), |toReal (FPR.mul a b) - toReal a * toReal b| ≤
      (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b| := by
  intro h
  refine not_error_of_sign_flip (computed := toReal (FPR.mul maxFinite maxFinite))
    (exact := toReal maxFinite * toReal maxFinite) ?_ ?_ (h maxFinite maxFinite)
  · rw [toReal_maxFinite]; exact mul_pos maxFiniteReal_pos maxFiniteReal_pos
  · rw [show FPR.mul maxFinite maxFinite = (0xBFEFFFFFFFFFFFFE : UInt64) from by decide]
    unfold toReal toRealBits
    rw [show FPR.decode (0xBFEFFFFFFFFFFFFE : UInt64) = ⟨true, 1022, 2 ^ 52 - 2⟩ from by
      unfold FPR.decode; decide]
    unfold FPR.Bits.toReal
    have hp : (0 : ℝ) < (2 : ℝ) ^ ((1022 : ℤ) - 1023) := zpow_pos (by norm_num) _
    norm_num

/-- A subnormal magnitude, `2 ^ (-1023)`: exponent field `0`, nonempty significand. -/
private def subnormal : FPR := (0x0008000000000000 : UInt64)

private theorem toReal_subnormal : toReal subnormal = (2 : ℝ) ^ (-(1023 : ℤ)) := by
  unfold toReal toRealBits
  rw [show FPR.decode subnormal = ⟨false, 0, 2 ^ 51⟩ from by unfold FPR.decode subnormal; decide]
  unfold FPR.Bits.toReal
  rw [show (-(1023 : ℤ)) = (51 : ℤ) + (-(1074 : ℤ)) from by norm_num,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

/-- `div_error` is false with only `toReal b ≠ 0`. The flush guard `dzu` fires on an operand
whose exponent field is `0`, so a subnormal numerator is discarded outright and the quotient
returns `+0` — against an exact quotient of `2 ^ (-1023)`. This is the subnormal half of the
operand restriction, and it needs no overflow: `FPR.div` simply does not implement subnormals. -/
theorem not_div_error_unrestricted :
    ¬ ∀ (a b : FPR), toReal b ≠ 0 → |toReal (FPR.div a b) - toReal a / toReal b| ≤
      (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b| := by
  intro h
  have hne : toReal FPR.one ≠ 0 := by rw [toReal_one]; norm_num
  refine not_error_of_sign_flip (computed := toReal (FPR.div subnormal FPR.one))
    (exact := toReal subnormal / toReal FPR.one) ?_ ?_ (h subnormal FPR.one hne)
  · rw [toReal_subnormal, toReal_one, div_one]
    exact zpow_pos (by norm_num) _
  · rw [div_eq_zero_of_exponent_eq_zero subnormal FPR.one
      (by unfold FPR.decode subnormal; decide)]
    unfold toReal toRealBits
    rw [show FPR.decode (0 : UInt64) = ⟨false, 0, 0⟩ from by unfold FPR.decode; decide]
    unfold FPR.Bits.toReal
    norm_num

/-- `sqrt_error` is false with only `0 ≤ toReal a`, and needs no overflow to fail: at `+∞` the
hypothesis holds because this denotation sends the non-finite encodings to `0`, so the bound
demands an exact answer — while `FPR.sqrt` returns `2 ^ 512`. -/
theorem not_sqrt_error_unrestricted :
    ¬ ∀ (a : FPR), 0 ≤ toReal a → |toReal (FPR.sqrt a) - Real.sqrt (toReal a)| ≤
      (2 : ℝ) ^ (-(52 : ℤ)) * Real.sqrt (toReal a) := by
  intro h
  have hinf : toReal (0x7FF0000000000000 : UInt64) = 0 := by
    unfold toReal toRealBits
    rw [show FPR.decode (0x7FF0000000000000 : UInt64) = ⟨false, 2047, 0⟩ from by
      unfold FPR.decode; decide]
    unfold FPR.Bits.toReal
    norm_num
  have hb := h (0x7FF0000000000000 : UInt64) (by rw [hinf])
  rw [hinf, Real.sqrt_zero, sub_zero, mul_zero,
    show FPR.sqrt (0x7FF0000000000000 : UInt64) = (0x5FF0000000000000 : UInt64) from by
      rw [sqrt_eq_make_z, sqrtPipeline_q2_eq, sqrtPipeline_q1_eq, sqrtPipeline_loopRes]
      decide] at hb
  rw [show toReal (0x5FF0000000000000 : UInt64) = (2 : ℝ) ^ (512 : ℤ) from by
    unfold toReal toRealBits
    rw [show FPR.decode (0x5FF0000000000000 : UInt64) = ⟨false, 1535, 0⟩ from by
      unfold FPR.decode; decide]
    unfold FPR.Bits.toReal
    norm_num] at hb
  rw [abs_of_pos (zpow_pos (by norm_num) _)] at hb
  exact absurd hb (not_le.mpr (zpow_pos (by norm_num) _))

/-! ## Underflow refutes the result-side hypothesis on its own

Overflow is not the whole story: `FPR.add` also fails on *ordinary* normal operands whose exact
difference is subnormal, which is why `FPR.InNormalMagnitudeRange` restricts the exact result and
not only the operands. -/

/-- Restricting only the operands is not enough. Both inputs here are normal, but their exact
difference `2 ^ (-1074)` is subnormal, and the alignment step mis-rounds it into a large negative
value. This is the counterexample that `FPR.InNormalMagnitudeRange` — a hypothesis on the *exact
result* — exists to exclude. -/
theorem not_sub_error_operands_only :
    ¬ ∀ (a b : FPR), FPR.IsNormal a → FPR.IsNormal b →
      |toReal (FPR.sub a b) - (toReal a - toReal b)| ≤
        (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a - toReal b| := by
  intro h
  have hna : FPR.IsNormal minNormalSucc := by
    unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode minNormalSucc; decide
  have hnb : FPR.IsNormal minNormal := by
    unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode minNormal; decide
  refine not_error_of_sign_flip (computed := toReal (FPR.sub minNormalSucc minNormal))
    (exact := toReal minNormalSucc - toReal minNormal) ?_ ?_ (h minNormalSucc minNormal hna hnb)
  · rw [toReal_minNormalSucc, toReal_minNormal]
    have : (0 : ℝ) < (2 : ℝ) ^ (-(1074 : ℤ)) := zpow_pos (by norm_num) _
    linarith
  · rw [show FPR.sub minNormalSucc minNormal = (0xFCD0000000000000 : UInt64) from by decide]
    unfold toReal toRealBits
    rw [show FPR.decode (0xFCD0000000000000 : UInt64) = ⟨true, 1997, 0⟩ from by
      unfold FPR.decode; decide]
    unfold FPR.Bits.toReal
    norm_num

/-! ## Why the operand domain admits the zero encodings

The closure statements cannot be phrased on `FPR.IsNormal`: exact cancellation leaves it, and
`FPR.InNormalMagnitudeRange` does not exclude that — it explicitly admits `0`. -/

/-- `FPR.IsNormal` is not closed under `FPR.add`, even on in-range sums: at `1 + (-1)` both
operands are normal, the exact sum `0` is in range through `FPR.InNormalMagnitudeRange`'s own
`r = 0` disjunct, and `FPR.add` returns `+0`, whose exponent field is `0`. This is why the
operand domain is `FPR.IsNormalOrZero`. -/
theorem not_add_isNormal_closed :
    ¬ ∀ (a b : FPR), FPR.IsNormal a → FPR.IsNormal b →
      FPR.InNormalMagnitudeRange (toReal a + toReal b) → FPR.IsNormal (FPR.add a b) := by
  intro h
  have hone : FPR.IsNormal FPR.one := by
    unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.one; decide
  have hneg : FPR.IsNormal (FPR.neg FPR.one) := by
    unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.neg FPR.one; decide
  have hrange : FPR.InNormalMagnitudeRange (toReal FPR.one + toReal (FPR.neg FPR.one)) :=
    Or.inl (by rw [toReal_neg, toReal_one]; ring)
  have hbad : ¬ FPR.IsNormal (FPR.add FPR.one (FPR.neg FPR.one)) := by
    unfold FPR.IsNormal FPR.Bits.IsNormal FPR.decode FPR.neg FPR.one; decide
  exact hbad (h FPR.one (FPR.neg FPR.one) hone hneg hrange)

/-- And the value it lands on really is `+0`, not something the denotation happens to send to
zero: every decoded field is `0`. -/
theorem decode_add_one_negOne :
    FPR.decode (FPR.add FPR.one (FPR.neg FPR.one)) = ⟨false, 0, 0⟩ := by
  unfold FPR.decode FPR.neg FPR.one; decide

/-! ## `expm_p63`'s scale factor

`expm_p63_error` constrains `ccs` to `[0, 1)`. Both ends are load-bearing; the lower end because
the fixed-point conversion drops the sign bit, and the upper because it keeps only 63 bits. -/

/-- `expm_p63_error` is false without its `ccs` hypotheses. At `ccs = 1` the fixed-point
conversion `⌊2 ^ 63 * ccs⌋` wraps to `0` and takes the whole product with it, for *every* `x` in
range — against a true value of `Real.exp (-x)`, which on this domain never falls below one
half. -/
theorem not_expm_p63_error_unrestricted :
    ¬ ∀ (x ccs : FPR), 0 ≤ toReal x → toReal x ≤ 694 / 1000 →
      |(((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
        (toReal ccs * Real.exp (-(toReal x)))| ≤ (2 : ℝ) ^ (-(51 : ℤ)) := by
  intro h
  have hb := h FPR.zero FPR.one (by rw [toReal_zero]) (by rw [toReal_zero]; norm_num)
  rw [toReal_zero, toReal_one, neg_zero, Real.exp_zero, one_mul,
    show FPR.expm_p63 FPR.zero FPR.one = (0 : UInt64) from by
      rw [expm_p63_eq]; decide] at hb
  rw [show (((0 : UInt64).toNat : ℕ) : ℝ) = 0 from by norm_num, zero_div, zero_sub,
    abs_neg, abs_one] at hb
  have : (2 : ℝ) ^ (-(51 : ℤ)) < 1 := by
    rw [show (2 : ℝ) ^ (-(51 : ℤ)) = ((2 : ℝ) ^ (51 : ℕ))⁻¹ from by rw [zpow_neg]; norm_num]
    rw [inv_lt_one_iff₀]; right; norm_num
  linarith

end

end Falcon.Concrete.FPRBridge
