/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FloatLike
import LatticeCrypto.Falcon.Concrete.FPRBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Approximate Arithmetic Framework

A generic framework for stating and composing floating-point error bounds, parameterized
by `FloatLike F`. This connects the `FloatLike` typeclass (used by all executable Falcon
algorithms) to exact `ℝ` arithmetic (used by the specification and security proofs).

## Design

The `HasRealSemantics` class asserts that a `FloatLike F` type has a denotation into `ℝ`
such that each arithmetic operation satisfies a relative error bound with machine epsilon
`ε`. For IEEE-754 binary64 (the precision used by Falcon), `ε = 2^{-52}`.

This factoring separates two concerns:
1. **Algorithmic correctness** (generic over `FloatLike F`): "If the arithmetic were exact,
   the algorithm would produce the right answer."
2. **Numerical precision** (specific to `FPR`): "FPR arithmetic is close enough to exact."

## Main Definitions

- `FloatLike.HasRealSemantics F ε` — typeclass asserting that `F` operations approximate
  `ℝ` operations with relative error at most `ε`.
- `FloatLike.HasRealSemantics.interp` — the denotation function `F → ℝ`.
- Composition lemmas for accumulated error through compound expressions.
- The `FPR` instance using `FPRBridge.toReal`.

## References

- Higham, N. "Accuracy and Stability of Numerical Algorithms." 2002, Chapter 3.
- Pornin, T. "Constant-time Falcon implementation." ePrint 2019/893, Section 3.
- IEEE 754-2019, Section 4 (rounding).
-/


noncomputable section

namespace FloatLike

/-- A `FloatLike F` type has real semantics with machine epsilon `ε` if there is a
denotation `interp : F → ℝ` such that each operation satisfies a relative error bound.

The machine epsilon for IEEE-754 binary64 is `2^{-52} ≈ 2.22 × 10^{-16}`. -/
class HasRealSemantics (F : Type) [FloatLike F] (ε : outParam ℝ) where
  interp : F → ℝ
  ε_nonneg : 0 ≤ ε
  ε_lt_one : ε < 1
  interp_zero : interp FloatLike.zero = 0
  interp_one : interp FloatLike.one = 1
  add_error : ∀ (a b : F),
    |interp (FloatLike.add a b) - (interp a + interp b)| ≤ ε * |interp a + interp b|
  mul_error : ∀ (a b : F),
    |interp (FloatLike.mul a b) - interp a * interp b| ≤ ε * |interp a * interp b|
  div_error : ∀ (a b : F), interp b ≠ 0 →
    |interp (FloatLike.div a b) - interp a / interp b| ≤ ε * |interp a / interp b|
  sqrt_error : ∀ (a : F), 0 ≤ interp a →
    |interp (FloatLike.sqrt a) - Real.sqrt (interp a)| ≤ ε * Real.sqrt (interp a)
  neg_exact : ∀ (a : F), interp (FloatLike.neg a) = -interp a
  sub_error : ∀ (a b : F),
    |interp (FloatLike.sub a b) - (interp a - interp b)| ≤ ε * |interp a - interp b|

namespace HasRealSemantics

variable {F : Type} [FloatLike F] {ε : ℝ} [self : HasRealSemantics F ε]

/-! ### Derived Bounds -/

/-- A relative-error bound `|result - target| ≤ ε · |target|` implies two-sided absolute
bounds `(1 - ε)·|target| ≤ |result| ≤ (1 + ε)·|target|`. Specialized to each operation
below. -/
private theorem result_bounds_of_error {target result : ℝ}
    (herr : |result - target| ≤ ε * |target|) :
    (1 - ε) * |target| ≤ |result| ∧ |result| ≤ (1 + ε) * |target| := by
  refine ⟨?_, ?_⟩
  · linarith [abs_sub_abs_le_abs_sub target result, abs_sub_comm target result]
  · linarith [abs_sub_abs_le_abs_sub result target]

/-- The result of an addition lies in `[(1-ε)(a+b), (1+ε)(a+b)]`. -/
theorem add_result_bounds (a b : F) :
    (1 - ε) * |self.interp a + self.interp b| ≤ |self.interp (FloatLike.add a b)| ∧
    |self.interp (FloatLike.add a b)| ≤
      (1 + ε) * |self.interp a + self.interp b| :=
  result_bounds_of_error (self.add_error a b)

/-- The result of a multiplication lies in `[(1-ε)(a·b), (1+ε)(a·b)]`. -/
theorem mul_result_bounds (a b : F) :
    (1 - ε) * |self.interp a * self.interp b| ≤ |self.interp (FloatLike.mul a b)| ∧
    |self.interp (FloatLike.mul a b)| ≤
      (1 + ε) * |self.interp a * self.interp b| :=
  result_bounds_of_error (self.mul_error a b)

/-! ### Compound Expression Error Bounds -/

/-- Error bound for `a * b + c * d`: the accumulated relative error is at most
`2ε + ε²`, the standard depth-2 relative-error bound `(1 + ε)^2 - 1`. -/
theorem compound_add_mul_error (a b c d : F) :
    |self.interp (FloatLike.add (FloatLike.mul a b) (FloatLike.mul c d)) -
      (self.interp a * self.interp b + self.interp c * self.interp d)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a * self.interp b| + |self.interp c * self.interp d|) := by
  have h_mul_ab := self.mul_error a b
  have h_mul_cd := self.mul_error c d
  have h_add := self.add_error (FloatLike.mul a b) (FloatLike.mul c d)
  have h_mul_ab_ub := (self.mul_result_bounds a b).2
  have h_mul_cd_ub := (self.mul_result_bounds c d).2
  have hε := self.ε_nonneg
  set u := self.interp (FloatLike.mul a b) with hu
  set v := self.interp (FloatLike.mul c d) with hv
  set r := self.interp (FloatLike.add (FloatLike.mul a b) (FloatLike.mul c d)) with hr
  set ab := self.interp a * self.interp b with hab
  set cd := self.interp c * self.interp d with hcd
  have h_eq : r - (ab + cd) = (r - (u + v)) + ((u - ab) + (v - cd)) := by ring
  have h_tri : |r - (ab + cd)| ≤ |r - (u + v)| + |u - ab| + |v - cd| := by
    rw [h_eq]; linarith [abs_add_le (r - (u + v)) ((u - ab) + (v - cd)),
      abs_add_le (u - ab) (v - cd)]
  have h_abs_ub : |u + v| ≤ (1 + ε) * |ab| + (1 + ε) * |cd| := by
    linarith [abs_add_le u v]
  have h_mid : |r - (ab + cd)| ≤ (2 * ε + ε ^ 2) * (|ab| + |cd|) := by
    have := calc ε * |u + v| + ε * |ab| + ε * |cd|
        ≤ ε * ((1 + ε) * |ab| + (1 + ε) * |cd|) + ε * |ab| + ε * |cd| := by nlinarith
      _ = (2 * ε + ε ^ 2) * (|ab| + |cd|) := by ring
    linarith
  exact h_mid

/-- Error bound for a Horner evaluation step `a * x + b`: the accumulated error is at
most `2ε + ε²` relative to the exact value. -/
theorem horner_step_error (a x b : F) :
    |self.interp (FloatLike.add (FloatLike.mul a x) b) -
      (self.interp a * self.interp x + self.interp b)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a * self.interp x| + |self.interp b|) := by
  have h_mul := self.mul_error a x
  have h_add := self.add_error (FloatLike.mul a x) b
  have h_mul_ub := (self.mul_result_bounds a x).2
  have hε := self.ε_nonneg
  have h_tri : |self.interp (FloatLike.add (FloatLike.mul a x) b) -
      (self.interp a * self.interp x + self.interp b)| ≤
      |self.interp (FloatLike.add (FloatLike.mul a x) b) -
        (self.interp (FloatLike.mul a x) + self.interp b)| +
      |self.interp (FloatLike.mul a x) - self.interp a * self.interp x| := by
    calc _ = |(self.interp (FloatLike.add (FloatLike.mul a x) b) -
              (self.interp (FloatLike.mul a x) + self.interp b)) +
              (self.interp (FloatLike.mul a x) - self.interp a * self.interp x)| := by
            ring_nf
      _ ≤ _ := abs_add_le _ _
  have h_abs_ub : |self.interp (FloatLike.mul a x) + self.interp b| ≤
      (1 + ε) * |self.interp a * self.interp x| + |self.interp b| := by
    linarith [abs_add_le (self.interp (FloatLike.mul a x)) (self.interp b)]
  nlinarith [abs_nonneg (self.interp a * self.interp x),
    abs_nonneg (self.interp b)]

/-- Error bound for one FFT butterfly step: given `a, b` and twiddle factor `w`,
the output `a + w·b` has accumulated error at most `2ε + ε²`. -/
theorem butterfly_add_error (a b w : F) :
    |self.interp (FloatLike.add a (FloatLike.mul w b)) -
      (self.interp a + self.interp w * self.interp b)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a| + |self.interp w * self.interp b|) := by
  have h_mul := self.mul_error w b
  have h_add := self.add_error a (FloatLike.mul w b)
  have h_mul_ub := (self.mul_result_bounds w b).2
  have hε := self.ε_nonneg
  have h_tri : |self.interp (FloatLike.add a (FloatLike.mul w b)) -
      (self.interp a + self.interp w * self.interp b)| ≤
      |self.interp (FloatLike.add a (FloatLike.mul w b)) -
        (self.interp a + self.interp (FloatLike.mul w b))| +
      |self.interp (FloatLike.mul w b) - self.interp w * self.interp b| := by
    calc _ = |(self.interp (FloatLike.add a (FloatLike.mul w b)) -
              (self.interp a + self.interp (FloatLike.mul w b))) +
              (self.interp (FloatLike.mul w b) - self.interp w * self.interp b)| := by
            ring_nf
      _ ≤ _ := abs_add_le _ _
  have h_abs_ub : |self.interp a + self.interp (FloatLike.mul w b)| ≤
      |self.interp a| + (1 + ε) * |self.interp w * self.interp b| := by
    linarith [abs_add_le (self.interp a) (self.interp (FloatLike.mul w b))]
  nlinarith [abs_nonneg (self.interp a), abs_nonneg (self.interp w * self.interp b)]

theorem butterfly_sub_error (a b w : F) :
    |self.interp (FloatLike.sub a (FloatLike.mul w b)) -
      (self.interp a - self.interp w * self.interp b)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a| + |self.interp w * self.interp b|) := by
  have h_mul := self.mul_error w b
  have h_sub := self.sub_error a (FloatLike.mul w b)
  have h_mul_ub := (self.mul_result_bounds w b).2
  have hε := self.ε_nonneg
  have h_tri : |self.interp (FloatLike.sub a (FloatLike.mul w b)) -
      (self.interp a - self.interp w * self.interp b)| ≤
      |self.interp (FloatLike.sub a (FloatLike.mul w b)) -
        (self.interp a - self.interp (FloatLike.mul w b))| +
      |self.interp (FloatLike.mul w b) - self.interp w * self.interp b| := by
    calc _ = |(self.interp (FloatLike.sub a (FloatLike.mul w b)) -
              (self.interp a - self.interp (FloatLike.mul w b))) +
              (-(self.interp (FloatLike.mul w b) - self.interp w * self.interp b))| := by
            ring_nf
      _ ≤ |self.interp (FloatLike.sub a (FloatLike.mul w b)) -
            (self.interp a - self.interp (FloatLike.mul w b))| +
          |-(self.interp (FloatLike.mul w b) - self.interp w * self.interp b)| :=
            abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have h_abs_ub : |self.interp a - self.interp (FloatLike.mul w b)| ≤
      |self.interp a| + (1 + ε) * |self.interp w * self.interp b| := by
    have h1 : |self.interp a - self.interp (FloatLike.mul w b)| ≤
        |self.interp a| + |self.interp (FloatLike.mul w b)| := by
      rw [show self.interp a - self.interp (FloatLike.mul w b) =
        self.interp a + (-self.interp (FloatLike.mul w b)) from sub_eq_add_neg _ _]
      exact le_trans (abs_add_le _ _) (by rw [abs_neg])
    linarith
  nlinarith [abs_nonneg (self.interp a), abs_nonneg (self.interp w * self.interp b)]

end HasRealSemantics

end FloatLike

/-! ## FPR Instance -/

/-- The machine epsilon for IEEE-754 binary64: `2^{-52}`. -/
def ieee754_machineEpsilon : ℝ := (2 : ℝ) ^ (-(52 : ℤ))

theorem ieee754_machineEpsilon_pos : 0 < ieee754_machineEpsilon := by
  unfold ieee754_machineEpsilon; positivity

theorem ieee754_machineEpsilon_lt_one : ieee754_machineEpsilon < 1 := by
  unfold ieee754_machineEpsilon
  norm_num

-- open Falcon.Concrete.FPR in
/- FPR satisfies `HasRealSemantics` with machine epsilon `2^{-52}`.

The `interp` denotation is `FPRBridge.toReal` (IEEE-754 bit interpretation).
The per-operation error bounds come from `FPRBridge.lean`.

**Not provable as stated.** The four `sorry` fields (`interp_zero`, `interp_one`, `neg_exact`,
`sub_error`) require reasoning about `FPRBridge.toReal`, which is defined via
`Float.ofBits` and `Float.toRat0`. Both are opaque to the Lean kernel:

- `Float.ofBits : UInt64 → Float` is an `extern` call into the runtime.
- `Float.toRat0 : Float → Rat` roundtrips through hardware floats.

To discharge these obligations we would need either:
1. An axiomatized IEEE-754 model (`axiom float_ofBits_zero : Float.ofBits 0 = ...`), or
2. A verified pure-Lean IEEE-754 decoder that replaces the opaque `Float` path.

Until then, these remain axiomatic trust assumptions about the FPR encoding. -/
-- instance : FloatLike.HasRealSemantics FPR ieee754_machineEpsilon where
--   interp := Falcon.Concrete.FPRBridge.toReal
--   ε_nonneg := le_of_lt ieee754_machineEpsilon_pos
--   ε_lt_one := ieee754_machineEpsilon_lt_one
--   interp_zero := by sorry
--   interp_one := by sorry
--   add_error := Falcon.Concrete.FPRBridge.add_error
--   mul_error := Falcon.Concrete.FPRBridge.mul_error
--   div_error := fun a b hb => Falcon.Concrete.FPRBridge.div_error a b hb
--   sqrt_error := fun a ha => Falcon.Concrete.FPRBridge.sqrt_error a ha
--   neg_exact := fun _ => by sorry
--   sub_error := fun _ _ => by sorry

end
