/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Falcon.Concrete.FloatLike
public import Extern.Falcon.FPRBridge
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Approximate Arithmetic Framework

A generic framework for stating and composing floating-point error bounds, parameterized
by `FloatLike F`. This connects the `FloatLike` typeclass (used by all executable Falcon
algorithms) to exact `ℝ` arithmetic (used by the specification and security proofs).

## Design

The `HasRealSemantics` class asserts that a `FloatLike F` type has a denotation into `ℝ`
such that each arithmetic operation satisfies a relative error bound with machine epsilon
`ε`. For IEEE-754 binary64 (the precision used by Falcon), `ε = 2^{-52}`.

No finite floating-point format can satisfy such a bound *unconditionally*: overflow
alone produces a result whose magnitude is unrelated to the exact one, so it cannot be
within any bounded relative epsilon of it. Every operation is therefore stated on a
`Valid` operand predicate and an `InRange` predicate on the exact real result, and each
operation's `_valid` field closes `Valid` under that same restriction, so a compound
expression can derive validity for its intermediate results rather than assuming it at each
step (see `compound_add_mul_error`, `horner_step_error`, and the `butterfly_*` lemmas below).

Only `Valid` propagates that way. `InRange` constrains the *exact* real result of a step, which
is a fact about the numbers an algorithm actually feeds in, not something closure can supply —
so every compound lemma below still takes an `InRange` premise per intermediate, and bounding
those stays an algorithm-specific obligation.

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

public section


noncomputable section

namespace FloatLike

/-- A `FloatLike F` type has real semantics with machine epsilon `ε` if there is a
denotation `interp : F → ℝ`, a validity predicate `Valid` on `F`, and a range predicate
`InRange` on `ℝ`, such that each operation satisfies a relative error bound — and
preserves `Valid` — on `Valid`, `InRange` operands.

`Valid` restricts operands to the format's well-behaved region (e.g. normal, finite
binary64 values, excluding subnormals and Inf/NaN); `InRange` restricts the *exact*
mathematical result of an operation to the magnitude window the format can round without
overflow or underflow. Neither restriction can be dropped: a finite format has no way to
honor a relative-error bound once the exact result leaves its representable range. The
`_valid` fields are what let the compound lemmas below chain several operations while
re-deriving `Valid` for each intermediate result, rather than needing it assumed at every
step. They do not do the same for `InRange`: each compound lemma takes one `InRange` premise
per exact intermediate, since no closure property can bound a quantity that depends on the
caller's actual inputs.

Carrying a domain that way costs something the unrestricted version did not have to think
about: the domain has to be non-degenerate, or the laws hold for nothing. `Valid := fun _ =>
False` satisfies every `_error` and `_valid` field vacuously, and `InRange := fun _ => False`
does the same, leaving only `interp_zero` / `interp_one` / `neg_exact` with any content — so
`[HasRealSemantics F ε]` on its own would be an assumption that says nothing, and every
compound lemma below could be instantiated at it. `valid_zero`, `valid_one` and
`inRange_of_valid` rule that out: the format's own constants are in the domain, and a value
the format holds is a result it can round to, so `InRange` is inhabited wherever `Valid` is.

That domain obligation reaches consumers too, and silently. A denotation is total, so it has
to send the non-finite encodings somewhere: the `FPR` instance sends Inf and NaN to `0`. A
downstream statement about `interp` of a computation that overflows, written *without* a
`Valid` gate on that computation, is therefore a true theorem — about `0`, not about the value
the algorithm produces. The error bounds here cannot be misread that way, since each one is
conditioned on its operands' validity, but nothing stops a caller from stating an ungated
corollary. `Valid` has to be threaded through every intermediate a proof reasons about.

The machine epsilon for IEEE-754 binary64 is `2^{-52} ≈ 2.22 × 10^{-16}`. -/
class HasRealSemantics (F : Type) [FloatLike F] (ε : outParam ℝ) where
  interp : F → ℝ
  /-- The operands on which this format's arithmetic laws are guaranteed to hold
  (e.g. normal, finite binary64 values). -/
  Valid : F → Prop
  /-- The exact real results this format can round without overflow or underflow. -/
  InRange : ℝ → Prop
  ε_nonneg : 0 ≤ ε
  ε_lt_one : ε < 1
  interp_zero : interp FloatLike.zero = 0
  interp_one : interp FloatLike.one = 1
  /-- The format's own constants are valid operands. -/
  valid_zero : Valid FloatLike.zero
  /-- The format's own constants are valid operands. -/
  valid_one : Valid FloatLike.one
  /-- A value the format holds is a result the format can round to. -/
  inRange_of_valid : ∀ (a : F), Valid a → InRange (interp a)
  add_error : ∀ (a b : F), Valid a → Valid b → InRange (interp a + interp b) →
    |interp (FloatLike.add a b) - (interp a + interp b)| ≤ ε * |interp a + interp b|
  add_valid : ∀ (a b : F), Valid a → Valid b → InRange (interp a + interp b) →
    Valid (FloatLike.add a b)
  mul_error : ∀ (a b : F), Valid a → Valid b → InRange (interp a * interp b) →
    |interp (FloatLike.mul a b) - interp a * interp b| ≤ ε * |interp a * interp b|
  mul_valid : ∀ (a b : F), Valid a → Valid b → InRange (interp a * interp b) →
    Valid (FloatLike.mul a b)
  div_error : ∀ (a b : F), Valid a → Valid b → interp b ≠ 0 →
    InRange (interp a / interp b) →
    |interp (FloatLike.div a b) - interp a / interp b| ≤ ε * |interp a / interp b|
  div_valid : ∀ (a b : F), Valid a → Valid b → interp b ≠ 0 →
    InRange (interp a / interp b) → Valid (FloatLike.div a b)
  sqrt_error : ∀ (a : F), Valid a → 0 ≤ interp a →
    |interp (FloatLike.sqrt a) - Real.sqrt (interp a)| ≤ ε * Real.sqrt (interp a)
  sqrt_valid : ∀ (a : F), Valid a → 0 ≤ interp a → Valid (FloatLike.sqrt a)
  neg_exact : ∀ (a : F), interp (FloatLike.neg a) = -interp a
  neg_valid : ∀ (a : F), Valid a → Valid (FloatLike.neg a)
  sub_error : ∀ (a b : F), Valid a → Valid b → InRange (interp a - interp b) →
    |interp (FloatLike.sub a b) - (interp a - interp b)| ≤ ε * |interp a - interp b|
  sub_valid : ∀ (a b : F), Valid a → Valid b → InRange (interp a - interp b) →
    Valid (FloatLike.sub a b)

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

/-- The result of an addition lies in `[(1-ε)(a+b), (1+ε)(a+b)]`, on `Valid`, `InRange`
operands. -/
theorem add_result_bounds (a b : F) (ha : self.Valid a) (hb : self.Valid b)
    (hr : self.InRange (self.interp a + self.interp b)) :
    (1 - ε) * |self.interp a + self.interp b| ≤ |self.interp (FloatLike.add a b)| ∧
    |self.interp (FloatLike.add a b)| ≤
      (1 + ε) * |self.interp a + self.interp b| :=
  result_bounds_of_error (self.add_error a b ha hb hr)

/-- The result of a multiplication lies in `[(1-ε)(a·b), (1+ε)(a·b)]`, on `Valid`, `InRange`
operands. -/
theorem mul_result_bounds (a b : F) (ha : self.Valid a) (hb : self.Valid b)
    (hr : self.InRange (self.interp a * self.interp b)) :
    (1 - ε) * |self.interp a * self.interp b| ≤ |self.interp (FloatLike.mul a b)| ∧
    |self.interp (FloatLike.mul a b)| ≤
      (1 + ε) * |self.interp a * self.interp b| :=
  result_bounds_of_error (self.mul_error a b ha hb hr)

/-! ### Compound Expression Error Bounds -/

/-- Error bound for `a * b + c * d`: the accumulated relative error is at most
`2ε + ε²`, the standard depth-2 relative-error bound `(1 + ε)^2 - 1`. -/
theorem compound_add_mul_error (a b c d : F)
    (ha : self.Valid a) (hb : self.Valid b) (hc : self.Valid c) (hd : self.Valid d)
    (hrab : self.InRange (self.interp a * self.interp b))
    (hrcd : self.InRange (self.interp c * self.interp d))
    (hradd : self.InRange
      (self.interp (FloatLike.mul a b) + self.interp (FloatLike.mul c d))) :
    |self.interp (FloatLike.add (FloatLike.mul a b) (FloatLike.mul c d)) -
      (self.interp a * self.interp b + self.interp c * self.interp d)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a * self.interp b| + |self.interp c * self.interp d|) := by
  have h_mul_ab := self.mul_error a b ha hb hrab
  have h_mul_cd := self.mul_error c d hc hd hrcd
  have hvab : self.Valid (FloatLike.mul a b) := self.mul_valid a b ha hb hrab
  have hvcd : self.Valid (FloatLike.mul c d) := self.mul_valid c d hc hd hrcd
  have h_add := self.add_error (FloatLike.mul a b) (FloatLike.mul c d) hvab hvcd hradd
  have h_mul_ab_ub := (self.mul_result_bounds a b ha hb hrab).2
  have h_mul_cd_ub := (self.mul_result_bounds c d hc hd hrcd).2
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
theorem horner_step_error (a x b : F)
    (ha : self.Valid a) (hx : self.Valid x) (hb : self.Valid b)
    (hrmul : self.InRange (self.interp a * self.interp x))
    (hradd : self.InRange (self.interp (FloatLike.mul a x) + self.interp b)) :
    |self.interp (FloatLike.add (FloatLike.mul a x) b) -
      (self.interp a * self.interp x + self.interp b)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a * self.interp x| + |self.interp b|) := by
  have h_mul := self.mul_error a x ha hx hrmul
  have hvmul : self.Valid (FloatLike.mul a x) := self.mul_valid a x ha hx hrmul
  have h_add := self.add_error (FloatLike.mul a x) b hvmul hb hradd
  have h_mul_ub := (self.mul_result_bounds a x ha hx hrmul).2
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
theorem butterfly_add_error (a b w : F)
    (ha : self.Valid a) (hw : self.Valid w) (hb : self.Valid b)
    (hrmul : self.InRange (self.interp w * self.interp b))
    (hradd : self.InRange (self.interp a + self.interp (FloatLike.mul w b))) :
    |self.interp (FloatLike.add a (FloatLike.mul w b)) -
      (self.interp a + self.interp w * self.interp b)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a| + |self.interp w * self.interp b|) := by
  have h_mul := self.mul_error w b hw hb hrmul
  have hvmul : self.Valid (FloatLike.mul w b) := self.mul_valid w b hw hb hrmul
  have h_add := self.add_error a (FloatLike.mul w b) ha hvmul hradd
  have h_mul_ub := (self.mul_result_bounds w b hw hb hrmul).2
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

theorem butterfly_sub_error (a b w : F)
    (ha : self.Valid a) (hw : self.Valid w) (hb : self.Valid b)
    (hrmul : self.InRange (self.interp w * self.interp b))
    (hrsub : self.InRange (self.interp a - self.interp (FloatLike.mul w b))) :
    |self.interp (FloatLike.sub a (FloatLike.mul w b)) -
      (self.interp a - self.interp w * self.interp b)| ≤
    (2 * ε + ε ^ 2) *
      (|self.interp a| + |self.interp w * self.interp b|) := by
  have h_mul := self.mul_error w b hw hb hrmul
  have hvmul : self.Valid (FloatLike.mul w b) := self.mul_valid w b hw hb hrmul
  have h_sub := self.sub_error a (FloatLike.mul w b) ha hvmul hrsub
  have h_mul_ub := (self.mul_result_bounds w b hw hb hrmul).2
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

open Falcon.Concrete.FPR in
/-- **`FPR` satisfies `HasRealSemantics` with machine epsilon `2 ^ (-52)`.**

The domain is `FPR.IsNormalOrZero` — normal and finite, or exactly `±0` — paired with
`FPR.InNormalMagnitudeRange` on the exact result. It excludes subnormals and the non-finite
encodings, both of which break the relative-error bounds; `FPRBridge.lean` carries a refutation
witness for each.

`FPR.IsNormal` alone would not do, and not for want of a proof: `add_valid` is *refutable* at
`1 + (-1)`, where both operands are normal, the exact sum `0` is in range through
`FPR.InNormalMagnitudeRange`'s own `r = 0` disjunct, and `FPR.add` returns `+0`, whose exponent
field is `0`. Exact cancellation is an `IsNormal`-losing failure mode that `InRange` does not
exclude — it explicitly *admits* zero. Admitting the two zero encodings repairs that without
readmitting subnormals or Inf/NaN.

The `interp` denotation is `FPRBridge.toReal`, a pure `Nat`/`Bool`/`ℝ` decoding of the IEEE-754
bit fields (`FPR.decode` + `FPR.Bits.toReal`) with no dependence on the opaque
`Float.ofBits`/`Float.toRat0` runtime path, so it reduces in the kernel. Every field below is a
theorem of `FPRBridge.lean` under the name it carries here, except that `div_error` / `div_valid`
take their hypotheses in a different order. -/
noncomputable instance : FloatLike.HasRealSemantics FPR ieee754_machineEpsilon where
  interp := Falcon.Concrete.FPRBridge.toReal
  Valid := Falcon.Concrete.FPRBridge.FPR.IsNormalOrZero
  InRange := Falcon.Concrete.FPRBridge.FPR.InNormalMagnitudeRange
  ε_nonneg := le_of_lt ieee754_machineEpsilon_pos
  ε_lt_one := ieee754_machineEpsilon_lt_one
  interp_zero := Falcon.Concrete.FPRBridge.toReal_zero
  interp_one := Falcon.Concrete.FPRBridge.toReal_one
  valid_zero := Falcon.Concrete.FPRBridge.FPR.isNormalOrZero_zero
  valid_one := Falcon.Concrete.FPRBridge.FPR.isNormalOrZero_one
  inRange_of_valid := fun _ h =>
    Falcon.Concrete.FPRBridge.FPR.inNormalMagnitudeRange_toReal_of_isNormalOrZero h
  add_error := Falcon.Concrete.FPRBridge.add_error
  add_valid := Falcon.Concrete.FPRBridge.add_isNormalOrZero
  mul_error := Falcon.Concrete.FPRBridge.mul_error
  mul_valid := Falcon.Concrete.FPRBridge.mul_isNormalOrZero
  div_error := fun a b ha hb hbne hr => Falcon.Concrete.FPRBridge.div_error a b hbne ha hb hr
  div_valid := fun a b ha hb hbne hr =>
    Falcon.Concrete.FPRBridge.div_isNormalOrZero a b hbne ha hb hr
  sqrt_error := Falcon.Concrete.FPRBridge.sqrt_error
  sqrt_valid := Falcon.Concrete.FPRBridge.sqrt_isNormalOrZero
  neg_exact := Falcon.Concrete.FPRBridge.toReal_neg
  neg_valid := fun _ => Falcon.Concrete.FPRBridge.FPR.isNormalOrZero_neg
  sub_error := Falcon.Concrete.FPRBridge.sub_error
  sub_valid := Falcon.Concrete.FPRBridge.sub_isNormalOrZero

end
