/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Negligible Functions

This file defines a simple wrapper around `SuperpolynomialDecay` for functions `ℕ → ℝ≥0∞`,
as this is usually the situation for cryptographic reductions.

## Main Results

- `negligible_zero`, `negligible_of_zero`: The zero function is negligible.
- `negligible_of_le`, `negligible_of_eventuallyLE`: Monotonicity — (eventually) bounded by
  negligible is negligible.
- `negligible_add`, `negligible_sum`: Finite sums of negligible functions are negligible;
  `negligible_ofReal_add`, `negligible_ofReal_sum` are the same through `ENNReal.ofReal`.
- `negligible_const_mul`, `negligible_pow_mul`, `negligible_polynomial_mul`: Polynomial factors
  are absorbed.
- `negligible_natMul_of_poly_bound`, `negligible_ofReal_natDiv_of_poly_bound`: Polynomially
  bounded numerators over negligible reciprocals.
- `negligible_iff_superpolynomialDecay_toReal`, `negligible_ofReal_iff`: The bridge to Mathlib's
  real-valued `SuperpolynomialDecay`, through which `negligible_iff_isBigO_toReal` and
  `negligible_iff_isLittleO_toReal` give the `O`/`o` characterizations.
-/

@[expose] public section

open ENNReal Asymptotics Filter

/-- A function `f` is negligible if it decays faster than any polynomial function. -/
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
  SuperpolynomialDecay atTop (fun x => ↑x) f

@[simp] theorem negligible_iff (f : ℕ → ℝ≥0∞) :
    negligible f ↔ SuperpolynomialDecay atTop (fun x => ↑x) f := Iff.rfl

lemma negligible_zero : negligible 0 := superpolynomialDecay_zero _ _

lemma negligible_of_zero {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n = 0) : negligible f :=
  funext hf ▸ negligible_zero

/-- Negligibility is monotone under eventual domination: if `f ≤ g` for all large `n` and `g` is
negligible, then `f` is. This is Mathlib's `SuperpolynomialDecay.trans_eventuallyLE` with `f`
squeezed between `0` and `g`. -/
theorem negligible_of_eventuallyLE {f g : ℕ → ℝ≥0∞} (hfg : ∀ᶠ n in atTop, f n ≤ g n)
    (hg : negligible g) : negligible f :=
  SuperpolynomialDecay.trans_eventuallyLE (Eventually.of_forall fun _ => zero_le)
    (superpolynomialDecay_zero _ _) hg (Eventually.of_forall fun _ => zero_le) hfg

/-- Negligibility is monotone: if `f ≤ g` pointwise and `g` is negligible, then `f` is. -/
theorem negligible_of_le {f g : ℕ → ℝ≥0∞} (hfg : ∀ n, f n ≤ g n) (hg : negligible g) :
    negligible f :=
  negligible_of_eventuallyLE (Eventually.of_forall hfg) hg

/-- Sum of two negligible functions is negligible. -/
theorem negligible_add {f g : ℕ → ℝ≥0∞} (hf : negligible f) (hg : negligible g) :
    negligible (f + g) :=
  hf.add hg

/-- `ENNReal.ofReal` of a sum of two real error families is negligible when each is. -/
theorem negligible_ofReal_add {a b : ℕ → ℝ} (ha : negligible fun n => ENNReal.ofReal (a n))
    (hb : negligible fun n => ENNReal.ofReal (b n)) :
    negligible fun n => ENNReal.ofReal (a n + b n) :=
  negligible_of_le (fun _ => ENNReal.ofReal_add_le) (negligible_add ha hb)

/-- `ENNReal.ofReal` of a finite sum of real error families is negligible when each is. -/
theorem negligible_ofReal_sum {ι : Type*} {s : Finset ι} {ε : ι → ℕ → ℝ}
    (h : ∀ i ∈ s, negligible fun n => ENNReal.ofReal (ε i n)) :
    negligible fun n => ENNReal.ofReal (∑ i ∈ s, ε i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact negligible_of_zero fun n => by simp
  | insert _ _ hnotin ih =>
    simp_rw [Finset.sum_insert hnotin]
    exact negligible_ofReal_add (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Constant multiple of a negligible function is negligible (requires `c ≠ ⊤`
because multiplication by `⊤` is discontinuous at `0` in `ℝ≥0∞`). -/
theorem negligible_const_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    negligible (fun n => c * f n) := by
  intro p
  simpa only [mul_zero] using
    (ENNReal.Tendsto.const_mul (hf p) (.inr hc)).congr (fun n => by rw [mul_left_comm])

/-- A finite sum of negligible functions is negligible. -/
theorem negligible_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ → ℝ≥0∞}
    (h : ∀ i ∈ s, negligible (f i)) :
    negligible (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact negligible_zero
  | insert _ _ hnotin ih =>
    simp_rw [Finset.sum_insert hnotin]
    exact negligible_add
      (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `f` is negligible, then `fun n => (↑n)^d * f n` is negligible for any fixed `d`.
Absorbs polynomial powers of the parameter into the superpolynomial decay. -/
theorem negligible_pow_mul {f : ℕ → ℝ≥0∞} (hf : negligible f) (d : ℕ) :
    negligible (fun n => (↑n : ℝ≥0∞) ^ d * f n) :=
  hf.param_pow_mul d

/-- If `f` is negligible, then `fun n => ↑(p.eval n) * f n` is negligible for any polynomial `p`.
This is the key lemma for handling polynomial-loss security reductions. -/
theorem negligible_polynomial_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    (p : Polynomial ℕ) :
    negligible (fun n => ↑(p.eval n) * f n) := by
  have heq : ∀ n, (↑(p.eval n) : ℝ≥0∞) * f n =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ↑(p.coeff i) * ((↑n : ℝ≥0∞) ^ i * f n) := by
    intro n
    simp [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  simp_rw [heq]
  exact negligible_sum fun i _ =>
    negligible_const_mul (negligible_pow_mul hf i) (ENNReal.natCast_ne_top _)

/-- A natural-number family bounded by a polynomial times a negligible family is negligible.
The basic closure used to absorb polynomial query / cardinality numerators into a negligible
reciprocal-cardinality factor. -/
theorem negligible_natMul_of_poly_bound {f : ℕ → ℝ≥0∞} (hf : negligible f)
    {g : ℕ → ℕ} {p : Polynomial ℕ} (hg : ∀ n, g n ≤ p.eval n) :
    negligible (fun n => (g n : ℝ≥0∞) * f n) :=
  negligible_of_le (g := fun n => ((p.eval n : ℕ) : ℝ≥0∞) * f n)
    (fun n => mul_le_mul' (by exact_mod_cast hg n) le_rfl)
    (negligible_polynomial_mul hf p)

/-- A slack term `numerator / cardinality` is negligible when the numerator is polynomially bounded
and the reciprocal cardinality is negligible. The `ENNReal.ofReal` wrapper is the framework idiom
for treating an `ℝ`-valued nonnegative error family asymptotically. -/
theorem negligible_ofReal_natDiv_of_poly_bound {C : ℕ → ℕ}
    (hC : negligible (fun n => (C n : ℝ≥0∞)⁻¹))
    {g : ℕ → ℕ} {p : Polynomial ℕ} (hg : ∀ n, g n ≤ p.eval n) :
    negligible (fun n => ENNReal.ofReal ((g n : ℝ) / (C n : ℝ))) :=
  negligible_of_le (g := fun n => (g n : ℝ≥0∞) * (C n : ℝ≥0∞)⁻¹)
    (fun n => by
      refine (ENNReal.ofReal_div_le (by positivity)).trans ?_
      rw [div_eq_mul_inv, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast])
    (negligible_natMul_of_poly_bound hC hg)

/-! ## Bridge to real-valued asymptotics

Mathlib's `SuperpolynomialDecay` API is stratified by typeclass, and its `O`/`o`
characterizations need a normed field, which `ℝ≥0∞` is not. For `⊤`-free families the two
lemmas below move the statement to `ℝ` through `ENNReal.toReal`, after which Mathlib's real
asymptotics apply verbatim. -/

/-- A `⊤`-free family is negligible iff its `toReal` image has superpolynomial decay in `ℝ`. -/
theorem negligible_iff_superpolynomialDecay_toReal {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n ≠ ⊤) :
    negligible f ↔ SuperpolynomialDecay atTop (Nat.cast : ℕ → ℝ) fun n => (f n).toReal := by
  simp only [negligible, SuperpolynomialDecay]
  refine forall_congr' fun k => ?_
  rw [← ENNReal.tendsto_toReal_zero_iff fun n =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)) (hf n)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]

/-- A nonnegative real error family is negligible (through `ENNReal.ofReal`) iff it has
superpolynomial decay in `ℝ`. -/
theorem negligible_ofReal_iff {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n) :
    negligible (fun n => ENNReal.ofReal (ε n)) ↔
      SuperpolynomialDecay atTop (Nat.cast : ℕ → ℝ) ε := by
  rw [negligible_iff_superpolynomialDecay_toReal fun n => ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal (hε _)]

/-- Negligibility as big-`O` against every integer power, on the `toReal` side. -/
theorem negligible_iff_isBigO_toReal {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n ≠ ⊤) :
    negligible f ↔ ∀ z : ℤ, (fun n => (f n).toReal) =O[atTop] fun n : ℕ => (n : ℝ) ^ z :=
  (negligible_iff_superpolynomialDecay_toReal hf).trans
    (superpolynomialDecay_iff_isBigO _ tendsto_natCast_atTop_atTop)

/-- Negligibility as little-`o` against every integer power, on the `toReal` side. -/
theorem negligible_iff_isLittleO_toReal {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n ≠ ⊤) :
    negligible f ↔ ∀ z : ℤ, (fun n => (f n).toReal) =o[atTop] fun n : ℕ => (n : ℝ) ^ z :=
  (negligible_iff_superpolynomialDecay_toReal hf).trans
    (superpolynomialDecay_iff_isLittleO _ tendsto_natCast_atTop_atTop)
