/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Negligible Functions

This file defines a simple wrapper around `SuperpolynomialDecay` for functions `ℕ → ℝ≥0∞`,
as this is usually the situation for cryptographic reductions.

## Main Results

- `negligible_zero`, `negligible_of_zero`: The zero function is negligible.
- `negligible_of_le`: Monotonicity — bounded by negligible is negligible.
- `negligible_add`: Sum of negligible functions is negligible.
- `negligible_sum`: Finite sum of negligible functions is negligible.
- `negligible_const_mul`: Constant multiple of negligible is negligible.
-/

open ENNReal Asymptotics Filter

/-- A function `f` is negligible if it decays faster than any polynomial function. -/
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
  SuperpolynomialDecay atTop (fun x ↦ ↑x) f

@[simp] def negligible_iff (f : ℕ → ℝ≥0∞) :
    negligible f ↔ SuperpolynomialDecay atTop (fun x ↦ ↑x) f := Iff.rfl

lemma negligible_zero : negligible 0 := superpolynomialDecay_zero _ _

lemma negligible_of_zero {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n = 0) : negligible f :=
  have : f = 0 := funext hf; this ▸ negligible_zero

/-- Negligibility is monotone: if `f ≤ g` pointwise and `g` is negligible, then `f` is. -/
theorem negligible_of_le {f g : ℕ → ℝ≥0∞} (hfg : ∀ n, f n ≤ g n) (hg : negligible g) :
    negligible f := by
  intro p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg p)
  · intro n; exact zero_le _
  · intro n; exact mul_le_mul_of_nonneg_left (hfg n) (zero_le _)

/-- Sum of two negligible functions is negligible. -/
theorem negligible_add {f g : ℕ → ℝ≥0∞} (hf : negligible f) (hg : negligible g) :
    negligible (f + g) :=
  hf.add hg

/-- Constant multiple of a negligible function is negligible (requires `c ≠ ⊤`
because multiplication by `⊤` is discontinuous at `0` in `ℝ≥0∞`). -/
theorem negligible_const_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    negligible (fun n => c * f n) := by
  intro p
  have h := ENNReal.Tendsto.const_mul (hf p) (.inr hc)
  simp only [mul_zero] at h
  exact h.congr (fun n => by rw [mul_left_comm])

/-- A finite sum of negligible functions is negligible. -/
theorem negligible_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ → ℝ≥0∞}
    (h : ∀ i ∈ s, negligible (f i)) :
    negligible (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact negligible_of_zero (fun _ => by simp)
  | insert _ _ hnotin ih =>
    simp_rw [Finset.sum_insert hnotin]
    exact negligible_add
      (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `f` is negligible, then `fun n => (↑n)^d * f n` is negligible for any fixed `d`.
Absorbs polynomial powers of the parameter into the superpolynomial decay. -/
theorem negligible_pow_mul {f : ℕ → ℝ≥0∞} (hf : negligible f) (d : ℕ) :
    negligible (fun n => (↑n : ℝ≥0∞) ^ d * f n) := fun k => by
  change Tendsto (fun (n : ℕ) => (↑n : ℝ≥0∞) ^ k * ((↑n : ℝ≥0∞) ^ d * f n)) atTop (nhds 0)
  simp_rw [← mul_assoc, ← pow_add]
  exact hf (k + d)

/-- If `f` is negligible, then `fun n => ↑(p.eval n) * f n` is negligible for any polynomial `p`.
This is the key lemma for handling polynomial-loss security reductions. -/
theorem negligible_polynomial_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    (p : Polynomial ℕ) :
    negligible (fun n => ↑(p.eval n) * f n) := by
  have heq : ∀ n, (↑(p.eval n) : ℝ≥0∞) * f n =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ↑(p.coeff i) * ((↑n : ℝ≥0∞) ^ i * f n) := by
    intro n
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    congr 1
    have h := @Polynomial.eval_eq_sum_range ℕ _ p n
    rw [h]; push_cast; rfl
  simp_rw [heq]
  exact negligible_sum fun i _ =>
    negligible_const_mul (negligible_pow_mul hf i) (ENNReal.natCast_ne_top _)
