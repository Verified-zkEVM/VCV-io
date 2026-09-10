/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Monad.Map
public import ToMathlib.Data.ENNReal.Finiteness

/-!
# Expected values of `ℝ≥0∞`-valued functionals

`expectedValue mx g` is `∑' x, Pr[= x | mx] * g x`, the average of `g` over the output of `mx`.
Failing runs contribute nothing, so on a computation that can fail this is the expectation of the
conditional-on-success value scaled by the success probability, not a conditional expectation.

`expectedValue` itself, its unfolding equation, monotonicity (`expectedValue_mono`,
`expectedValue_mono_of_support`, both `@[gcongr]`), the constant bounds, and additivity live in
`VCVio.EvalDist.Defs.Basic`, next to `probOutput`, so that the bind equations of
`VCVio.EvalDist.Monad.Basic` can be stated through it. The laws below are the ones a recursion
consumes: `pure` and `bind` (`expectedValue_bind` is the tower property) and linearity over a
`Finset` sum. `OracleComp.EvalDist.acceptRatio`
and the coordinate-wise fork's `forkSuccOf` are expectations in this sense, and are left written
out; this definition is for the places where the functional itself recurses.
-/

@[expose] public section

open scoped ENNReal

universe u v w

namespace OracleComp.EvalDist

variable {α β : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]

section lawful

variable [LawfulMonadLiftT m SPMF]

@[simp] theorem expectedValue_pure (x : α) (g : α → ℝ≥0∞) :
    expectedValue (pure x : m α) g = g x := by
  classical
  simp [expectedValue_def]

/-- The tower property: averaging a bind is averaging the inner averages. -/
theorem expectedValue_bind (mx : m α) (my : α → m β) (g : β → ℝ≥0∞) :
    expectedValue (mx >>= my) g = expectedValue mx fun x => expectedValue (my x) g := by
  simp only [expectedValue_def, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

@[simp] theorem expectedValue_map [LawfulMonad m] (mx : m α) (f : α → β)
    (g : β → ℝ≥0∞) : expectedValue (f <$> mx) g = expectedValue mx fun x => g (f x) := by
  simp only [map_eq_bind_pure_comp, expectedValue_bind, Function.comp_apply, expectedValue_pure]

/-- A bound that holds for every inner average bounds the bind. -/
theorem expectedValue_bind_le_of_le {mx : m α} {my : α → m β}
    {g : β → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, expectedValue (my x) g ≤ c) :
    expectedValue (mx >>= my) g ≤ c := by
  rw [expectedValue_bind]; exact expectedValue_le_of_le mx h

end lawful

omit [Monad m] in
/-- A finite-valued functional on a finite result type has finite expectation. -/
@[aesop (rule_sets := [finiteness]) safe apply]
theorem expectedValue_ne_top_of_finite [Finite α] (mx : m α) {g : α → ℝ≥0∞}
    (hg : ∀ x, g x ≠ ⊤) : expectedValue mx g ≠ ⊤ := by
  classical
  let := Fintype.ofFinite α
  rw [expectedValue_def, tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun x _ => ENNReal.mul_ne_top probOutput_ne_top (hg x)

omit [Monad m] in
/-- A supplied finite uniform bound on a functional gives a finite expectation. -/
theorem expectedValue_ne_top_of_le (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (hg : ∀ x, g x ≤ c) : expectedValue mx g ≠ ⊤ :=
  ne_top_of_le_ne_top hc (expectedValue_le_of_le mx hg)

omit [Monad m] in
/-- A constant functional averages to itself, provided no mass is lost to failure. -/
theorem expectedValue_const {mx : m α} (hmass : Pr[⊥ | mx] = 0) (c : ℝ≥0∞) :
    expectedValue mx (fun _ => c) = c := by
  rw [expectedValue, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hmass, one_mul]

omit [Monad m] in
/-- Linearity over a finite sum of functionals. -/
theorem expectedValue_finsetSum {ι' : Type w} (mx : m α) (s : Finset ι') (g : ι' → α → ℝ≥0∞) :
    expectedValue mx (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, expectedValue mx (g i) :=
  tsum_probOutput_mul_finsetSum mx s g

omit [Monad m] in
/-- Two computations with the same output distribution have the same expectations. -/
theorem expectedValue_congr {mx my : m α} (h : ∀ x, Pr[= x | mx] = Pr[= x | my]) (g : α → ℝ≥0∞) :
    expectedValue mx g = expectedValue my g :=
  tsum_congr fun x => by rw [h x]

end OracleComp.EvalDist
