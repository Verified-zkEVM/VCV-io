/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Monad.Map

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

@[simp] theorem expectedValue_pure [LawfulMonadLiftT m SPMF] (x : α) (g : α → ℝ≥0∞) :
    expectedValue (pure x : m α) g = g x := by
  classical
  rw [expectedValue]
  refine (tsum_eq_single x fun y hy => ?_).trans ?_
  · rw [probOutput_pure, if_neg hy, zero_mul]
  · rw [probOutput_pure_self, one_mul]

/-- The tower property: averaging a bind is averaging the inner averages. -/
theorem expectedValue_bind [LawfulMonadLiftT m SPMF] (mx : m α) (my : α → m β) (g : β → ℝ≥0∞) :
    expectedValue (mx >>= my) g = expectedValue mx fun x => expectedValue (my x) g := by
  simp only [expectedValue, probOutput_bind_eq_tsum]
  calc ∑' y : β, (∑' x : α, Pr[= x | mx] * Pr[= y | my x]) * g y
      = ∑' (y : β) (x : α), Pr[= x | mx] * (Pr[= y | my x] * g y) := by
        refine tsum_congr fun y => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun x => by ring
    _ = ∑' (x : α) (y : β), Pr[= x | mx] * (Pr[= y | my x] * g y) := ENNReal.tsum_comm
    _ = ∑' x : α, Pr[= x | mx] * ∑' y : β, Pr[= y | my x] * g y :=
        tsum_congr fun _ => ENNReal.tsum_mul_left

theorem expectedValue_map [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m α) (f : α → β)
    (g : β → ℝ≥0∞) : expectedValue (f <$> mx) g = expectedValue mx fun x => g (f x) := by
  rw [map_eq_bind_pure_comp, expectedValue_bind]
  exact tsum_congr fun x => by simp only [Function.comp_apply, expectedValue_pure]

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
