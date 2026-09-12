/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Expectation

/-!
# Structural simplification of expectations

Mapping a computation precomposes the payoff without expanding an expectation into a sum.
These ordinary-import tests require only a lawful subprobability lift, with no support semantics
or losslessness assumptions. The negative probe isolates the contribution of the map rule.
-/

public section

open OracleComp.EvalDist
open scoped ENNReal

namespace VCVioTest.Tactic.Expectation

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α β γ : Type u}

example (mx : m α) (f : α → β) (g : β → ℝ≥0∞) :
    expectedValue (f <$> mx) g = expectedValue mx (fun x => g (f x)) := by simp

example (mx : m α) (f : α → β) (g : β → γ) (h : γ → ℝ≥0∞) :
    expectedValue (g <$> (f <$> mx)) h = expectedValue mx (fun x => h (g (f x))) := by simp

example (mx : m α) (f : Fin 3 → α → β) (g : β → ℝ≥0∞) :
    ∑ i, expectedValue (f i <$> mx) g = ∑ i, expectedValue mx (fun x => g (f i x)) := by simp

example (mx : SPMF Empty) (f : Empty → Unit) (g : Unit → ℝ≥0∞) :
    expectedValue (f <$> mx) g = expectedValue mx (fun x => g (f x)) := by simp

/-- Without the map rule, a generic mapped expectation is not simplified. -/
example (mx : m α) (f : α → β) (g : β → ℝ≥0∞) :
    expectedValue (f <$> mx) g = expectedValue mx (fun x => g (f x)) := by
  fail_if_success solve | simp [-expectedValue_map]
  simp

end VCVioTest.Tactic.Expectation
