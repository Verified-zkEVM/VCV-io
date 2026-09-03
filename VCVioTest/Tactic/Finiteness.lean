/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Option
public import ToMathlib.Data.ENNReal.Finiteness

/-!
# `finiteness` on probability terms

Canaries for the `finiteness` rule-set tags on `probOutput_ne_top`, `probEvent_ne_top`,
`probFailure_ne_top`, and `tsum_probOutput_ne_top`, and for the `Finset.sum` rule.
-/

public section

open scoped ENNReal

namespace VCVioTest.Finiteness

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]

example (mx : m α) (x : α) : Pr[= x | mx] ≠ ⊤ := by finiteness

example (mx : m α) (p : α → Prop) : Pr[ p | mx] * 2 ≠ ⊤ := by finiteness

example (mx : m α) (x : α) : Pr[⊥ | mx] + Pr[= x | mx] / 2 ≠ ⊤ := by finiteness

example (mx : m α) (x : α) : Pr[= x | mx] < ⊤ := by finiteness

example (mx : m α) : ∑' x, Pr[= x | mx] ≠ ⊤ := by finiteness

example (mx : m α) (c : ℝ≥0∞) (hc : c ≠ ⊤) : (∑' x, Pr[= x | mx]) * c ≠ ⊤ := by finiteness

example [Fintype α] (mx : m α) : ∑ x : α, Pr[= x | mx] ≠ ⊤ := by finiteness

end VCVioTest.Finiteness
