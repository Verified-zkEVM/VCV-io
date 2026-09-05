/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Option
public import VCVio.OracleComp.Constructions.SampleableType
public import Mathlib.Tactic.Positivity.Finset
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

/-- A quotient by a cardinality, the shape of the slack terms in the tag-reader bounds. The
nonzero side goal is `positivity`'s, and its `Fintype.card` extension lives in
`Mathlib.Tactic.Positivity.Finset`, which a file using this shape has to import. -/
example {D : Type} [Fintype D] [Nonempty D] (a : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / (Fintype.card D : ℝ≥0∞) ≠ ⊤ := by finiteness

/-- A coin and a die, drawn independently. -/
def coinDie : ProbComp (Bool × Fin 6) := do
  let b ← $ᵗ Bool
  let d ← $ᵗ (Fin 6)
  pure (b, d)

example : Pr[= (true, 0) | coinDie] * 3 + Pr[⊥ | coinDie] / 2 ≠ ⊤ := by finiteness

/-- Not a `finiteness` rule, by design: an unbounded functional has no finite expectation, so
the bound is supplied by hand. -/
example (mx : m α) (g : α → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) (h : ∀ x, g x ≤ c) :
    OracleComp.EvalDist.expectedValue mx g ≠ ⊤ :=
  ne_top_of_le_ne_top hc (OracleComp.EvalDist.expectedValue_le_of_le mx h)

end VCVioTest.Finiteness
