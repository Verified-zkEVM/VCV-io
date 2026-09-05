/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# `gcongr` on probability bounds

Canaries for the `@[gcongr]` tags on `expectedValue` and `probEvent`: `gcongr` descends through
`∑' x, Pr[= x | mx] * f x`, through `expectedValue` with a support-restricted hypothesis, and
through `Pr[p | mx]`; a bind is not a `gcongr` head and is routed through
`probEvent_bind_eq_expectedValue`.
-/

public section

open scoped ENNReal
open OracleComp.EvalDist

namespace VCVioTest.GCongr

universe u v

variable {α β : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]
  [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]

example (mx : m α) (f g : α → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    ∑' x, Pr[= x | mx] * f x ≤ ∑' x, Pr[= x | mx] * g x := by
  gcongr with x
  exact h x

example (mx : m α) (f g : α → ℝ≥0∞) (h : ∀ x ∈ support mx, f x ≤ g x) :
    expectedValue mx f ≤ expectedValue mx g := by
  gcongr with x hx
  exact h x hx

example (mx : m α) (p q : α → Prop) (h : ∀ x ∈ support mx, p x → q x) :
    Pr[ p | mx] ≤ Pr[ q | mx] := by
  gcongr with x hx
  exact h x hx

example (mx : m α) (my oc : α → m β) (q : β → Prop)
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ Pr[ q | oc x]) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] := by
  fail_if_success gcongr
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue]
  gcongr with x hx
  exact h x hx

example (mx : m α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ x, f x ≤ c) :
    expectedValue mx f + 1 ≤ c + 1 := by
  gcongr ?_ + 1
  exact expectedValue_le_of_le mx h

/-- Averages of inner averages: after `expectedValue_bind`, `gcongr` descends into the
continuation with the support hypothesis. -/
example (mx : m α) (my my' : α → m β) (g : β → ℝ≥0∞)
    (h : ∀ x ∈ support mx, expectedValue (my x) g ≤ expectedValue (my' x) g) :
    expectedValue (mx >>= my) g ≤ expectedValue (mx >>= my') g := by
  rw [expectedValue_bind, expectedValue_bind]
  gcongr with x hx
  exact h x hx

/-- The forking-lemma shape: a truncated subtraction of finite sums (Mathlib's
`tsub_le_tsub_left` and `Finset.sum_le_sum` are `gcongr` lemmas). -/
example (f g : Fin 3 → ℝ≥0∞) (h : ∀ s, g s ≤ f s) : 1 - ∑ s, f s ≤ 1 - ∑ s, g s := by
  gcongr with s
  exact h s

/-- A coin and a die, drawn independently. -/
def coinDie : ProbComp (Bool × Fin 6) := do
  let b ← $ᵗ Bool
  let d ← $ᵗ (Fin 6)
  pure (b, d)

example : Pr[fun z => z.1 = true ∧ z.2 ≤ 2 | coinDie] ≤ Pr[fun z => z.2 ≤ 2 | coinDie] := by
  gcongr with z hz
  exact And.right

end VCVioTest.GCongr
