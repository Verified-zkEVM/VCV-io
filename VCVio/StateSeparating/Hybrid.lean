/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.StateSeparating.DistEquiv

/-!
# State-separating handlers: hybrid arguments

Hybrid and linked-game advantage lemmas for `QueryImpl.Stateful` handlers with
explicit initial states.
-/

universe uₑ uₘ

open OracleSpec OracleComp

namespace QueryImpl.Stateful

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- Hybrid lemma for any sequence of stateful handlers and explicit initial
states. -/
theorem advantage_hybrid {σ : ℕ → Type}
    (h : (i : ℕ) → QueryImpl.Stateful unifSpec E (σ i))
    (s : (i : ℕ) → σ i)
    (A : OracleComp E Bool) (n : ℕ) :
    (h 0).advantage (s 0) (h n) (s n) A ≤
      ∑ i ∈ Finset.range n, (h i).advantage (s i) (h (i + 1)) (s (i + 1)) A := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (h 0).advantage (s 0) (h (n + 1)) (s (n + 1)) A
        ≤ (h 0).advantage (s 0) (h n) (s n) A
            + (h n).advantage (s n) (h (n + 1)) (s (n + 1)) A :=
          advantage_triangle _ _ _ _ _ _ _
      _ ≤ (∑ i ∈ Finset.range n,
            (h i).advantage (s i) (h (i + 1)) (s (i + 1)) A)
            + (h n).advantage (s n) (h (n + 1)) (s (n + 1)) A := by
          gcongr
      _ = ∑ i ∈ Finset.range (n + 1),
            (h i).advantage (s i) (h (i + 1)) (s (i + 1)) A := by
          rw [Finset.sum_range_succ]

variable {ιₘ : Type uₘ}
  {M : OracleSpec.{uₘ, 0} ιₘ} {σP σ₀ σ₁ : Type}

/-- Advantage form of the linked-game reduction. The outer handler and its
initial state are absorbed into the shifted client. -/
theorem advantage_link_left_eq_advantage_shiftLeft
    (outer : QueryImpl.Stateful M E σP) (sP : σP)
    (inner₀ : QueryImpl.Stateful unifSpec M σ₀) (s₀ : σ₀)
    (inner₁ : QueryImpl.Stateful unifSpec M σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) :
    (outer.link inner₀).advantage (sP, s₀) (outer.link inner₁) (sP, s₁) A =
      inner₀.advantage s₀ inner₁ s₁ (outer.shiftLeft sP A) := by
  unfold advantage runProb
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]

end QueryImpl.Stateful
