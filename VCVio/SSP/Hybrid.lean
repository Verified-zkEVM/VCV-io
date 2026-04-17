/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.Advantage
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# State-Separating Proofs: Hybrid arguments and the linked-game reduction

This file collects two staple SSP results, phrased at the package level:

* `Package.advantage_hybrid` — the iterated triangle inequality for an `n`-step hybrid.
  Given a sequence of games `G₀, G₁, ..., Gₙ` (with potentially different state types) and a
  single Boolean adversary `A`, the distinguishing advantage between `G₀` and `Gₙ` is bounded
  by the sum of consecutive advantages.

* `Package.shiftLeft` and `Package.run_link_eq_run_shiftLeft` — the SSP "reduction"
  view of `run_link`: running the linked game `(P.link Q)` against an adversary `A` produces
  the same `OracleComp` distribution as running the inner game `Q` against the *shifted
  adversary* `P.shiftLeft A`. The advantage-level corollary
  `Package.advantage_link_left_eq_advantage_shiftLeft` says that replacing the inner game in
  `P.link _` only shifts the adversary; the outer reduction package `P` becomes part of the
  new adversary, exactly as in SSProve.

These two ingredients together justify the standard SSP game-hopping pattern: produce a chain
of intermediate games related by `link`-ed reductions, then collapse the chain via the hybrid
inequality.
-/

universe u v w

open OracleSpec OracleComp ProbComp

namespace VCVio.SSP

namespace Package

variable {ιᵢ ιₘ ιₑ : Type}
  {I : OracleSpec ιᵢ} {M : OracleSpec ιₘ} {E : OracleSpec ιₑ}

/-! ### Iterated triangle inequality (hybrid argument) -/

/-- **Hybrid lemma.** For any sequence of games `G 0, G 1, ..., G n` and any single Boolean
adversary `A`, the distinguishing advantage between the endpoints is bounded by the sum of
consecutive advantages.

The state types may differ from step to step: `σ : ℕ → Type` and `G i : Package unifSpec E (σ i)`.
This is just the iterated `boolDistAdvantage` triangle inequality, packaged for SSP-style
game-hopping proofs. -/
theorem advantage_hybrid {σ : ℕ → Type} (G : (i : ℕ) → Package unifSpec E (σ i))
    (A : OracleComp E Bool) (n : ℕ) :
    (G 0).advantage (G n) A ≤
      ∑ i ∈ Finset.range n, (G i).advantage (G (i + 1)) A := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (G 0).advantage (G (n + 1)) A
        ≤ (G 0).advantage (G n) A + (G n).advantage (G (n + 1)) A :=
          advantage_triangle _ _ _ _
      _ ≤ (∑ i ∈ Finset.range n, (G i).advantage (G (i + 1)) A) +
            (G n).advantage (G (n + 1)) A := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (G i).advantage (G (i + 1)) A := by
          rw [Finset.sum_range_succ]

/-! ### Shifted adversary and the SSP reduction lemma -/

variable {σ₁ σ₂ : Type}

/-- The **shifted adversary** obtained by absorbing the outer reduction package `P` into the
adversary. Given an outer reduction `P : Package M E σ₁` and an external adversary
`A : OracleComp E α` querying the export interface `E`, this returns an adversary against the
intermediate interface `M` by simulating `A` through `P.impl` and projecting away the
final outer state.

This is the SSP "reduction-to-the-distinguisher" move: the outer package becomes part of the
adversary, so a fresh round of analysis only needs to consider the inner game. -/
def shiftLeft (P : Package M E σ₁) {α : Type} (A : OracleComp E α) :
    OracleComp M α :=
  Prod.fst <$> (simulateQ P.impl A).run P.init

@[simp]
lemma shiftLeft_pure (P : Package M E σ₁) {α : Type} (x : α) :
    P.shiftLeft (pure x) = pure x := by
  simp [shiftLeft, simulateQ_pure, StateT.run_pure]

/-- **SSP reduction (program form).** Running the linked game `(P.link Q)` against adversary
`A` produces the same `OracleComp` distribution as running the inner game `Q` against the
*shifted* adversary `P.shiftLeft A`.

This is the equational form of the "swap the outer reduction into the adversary" step. The
advantage-level corollary `advantage_link_left_eq_advantage_shiftLeft` follows by rewriting
both sides under `boolDistAdvantage`. -/
theorem run_link_eq_run_shiftLeft {α : Type}
    (P : Package M E σ₁) (Q : Package I M σ₂) (A : OracleComp E α) :
    (P.link Q).run A = Q.run (P.shiftLeft A) := by
  -- Both sides reduce to `(fun p => p.1.1) <$> (simulateQ Q.impl X).run Q.init`,
  -- where `X = (simulateQ P.impl A).run P.init`.
  rw [run_link]
  simp only [shiftLeft, Package.run, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **SSP reduction (advantage form).** With the same outer reduction package
`P : Package M E σ₁` linked to two candidate inner games `Q₀, Q₁` exporting `M`, the
distinguishing advantage between the linked games equals the advantage between the inner
games against the *shifted adversary* `P.shiftLeft A`. The outer reduction package `P` is
absorbed into the adversary. -/
theorem advantage_link_left_eq_advantage_shiftLeft {σ_Q₀ σ_Q₁ : Type}
    (P : Package M E σ₁)
    (Q₀ : Package unifSpec M σ_Q₀) (Q₁ : Package unifSpec M σ_Q₁)
    (A : OracleComp E Bool) :
    (P.link Q₀).advantage (P.link Q₁) A =
      Q₀.advantage Q₁ (P.shiftLeft A) := by
  unfold advantage runProb
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]

end Package

end VCVio.SSP
