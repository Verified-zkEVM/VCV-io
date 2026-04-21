/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.Advantage
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import VCVio.SSP.Composition

/-!
# State-Separating Proofs: Hybrid arguments and the linked-game reduction

This file collects two staple SSP results, phrased at the package level:

* `Package.advantage_hybrid` — the iterated triangle inequality for an `n`-step hybrid.
  Given a sequence of games `G₀, G₁, ..., Gₙ` (with potentially different state types) and a
  single Boolean adversary `A`, the distinguishing advantage between `G₀` and `Gₙ` is bounded
  by the sum of consecutive advantages.

* `Package.advantage_link_left_eq_advantage_shiftLeft` — the advantage-level corollary of the
  program-level `run_link_eq_run_shiftLeft` (proved in `VCVio.SSP.Composition`): replacing the
  inner game in `P.link _` only shifts the adversary; the outer reduction package `P` becomes
  part of the new adversary, exactly as in SSProve.

These two ingredients together justify the standard SSP game-hopping pattern: produce a chain
of intermediate games related by `link`-ed reductions, then collapse the chain via the hybrid
inequality.

## Universe layout

Everything in this file is fixed at `Type 0`, matching `Package.advantage`: `ProbComp : Type
→ Type` and the adversary returns a `Bool : Type`, so the export / intermediate indices,
ranges, and state are all `Type`. Only the export index universes remain free in `uₘ, uₑ`.

Note that the raw program-level `shiftLeft` and `run_link_eq_run_shiftLeft` retain their full
universe polymorphism over `uᵢ, uₘ, uₑ, v`; they live in `VCVio.SSP.Composition`. The hybrid
theorem and the advantage-level reduction below are pinned to `Type 0` by `ProbComp`. -/

open OracleSpec OracleComp ProbComp

namespace VCVio.SSP

namespace Package

/-! ### Iterated triangle inequality (hybrid argument) -/

section Hybrid

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ}

/-- **Hybrid lemma.** For any sequence of games `G 0, G 1, ..., G n` and any single Boolean
adversary `A`, the distinguishing advantage between the endpoints is bounded by the sum of
consecutive advantages.

The state types may differ from step to step: `σ : ℕ → Type` and
`G i : Package unifSpec E (σ i)`. This is just the iterated `boolDistAdvantage` triangle
inequality, packaged for SSP-style game-hopping proofs. -/
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

end Hybrid

/-! ### Advantage-form reduction -/

variable {ιₘ ιₑ : Type}
  {M : OracleSpec.{0, 0} ιₘ} {E : OracleSpec.{0, 0} ιₑ}
  {σ₁ : Type}

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
