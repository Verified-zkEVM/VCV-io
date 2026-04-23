/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Advantage
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import VCVio.HeapSSP.Composition

/-!
# HeapSSP: Hybrid arguments and the linked-game reduction

Heap-package counterpart of `VCVio.SSP.Hybrid`.

* `Package.advantage_hybrid` — iterated triangle inequality for an `n`-step
  hybrid. Given a sequence of heap-packages `G₀, G₁, ..., Gₙ` (with
  potentially different identifier sets) and a single Boolean adversary
  `A`, the distinguishing advantage between `G₀` and `Gₙ` is bounded by
  the sum of consecutive advantages.

* `Package.advantage_link_left_eq_advantage_shiftLeft` — advantage-level
  corollary of the program-level `run_link_eq_run_shiftLeft` (proved in
  `VCVio.HeapSSP.Composition`): replacing the inner game in `P.link _`
  only shifts the adversary; the outer reduction package `P` becomes
  part of the new adversary, exactly as in SSProve and the SSP layer.

These two ingredients together justify the standard SSP game-hopping
pattern: produce a chain of intermediate games related by `link`-ed
reductions, then collapse the chain via the hybrid inequality.

## Universe layout

`ProbComp : Type → Type` and the adversary's return type `Bool : Type`
pin the intermediate range, export range, and cell-value type to `Type 0`.
The index universes `uₘ, uₑ` for the intermediate and export specs remain
*independent*, matching `VCVio.HeapSSP.Advantage`.

The raw program-level `shiftLeft` and `run_link_eq_run_shiftLeft` retain
their full universe polymorphism over `uᵢ, uₘ, uₑ, vᵢ, v`; they live in
`VCVio.HeapSSP.Composition`. Only ranges and cell-value type are pinned
to `Type 0` here, because `advantage` is already so pinned. -/

universe uₘ uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.HeapSSP

namespace Package

/-! ### Iterated triangle inequality (hybrid argument) -/

section Hybrid

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- **Hybrid lemma.** For any sequence of heap-packages `G 0, G 1, ..., G n`
and any single Boolean adversary `A`, the distinguishing advantage between
the endpoints is bounded by the sum of consecutive advantages.

The identifier sets may differ from step to step: `Ident : ℕ → Type`,
`[CellSpec (Ident i)]`, and `G i : Package unifSpec E (Ident i)`. The
iterated `boolDistAdvantage` triangle inequality, packaged for SSP-style
game-hopping proofs in the heap framework. -/
theorem advantage_hybrid {Ident : ℕ → Type} [∀ i, CellSpec.{0, 0} (Ident i)]
    (G : (i : ℕ) → Package unifSpec E (Ident i))
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

variable {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {M : OracleSpec.{uₘ, 0} ιₘ} {E : OracleSpec.{uₑ, 0} ιₑ}
  {Ident_P : Type} [CellSpec.{0, 0} Ident_P]

/-- **SSP reduction (advantage form).** With the same outer reduction package
`P : Package M E Ident_P` linked to two candidate inner games `Q₀, Q₁`
exporting `M`, the distinguishing advantage between the linked games equals
the advantage between the inner games against the *shifted adversary*
`P.shiftLeft A`. The outer reduction package `P` is absorbed into the
adversary. -/
theorem advantage_link_left_eq_advantage_shiftLeft
    {Ident_Q₀ Ident_Q₁ : Type}
    [CellSpec.{0, 0} Ident_Q₀] [CellSpec.{0, 0} Ident_Q₁]
    (P : Package M E Ident_P)
    (Q₀ : Package unifSpec M Ident_Q₀) (Q₁ : Package unifSpec M Ident_Q₁)
    (A : OracleComp E Bool) :
    (P.link Q₀).advantage (P.link Q₁) A =
      Q₀.advantage Q₁ (P.shiftLeft A) := by
  unfold advantage runProb
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]

end Package

end VCVio.HeapSSP
