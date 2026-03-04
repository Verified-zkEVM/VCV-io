/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.SimulateQ
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Ergonomic Notation and Convenience Layer for Program Logic

This file provides user-facing notation, convenience predicates, and tactic macros
for game-hopping proofs. The goal is that standard game-hopping proofs never see `ℝ≥0∞`.

## Notation tiers

- Tier 1 (unary): `⦃P⦄ c ⦃Q⦄` — quantitative Hoare triple
- Tier 2 (pRHL): `c₁ ≡ₚ c₂` — game equivalence (equality coupling)
- Tier 2b: `c₁ ≈⟨R⟩ c₂` — relational triple with explicit relation
- Tier 3 (apRHL): `c₁ ≈[ε]⟨R⟩ c₂` — approximate relational triple
- Tier 4 (eRHL): `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` — full quantitative relational triple

## Convenience predicates

- `GameEquiv g₁ g₂` — two games have the same output distribution
- `AdvBound game ε` — advantage of a game is at most `ε`
-/

open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β : Type}

/-! ## Convenience predicates -/

/-- Two games have the same output distribution. -/
def GameEquiv (g₁ g₂ : OracleComp spec₁ α) : Prop :=
  evalDist g₁ = evalDist g₂

/-- Advantage of a Boolean game is at most `ε` (measured as deviation from 1/2). -/
def AdvBound (game : OracleComp spec₁ Bool) (ε : ℝ) : Prop :=
  |Pr[= true | game].toReal - 1/2| ≤ ε

/-! ## Bridge lemmas -/

/-- Game equivalence from exact pRHL equality coupling. -/
theorem GameEquiv.of_relTriple'
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.RelTriple' (spec₁ := spec₁) (spec₂ := spec₁) g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  Relational.gameEquiv_of_relTriple'_eqRel h

/-- Game equivalence from zero-error approximate coupling. -/
theorem GameEquiv.of_approxRelTriple_zero
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.ApproxRelTriple (spec₁ := spec₁) (spec₂ := spec₁) 0 g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  GameEquiv.of_relTriple' ((Relational.relTriple'_eq_approxRelTriple_zero).mpr h)

/-- Advantage bound via TV distance. -/
theorem AdvBound.of_tvDist
    {game₁ game₂ : OracleComp spec₁ Bool}
    {ε₁ ε₂ : ℝ}
    (hbound : AdvBound game₁ ε₁)
    (htv : tvDist game₁ game₂ ≤ ε₂) :
    AdvBound game₂ (ε₁ + ε₂) := by
  sorry

/-! ## Tactic macros -/

/-- `game_wp` decomposes unary WP goals by repeatedly applying WP rules. -/
macro "game_wp" : tactic =>
  `(tactic| (
    simp only [game_rule]
    repeat (first | rw [wp_bind] | rw [wp_query] | rw [wp_pure] | rw [wp_ite])
    try simp [game_rule]
  ))

/-- `game_rel` decomposes relational coupling goals by stepping through bind structure. -/
macro "game_rel" : tactic =>
  `(tactic| (
    repeat (first
      | exact Relational.relTriple_refl _
      | apply Relational.relTriple_bind _ (fun _ _ _ => _)
      | apply Relational.relTriple_eqRel_of_eq rfl)
    all_goals try simp [game_rule]
  ))

end OracleComp.ProgramLogic
