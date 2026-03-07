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

## Notation (activate with `open scoped OracleComp.ProgramLogic`)

### Prop indicator (Std.Do-inspired)
- `⌜P⌝` — inject `Prop` into `ℝ≥0∞` (1 if true, 0 if false)

### Unary (Std.Do-inspired)
- `wp⟦c⟧` — quantitative WP (partial application, use as `wp⟦c⟧ post`)
- `⦃P⦄ c ⦃Q⦄` — quantitative Hoare triple (`P ≤ wp c Q`)

### Game-level
- `g₁ ≡ₚ g₂` — game equivalence (`evalDist g₁ = evalDist g₂`)

### Relational (EasyCrypt-inspired)
- `⟪c₁ ~ c₂ | R⟫` — pRHL coupling triple
- `⟪c₁ ≈[ε] c₂ | R⟫` — approximate coupling triple
- `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` — eRHL quantitative relational triple

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

@[refl] theorem GameEquiv.rfl {g : OracleComp spec₁ α} : GameEquiv g g := Eq.refl _

theorem GameEquiv.symm {g₁ g₂ : OracleComp spec₁ α}
    (h : GameEquiv g₁ g₂) : GameEquiv g₂ g₁ := Eq.symm h

theorem GameEquiv.trans {g₁ g₂ g₃ : OracleComp spec₁ α}
    (h₁ : GameEquiv g₁ g₂) (h₂ : GameEquiv g₂ g₃) : GameEquiv g₁ g₃ :=
  Eq.trans h₁ h₂

theorem GameEquiv.probOutput_eq {g₁ g₂ : OracleComp spec₁ α}
    (h : GameEquiv g₁ g₂) (x : α) : Pr[= x | g₁] = Pr[= x | g₂] := by
  show evalDist g₁ x = evalDist g₂ x; rw [h]

/-! ## Prop-to-ℝ≥0∞ indicator -/

open scoped Classical in
/-- Indicator embedding: lifts `P : Prop` into `ℝ≥0∞` as `1` (true) or `0` (false).
This is the quantitative analogue of Std.Do's `⌜P⌝ : SPred`. -/
noncomputable def propInd (P : Prop) : ℝ≥0∞ := if P then 1 else 0

@[simp] lemma propInd_true : propInd True = 1 := if_pos trivial
@[simp] lemma propInd_false : propInd False = 0 := if_neg not_false

lemma propInd_eq_ite {P : Prop} [Decidable P] : propInd P = if P then 1 else 0 := by
  simp [propInd]

open scoped Classical in
lemma propInd_and {P Q : Prop} : propInd (P ∧ Q) = propInd P * propInd Q := by
  unfold propInd
  split_ifs with hpq hp hq <;> simp_all

open scoped Classical in
lemma propInd_mono {P Q : Prop} (h : P → Q) : propInd P ≤ propInd Q := by
  unfold propInd
  split_ifs with hp hq
  · exact le_refl 1
  · exact absurd (h hp) hq
  · exact zero_le _
  · exact le_refl 0

/-! ## Notation -/

/-- Prop indicator: `⌜P⌝ = 1` if `P` holds, `0` otherwise.
Mirrors Std.Do's `⌜P⌝ : SPred` but targets `ℝ≥0∞`. -/
scoped notation "⌜" P "⌝" => propInd P

/-- Quantitative WP: `wp⟦c⟧ post` or just `wp⟦c⟧` for partial application. -/
scoped notation "wp⟦" c "⟧" => wp c

/-- Quantitative Hoare triple: `⦃P⦄ c ⦃Q⦄` means `P ≤ wp c Q`.
Uses `syntax` + `macro_rules` (not `notation`) because `⦃⦄` overlaps
with Lean's strict-implicit binder syntax. -/
scoped syntax:lead "⦃" term "⦄ " term:lead " ⦃" term "⦄" : term
macro_rules | `(⦃$P⦄ $c ⦃$Q⦄) => `(Triple $P $c $Q)

/-- Game equivalence: `g₁ ≡ₚ g₂` means `evalDist g₁ = evalDist g₂`.
Uses `syntax` + `macro_rules` because `≡` conflicts with Mathlib's
modular equivalence notation (`a ≡ b [MOD n]`). -/
scoped syntax:50 term:50 " ≡ₚ " term:51 : term
macro_rules | `($a ≡ₚ $b) => `(GameEquiv $a $b)

/-- pRHL coupling: `⟪c₁ ~ c₂ | R⟫` means `RelTriple c₁ c₂ R`. -/
scoped notation "⟪" c₁ " ~ " c₂ " | " R "⟫" => Relational.RelTriple c₁ c₂ R

/-- Approximate coupling: `⟪c₁ ≈[ε] c₂ | R⟫` means `ApproxRelTriple ε c₁ c₂ R`. -/
scoped notation "⟪" c₁ " ≈[" ε "] " c₂ " | " R "⟫" =>
  Relational.ApproxRelTriple ε c₁ c₂ R

/-- eRHL quantitative relational triple:
`⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` means `eRelTriple f c₁ c₂ g`. -/
scoped syntax:lead "⦃" term "⦄ " term:lead " ≈ₑ " term:lead " ⦃" term "⦄" : term
macro_rules | `(⦃$f⦄ $c₁ ≈ₑ $c₂ ⦃$g⦄) => `(Relational.eRelTriple $f $c₁ $c₂ $g)

/-! ## Bridge lemmas: `⌜⌝` and existing API -/

/-- `probEvent` equals WP of propInd postcondition. -/
lemma probEvent_eq_wp_propInd {ι : Type u} {spec : OracleSpec ι}
    [spec.Fintype] [spec.Inhabited] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[p | oa] = wp oa (fun x => ⌜p x⌝) := by
  classical
  have h := probEvent_eq_wp_indicator oa p
  simp only [propInd_eq_ite] at *
  exact h

/-- `RelPost.indicator` is pointwise `⌜⌝`. -/
lemma Relational.RelPost.indicator_eq_propInd {α β : Type}
    (R : Relational.RelPost α β) (a : α) (b : β) :
    Relational.RelPost.indicator R a b = ⌜R a b⌝ := by
  simp [Relational.RelPost.indicator, propInd]

/-- Almost-sure correctness: `⦃⌜True⌝⦄ c ⦃fun x => ⌜p x⌝⦄` iff `Pr[p | c] = 1`. -/
lemma triple_propInd_iff_probEvent_eq_one {ι : Type u} {spec : OracleSpec ι}
    [spec.Fintype] [spec.Inhabited] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    Triple (spec := spec) ⌜True⌝ oa (fun x => ⌜p x⌝) ↔ Pr[p | oa] = 1 := by
  show ⌜True⌝ ≤ wp oa (fun x => ⌜p x⌝) ↔ Pr[p | oa] = 1
  rw [propInd_true, ← probEvent_eq_wp_propInd]
  exact one_le_probEvent_iff

/-! ## Bridge lemmas: game equivalence and advantage -/

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

/-- Game equivalence from basic pRHL equality coupling. -/
theorem GameEquiv.of_relTriple
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.RelTriple (spec₁ := spec₁) (spec₂ := spec₁) g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  Relational.evalDist_eq_of_relTriple_eqRel h

/-- A bijection on a uniform sample is still uniform.
This is the key lemma behind OTP-style perfect secrecy proofs. -/
theorem GameEquiv.map_uniformSample_bij [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    GameEquiv (f <$> ($ᵗ α : ProbComp α)) ($ᵗ α : ProbComp α) := by
  conv_rhs => rw [← id_map ($ᵗ α : ProbComp α)]
  exact GameEquiv.of_relTriple
    (Relational.relTriple_map
      (Relational.relTriple_uniformSample_bij hf _ (fun _ => Eq.refl _)))

/-- Game equivalence is a congruence for bind. -/
theorem GameEquiv.bind_congr {g₁ g₂ : OracleComp spec₁ α}
    {f₁ f₂ : α → OracleComp spec₁ β}
    (hg : GameEquiv g₁ g₂) (hf : ∀ a, GameEquiv (f₁ a) (f₂ a)) :
    GameEquiv (g₁ >>= f₁) (g₂ >>= f₂) := by
  simp only [GameEquiv, evalDist_bind] at *; rw [hg]; congr 1; funext a; exact hf a

/-- Game equivalence is a congruence for map. -/
theorem GameEquiv.map_congr {g₁ g₂ : OracleComp spec₁ α} (f : α → β)
    (hg : GameEquiv g₁ g₂) :
    GameEquiv (f <$> g₁) (f <$> g₂) := by
  simp only [GameEquiv, evalDist_map] at *; rw [hg]

/-- Advantage bound via TV distance. -/
theorem AdvBound.of_tvDist
    {game₁ game₂ : OracleComp spec₁ Bool}
    {ε₁ ε₂ : ℝ}
    (hbound : AdvBound game₁ ε₁)
    (htv : tvDist game₁ game₂ ≤ ε₂) :
    AdvBound game₂ (ε₁ + ε₂) := by
  unfold AdvBound at *
  have hdiff := abs_probOutput_toReal_sub_le_tvDist game₁ game₂
  rw [abs_le] at hbound hdiff ⊢
  obtain ⟨hd1, hd2⟩ := hdiff
  obtain ⟨hb1, hb2⟩ := hbound
  constructor <;> linarith

/-- Transfer advantage bounds across equivalent games. -/
theorem AdvBound.of_gameEquiv {g₁ g₂ : OracleComp spec₁ Bool} {ε : ℝ}
    (heq : GameEquiv g₁ g₂) (hbound : AdvBound g₁ ε) :
    AdvBound g₂ ε := by
  unfold AdvBound at *; rwa [← heq.probOutput_eq]

/-! ## Tactic macros -/

/-- `game_wp` decomposes unary WP goals by repeatedly applying WP rules. -/
macro "game_wp" : tactic =>
  `(tactic| (
    simp only [game_rule]
    repeat (first | rw [wp_bind] | rw [wp_query] | rw [wp_pure] | rw [wp_ite]
                  | rw [wp_uniformSample])
    try simp [game_rule]
  ))

/-- `game_rel` decomposes relational coupling goals by stepping through bind structure. -/
macro "game_rel" : tactic =>
  `(tactic| (
    repeat (first
      | exact Relational.relTriple_refl _
      | apply Relational.relTriple_bind _ (fun _ _ _ => _)
      | apply Relational.relTriple_eqRel_of_evalDist_eq; try rfl
      | apply Relational.relTriple_eqRel_of_eq rfl
      | apply Relational.relTriple_query
      | apply Relational.relTriple_query_bij)
    all_goals try simp [game_rule]
  ))

/-- `coupling` decomposes `RelTriple` goals through bind/query structure. -/
macro "coupling" : tactic =>
  `(tactic| (
    repeat (first
      | exact Relational.relTriple_refl _
      | apply Relational.relTriple_bind _ (fun _ _ _ => _)
      | apply Relational.relTriple_eqRel_of_evalDist_eq; try rfl
      | apply Relational.relTriple_eqRel_of_eq rfl
      | apply Relational.relTriple_query
      | apply Relational.relTriple_query_bij)
    all_goals try simp [game_rule]
  ))

/-- `game_hop` tries to close a game-hopping step via coupling or TV distance bound.
Always enters `RelTriple` (not `RelTriple'`) so step-through tactics apply. -/
macro "game_hop" : tactic =>
  `(tactic| (
    first
      | (apply GameEquiv.of_relTriple; coupling)
      | (apply AdvBound.of_tvDist <;> [skip; try simp [game_rule]])
  ))

end OracleComp.ProgramLogic
