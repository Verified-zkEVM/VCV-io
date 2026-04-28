/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Relational
import VCVio.OracleComp.Constructions.Replicate

/-!
# Relational VCGen Step Examples

This file validates one-step relational tactic behavior.
-/

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational
open Lean.Order
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β γ δ : Type}

/-! ## Basic relational stepping -/

example (oa : OracleComp spec α) :
    ⟪oa ~ oa | EqRel α⟫ := by
  rvcstep

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    (hoa : ⟪oa₁ ~ oa₂ | EqRel α⟫)
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | EqRel β⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | EqRel β⟫ := by
  rvcstep

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep using S

example (f : α → OracleComp spec β) :
    ∀ x, ⟪f x ~ f x | EqRel β⟫ := by
  rvcstep as ⟨x⟩
  rvcstep

example (t : spec.Domain) :
    ⟪(query t : OracleComp spec (spec.Range t))
     ~ (query t : OracleComp spec (spec.Range t))
     | EqRel (spec.Range t)⟫ := by
  rvcstep

example {oa : OracleComp spec α} {ob : OracleComp spec β} {R : RelPost α β}
    (h : ⟪oa ~ ob | R⟫) :
    ⟪ob ~ oa | fun b a => R a b⟫ := by
  rvcstep sym
  exact h

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R : RelPost α β} (h : ⟪oa ~ ob | R⟫) :
    ⟪oa ~ ob | fun a b => R a b ∧ True⟫ := by
  rvcstep upto R
  · exact h
  · intro a b hab
    exact ⟨hab, trivial⟩

/--
info: [vcspec cache] miss `OracleComp.ProgramLogic.Relational.relTriple_map` (folded, relTriple)
-/
#guard_msgs in
set_option vcvio.vcgen.traceCachedRules true in
example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R : RelPost γ δ} {f : α → γ} {g : β → δ}
    (h : ⟪oa ~ ob | fun a b => R (f a) (g b)⟫) :
    ⟪f <$> oa ~ g <$> ob | R⟫ := by
  rvcstep

/-! ## Bijective random sampling -/

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | fun x y => y = f x⟫ := by
  rvcstep using f
  · exact hf
  · intro x
    rfl

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | fun x y => y = f x⟫ := by
  rvcstep
  · exact hf
  · intro x
    rfl

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪(($ᵗ α : ProbComp α) >>= fun x => pure x)
     ~ (($ᵗ α : ProbComp α) >>= fun x => pure x)
     | fun x y => y = f x⟫ := by
  rvcstep using f
  · exact relTriple_pure_pure rfl
  · exact hf

example [SampleableType α] (post : α → α → ℝ≥0∞) :
    ⦃∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a a⦄
      ($ᵗ α : ProbComp α) ≈ₑ ($ᵗ α : ProbComp α)
    ⦃post⦄ := by
  rvcstep

example (t : spec.Domain) (post : spec.Range t → spec.Range t → ℝ≥0∞) :
    ⦃∑' a : spec.Range t,
      Pr[= a | (query t : OracleComp spec (spec.Range t))] * post a a⦄
      (query t : OracleComp spec (spec.Range t)) ≈ₑ
      (query t : OracleComp spec (spec.Range t))
    ⦃post⦄ := by
  rvcstep

/-! ## Iteration rules -/

example {oa₁ oa₂ : OracleComp spec α} (n : ℕ)
    (h : ⟪oa₁ ~ oa₂ | EqRel α⟫) :
    ⟪oa₁.replicate n ~ oa₂.replicate n | EqRel (List α)⟫ := by
  rvcstep

example {oa : OracleComp spec α} {ob : OracleComp spec β} (n : ℕ)
    {R : RelPost α β}
    (h : ⟪oa ~ ob | R⟫) :
    ⟪oa.replicate n ~ ob.replicate n | List.Forall₂ R⟫ := by
  rvcstep

example {xs : List α} {f : α → OracleComp spec β} {g : α → OracleComp spec β}
    (hfg : ∀ a, ⟪f a ~ g a | EqRel β⟫) :
    ⟪xs.mapM f ~ xs.mapM g | EqRel (List β)⟫ := by
  rvcstep

example {xs : List α} {ys : List β}
    {S : α → β → Prop}
    {f : α → OracleComp spec γ} {g : β → OracleComp spec γ}
    {R : RelPost γ γ}
    (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → ⟪f a ~ g b | R⟫) :
    ⟪xs.mapM f ~ ys.mapM g | List.Forall₂ R⟫ := by
  rvcstep

example {σ₁ σ₂ : Type}
    {xs : List α}
    {f : σ₁ → α → OracleComp spec σ₁}
    {g : σ₂ → α → OracleComp spec σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → ⟪f t₁ a ~ g t₂ a | S⟫) :
    ⟪xs.foldlM f s₁ ~ xs.foldlM g s₂ | S⟫ := by
  rvcstep

example {σ₁ σ₂ : Type}
    {xs : List α} {ys : List β}
    {Rin : α → β → Prop}
    {f : σ₁ → α → OracleComp spec σ₁}
    {g : σ₂ → β → OracleComp spec σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → ∀ t₁ t₂, S t₁ t₂ → ⟪f t₁ a ~ g t₂ b | S⟫) :
    ⟪xs.foldlM f s₁ ~ ys.foldlM g s₂ | S⟫ := by
  rvcstep

/-! ## Pure / ite rules -/

example (a : α) :
    ⟪(pure a : OracleComp spec α) ~ (pure a : OracleComp spec α) | EqRel α⟫ := by
  rvcstep

example {c : Prop} [Decidable c]
    {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h1 : ⟪oa₁ ~ ob₁ | EqRel α⟫)
    (h2 : ⟪oa₂ ~ ob₂ | EqRel α⟫) :
    ⟪(if c then oa₁ else oa₂) ~ (if c then ob₁ else ob₂) | EqRel α⟫ := by
  rvcstep

/-! ## Auto relational hint consumption -/

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen

/-! ## Leaf closure via equality hypotheses

These exercise the augmented leaf closer that calls `subst_vars` and tries the
canonical pure/refl rules afterward, so syntactically-distinct pure values that
become equal under local equalities close automatically. -/

example {a b : α} (h : a = b) :
    ⟪(pure a : OracleComp spec α) ~ (pure b : OracleComp spec α) | EqRel α⟫ := by
  rvcstep

example {a b : α} (h : b = a) :
    ⟪(pure a : OracleComp spec α) ~ (pure b : OracleComp spec α) | EqRel α⟫ := by
  rvcstep

/-! ## Bind normalization

These exercise the monadic-normalization pre-pass: nested `>>=` and `pure`-binds
get flattened so the relational planner sees aligned bind shapes (or bypasses
the bind rule entirely when both sides reduce to a leaf). -/

example {a : α} {f : α → OracleComp spec β} :
    ⟪(do let x ← pure a; f x) ~ f a | EqRel β⟫ := by
  simpa only [pure_bind] using (relTriple_refl (oa := f a))

example {oa : OracleComp spec α} {f : α → OracleComp spec β} {g : β → OracleComp spec γ} :
    ⟪((oa >>= f) >>= g) ~ (do let x ← oa; let y ← f x; g y) | EqRel γ⟫ := by
  simpa only [bind_assoc] using
    (relTriple_refl (oa := oa >>= fun x => f x >>= g))

/-! ## Regression: multi-goal isolation

Not an idiomatic-usage example. The deliberately unfocused `rvcstep` below
exercises the corner case where `rvcstep` is invoked with sibling goals visible
in the goal list (the pattern `linter.style.multiGoal` discourages on style
grounds, but which must still behave *correctly* when used). Previously, when
the sample subgoal of `relTriple_bind` auto-closed, an unconditional
swap-and-close pass could pull a trailing sibling ahead of the bind continuation
and silently discharge it. The fix in `closeSampleAndReorderBindGoals` keeps
`rest` untouched at the tail. -/

example {oa : OracleComp spec α} {f g : α → OracleComp spec β}
    (ob : OracleComp spec α)
    (hf : ∀ a, ⟪f a ~ g a | EqRel β⟫) :
    (⟪oa >>= f ~ oa >>= g | EqRel β⟫) ∧ (⟪ob ~ ob | EqRel α⟫) := by
  constructor
  · refine relTriple_bind (R := EqRel α) (relTriple_refl (oa := oa)) ?_
    intro a₁ a₂ h
    subst h
    exact hf a₁
  · exact relTriple_refl (oa := ob)

/-! ## Quantitative `Std.Do'.RelTriple` path -/

example (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    ⦃post a b⦄
      (pure a : OracleComp spec α) ≈ₑ (pure b : OracleComp spec β)
    ⦃post⦄ := by
  rvcstep

example (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    post a b ⊑
      rwp⟦(pure a : OracleComp spec α) ~ (pure b : OracleComp spec β) |
        post ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcstep

example (a : α) (b : β)
    (f : α → OracleComp spec γ) (g : β → OracleComp spec δ)
    (post : γ → δ → ℝ≥0∞) :
    rwp⟦f a ~ g b | post ; epost⟨⟩, epost⟨⟩⟧ ⊑
      rwp⟦
        (do
          let x ← (pure a : OracleComp spec α)
          f x)
        ~
        (do
          let y ← (pure b : OracleComp spec β)
          g y)
      | post ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcgen

example [DecidableEq γ] [DecidableEq δ] (a : α) (b : β)
    (f : α → γ) (g : β → δ)
    (post : γ → δ → ℝ≥0∞) :
    post (f a) (g b) ⊑
      rwp⟦
        (do
          let x ← (pure a : OracleComp spec α)
          pure (f x))
        ~
        (do
          let y ← (pure b : OracleComp spec β)
          pure (g y))
      | post ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcgen

example (a : α) (b : β)
    (f : α → OracleComp spec γ)
    (post : γ → β → ℝ≥0∞) :
    rwp⟦f a ~ (pure b : OracleComp spec β) | post ; epost⟨⟩, epost⟨⟩⟧ ⊑
      rwp⟦
        (do
          let x ← (pure a : OracleComp spec α)
          f x)
        ~
        (pure b : OracleComp spec β)
      | post ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcstep left
  rvcgen

example (a : α) (b : β)
    (g : β → OracleComp spec δ)
    (post : α → δ → ℝ≥0∞) :
    rwp⟦(pure a : OracleComp spec α) ~ g b | post ; epost⟨⟩, epost⟨⟩⟧ ⊑
      rwp⟦
        (pure a : OracleComp spec α)
        ~
        (do
          let y ← (pure b : OracleComp spec β)
          g y)
      | post ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcstep right
  rvcgen

example (a : α) (b : β)
    (f : α → OracleComp spec γ)
    (post : γ → β → ℝ≥0∞) :
    ⦃rwp⟦f a ~ (pure b : OracleComp spec β) | post ; epost⟨⟩, epost⟨⟩⟧⦄
      (do
        let x ← (pure a : OracleComp spec α)
        f x) ≈ₑ (pure b : OracleComp spec β)
    ⦃post⦄ := by
  rvcstep left
  rvcgen

example (a : α) (b : β)
    (g : β → OracleComp spec δ)
    (post : α → δ → ℝ≥0∞) :
    ⦃rwp⟦(pure a : OracleComp spec α) ~ g b | post ; epost⟨⟩, epost⟨⟩⟧⦄
      (pure a : OracleComp spec α) ≈ₑ
      (do
        let y ← (pure b : OracleComp spec β)
        g y)
    ⦃post⦄ := by
  rvcstep right
  rvcgen

