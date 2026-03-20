/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics
import VCVio.OracleComp.Constructions.Replicate

/-!
# Relational VCGen Tactic Examples

This file validates relational tactics from `VCVio.ProgramLogic.Tactics`:
`rvcstep`, `rvcgen`, `rel_conseq`, `rel_inline`, `rel_dist`.
-/

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β γ : Type}

/-! ## Basic relational stepping -/

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    (hoa : ⟪oa₁ ~ oa₂ | EqRel α⟫)
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | EqRel β⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | EqRel β⟫ := by
  rvcstep
  exact hoa

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep using S
  · exact hoa

example (f : α → OracleComp spec β) :
    ∀ x, ⟪f x ~ f x | EqRel β⟫ := by
  rvcstep as ⟨x⟩
  rvcstep

example (t : spec.Domain) :
    ⟪(liftM (query t) : OracleComp spec (spec.Range t))
     ~ (liftM (query t) : OracleComp spec (spec.Range t))
     | EqRel (spec.Range t)⟫ := by
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

/-! ## Iteration rules -/

example {oa₁ oa₂ : OracleComp spec α} (n : ℕ)
    (h : ⟪oa₁ ~ oa₂ | EqRel α⟫) :
    ⟪oa₁.replicate n ~ oa₂.replicate n | EqRel (List α)⟫ := by
  rvcstep
  exact h

example {oa : OracleComp spec α} {ob : OracleComp spec β} (n : ℕ)
    {R : RelPost α β}
    (h : ⟪oa ~ ob | R⟫) :
    ⟪oa.replicate n ~ ob.replicate n | List.Forall₂ R⟫ := by
  rvcstep
  exact h

example {xs : List α} {f : α → OracleComp spec β} {g : α → OracleComp spec β}
    (hfg : ∀ a, ⟪f a ~ g a | EqRel β⟫) :
    ⟪xs.mapM f ~ xs.mapM g | EqRel (List β)⟫ := by
  rvcstep
  exact hfg

example {xs : List α} {ys : List β}
    {S : α → β → Prop}
    {f : α → OracleComp spec γ} {g : β → OracleComp spec γ}
    {R : RelPost γ γ}
    (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → ⟪f a ~ g b | R⟫) :
    ⟪xs.mapM f ~ ys.mapM g | List.Forall₂ R⟫ := by
  rvcstep using S
  · exact hxy
  · exact hfg

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
  · exact hs
  · exact hfg

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
  rvcstep using Rin
  · exact hs
  · exact hxy
  · exact hfg

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
  · exact h1
  · exact h2

/-! ## `rel_conseq` / `rel_inline` / `rel_dist` -/

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq
  · exact h
  · exact hpost

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq with R
  · exact h
  · exact hpost

private def inlineId (oa : OracleComp spec α) : OracleComp spec α := oa

example (oa : OracleComp spec α) :
    ⟪inlineId oa ~ oa | EqRel α⟫ := by
  rel_inline inlineId

/-! ## Auto relational hint consumption -/

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep
  · exact hoa

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen

/-! ## Registered `@[vcspec]` relational theorems -/

@[irreducible] def wrappedTrueLeft : OracleComp spec Bool := pure true
@[irreducible] def wrappedTrueRight : OracleComp spec Bool := pure true

@[local vcspec] theorem relTriple_wrappedTruePair :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  simpa [wrappedTrueLeft, wrappedTrueRight] using
    (relTriple_refl (pure true : OracleComp spec Bool))

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep with relTriple_wrappedTruePair

/--
info: Try this:

  [apply] rvcstep with relTriple_wrappedTruePair
-/
#guard_msgs in
example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep?

/--
error: rvcstep using hf: the explicit hint did not match the current relational goal shape.
`using` is interpreted by goal shape as one of:
- bind cut relation
- random/query bijection
- `List.mapM` / `List.foldlM` input relation
- `simulateQ` state relation

Viable local `using` hints here: `S`
Goal:
  ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫
-/
#guard_msgs in
example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep using hf

/-! ## Relational consequence close -/

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rvcgen
