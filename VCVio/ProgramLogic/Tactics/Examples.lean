/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics
import VCVio.OracleComp.Constructions.Replicate

/-!
# Examples and Tests for VCGen-Style Tactics

This file validates the user-facing tactic surface imported from
`VCVio.ProgramLogic.Tactics`.
-/

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β γ : Type}

/-! ## Notation examples -/

example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa >>= f⟧ post = wp⟦oa⟧ (fun u => wp⟦f u⟧ post) := by
  wp_step

example (oa : OracleComp spec α) :
    ⟪oa ~ oa | EqRel α⟫ := by
  rvcgen_step

/-! ## Unary examples -/

section Unary

example (x : α) (post : α → ℝ≥0∞) :
    wp⟦(pure x : OracleComp spec α)⟧ post = post x := by
  wp_step

example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦if c then a else b⟧ post = if c then wp⟦a⟧ post else wp⟦b⟧ post := by
  wp_step

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate (n + 1)⟧ post =
      wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) := by
  wp_step

example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦(x :: xs).mapM f⟧ post =
      wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys))) := by
  wp_step

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (post : β → ℝ≥0∞) :
    wp⟦(x :: xs).foldlM f init⟧ post =
      wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post) := by
  wp_step

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  qvcgen_step
  exact hob

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃1⦄ oa ⦃cut⦄) (h2 : ∀ x, ⦃cut x⦄ ob x ⦃post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  qvcgen

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃pre⦄ oa.replicate n ⦃post⦄ := by
  qvcgen_step inv I
  · exact hpre
  · intro xs; exact hpost xs
  · exact hstep

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {z : γ} :
    Pr[= z | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= z | my >>= fun b => mx >>= fun a => f a b] := by
  qvcgen_step

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  qvcgen_step rw congr
  exact h _ ‹_›

example : ⌜(True : Prop)⌝ * ⌜(True : Prop)⌝ = (1 : ℝ≥0∞) := by
  exp_norm

end Unary

/-! ## Relational VCGen examples -/

section Relational

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    (hoa : ⟪oa₁ ~ oa₂ | EqRel α⟫)
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | EqRel β⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | EqRel β⟫ := by
  rvcgen_step
  exact hoa

example (t : spec.Domain) :
    ⟪(liftM (query t) : OracleComp spec (spec.Range t))
     ~ (liftM (query t) : OracleComp spec (spec.Range t))
     | EqRel (spec.Range t)⟫ := by
  rvcgen_step

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | fun x y => y = f x⟫ := by
  rvcgen_step using f
  · exact hf
  · intro x
    rfl

example {oa₁ oa₂ : OracleComp spec α} (n : ℕ)
    (h : ⟪oa₁ ~ oa₂ | EqRel α⟫) :
    ⟪oa₁.replicate n ~ oa₂.replicate n | EqRel (List α)⟫ := by
  rvcgen_step
  exact h

example {xs : List α} {f : α → OracleComp spec β} {g : α → OracleComp spec β}
    (hfg : ∀ a, ⟪f a ~ g a | EqRel β⟫) :
    ⟪xs.mapM f ~ xs.mapM g | EqRel (List β)⟫ := by
  rvcgen_step
  exact hfg

example {xs : List α} {ys : List β}
    {S : α → β → Prop}
    {f : α → OracleComp spec γ} {g : β → OracleComp spec γ}
    {R : RelPost γ γ}
    (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → ⟪f a ~ g b | R⟫) :
    ⟪xs.mapM f ~ ys.mapM g | List.Forall₂ R⟫ := by
  rvcgen_step using S
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
  rvcgen_step
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
  rvcgen_step using Rin
  · exact hs
  · exact hxy
  · exact hfg

example (a : α) :
    ⟪(pure a : OracleComp spec α) ~ (pure a : OracleComp spec α) | EqRel α⟫ := by
  rvcgen_step

example {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    ⟪(pure a : OracleComp spec α) ~ (pure b : OracleComp spec β) | R⟫ := by
  exact Relational.relTriple_pure_pure h

example {c : Prop} [Decidable c]
    {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h1 : ⟪oa₁ ~ ob₁ | EqRel α⟫)
    (h2 : ⟪oa₂ ~ ob₂ | EqRel α⟫) :
    ⟪(if c then oa₁ else oa₂) ~ (if c then ob₁ else ob₂) | EqRel α⟫ := by
  rvcgen_step
  · exact h1
  · exact h2

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq with R
  · exact h
  · exact hpost

end Relational

/-! ## Proof mode entry / exit examples -/

section EntryExit

example {g₁ g₂ g₃ : OracleComp spec α}
    (h₁ : g₁ ≡ₚ g₂) (h₂ : g₂ ≡ₚ g₃) :
    g₁ ≡ₚ g₃ := by
  game_trans g₂
  · exact h₁
  · exact h₂

section ByUpto

variable {σ : Type} {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (oa : OracleComp spec α) (s₀ : σ)
    (h_init : ¬bad s₀)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  by_upto bad
  · exact h_init
  · exact h_agree
  · exact h_mono₁
  · exact h_mono₂

end ByUpto

section RelSim

variable {σ₁ σ₂ : Type} {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    ⟪(simulateQ impl₁ oa).run s₁
     ~ (simulateQ impl₂ oa).run s₂
     | fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2⟫ := by
  rvcgen_step using R_state
  all_goals first | exact himpl | exact hs

example
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    ⟪(simulateQ impl₁ oa).run' s₁
     ~ (simulateQ impl₂ oa).run' s₂
     | EqRel α⟫ := by
  rvcgen_step
  all_goals first | exact himpl | exact hs

end RelSim

section RelSimDist

variable {σ : Type} {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example
    (impl₁ : QueryImpl spec (StateT σ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s : σ),
      evalDist ((impl₁ t).run s) = evalDist ((impl₂ t).run s))
    (s₁ s₂ : σ) (hs : s₁ = s₂) :
    ⟪(simulateQ impl₁ oa).run' s₁
     ~ (simulateQ impl₂ oa).run' s₂
     | EqRel α⟫ := by
  rvcgen_step
  · exact himpl
  · exact hs

end RelSimDist

section GameEquiv

example [SampleableType α]
    (f : α → α) (hf : Function.Bijective f) :
    (f <$> ($ᵗ α : ProbComp α)) ≡ₚ ($ᵗ α : ProbComp α) := by
  conv_rhs => rw [← id_map ($ᵗ α : ProbComp α)]
  by_equiv
  rvcgen
  · exact hf
  · exact rfl

end GameEquiv

section RelDist

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) :
    ⟪oa ~ ob | EqRel α⟫ := by
  rel_dist
  exact h

end RelDist

end EntryExit

/-! ## Probability rewrite examples -/

section Probability

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α β γ δ : Type}

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  qvcgen_step
  exact h _ ‹_›

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {y : γ} :
    Pr[= y | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= y | my >>= fun b => mx >>= fun a => f a b] := by
  qvcgen_step rw

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {mz : OracleComp spec γ} {f : α → β → γ → OracleComp spec δ} {y : δ} :
    Pr[= y | mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
    Pr[= y | mx >>= fun a => mz >>= fun c => my >>= fun b => f a b c] := by
  qvcgen_step rw under 1

end Probability
