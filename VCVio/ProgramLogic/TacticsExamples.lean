/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics
import VCVio.OracleComp.Constructions.Replicate

/-!
# Examples and Tests for VCGen-Style Tactics

This file validates the step-through tactics defined in `Tactics.lean`
and demonstrates the notation from `Notation.lean`.
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

-- `wp⟦c⟧` for quantitative WP
example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa >>= f⟧ post = wp⟦oa⟧ (fun u => wp⟦f u⟧ post) := by
  wp_step

-- `⦃P⦄ c ⦃Q⦄` for quantitative Hoare triple
example (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    ⦃Pr[p | oa]⦄ oa ⦃fun x => if p x then 1 else 0⦄ := by
  exact triple_probEvent_indicator oa p

-- `⌜P⌝` for Prop → ℝ≥0∞ indicator (like Std.Do's ⌜P⌝ but quantitative)
example (oa : OracleComp spec α) (p : α → Prop) :
    Pr[p | oa] = wp⟦oa⟧ (fun x => ⌜p x⌝) := by
  exact probEvent_eq_wp_propInd oa p

-- `⌜⌝` in postconditions: indicator values
example : ⌜(True : Prop)⌝ = (1 : ℝ≥0∞) := propInd_true
example : ⌜(False : Prop)⌝ = (0 : ℝ≥0∞) := propInd_false

-- Almost-sure correctness: `⦃⌜True⌝⦄ c ⦃fun x => ⌜p x⌝⦄` iff `Pr[p | c] = 1`
example (oa : OracleComp spec α) (p : α → Prop) (h : Pr[p | oa] = 1) :
    ⦃⌜True⌝⦄ oa ⦃fun x => ⌜p x⌝⦄ := by
  rwa [triple_propInd_iff_probEvent_eq_one]

-- `g₁ ≡ₚ g₂` for game equivalence
example {g₁ g₂ : OracleComp spec α} (h : evalDist g₁ = evalDist g₂) :
    g₁ ≡ₚ g₂ := h

-- `⟪c₁ ~ c₂ | R⟫` for pRHL coupling
example (oa : OracleComp spec α) :
    ⟪oa ~ oa | EqRel α⟫ := by
  rel_skip

/-! ## `wp_step` examples -/

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

/-! ## `hoare_step` examples -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  hoare_step
  · exact hoa
  · exact hob

example (x : α) (pre : ℝ≥0∞) (post : α → ℝ≥0∞)
    (h : pre ≤ post x) :
    ⦃pre⦄ (pure x : OracleComp spec α) ⦃post⦄ := by
  hoare_step
  exact h

example (oa : OracleComp spec α) (n : ℕ) (pre : ℝ≥0∞) (post : List α → ℝ≥0∞)
    (h : pre ≤ wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs)))) :
    ⦃pre⦄ oa.replicate (n + 1) ⦃post⦄ := by
  hoare_step
  exact h

example (x : α) (xs : List α) (f : α → OracleComp spec β)
    (pre : ℝ≥0∞) (post : List β → ℝ≥0∞)
    (h : pre ≤ wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys)))) :
    ⦃pre⦄ (x :: xs).mapM f ⦃post⦄ := by
  hoare_step
  exact h

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (pre : ℝ≥0∞) (post : β → ℝ≥0∞)
    (h : pre ≤ wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post)) :
    ⦃pre⦄ (x :: xs).foldlM f init ⦃post⦄ := by
  hoare_step
  exact h

/-! ## `wp_seq` / `hoare_seq` examples -/

example (oa : OracleComp spec α) (f : α → OracleComp spec β)
    (g : β → OracleComp spec γ) (post : γ → ℝ≥0∞) :
    wp⟦oa >>= f >>= g⟧ post = wp⟦oa⟧ (fun a => wp⟦f a⟧ (fun b => wp⟦g b⟧ post)) := by
  wp_seq 2

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {g : β → OracleComp spec γ}
    {pre : ℝ≥0∞} {cut₁ : α → ℝ≥0∞} {cut₂ : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut₁⦄)
    (hof : ∀ a, ⦃cut₁ a⦄ f a ⦃cut₂⦄)
    (hog : ∀ b, ⦃cut₂ b⦄ g b ⦃post⦄) :
    ⦃pre⦄ (oa >>= f >>= g) ⦃post⦄ := by
  hoare_seq 2
  · exact hoa
  · exact hof
  · exact hog

/-! ## `game_hoare` example -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {g : β → OracleComp spec γ}
    {pre : ℝ≥0∞} {cut₁ : α → ℝ≥0∞} {cut₂ : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut₁⦄)
    (hof : ∀ a, ⦃cut₁ a⦄ f a ⦃cut₂⦄)
    (hog : ∀ b, ⦃cut₂ b⦄ g b ⦃post⦄) :
    ⦃pre⦄ (oa >>= f >>= g) ⦃post⦄ := by
  game_hoare
  · exact hoa
  · exact hof
  · exact hog

/-! ## `rel_step` examples -/

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    (hoa : ⟪oa₁ ~ oa₂ | EqRel α⟫)
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | EqRel β⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | EqRel β⟫ := by
  rel_step
  · exact hoa
  · intro a₁ a₂ h; exact hf a₁ a₂ h

/-! ## `rel_seq` examples -/

example {oa : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    {g₁ g₂ : β → OracleComp spec γ}
    {R₁ : RelPost β β} {R₂ : RelPost γ γ}
    (hf : ∀ a, ⟪f₁ a ~ f₂ a | R₁⟫)
    (hg : ∀ b₁ b₂, R₁ b₁ b₂ → ⟪g₁ b₁ ~ g₂ b₂ | R₂⟫) :
    ⟪oa >>= f₁ >>= g₁ ~ oa >>= f₂ >>= g₂ | R₂⟫ := by
  rel_seq 2 using R₁
  · rel_skip
  · intro a₁ a₂ h
    rw [EqRel] at h
    subst h
    exact hf a₁
  · exact hg

/-! ## `rel_rnd` examples -/

example (t : spec.Domain) :
    ⟪(liftM (query t) : OracleComp spec (spec.Range t))
     ~ (liftM (query t) : OracleComp spec (spec.Range t))
     | EqRel (spec.Range t)⟫ := by
  rel_rnd

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | fun x y => y = f x⟫ := by
  rel_rnd
  · exact hf
  · intro x
    rfl

/-! ## `rel_replicate` examples -/

example {oa₁ oa₂ : OracleComp spec α} (n : ℕ)
    (h : ⟪oa₁ ~ oa₂ | EqRel α⟫) :
    ⟪oa₁.replicate n ~ oa₂.replicate n | EqRel (List α)⟫ := by
  rel_replicate
  exact h

example {oa : OracleComp spec α} {ob : OracleComp spec β} (n : ℕ)
    {R : RelPost α β}
    (h : ⟪oa ~ ob | R⟫) :
    ⟪oa.replicate n ~ ob.replicate n | List.Forall₂ R⟫ := by
  rel_replicate
  exact h

/-! ## `rel_mapM` examples -/

example {xs : List α} {f : α → OracleComp spec β} {g : α → OracleComp spec β}
    (hfg : ∀ a, ⟪f a ~ g a | EqRel β⟫) :
    ⟪xs.mapM f ~ xs.mapM g | EqRel (List β)⟫ := by
  rel_mapM
  exact hfg

example {xs : List α} {ys : List β}
    {S : α → β → Prop}
    {f : α → OracleComp spec γ} {g : β → OracleComp spec γ}
    {R : RelPost γ γ}
    (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → ⟪f a ~ g b | R⟫) :
    ⟪xs.mapM f ~ ys.mapM g | List.Forall₂ R⟫ := by
  rel_mapM using S
  · exact hxy
  · exact hfg

/-! ## `rel_foldlM` examples -/

example {σ₁ σ₂ : Type}
    {xs : List α}
    {f : σ₁ → α → OracleComp spec σ₁}
    {g : σ₂ → α → OracleComp spec σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → ⟪f t₁ a ~ g t₂ a | S⟫) :
    ⟪xs.foldlM f s₁ ~ xs.foldlM g s₂ | S⟫ := by
  rel_foldlM
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
  rel_foldlM using Rin
  · exact hs
  · exact hxy
  · exact hfg

/-! ## `rel_skip` examples -/

example (oa : OracleComp spec α) :
    ⟪oa ~ oa | EqRel α⟫ := by
  rel_skip

/-! ## Combined: `rel_step` + `rel_rnd` + `rel_skip` -/

example (t : spec.Domain) (f : spec.Range t → OracleComp spec β)
    (R : RelPost β β)
    (hf : ∀ u, ⟪f u ~ f u | R⟫) :
    ⟪(liftM (query t) : OracleComp spec _) >>= f
     ~ (liftM (query t) : OracleComp spec _) >>= f | R⟫ := by
  rel_step
  · rel_rnd
  · intro a₁ a₂ h; rw [EqRel] at h; subst h; exact hf a₁

/-! ## `wp_step` with `wp_map` -/

example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp⟦f <$> oa⟧ post = wp⟦oa⟧ (post ∘ f) := by
  wp_step

/-! ## `rel_pure` examples -/

example (a : α) :
    ⟪(pure a : OracleComp spec α) ~ (pure a : OracleComp spec α) | EqRel α⟫ := by
  rel_pure

example {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    ⟪(pure a : OracleComp spec α) ~ (pure b : OracleComp spec β) | R⟫ := by
  rel_pure

/-! ## `rel_cond` examples -/

example {c : Prop} [Decidable c]
    {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h1 : ⟪oa₁ ~ ob₁ | EqRel α⟫)
    (h2 : ⟪oa₂ ~ ob₂ | EqRel α⟫) :
    ⟪(if c then oa₁ else oa₂) ~ (if c then ob₁ else ob₂) | EqRel α⟫ := by
  rel_cond
  · exact h1
  · exact h2

/-! ## `rel_conseq` examples -/

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

/-! ## `game_trans` examples -/

example {g₁ g₂ g₃ : OracleComp spec α}
    (h₁ : g₁ ≡ₚ g₂) (h₂ : g₂ ≡ₚ g₃) :
    g₁ ≡ₚ g₃ := by
  game_trans g₂
  · exact h₁
  · exact h₂

/-! ## `by_upto` examples -/

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

/-! ## `rel_sim` examples -/

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
  rel_sim using R_state
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
  rel_sim
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
     | fun x y => x = y⟫ := by
  rel_sim
  all_goals first | exact himpl | exact hs

end RelSim

/-! ## `rel_sim_dist` examples -/

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
  rel_sim_dist
  · exact himpl
  · exact hs

end RelSimDist

/-! ## Multi-step composed example -/

example
    (oa : OracleComp spec α)
    (f g : α → OracleComp spec β)
    (R : RelPost β β)
    (hfg : ∀ a, ⟪f a ~ g a | R⟫) :
    ⟪oa >>= f ~ oa >>= g | R⟫ := by
  rel_step
  · rel_skip
  · intro a₁ a₂ h; rw [EqRel] at h; subst h; exact hfg a₁

/-! -------------------------------------------------------------------
  ## Tier 2: Multi-step relational proofs
  ------------------------------------------------------------------- -/

/-! ### Sequential coupling with `rel_step using`

Two programs sample, then apply *different* continuations.
We couple the samples with `EqRel` (via `rel_step`), then discharge each
continuation independently. Uses `rel_step using` for the explicit intermediate
relation. -/
example
    (oa : OracleComp spec α)
    (f₁ f₂ : α → OracleComp spec β)
    (g₁ g₂ : β → OracleComp spec γ)
    (R₁ : RelPost β β)
    (R₂ : RelPost γ γ)
    (hf : ⟪oa >>= f₁ ~ oa >>= f₂ | R₁⟫)
    (hg : ∀ b₁ b₂, R₁ b₁ b₂ → ⟪g₁ b₁ ~ g₂ b₂ | R₂⟫) :
    ⟪oa >>= f₁ >>= g₁ ~ oa >>= f₂ >>= g₂ | R₂⟫ := by
  rel_step using R₁
  · exact hf
  · exact hg

/-! ### Bijective coupling for uniform sampling

If `f` is a bijection, then sampling `x` uniformly and sampling `f x` uniformly
produce related outputs under `R x (f x)`. -/
example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | (fun x y => y = f x)⟫ := by
  exact relTriple_uniformSample_bij hf _ (fun x => rfl)

/-! ### Coupling with non-trivial intermediate relation

We can also couple two programs where the first halves are related by a
*non-equality* relation, as long as the continuations respect that relation. -/
example (oa ob : OracleComp spec α)
    (fa fb : α → OracleComp spec β)
    (R : RelPost α α)
    (S : RelPost β β)
    (hxy : ⟪oa ~ ob | R⟫)
    (hfg : ∀ a b, R a b → ⟪fa a ~ fb b | S⟫) :
    ⟪oa >>= fa ~ ob >>= fb | S⟫ := by
  exact relTriple_bind hxy hfg

/-! -------------------------------------------------------------------
  ## Tier 3: Game equivalence and game-hopping
  ------------------------------------------------------------------- -/

section GameEquiv

/-! ### Mini "perfect secrecy" via bijective coupling

**Setup**: For any type `α` with `SampleableType` (so `$ᵗ α` is uniform), and any
bijection `f : α → α`, the game that samples `x` and returns `f x` has the same
distribution as sampling `x` directly.

**Proof**: Lift to relational mode with `GameEquiv.of_relTriple`, then apply
`relTriple_map` + `relTriple_uniformSample_bij`. This is the core pattern behind
OTP-style perfect secrecy proofs — a bijection on a uniform sample is still uniform. -/
example [SampleableType α]
    (f : α → α) (hf : Function.Bijective f) :
    (f <$> ($ᵗ α : ProbComp α)) ≡ₚ ($ᵗ α : ProbComp α) := by
  conv_rhs => rw [← id_map ($ᵗ α : ProbComp α)]
  apply GameEquiv.of_relTriple
  apply relTriple_map
  exact relTriple_uniformSample_bij hf _ (fun _ => rfl)

/-! ### Two-step game hop: factor through an intermediate game

Game A: sample `x`, sample `y`, return `(x, y)`
Game B: sample `y`, sample `x`, return `(x, y)`

They are equivalent because uniform sampling is independent (order doesn't matter).
The proof uses `prob_swap` to reorder the binds. -/
example [SampleableType α] [SampleableType β] :
    (do let x ← ($ᵗ α : ProbComp α); let y ← ($ᵗ β : ProbComp β); pure (x, y)) ≡ₚ
    (do let y ← ($ᵗ β : ProbComp β); let x ← ($ᵗ α : ProbComp α); pure (x, y)) := by
  unfold GameEquiv
  apply evalDist_ext; intro t
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  exact probEvent_bind_bind_swap _ _ _ _

/-! ### Game hop with conditional branching

Game A: flip a coin; if heads, return `oa`; if tails, return `ob`.
Game B: same structure.
If both branches are individually equivalent, the full games are equivalent. -/
example {c : Prop} [Decidable c]
    {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h_heads : oa₁ ≡ₚ oa₂) (h_tails : ob₁ ≡ₚ ob₂) :
    (if c then oa₁ else ob₁) ≡ₚ (if c then oa₂ else ob₂) := by
  split_ifs <;> assumption

end GameEquiv

/-! -------------------------------------------------------------------
  ## Tier 4: Game-hopping chain
  ------------------------------------------------------------------- -/

section GameHopping

/-! ### Transitivity of game equivalence via `game_trans`

A chain of game hops: if Game₀ ≡ₚ Game₁ and Game₁ ≡ₚ Game₂, then Game₀ ≡ₚ Game₂.
This is the fundamental tool for multi-step game-hopping proofs. -/
example {g₀ g₁ g₂ : OracleComp spec α}
    (h₁ : g₀ ≡ₚ g₁) (h₂ : g₁ ≡ₚ g₂) :
    g₀ ≡ₚ g₂ := by
  game_trans g₁
  · exact h₁
  · exact h₂

/-! ### Relational coupling via `game_rel'`

When both sides are identical, `game_rel'` automatically decomposes
through all the bind/query structure and closes everything by reflexivity. -/
example (t₁ t₂ : spec.Domain)
    (f : spec.Range t₁ → spec.Range t₂ → OracleComp spec α) :
    ⟪(do let x ← (liftM (query t₁) : OracleComp spec _)
         let y ← (liftM (query t₂) : OracleComp spec _)
         f x y)
     ~ (do let x ← (liftM (query t₁) : OracleComp spec _)
           let y ← (liftM (query t₂) : OracleComp spec _)
           f x y)
     | EqRel α⟫ := by
  game_rel'

/-! ### Probability preservation under game equivalence

Once we have `g₁ ≡ₚ g₂`, any probability statement about `g₁` transfers to `g₂`.
This is how game hops let us reason about the original game by analyzing the
final (simpler) game. -/
example {g₁ g₂ : OracleComp spec α} (h : g₁ ≡ₚ g₂) (x : α) :
    Pr[= x | g₁] = Pr[= x | g₂] := GameEquiv.probOutput_eq h x

/-! ### Composing game equivalences with different post-processing

If two games are equivalent, we can compose them with the same post-processing
and maintain equivalence. This is the "compatible games" pattern used in
all standard game-hopping arguments. -/
example {g₁ g₂ : OracleComp spec α}
    (h : g₁ ≡ₚ g₂) (f : α → OracleComp spec β) :
    (g₁ >>= f) ≡ₚ (g₂ >>= f) := by
  show evalDist (g₁ >>= f) = evalDist (g₂ >>= f)
  rw [evalDist_bind, evalDist_bind, h]

end GameHopping

/-! -------------------------------------------------------------------
  ## Tier 5: Putting it all together — mini OTP privacy
  ------------------------------------------------------------------- -/

section MiniOTP

/-! ### XOR-mask perfect secrecy (abstract version)

This is a miniature version of the OTP perfect secrecy proof.
Given any bijection `mask : α → α → α` (like XOR) where for any fixed `m`,
`mask m ·` is a bijection, we prove that masking a message with a random key
produces a distribution independent of the message.

**Game hops**:
```
Game(m₁): mask m₁ <$> $ᵗ α
   ≡ₚ (bijection on uniform = uniform)
Uniform: $ᵗ α
   ≡ₚ (reverse)
Game(m₂): mask m₂ <$> $ᵗ α
```

**Tactics used**: `game_trans`, `GameEquiv.map_uniformSample_bij` -/
example [SampleableType α]
    (mask : α → α → α) (m₁ m₂ : α)
    (h₁ : Function.Bijective (mask m₁))
    (h₂ : Function.Bijective (mask m₂)) :
    (mask m₁ <$> ($ᵗ α : ProbComp α)) ≡ₚ
    (mask m₂ <$> ($ᵗ α : ProbComp α)) := by
  game_trans ($ᵗ α : ProbComp α)
  · exact GameEquiv.map_uniformSample_bij h₁
  · exact GameEquiv.symm (GameEquiv.map_uniformSample_bij h₂)

end MiniOTP

/-! ## `rel_dist` examples -/

section RelDist

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α : Type}

/-- `rel_dist` reduces a `RelTriple` goal to `evalDist` equality. -/
example {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) :
    ⟪oa ~ ob | EqRel α⟫ := by
  rel_dist
  exact h

end RelDist

/-! ## `prob_congr` examples -/

section ProbCongr

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-- `prob_congr` decomposes a bind congruence into a pointwise subgoal. -/
example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  prob_congr
  exact h

/-- `prob_congr'` variant without support restriction. -/
example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  prob_congr'
  exact h

end ProbCongr

/-! ## `prob_swap_rw` examples -/

section ProbSwapRw

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]

/-- `prob_swap_rw` rewrites the swap and leaves the goal open for further work. -/
example {α β γ : Type} {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {y : γ} :
    Pr[= y | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= y | my >>= fun b => mx >>= fun a => f a b] := by
  prob_swap_rw

end ProbSwapRw
