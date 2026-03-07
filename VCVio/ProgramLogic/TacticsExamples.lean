/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics

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

/-! ## `rel_step` examples -/

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    (hoa : ⟪oa₁ ~ oa₂ | EqRel α⟫)
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | EqRel β⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | EqRel β⟫ := by
  rel_step
  · exact hoa
  · intro a₁ a₂ h; exact hf a₁ a₂ h

/-! ## `rel_rnd` examples -/

example (t : spec.Domain) :
    ⟪(liftM (query t) : OracleComp spec (spec.Range t))
     ~ (liftM (query t) : OracleComp spec (spec.Range t))
     | EqRel (spec.Range t)⟫ := by
  rel_rnd

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

/-! ## `relTriple_if` example -/

example {c : Prop} [Decidable c]
    {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h1 : ⟪oa₁ ~ ob₁ | EqRel α⟫)
    (h2 : ⟪oa₂ ~ ob₂ | EqRel α⟫) :
    ⟪(if c then oa₁ else oa₂) ~ (if c then ob₁ else ob₂) | EqRel α⟫ := by
  apply relTriple_if
  · intro _; exact h1
  · intro _; exact h2

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

/-! ### Transitivity of game equivalence

A chain of game hops: if Game₀ ≡ₚ Game₁ and Game₁ ≡ₚ Game₂, then Game₀ ≡ₚ Game₂.
This is the fundamental tool for multi-step game-hopping proofs. -/
example {g₀ g₁ g₂ : OracleComp spec α}
    (h₁ : g₀ ≡ₚ g₁) (h₂ : g₁ ≡ₚ g₂) :
    g₀ ≡ₚ g₂ := GameEquiv.trans h₁ h₂

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

**Tactics used**: `by_equiv`, `rel_rnd using`, `relTriple_map` -/
example [SampleableType α]
    (mask : α → α → α) (m₁ m₂ : α)
    (h₁ : Function.Bijective (mask m₁))
    (h₂ : Function.Bijective (mask m₂)) :
    (mask m₁ <$> ($ᵗ α : ProbComp α)) ≡ₚ
    (mask m₂ <$> ($ᵗ α : ProbComp α)) := by
  -- Chain: Game(m₁) →[bij] Uniform →[bij⁻¹] Game(m₂)
  exact GameEquiv.trans
    (GameEquiv.map_uniformSample_bij h₁)
    (GameEquiv.symm (GameEquiv.map_uniformSample_bij h₂))

end MiniOTP
