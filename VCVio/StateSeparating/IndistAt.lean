/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.StateSeparating.Hybrid

/-!
# State-separating handlers: ε-indistinguishability

`QueryImpl.Stateful.IndistAt h₀ s₀ h₁ s₁ ε` bounds the Boolean
distinguishing advantage between two stateful handlers from explicit initial
states.
-/

universe uₑ uₘ

open OracleSpec OracleComp

namespace QueryImpl.Stateful

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- ε-bounded indistinguishability of two stateful handlers from explicit
initial states. -/
def IndistAt {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁) (ε : ℝ) : Prop :=
  ∀ (A : OracleComp E Bool), h₀.advantage s₀ h₁ s₁ A ≤ ε

@[inherit_doc IndistAt]
scoped notation:50 "(" h₀ ", " s₀ ")" " ≈ᵈ[" ε "] " "(" h₁ ", " s₁ ")" =>
  QueryImpl.Stateful.IndistAt h₀ s₀ h₁ s₁ ε

namespace IndistAt

variable {σ σ₀ σ₁ σ₂ : Type}

protected theorem refl (h : QueryImpl.Stateful unifSpec E σ) (s : σ) :
    (h, s) ≈ᵈ[0] (h, s) := by
  intro A
  rw [advantage_self]

protected theorem symm
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) : (h₁, s₁) ≈ᵈ[ε] (h₀, s₀) := fun A => by
  rw [advantage_symm]
  exact h A

protected theorem trans
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₂ : QueryImpl.Stateful unifSpec E σ₂} {s₂ : σ₂} {ε₀ ε₁ : ℝ}
    (h₀₁ : (h₀, s₀) ≈ᵈ[ε₀] (h₁, s₁)) (h₁₂ : (h₁, s₁) ≈ᵈ[ε₁] (h₂, s₂)) :
    (h₀, s₀) ≈ᵈ[ε₀ + ε₁] (h₂, s₂) :=
  fun A => (advantage_triangle h₀ s₀ h₁ s₁ h₂ s₂ A).trans
    (add_le_add (h₀₁ A) (h₁₂ A))

/-! ## ε-monotonicity -/

theorem mono
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε ε' : ℝ}
    (h_le : ε ≤ ε') (h : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) :
    (h₀, s₀) ≈ᵈ[ε'] (h₁, s₁) := fun A => (h A).trans h_le

theorem refl_le {ε : ℝ} (h : QueryImpl.Stateful unifSpec E σ) (s : σ) (hε : 0 ≤ ε) :
    (h, s) ≈ᵈ[ε] (h, s) :=
  IndistAt.mono hε (IndistAt.refl h s)

/-! ## Bridge from `DistEquiv` -/

theorem of_distEquiv
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) : (h₀, s₀) ≈ᵈ[0] (h₁, s₁) := fun A => by
  rw [DistEquiv.advantage_zero h]

theorem distEquiv_left
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ} {s₀' : σ}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (h₀, s₀) ≡ᵈ (h₀', s₀'))
    (hi : (h₀', s₀') ≈ᵈ[ε] (h₁, s₁)) :
    (h₀, s₀) ≈ᵈ[ε] (h₁, s₁) := fun A => by
  rw [DistEquiv.advantage_left h h₁ s₁]
  exact hi A

theorem distEquiv_right
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ} {s₁' : σ} {ε : ℝ}
    (h : (h₁, s₁) ≡ᵈ (h₁', s₁'))
    (hi : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) :
    (h₀, s₀) ≈ᵈ[ε] (h₁', s₁') := fun A => by
  rw [← DistEquiv.advantage_right h₀ s₀ h]
  exact hi A

/-! ## Bridge to advantage -/

theorem advantage_le
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A ≤ ε := h A

theorem of_advantage_le
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : ∀ (A : OracleComp E Bool), h₀.advantage s₀ h₁ s₁ A ≤ ε) :
    (h₀, s₀) ≈ᵈ[ε] (h₁, s₁) := h

/-! ## Hybrid and compositional bounds -/

theorem hybrid {n : ℕ} {σ : ℕ → Type} {ε : ℕ → ℝ}
    (h : (i : ℕ) → QueryImpl.Stateful unifSpec E (σ i))
    (s : (i : ℕ) → σ i)
    (hh : ∀ i ∈ Finset.range n, (h i, s i) ≈ᵈ[ε i] (h (i + 1), s (i + 1))) :
    (h 0, s 0) ≈ᵈ[∑ i ∈ Finset.range n, ε i] (h n, s n) := fun A =>
  (advantage_hybrid h s A n).trans (Finset.sum_le_sum (fun i hi => hh i hi A))

section LinkCongr

variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}
variable {σ_P : Type}

theorem link_inner_congr (outer : QueryImpl.Stateful M E σ_P) (sP : σ_P)
    {inner₀ : QueryImpl.Stateful unifSpec M σ₀} {s₀ : σ₀}
    {inner₁ : QueryImpl.Stateful unifSpec M σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (inner₀, s₀) ≈ᵈ[ε] (inner₁, s₁)) :
    (outer.link inner₀, (sP, s₀)) ≈ᵈ[ε] (outer.link inner₁, (sP, s₁)) := by
  intro A
  rw [advantage_link_left_eq_advantage_shiftLeft]
  exact h (outer.shiftLeft sP A)

end LinkCongr

end IndistAt

end QueryImpl.Stateful
