/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.StateSeparating.Advantage

/-!
# State-separating handlers: distributional equivalence

`QueryImpl.Stateful.DistEquiv h₀ s₀ h₁ s₁` says that two stateful handlers,
started from explicit initial states, produce the same output distribution
against every client computation.
-/

universe uᵢ uₑ uₘ

open OracleSpec OracleComp

namespace QueryImpl.Stateful

variable {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, 0} ιᵢ}
variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- Perfect distributional equivalence of two stateful handlers from explicit
initial states. -/
def DistEquiv [I.Fintype] [I.Inhabited] {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful I E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful I E σ₁) (s₁ : σ₁) : Prop :=
  ∀ {α : Type} (A : OracleComp E α),
    𝒟[h₀.run s₀ A] = 𝒟[h₁.run s₁ A]

@[inherit_doc DistEquiv]
scoped notation:50 "(" h₀ ", " s₀ ")" " ≡ᵈ " "(" h₁ ", " s₁ ")" =>
  QueryImpl.Stateful.DistEquiv h₀ s₀ h₁ s₁

/-- Perfect distributional equivalence from default initial states. -/
def DistEquiv₀ [I.Fintype] [I.Inhabited] {σ₀ σ₁ : Type}
    [Inhabited σ₀] [Inhabited σ₁]
    (h₀ : QueryImpl.Stateful I E σ₀) (h₁ : QueryImpl.Stateful I E σ₁) : Prop :=
  QueryImpl.Stateful.DistEquiv h₀ default h₁ default

@[inherit_doc DistEquiv₀]
scoped infix:50 " ≡ᵈ₀ " => QueryImpl.Stateful.DistEquiv₀

namespace DistEquiv

variable {σ σ₀ σ₁ σ₂ : Type}
variable [I.Fintype] [I.Inhabited]

private lemma simulateQ_StateT_evalDist_congr_import {α : Type}
    {h₀ h₁ : QueryImpl E (StateT σ (OracleComp I))}
    (hh : ∀ (q : E.Domain) (s : σ),
      𝒟[(h₀ q).run s] = 𝒟[(h₁ q).run s])
    (A : OracleComp E α) (s : σ) :
    𝒟[(simulateQ h₀ A).run s] = 𝒟[(simulateQ h₁ A).run s] := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, evalDist_bind]
    rw [hh t s]
    refine bind_congr fun p => ?_
    exact ih p.1 p.2

/-! ## Relation laws -/

protected theorem refl (h : QueryImpl.Stateful I E σ) (s : σ) :
    (h, s) ≡ᵈ (h, s) := fun _ => rfl

protected theorem symm
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) : (h₁, s₁) ≡ᵈ (h₀, s₀) :=
  fun A => (h A).symm

protected theorem trans
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    {h₂ : QueryImpl.Stateful I E σ₂} {s₂ : σ₂}
    (h₀₁ : (h₀, s₀) ≡ᵈ (h₁, s₁)) (h₁₂ : (h₁, s₁) ≡ᵈ (h₂, s₂)) :
    (h₀, s₀) ≡ᵈ (h₂, s₂) :=
  fun A => (h₀₁ A).trans (h₁₂ A)

/-! ## Constructors -/

theorem of_run_evalDist
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    (h : ∀ {α : Type} (A : OracleComp E α),
      𝒟[h₀.run s₀ A] = 𝒟[h₁.run s₁ A]) :
    (h₀, s₀) ≡ᵈ (h₁, s₁) := fun A => h A

theorem run_evalDist_eq
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) {α : Type} (A : OracleComp E α) :
    𝒟[h₀.run s₀ A] = 𝒟[h₁.run s₁ A] := h A

theorem run₀_evalDist_eq
    {h₀ : QueryImpl.Stateful I E σ₀} {h₁ : QueryImpl.Stateful I E σ₁}
    [Inhabited σ₀] [Inhabited σ₁]
    (h : h₀ ≡ᵈ₀ h₁) {α : Type} (A : OracleComp E α) :
    𝒟[h₀.run₀ A] = 𝒟[h₁.run₀ A] :=
  h A

theorem runProb_evalDist_eq
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) {α : Type} (A : OracleComp E α) :
    𝒟[h₀.runProb s₀ A] = 𝒟[h₁.runProb s₁ A] := by
  rw [runProb_eq_run, runProb_eq_run]
  exact h A

theorem runProb₀_evalDist_eq
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {h₁ : QueryImpl.Stateful unifSpec E σ₁}
    [Inhabited σ₀] [Inhabited σ₁]
    (h : h₀ ≡ᵈ₀ h₁) {α : Type} (A : OracleComp E α) :
    𝒟[h₀.runProb₀ A] = 𝒟[h₁.runProb₀ A] := by
  rw [runProb₀, runProb₀]
  exact run₀_evalDist_eq h A

theorem of_run_eq
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    (h : ∀ {α : Type} (A : OracleComp E α), h₀.run s₀ A = h₁.run s₁ A) :
    (h₀, s₀) ≡ᵈ (h₁, s₁) :=
  fun A => by rw [h A]

theorem of_step
    {h₀ h₁ : QueryImpl.Stateful I E σ}
    (h_impl : ∀ (q : E.Domain) (s : σ),
      𝒟[(h₀ q).run s] = 𝒟[(h₁ q).run s])
    (s₀ : σ) :
    (h₀, s₀) ≡ᵈ (h₁, s₀) := by
  intro α A
  unfold QueryImpl.Stateful.run
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  exact simulateQ_StateT_evalDist_congr_import h_impl A s₀

theorem of_step_bij
    (h₀ : QueryImpl.Stateful unifSpec E σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (φ : σ₀ ≃ σ₁)
    (h_impl : ∀ (q : E.Domain) (s : σ₀),
      𝒟[(h₀ q).run s] =
        𝒟[Prod.map id φ.symm <$> (h₁ q).run (φ s)])
    (s₀ : σ₀) :
    (h₀, s₀) ≡ᵈ (h₁, φ s₀) := by
  intro α A
  unfold QueryImpl.Stateful.run
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  have hbij := simulateQ_StateT_evalDist_congr_of_bij h₀ h₁ φ h_impl A s₀
  rw [hbij, evalDist_map]
  simp only [Functor.map_map, Prod.map_fst, id_eq]

/-! ## Bridge to advantage -/

theorem advantage_left
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ} {s₀' : σ}
    (h : (h₀, s₀) ≡ᵈ (h₀', s₀'))
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₀'.advantage s₀' h₁ s₁ A :=
  advantage_eq_of_evalDist_runProb_eq (h A)

theorem advantage_right
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ} {s₁' : σ}
    (h : (h₁, s₁) ≡ᵈ (h₁', s₁')) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₀.advantage s₀ h₁' s₁' A :=
  advantage_eq_of_evalDist_runProb_eq_right (h A)

theorem advantage_zero
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = 0 := by
  rw [advantage_left h h₁ s₁ A, advantage_self]

/-! ## Compositional congruences -/

section LinkCongr

variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}
variable {σ_P : Type}

theorem link_inner_congr (outer : QueryImpl.Stateful M E σ_P) (sP : σ_P)
    {inner₀ : QueryImpl.Stateful unifSpec M σ₀} {s₀ : σ₀}
    {inner₁ : QueryImpl.Stateful unifSpec M σ₁} {s₁ : σ₁}
    (h : (inner₀, s₀) ≡ᵈ (inner₁, s₁)) :
    (outer.link inner₀, (sP, s₀)) ≡ᵈ (outer.link inner₁, (sP, s₁)) := by
  intro α A
  change 𝒟[(outer.link inner₀).runProb (sP, s₀) A] =
    𝒟[(outer.link inner₁).runProb (sP, s₁) A]
  rw [runProb_eq_run, runProb_eq_run, run_link_eq_run_shiftLeft,
    run_link_eq_run_shiftLeft]
  exact h (outer.shiftLeft sP A)

end LinkCongr

section ParCongr

variable {ιᵢ₁ : Type uₘ} {ιᵢ₂ : Type uₘ}
  {I₁ : OracleSpec.{uₘ, 0} ιᵢ₁} {I₂ : OracleSpec.{uₘ, 0} ιᵢ₂}
  [I₁.Fintype] [I₁.Inhabited] [I₂.Fintype] [I₂.Inhabited]
  {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {E₁ : OracleSpec.{uₑ, 0} ιₑ₁} {E₂ : OracleSpec.{uₑ, 0} ιₑ₂}
  {σ₁ σ₂ : Type}

/-- `par` congruence on both sides from per-factor handler equivalences with
explicit initial states. -/
theorem par_congr
    {h₁ h₁' : QueryImpl.Stateful I₁ E₁ σ₁} {s₁ : σ₁}
    {h₂ h₂' : QueryImpl.Stateful I₂ E₂ σ₂} {s₂ : σ₂}
    (hh₁ : ∀ (q : E₁.Domain) (s : σ₁),
      𝒟[(h₁ q).run s] = 𝒟[(h₁' q).run s])
    (hh₂ : ∀ (q : E₂.Domain) (s : σ₂),
      𝒟[(h₂ q).run s] = 𝒟[(h₂' q).run s]) :
    (h₁.par h₂, (s₁, s₂)) ≡ᵈ (h₁'.par h₂', (s₁, s₂)) := by
  refine of_step ?_ (s₁, s₂)
  intro q s
  rcases q with t | t
  · change 𝒟[(Prod.map id (·, s.2)) <$> liftComp ((h₁ t).run s.1) (I₁ + I₂)] =
      𝒟[(Prod.map id (·, s.2)) <$> liftComp ((h₁' t).run s.1) (I₁ + I₂)]
    refine evalDist_map_eq_of_evalDist_eq ?_ _
    rw [evalDist_liftComp, evalDist_liftComp]
    exact hh₁ t s.1
  · change 𝒟[(Prod.map id (s.1, ·)) <$> liftComp ((h₂ t).run s.2) (I₁ + I₂)] =
      𝒟[(Prod.map id (s.1, ·)) <$> liftComp ((h₂' t).run s.2) (I₁ + I₂)]
    refine evalDist_map_eq_of_evalDist_eq ?_ _
    rw [evalDist_liftComp, evalDist_liftComp]
    exact hh₂ t s.2

end ParCongr

end DistEquiv

end QueryImpl.Stateful
