/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.StateSeparating

/-!
# State-separating handlers: advantage and `evalDist` congruences

This file contains the probability-facing lower API for
`QueryImpl.Stateful`. It keeps the proof-theory layer close to the SSP
literature while leaving the core handler object as the unbundled
`QueryImpl.Stateful I E σ`.
-/

universe uₑ

open OracleSpec OracleComp ProbComp

namespace QueryImpl.Stateful

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ} {σ : Type}

/-! ## Bridging to `ProbComp` -/

/-- Run a probability-only stateful handler from an explicit initial state. -/
@[reducible]
def runProb {α : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E α) : ProbComp α :=
  h.run s₀ A

/-- Run a probability-only stateful handler from the default initial state. -/
@[reducible]
def runProb₀ {α : Type} [Inhabited σ] (h : QueryImpl.Stateful unifSpec E σ)
    (A : OracleComp E α) : ProbComp α :=
  h.run₀ A

@[simp]
lemma runProb_eq_run {α : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E α) :
    h.runProb s₀ A = h.run s₀ A := rfl

/-! ## Advantage and triangle inequality -/

/-- Boolean distinguishing advantage between two probability-only stateful
handlers, with explicit initial states. -/
noncomputable def advantage {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) : ℝ :=
  (h₀.runProb s₀ A).boolDistAdvantage (h₁.runProb s₁ A)

/-- Boolean distinguishing advantage from default initial states. -/
noncomputable def advantage₀ {σ₀ σ₁ : Type} [Inhabited σ₀] [Inhabited σ₁]
    (h₀ : QueryImpl.Stateful unifSpec E σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁)
    (A : OracleComp E Bool) : ℝ :=
  h₀.advantage default h₁ default A

@[simp]
lemma advantage_self (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) :
    h.advantage s₀ h s₀ A = 0 := by
  simp [advantage, ProbComp.boolDistAdvantage]

lemma advantage_symm {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₁.advantage s₁ h₀ s₀ A := by
  unfold advantage ProbComp.boolDistAdvantage
  exact abs_sub_comm _ _

lemma advantage_eq_of_evalDist_runProb_eq {σ₀ σ₀' σ₁ : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ₀'} {s₀' : σ₀'}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {A : OracleComp E Bool}
    (h_eq : 𝒟[h₀.runProb s₀ A] = 𝒟[h₀'.runProb s₀' A]) :
    h₀.advantage s₀ h₁ s₁ A = h₀'.advantage s₀' h₁ s₁ A := by
  unfold advantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl h_eq]

lemma advantage_eq_of_evalDist_runProb_eq_right {σ₀ σ₁ σ₁' : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ₁'} {s₁' : σ₁'}
    {A : OracleComp E Bool}
    (h_eq : 𝒟[h₁.runProb s₁ A] = 𝒟[h₁'.runProb s₁' A]) :
    h₀.advantage s₀ h₁ s₁ A = h₀.advantage s₀ h₁' s₁' A := by
  unfold advantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl h_eq]

lemma advantage_triangle {σ₀ σ₁ σ₂ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (h₂ : QueryImpl.Stateful unifSpec E σ₂) (s₂ : σ₂)
    (A : OracleComp E Bool) :
    h₀.advantage s₀ h₂ s₂ A ≤
      h₀.advantage s₀ h₁ s₁ A + h₁.advantage s₁ h₂ s₂ A :=
  ProbComp.boolDistAdvantage_triangle _ _ _

/-! ## `evalDist` congruence for handlers -/

lemma simulateQ_evalDist_congr {α : Type}
    {h₁ h₂ : QueryImpl E ProbComp}
    (hh : ∀ (q : E.Domain), 𝒟[h₁ q] = 𝒟[h₂ q])
    (A : OracleComp E α) :
    𝒟[simulateQ h₁ A] = 𝒟[simulateQ h₂ A] := by
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, evalDist_bind]
    rw [hh t]
    refine bind_congr fun u => ?_
    exact ih u

lemma simulateQ_StateT_evalDist_congr {α : Type}
    {h₁ h₂ : QueryImpl E (StateT σ ProbComp)}
    (hh : ∀ (q : E.Domain) (s : σ),
      𝒟[(h₁ q).run s] = 𝒟[(h₂ q).run s])
    (A : OracleComp E α) (s : σ) :
    𝒟[(simulateQ h₁ A).run s] = 𝒟[(simulateQ h₂ A).run s] := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, evalDist_bind]
    rw [hh t s]
    refine bind_congr fun p => ?_
    exact ih p.1 p.2

lemma simulateQ_StateT_evalDist_congr_of_bij {α : Type} {σ₁ σ₂ : Type}
    (h₁ : QueryImpl E (StateT σ₁ ProbComp))
    (h₂ : QueryImpl E (StateT σ₂ ProbComp))
    (φ : σ₁ ≃ σ₂)
    (hh : ∀ (q : E.Domain) (s : σ₁),
      𝒟[(h₁ q).run s] =
      𝒟[Prod.map id φ.symm <$> (h₂ q).run (φ s)])
    (A : OracleComp E α) (s : σ₁) :
    𝒟[(simulateQ h₁ A).run s] =
    𝒟[Prod.map id φ.symm <$> (simulateQ h₂ A).run (φ s)] := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
      Equiv.symm_apply_apply]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind, evalDist_bind, evalDist_map, hh t s]
    simp only [map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨x, s'⟩
    have hih := ih x (φ.symm s')
    rw [Equiv.apply_symm_apply] at hih
    simpa [Prod.map] using hih

/-! ## Functoriality of `runProb` -/

lemma runProb_map {α β : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (f : α → β) (A : OracleComp E α) :
    h.runProb s₀ (f <$> A) = f <$> h.runProb s₀ A := by
  change h.run s₀ (f <$> A) = f <$> h.run s₀ A
  unfold QueryImpl.Stateful.run
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp

end QueryImpl.Stateful
