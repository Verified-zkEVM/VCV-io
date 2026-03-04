/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Quantitative
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Relational `simulateQ` Rules

This file provides the highest-leverage theorems for game-hopping proofs:
relational coupling through oracle simulation, and the "identical until bad" lemma.

## Main results

- `relTriple_simulateQ_run`: If two stateful oracle implementations are related by a state
  invariant and produce equal outputs, then simulating a computation with either implementation
  preserves the invariant and output equality.
- `relTriple_simulateQ_run'`: Projection that only asserts output equality.
- `tvDist_simulateQ_le_probEvent_bad`: "Identical until bad" — if two oracle implementations
  agree whenever a "bad" flag is unset, the TV distance between their simulations is bounded
  by the probability of bad being set.
-/

open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

/-! ## Relational simulateQ rules -/

/-- Core relational `simulateQ` theorem with state invariant.
If two oracle implementations produce equal outputs and preserve a state invariant `R_state`,
then the full simulation also preserves the invariant and output equality. -/
theorem relTriple_simulateQ_run
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run s₁)
      ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x =>
    simp
<<<<<<< Current (Your changes)
    exact hs
  | query_bind t oa ih =>
    simp [StateT.run_bind]
    exact (relTriple_bind (himpl t s₁ s₂ hs) (fun ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨eq_u, hs'⟩ => by
      dsimp at eq_u hs' ⊢; subst eq_u; exact ih u₁ s₁' s₂' hs')) trivial
=======
    apply MAlgRelOrdered.triple_pure
    exact ⟨rfl, hs⟩
  | query_bind t oa ih =>
    simp [StateT.run_bind]
    apply relTriple_bind (himpl t s₁ s₂ hs)
    intro ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨eq_u, hs'⟩
    dsimp at eq_u hs' ⊢
    subst eq_u
    exact ih u₁ s₁' s₂' hs'
>>>>>>> Incoming (Background Agent changes)

-- TODO: move to Relational/Basic.lean
private lemma relTriple_map {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {α β γ δ : Type} {R : RelPost γ δ}
    {f : α → γ} {g : β → δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple oa ob (fun a b => R (f a) (g b))) :
    RelTriple (f <$> oa) (g <$> ob) R := by
  have h1 : RelWP oa ob (fun a b => R (f a) (g b)) ≤ RelWP oa (g <$> ob) (fun a d => R (f a) d) :=
    MAlgRelOrdered.relWP_map_right g oa ob _
  have h2 : RelWP oa (g <$> ob) (fun a d => R (f a) d) ≤ RelWP (f <$> oa) (g <$> ob) R :=
    MAlgRelOrdered.relWP_map_left f oa (g <$> ob) _
  exact le_trans h (le_trans h1 h2)

/-- Projection: relational `simulateQ` preserving only output equality. -/
theorem relTriple_simulateQ_run'
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run' s₁)
      ((simulateQ impl₂ oa).run' s₂)
      (EqRel α) := by
  have h := relTriple_simulateQ_run impl₁ impl₂ R_state oa himpl s₁ s₂ hs
  have h_weak : RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => (EqRel α) (Prod.fst p₁) (Prod.fst p₂)) := by
    apply relTriple_post_mono h
    intro p₁ p₂ hp
    exact hp.1
  exact relTriple_map h_weak

/-! ## "Identical until bad" fundamental lemma -/

private lemma probOutput_simulateQ_run_eq_zero_of_bad
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_mono : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀)
    (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp [probOutput_eq_zero_iff]
    intro h_eq
    subst h_eq
    exact hs h_bad
  | query_bind t oa ih =>
    simp [StateT.run_bind, probOutput_bind_eq_tsum]
    apply ENNReal.tsum_eq_zero.mpr
    intro u
    by_cases h_u : u ∈ support ((impl t).run s₀)
    · have h_bad_u := h_mono t s₀ h_bad u h_u
      have ih_u := ih u.1 u.2 h_bad_u
      rw [ih_u, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support h_u, zero_mul]

private lemma probOutput_simulateQ_run_eq_of_not_bad
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] = Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    by_cases h_bad : bad s₀
    · have hz1 := probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (pure a) s₀ h_bad x s hs
      have hz2 := probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (pure a) s₀ h_bad x s hs
      rw [hz1, hz2]
    · rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · have hz1 := probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (query t >>= oa) s₀ h_bad x s hs
      have hz2 := probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (query t >>= oa) s₀ h_bad x s hs
      rw [hz1, hz2]
    · simp [StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      have eq_impl : (impl₁ t).run s₀ = (impl₂ t).run s₀ := h_agree t s₀ h_bad
      rw [eq_impl]
      refine ENNReal.tsum_congr (fun u => ?_)
      congr 1
      exact ih u.1 u.2

private lemma probEvent_not_bad_eq
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun x => ¬bad x.2 | (simulateQ impl₁ oa).run s₀] =
    Pr[fun x => ¬bad x.2 | (simulateQ impl₂ oa).run s₀] := by
  have hz1 := probEvent_eq_tsum_ite ((simulateQ impl₁ oa).run s₀) (fun x => ¬bad x.2)
  have hz2 := probEvent_eq_tsum_ite ((simulateQ impl₂ oa).run s₀) (fun x => ¬bad x.2)
  rw [hz1, hz2]
  refine ENNReal.tsum_congr (fun x => ?_)
  split_ifs with h_not_bad
  · exact probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀ x.1 x.2 h_not_bad
  · rfl

private lemma probEvent_bad_eq
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] =
    Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  have h_fail₁ : Pr[⊥ | (simulateQ impl₁ oa).run s₀] = 0 := HasEvalPMF.probFailure_eq_zero
  have h_fail₂ : Pr[⊥ | (simulateQ impl₂ oa).run s₀] = 0 := HasEvalPMF.probFailure_eq_zero
  rw [h_fail₁, tsub_zero] at h1
  rw [h_fail₂, tsub_zero] at h2
  have h_not_bad := probEvent_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
  -- Pr[bad] + Pr[¬bad] = 1, since Pr[¬bad] match, Pr[bad] match.
  sorry

/-- The fundamental lemma of game playing: if two oracle implementations agree whenever
a "bad" flag is unset, then the total variation distance between the two simulations
is bounded by the probability that bad gets set.

NOTE: This theorem requires a monotonicity assumption on `bad`, otherwise it is false.
For details, see `PROMPT_04B_BLOCKER.md`. -/
theorem tvDist_simulateQ_le_probEvent_bad
    {σ : Type}
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
  let sim₁ := (simulateQ impl₁ oa).run s₀
  let sim₂ := (simulateQ impl₂ oa).run s₀
  have h_map := tvDist_map_le (m := OracleComp spec) Prod.fst sim₁ sim₂
  have h_eq : ∀ x, ¬bad x.2 → Pr[= x | sim₁] = Pr[= x | sim₂] := by
    intro x hx
    exact probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀ x hx
  
  have h_bad_eq : Pr[bad ∘ Prod.snd | sim₁] = Pr[bad ∘ Prod.snd | sim₂] :=
    probEvent_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
    
  -- We now just need to use `h_eq` and `h_bad_eq` to bound `PMF.etvDist`.
  -- PMF.etvDist p q = (1/2) * ∑' x, |p x - q x|
  -- The terms where ¬bad x.2 match exactly, so absDiff is 0.
  -- For terms where bad x.2, |p x - q x| ≤ p x + q x.
  -- Summing these gives Pr[bad | p] + Pr[bad | q] = 2 * Pr[bad | p].
  -- Dividing by 2 gives exactly Pr[bad | p].
  sorry



end OracleComp.ProgramLogic.Relational
