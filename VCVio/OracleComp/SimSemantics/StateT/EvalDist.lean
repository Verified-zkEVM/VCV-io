/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Distribution Semantics of Simulation through `StateT` Handlers

Bridges between `simulateQ` through a `StateT`-valued `QueryImpl` and the distribution
semantics on `OracleComp` (`evalDist`, `support`, `probOutput`, `probEvent`). The
non-stateful counterpart `evalDist_simulateQ_eq_evalDist` lives in
`VCVio/OracleComp/EvalDist.lean`; the structural identity
`StateT_run'_simulateQ_eq_self` used below is defined in
`VCVio/OracleComp/SimSemantics/StateT/Basic.lean`.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type w}

section simulateQ_evalDist

variable [spec.Fintype] [spec.Inhabited]

/-- If a `StateT` oracle implementation preserves distributions (each oracle query produces a
uniform distribution after discarding state), then `simulateQ` followed by `run'` preserves
`evalDist`. This is the key lemma for security proofs: it shows that stateful oracle
implementations (e.g. counting/logging oracles) don't change outcome probabilities. -/
lemma evalDist_simulateQ_run'_eq_evalDist {σ τ : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec.Domain) (s : σ),
      𝒟[(so t).run' s] = OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (s : σ) (oa : OracleComp spec τ) :
    𝒟[(simulateQ so oa).run' s] = 𝒟[oa] := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp
  | query_bind t mx ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    change 𝒟[Prod.fst <$> ((so t).run s >>= fun p =>
      (simulateQ so (mx p.1)).run p.2)] = _
    rw [@map_bind (OracleComp spec), show (fun p : spec.Range t × σ =>
        Prod.fst <$> (simulateQ so (mx p.1)).run p.2) =
      (fun p => (simulateQ so (mx p.1)).run' p.2) from rfl]
    rw [evalDist_bind]; simp_rw [ih]
    rw [← evalDist_bind]
    rw [show ((so t).run s >>= fun p : spec.Range t × σ => mx p.1) =
      ((so t).run' s >>= mx) from
      (bind_map_left (m := OracleComp spec) Prod.fst ((so t).run s) mx).symm]
    rw [evalDist_bind, h t s]
    change OptionT.lift (PMF.uniformOfFintype (spec.Range t)) >>= (fun u => 𝒟[mx u]) = _
    rw [show (fun u => 𝒟[mx u]) = evalDist ∘ mx from rfl]
    exact (evalDist_query_bind t mx).symm

/-- Stronger version with computational hypothesis: if the implementation passes through
queries exactly, then `simulateQ` preserves `evalDist`. -/
lemma evalDist_simulateQ_run'_of_run'_eq_query {σ τ : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ t s, (so t).run' s = query t)
    (s : σ) (oa : OracleComp spec τ) :
    𝒟[(simulateQ so oa).run' s] = 𝒟[oa] := by
  rw [StateT_run'_simulateQ_eq_self so h]

/-- Corollary for `probOutput`: stateful simulation preserves output probabilities. -/
lemma probOutput_simulateQ_run'_eq {σ τ : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec.Domain) (s : σ),
      𝒟[(so t).run' s] = OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (s : σ) (oa : OracleComp spec τ) (x : τ) :
    Pr[= x | (simulateQ so oa).run' s] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ_run'_eq_evalDist so h s oa)) x

/-- Corollary for `probEvent`: stateful simulation preserves event probabilities. -/
lemma probEvent_simulateQ_run'_eq {σ τ : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec.Domain) (s : σ),
      𝒟[(so t).run' s] = OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (s : σ) (oa : OracleComp spec τ) (p : τ → Prop) :
    Pr[ p | (simulateQ so oa).run' s] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator]
  congr 1; funext x
  simp only [probOutput_simulateQ_run'_eq so h s oa]

lemma evalDist_simulateQ_run_eq_of_impl_evalDist_eq
    {ι' : Type} {spec' : OracleSpec ι'}
    {σ α : Type}
    (impl₁ impl₂ : QueryImpl spec' (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec'.Domain) (s : σ),
      𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    (comp : OracleComp spec' α) (s : σ) :
    𝒟[(simulateQ impl₁ comp).run s] =
      𝒟[(simulateQ impl₂ comp).run s] := by
  revert s
  induction comp using OracleComp.inductionOn with
  | pure _ => intro _; rfl
  | query_bind t oa ih =>
    intro s
    simp only [simulateQ_query_bind, StateT.run_bind]
    rw [evalDist_bind, evalDist_bind]
    congr 1
    · exact h t s
    · funext ⟨u, s'⟩; exact ih u s'

end simulateQ_evalDist

section support_simulateQ_StateT

/-- Simulating an `OracleComp` through a stateful implementation in monad `m` can only shrink the
support: any output reachable after simulation was already reachable in the original computation
(where oracle queries may return any value). This is the support-level analogue of
`evalDist_simulateQ_run'_eq_evalDist`. -/
theorem support_simulateQ_run'_subset
    {m : Type w → Type _} [Monad m] [LawfulMonad m] [HasEvalSet m] {σ : Type w}
    (impl : QueryImpl spec (StateT σ m))
    (oa : OracleComp spec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, support_pure]
    exact Set.Subset.rfl
  | query_bind t k ih =>
    intro x hx
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq] at hx
    rw [support_map] at hx
    obtain ⟨⟨a, s'⟩, hmem, ha⟩ := hx
    rw [StateT.run_bind] at hmem
    rw [support_bind] at hmem
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨⟨u, s''⟩, _, hmem'⟩ := hmem
    have hrun' : a ∈ support ((simulateQ impl (k u)).run' s'') := by
      rw [StateT.run'_eq, support_map]
      exact ⟨(a, s'), hmem', rfl⟩
    have hih := ih u s'' hrun'
    rw [support_bind]
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨u, mem_support_query t u, ha ▸ hih⟩

end support_simulateQ_StateT

end OracleComp
