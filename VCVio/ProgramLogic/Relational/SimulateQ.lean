/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Basic
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.QueryBound
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
variable {α : Type}

/-! ## Relational simulateQ rules -/

/-- Core relational `simulateQ` theorem with state invariant.
If two oracle implementations produce equal outputs and preserve a state invariant `R_state`,
then the full simulation also preserves the invariant and output equality. -/
theorem relTriple_simulateQ_run
    {ι₁ : Type u} {ι₂ : Type u}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
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
    simp only [simulateQ_pure, StateT.run_pure, relTriple_iff_relWP,
      MAlgRelOrdered.relWP_pure, true_and]
    exact hs
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, relTriple_iff_relWP, relWP_iff_couplingPost]
    exact (relTriple_bind (himpl t s₁ s₂ hs) (fun ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨eq_u, hs'⟩ => by
      dsimp at eq_u hs' ⊢; subst eq_u; exact ih u₁ s₁' s₂' hs')) trivial

/-- Projection: relational `simulateQ` preserving only output equality. -/
theorem relTriple_simulateQ_run'
    {ι₁ : Type u} {ι₂ : Type u}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
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

/-- Exact-distribution specialization of `relTriple_simulateQ_run'`.

If corresponding oracle calls have identical full `(output, state)` distributions whenever the
states are equal, then the simulated computations have identical output distributions. This
packages the common pattern "prove per-query `evalDist` equality, then use `Eq` as the state
invariant" into a single theorem. -/
theorem relTriple_simulateQ_run'_of_impl_evalDist_eq
    {ι₁ : Type u} {ι₂ : Type u}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {σ : Type}
    (impl₁ : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s : σ),
      evalDist ((impl₁ t).run s) = evalDist ((impl₂ t).run s))
    (s₁ s₂ : σ) (hs : s₁ = s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run' s₁)
      ((simulateQ impl₂ oa).run' s₂)
      (EqRel α) := by
  refine relTriple_simulateQ_run' impl₁ impl₂ Eq oa ?_ s₁ s₂ hs
  intro t s₁ s₂ hs'
  cases hs'
  exact relTriple_of_evalDist_eq (himpl t s₁) (fun _ => ⟨rfl, rfl⟩)

/-- If two stateful oracle implementations agree on every query while `Inv` holds, and the
second implementation preserves `Inv`, then the full simulations have identical `(output, state)`
distributions from any invariant-satisfying initial state. -/
theorem relTriple_simulateQ_run_of_impl_eq_preservesInv
    {ι : Type} {spec : OracleSpec ι}
    {σ : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (oa : OracleComp spec α)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ), Inv s →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (s : σ) (hs : Inv s) :
    RelTriple
      ((simulateQ impl₁ oa).run s)
      ((simulateQ impl₂ oa).run s)
      (fun p₁ p₂ => p₁ = p₂ ∧ Inv p₁.2) := by
  have hrel :
      RelTriple
        ((simulateQ impl₁ oa).run s)
        ((simulateQ impl₂ oa).run s)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2 ∧ Inv p₁.2) := by
    refine relTriple_simulateQ_run (spec := spec) (spec₁ := unifSpec) (spec₂ := unifSpec)
      impl₁ impl₂ (fun s₁ s₂ => s₁ = s₂ ∧ Inv s₁) oa ?_ s s
      ⟨rfl, hs⟩
    intro t s₁ s₂ hs'
    rcases hs' with ⟨rfl, hs₁⟩
    rw [himpl_eq t s₁ hs₁]
    apply (relTriple_iff_relWP
      (oa := (impl₂ t).run s₁)
      (ob := (impl₂ t).run s₁)
      (R := fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2 ∧ Inv p₁.2)).2
    refine ⟨_root_.SPMF.Coupling.refl (evalDist ((impl₂ t).run s₁)), ?_⟩
    intro z hz
    rcases (mem_support_bind_iff
      (evalDist ((impl₂ t).run s₁))
      (fun a => (pure (a, a) : SPMF ((spec.Range t × σ) × (spec.Range t × σ)))) z).1 hz with
      ⟨a, ha, hz'⟩
    have hzEq : z = (a, a) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    have ha' : a ∈ support ((impl₂ t).run s₁) := by
      simpa [mem_support_iff, probOutput_def] using ha
    have hInv : Inv a.2 := hpres₂ t s₁ hs₁ a ha'
    subst hzEq
    simp [hInv]
  refine relTriple_post_mono hrel ?_
  intro p₁ p₂ hp
  exact ⟨Prod.ext hp.1 hp.2.1, hp.2.2⟩

/-- Exact-equality specialization of `relTriple_simulateQ_run_of_impl_eq_preservesInv`.

This weakens the stronger invariant-carrying postcondition to plain equality on `(output, state)`,
which is the shape consumed directly by probability-transport lemmas and theorem-driven
`rvcgen` steps. -/
theorem relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
    {ι : Type} {spec : OracleSpec ι}
    {σ : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (oa : OracleComp spec α)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ), Inv s →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (s : σ) (hs : Inv s) :
    RelTriple
      ((simulateQ impl₁ oa).run s)
      ((simulateQ impl₂ oa).run s)
      (EqRel (α × σ)) := by
  refine relTriple_post_mono
    (relTriple_simulateQ_run_of_impl_eq_preservesInv
      impl₁ impl₂ Inv oa himpl_eq hpres₂ s hs) ?_
  intro p₁ p₂ hp
  exact hp.1

/-- Output-probability projection of
`relTriple_simulateQ_run_of_impl_eq_preservesInv`. -/
theorem probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
    {ι : Type} {spec : OracleSpec ι}
    {σ : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (oa : OracleComp spec α)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ), Inv s →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (s : σ) (hs : Inv s) (z : α × σ) :
    Pr[= z | (simulateQ impl₁ oa).run s] =
      Pr[= z | (simulateQ impl₂ oa).run s] := by
  have hrel := relTriple_simulateQ_run_of_impl_eq_preservesInv
    impl₁ impl₂ Inv oa himpl_eq hpres₂ s hs
  exact probOutput_eq_of_relTriple_eqRel
    (relTriple_post_mono hrel (fun _ _ hp => hp.1)) z

/-- Query-bounded exact-output transport for `simulateQ`.

If `oa` satisfies a structural query bound `IsQueryBound budget canQuery cost`, the two
implementations agree on every query that the bound permits, and the second implementation
preserves a budget-indexed invariant `Inv`, then the full simulated computations have identical
output-state probabilities from any initial state satisfying `Inv`. -/
theorem probOutput_simulateQ_run_eq_of_impl_eq_queryBound
    {ι : Type} {spec : OracleSpec ι}
    {σ : Type _} {B : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → B → Prop)
    (canQuery : spec.Domain → B → Prop)
    (cost : spec.Domain → B → B)
    (oa : OracleComp spec α)
    (budget : B)
    (hbound : oa.IsQueryBound budget canQuery cost)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ) (b : B),
      Inv s b → canQuery t b → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ) (b : B), Inv s b → canQuery t b →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2 (cost t b))
    (s : σ) (hs : Inv s budget) (z : α × σ) :
    Pr[= z | (simulateQ impl₁ oa).run s] =
      Pr[= z | (simulateQ impl₂ oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s budget z with
  | pure x =>
      simp
  | query_bind t oa ih =>
      rw [isQueryBound_query_bind_iff] at hbound
      rcases hbound with ⟨hcan, hcont⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [himpl_eq t s budget hs hcan]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr fun p => ?_
      by_cases hp : p ∈ support ((impl₂ t).run s)
      · have hs' : Inv p.2 (cost t budget) := hpres₂ t s budget hs hcan p hp
        congr 1
        exact ih p.1 (cost t budget) (hcont p.1) p.2 hs' z
      · simp [(probOutput_eq_zero_iff _ _).2 hp]

/-- State-projection transport for `simulateQ.run`.

If each oracle call under `impl₁` becomes the corresponding `impl₂` call after mapping the state
with `proj`, then the full simulated runs agree under the same projection. -/
theorem map_run_simulateQ_eq_of_query_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) := by
                  refine bind_congr fun x => ?_
                  simpa using ih x.1 x.2
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  exact
                    (bind_map_left (m := ProbComp) (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

/-- `run'` projection corollary of `map_run_simulateQ_eq_of_query_map_eq`. -/
theorem run'_simulateQ_eq_of_query_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq impl₁ impl₂ proj hproj oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

/-- Relational transport corollary of `run'_simulateQ_eq_of_query_map_eq`. -/
theorem relTriple_simulateQ_run'_of_query_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    RelTriple
      ((simulateQ impl₁ oa).run' s)
      ((simulateQ impl₂ oa).run' (proj s))
      (EqRel α) :=
  relTriple_eqRel_of_eq (run'_simulateQ_eq_of_query_map_eq impl₁ impl₂ proj hproj oa s)

/-- Generalized state-projection theorem: if applying `proj` to the state commutes with each
oracle step, then it commutes with the full simulation. Generalizes the `ProbComp` version
to any target spec. -/
theorem map_run_simulateQ_eq_of_query_map_eq'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) := by
                  refine bind_congr fun x => ?_
                  simpa using ih x.1 x.2
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  exact
                    (bind_map_left (m := OracleComp spec') (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

/-- `run'` projection corollary of `map_run_simulateQ_eq_of_query_map_eq'`. -/
theorem run'_simulateQ_eq_of_query_map_eq'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq' impl₁ impl₂ proj hproj oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

/-! ## "Identical until bad" fundamental lemma -/

variable [spec.Fintype] [spec.Inhabited]

private lemma probOutput_simulateQ_run_eq_zero_of_bad
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (h_mono : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀)
    (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    rw [simulateQ_pure]
    show Pr[= (x, s) | (pure a : StateT σ (OracleComp spec) α).run s₀] = 0
    simp only [StateT.run_pure, probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff, not_and]
    rintro rfl rfl
    exact hs h_bad
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, probOutput_eq_zero_iff, support_bind, Set.mem_iUnion, exists_prop,
      Prod.exists, not_exists, not_and]
    intro u s' h_mem
    rw [← probOutput_eq_zero_iff]
    exact ih u s' (h_mono t s₀ h_bad (u, s') h_mem)

private lemma probOutput_simulateQ_run_eq_of_not_bad
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] =
      Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (pure a) s₀ h_bad x s hs,
          probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (pure a) s₀ h_bad x s hs]
    · rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ _ s₀ h_bad x s hs,
          probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ _ s₀ h_bad x s hs]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, h_agree t s₀ h_bad]
      exact tsum_congr (fun ⟨u, s'⟩ => by congr 1; exact ih u s')

private lemma probEvent_not_bad_eq
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[ fun x => ¬bad x.2 | (simulateQ impl₁ oa).run s₀] =
    Pr[ fun x => ¬bad x.2 | (simulateQ impl₂ oa).run s₀] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr (fun ⟨a, s⟩ => ?_)
  split_ifs with h
  · rfl
  · exact probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
      a s h

private lemma probEvent_bad_eq
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] =
    Pr[ bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h1 h2
  have h_not_bad := probEvent_not_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
  have h_not_bad' : Pr[ fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] =
      Pr[ fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] :=
    h_not_bad
  have hne : Pr[ fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top probEvent_le_one
  calc Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀]
      = 1 - Pr[ fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] := by
        rw [← h1]; exact (ENNReal.add_sub_cancel_right hne).symm
    _ = 1 - Pr[ fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] := by
        rw [h_not_bad']
    _ = Pr[ bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
        rw [← h2]; exact ENNReal.add_sub_cancel_right
          (ne_top_of_le_ne_top one_ne_top probEvent_le_one)

/-- The fundamental lemma of game playing: if two oracle implementations agree whenever
a "bad" flag is unset, then the total variation distance between the two simulations
is bounded by the probability that bad gets set.

Both implementations must satisfy a monotonicity condition: once `bad s` holds, it must
remain true in all reachable successor states. Without this, the theorem is false — an
implementation could enter a bad state (where agreement is not required), diverge, and
then return to a non-bad state, producing different outputs with `Pr[bad] = 0`.
Monotonicity is needed on both sides because the proof establishes pointwise equality
`Pr[= (x,s) | sim₁] = Pr[= (x,s) | sim₂]` for all `¬bad s`, which requires ruling out
bad-to-non-bad transitions in each implementation independently. -/
theorem tvDist_simulateQ_le_probEvent_bad
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (oa : OracleComp spec α) (s₀ : σ)
    (h_init : ¬bad s₀)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  classical
  have _hs₀ : ¬bad s₀ := h_init
  let sim₁ := (simulateQ impl₁ oa).run s₀
  let sim₂ := (simulateQ impl₂ oa).run s₀
  have h_eq : ∀ (x : α) (s : σ), ¬bad s →
      Pr[= (x, s) | sim₁] = Pr[= (x, s) | sim₂] :=
    fun x s hs => probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree
      h_mono₁ h_mono₂ oa s₀ x s hs
  have h_bad_eq : Pr[ bad ∘ Prod.snd | sim₁] = Pr[ bad ∘ Prod.snd | sim₂] :=
    probEvent_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
  have h_tv_joint : tvDist sim₁ sim₂ ≤ Pr[ bad ∘ Prod.snd | sim₁].toReal :=
    tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂) (bad ∘ Prod.snd)
      (fun xs hxs => by
        rcases xs with ⟨x, s⟩
        simpa using h_eq x s hxs)
      h_bad_eq
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤ tvDist sim₁ sim₂ := by
    simpa [sim₁, sim₂, StateT.run'] using
      (tvDist_map_le (m := OracleComp spec) (α := α × σ) (β := α) Prod.fst sim₁ sim₂)
  exact le_trans h_map h_tv_joint

/-! ## Distributional "identical until bad"

The `_dist` variant weakens the agreement hypothesis from definitional equality
(`impl₁ t).run s = (impl₂ t).run s`) to distributional equality
(`∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s]`).
This is needed when the two implementations differ intensionally but agree on
output probabilities. -/

open scoped Classical in
private lemma probOutput_simulateQ_run_eq_of_not_bad_dist
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] =
      Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (pure a) s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (pure a) s₀ h_bad x s hs]
    · rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ _ s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ _ s₀ h_bad x s hs]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      have step1 : ∀ (p : spec.Range t × σ),
          Pr[= p | (impl₁ t).run s₀] *
            Pr[= (x, s) | (simulateQ impl₁ (oa p.1)).run p.2] =
          Pr[= p | (impl₁ t).run s₀] *
            Pr[= (x, s) | (simulateQ impl₂ (oa p.1)).run p.2] := by
        intro ⟨u, s'⟩; congr 1; exact ih u s'
      rw [show (∑' p, Pr[= p | (impl₁ t).run s₀] *
          Pr[= (x, s) | (simulateQ impl₁ (oa p.1)).run p.2]) =
          (∑' p, Pr[= p | (impl₁ t).run s₀] *
          Pr[= (x, s) | (simulateQ impl₂ (oa p.1)).run p.2]) from
        tsum_congr step1]
      exact tsum_congr (fun p => by rw [h_agree_dist t s₀ h_bad p])

open scoped Classical in
private lemma probEvent_not_bad_eq_dist
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun x => ¬bad x.2 | (simulateQ impl₁ oa).run s₀] =
    Pr[fun x => ¬bad x.2 | (simulateQ impl₂ oa).run s₀] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr (fun ⟨a, s⟩ => ?_)
  split_ifs with h
  · rfl
  · exact probOutput_simulateQ_run_eq_of_not_bad_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂
      oa s₀ a s h

open scoped Classical in
private lemma probEvent_bad_eq_dist
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] =
    Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h1 h2
  have h_not_bad := probEvent_not_bad_eq_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂ oa s₀
  have h_not_bad' : Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] =
      Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] :=
    h_not_bad
  have hne : Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  calc Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀]
      = 1 - Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] := by
        rw [← h1]; exact (ENNReal.add_sub_cancel_right hne).symm
    _ = 1 - Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] := by
        rw [h_not_bad']
    _ = Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
        rw [← h2]; exact ENNReal.add_sub_cancel_right
          (ne_top_of_le_ne_top (by simp) probEvent_le_one)

open scoped Classical in
/-- Distributional variant of `tvDist_simulateQ_le_probEvent_bad`:
weakens the agreement hypothesis from definitional equality to distributional equality
(pointwise equal output probabilities). -/
theorem tvDist_simulateQ_le_probEvent_bad_dist
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop)
    (oa : OracleComp spec α) (s₀ : σ)
    (_ : ¬bad s₀)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  classical
  let sim₁ := (simulateQ impl₁ oa).run s₀
  let sim₂ := (simulateQ impl₂ oa).run s₀
  have h_eq : ∀ (x : α) (s : σ), ¬bad s →
      Pr[= (x, s) | sim₁] = Pr[= (x, s) | sim₂] :=
    fun x s hs => probOutput_simulateQ_run_eq_of_not_bad_dist impl₁ impl₂ bad h_agree_dist
      h_mono₁ h_mono₂ oa s₀ x s hs
  have h_bad_eq : Pr[bad ∘ Prod.snd | sim₁] = Pr[bad ∘ Prod.snd | sim₂] :=
    probEvent_bad_eq_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂ oa s₀
  have h_tv_joint : tvDist sim₁ sim₂ ≤ Pr[bad ∘ Prod.snd | sim₁].toReal :=
    tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂) (bad ∘ Prod.snd)
      (fun xs hxs => by
        rcases xs with ⟨x, s⟩
        simpa using h_eq x s hxs)
      h_bad_eq
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤ tvDist sim₁ sim₂ := by
    simpa [sim₁, sim₂, StateT.run'] using
      (tvDist_map_le (m := OracleComp spec) (α := α × σ) (β := α) Prod.fst sim₁ sim₂)
  exact le_trans h_map h_tv_joint

end OracleComp.ProgramLogic.Relational
