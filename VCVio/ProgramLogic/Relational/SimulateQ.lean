/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Basic
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateProjection
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

/-! ### `WriterT` analogue -/

/-- `WriterT` analogue of `relTriple_simulateQ_run`.

If two writer-transformed oracle implementations produce outputs related by a reflexive-and-closed
relation `R_writer` on the accumulated logs, then the full simulation preserves output equality
together with the accumulated-log relation.

`hR_one` witnesses reflexivity at the empty accumulator (the run-start value), and `hR_mul`
closes `R_writer` under the monoid multiplication used by `WriterT`'s bind. Together these make
`R_writer` a *monoid congruence* on the two writer spaces, which is precisely the structural
requirement for whole-program accumulation. -/
theorem relTriple_simulateQ_run_writerT
    {ι₁ : Type u} {ι₂ : Type u}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec₂)))
    (R_writer : ω₁ → ω₂ → Prop)
    (hR_one : R_writer 1 1)
    (hR_mul : ∀ w₁ w₁' w₂ w₂', R_writer w₁ w₂ → R_writer w₁' w₂' →
      R_writer (w₁ * w₁') (w₂ * w₂'))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain),
      RelTriple ((impl₁ t).run) ((impl₂ t).run)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2)) :
    RelTriple
      (simulateQ impl₁ oa).run
      (simulateQ impl₂ oa).run
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure, relTriple_iff_relWP,
      MAlgRelOrdered.relWP_pure, true_and]
    exact hR_one
  | query_bind t _ ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind, relTriple_iff_relWP,
      relWP_iff_couplingPost]
    refine (relTriple_bind (himpl t) (fun ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ ⟨eq_u, hw⟩ => ?_)) trivial
    dsimp at eq_u hw ⊢
    subst eq_u
    have h_ih := ih u₁
    refine relTriple_map
      (R := fun (p₁ : α × ω₁) (p₂ : α × ω₂) => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2) ?_
    refine relTriple_post_mono h_ih ?_
    rintro ⟨a, v₁⟩ ⟨b, v₂⟩ ⟨hab, hv⟩
    exact ⟨hab, hR_mul _ _ _ _ hw hv⟩

/-- `WriterT` analogue of `relTriple_simulateQ_run_of_impl_eq_preservesInv`.

If two writer-transformed oracle implementations agree pointwise on
`.run` (i.e. every per-query increment is identical as an `OracleComp`),
then the whole simulations yield identical `(output, accumulator)`
distributions.

`WriterT` handlers are stateless (`.run` takes no argument), so the
hypothesis is a plain equality rather than an invariant-gated
implication. The postcondition is strict equality on `α × ω`. -/
theorem relTriple_simulateQ_run_writerT_of_impl_eq
    {ι₁ : Type u}
    {spec₁ : OracleSpec ι₁} [spec₁.Fintype] [spec₁.Inhabited]
    {ω : Type} [Monoid ω]
    (impl₁ impl₂ : QueryImpl spec (WriterT ω (OracleComp spec₁)))
    (himpl_eq : ∀ (t : spec.Domain), (impl₁ t).run = (impl₂ t).run)
    (oa : OracleComp spec α) :
    RelTriple
      (simulateQ impl₁ oa).run
      (simulateQ impl₂ oa).run
      (EqRel (α × ω)) := by
  have hpair : RelTriple
      (simulateQ impl₁ oa).run
      (simulateQ impl₂ oa).run
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ Eq p₁.2 p₂.2) := by
    refine relTriple_simulateQ_run_writerT (spec₁ := spec₁) (spec₂ := spec₁)
      impl₁ impl₂ (fun (w₁ w₂ : ω) => w₁ = w₂) rfl ?_ oa ?_
    · rintro w₁ w₁' w₂ w₂' rfl rfl; rfl
    · intro t
      rw [himpl_eq t]
      apply (relTriple_iff_relWP
        (oa := (impl₂ t).run) (ob := (impl₂ t).run)
        (R := fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2)).2
      refine ⟨_root_.SPMF.Coupling.refl (evalDist ((impl₂ t).run)), ?_⟩
      intro z hz
      rcases (mem_support_bind_iff
        (evalDist ((impl₂ t).run))
        (fun a => (pure (a, a) : SPMF ((spec.Range t × ω) × (spec.Range t × ω)))) z).1 hz with
        ⟨a, _ha, hz'⟩
      have hzEq : z = (a, a) := by
        simpa [support_pure, Set.mem_singleton_iff] using hz'
      subst hzEq
      exact ⟨rfl, rfl⟩
  refine relTriple_post_mono hpair ?_
  rintro ⟨a₁, w₁⟩ ⟨a₂, w₂⟩ ⟨ha, hw⟩
  exact Prod.ext ha hw

/-- Output-probability projection of
`relTriple_simulateQ_run_writerT_of_impl_eq`: two `WriterT` handlers with
pointwise-equal `.run` yield identical `(output, accumulator)` probability
distributions. -/
theorem probOutput_simulateQ_run_writerT_eq_of_impl_eq
    {ι₁ : Type u}
    {spec₁ : OracleSpec ι₁} [spec₁.Fintype] [spec₁.Inhabited]
    {ω : Type} [Monoid ω]
    (impl₁ impl₂ : QueryImpl spec (WriterT ω (OracleComp spec₁)))
    (himpl_eq : ∀ (t : spec.Domain), (impl₁ t).run = (impl₂ t).run)
    (oa : OracleComp spec α) (z : α × ω) :
    Pr[= z | (simulateQ impl₁ oa).run] =
      Pr[= z | (simulateQ impl₂ oa).run] :=
  probOutput_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run_writerT_of_impl_eq impl₁ impl₂ himpl_eq oa) z

/-- `evalDist` equality projection of
`relTriple_simulateQ_run_writerT_of_impl_eq`. -/
theorem evalDist_simulateQ_run_writerT_eq_of_impl_eq
    {ι₁ : Type u}
    {spec₁ : OracleSpec ι₁} [spec₁.Fintype] [spec₁.Inhabited]
    {ω : Type} [Monoid ω]
    (impl₁ impl₂ : QueryImpl spec (WriterT ω (OracleComp spec₁)))
    (himpl_eq : ∀ (t : spec.Domain), (impl₁ t).run = (impl₂ t).run)
    (oa : OracleComp spec α) :
    evalDist (simulateQ impl₁ oa).run =
      evalDist (simulateQ impl₂ oa).run :=
  evalDist_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run_writerT_of_impl_eq impl₁ impl₂ himpl_eq oa)

/-- Projection of `relTriple_simulateQ_run_writerT` onto the output component. -/
theorem relTriple_simulateQ_run_writerT'
    {ι₁ : Type u} {ι₂ : Type u}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec₂)))
    (R_writer : ω₁ → ω₂ → Prop)
    (hR_one : R_writer 1 1)
    (hR_mul : ∀ w₁ w₁' w₂ w₂', R_writer w₁ w₂ → R_writer w₁' w₂' →
      R_writer (w₁ * w₁') (w₂ * w₂'))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain),
      RelTriple ((impl₁ t).run) ((impl₂ t).run)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2)) :
    RelTriple
      (Prod.fst <$> (simulateQ impl₁ oa).run)
      (Prod.fst <$> (simulateQ impl₂ oa).run)
      (EqRel α) := by
  have h := relTriple_simulateQ_run_writerT impl₁ impl₂ R_writer hR_one hR_mul oa himpl
  have hweak : RelTriple (simulateQ impl₁ oa).run (simulateQ impl₂ oa).run
      (fun p₁ p₂ => (EqRel α) p₁.1 p₂.1) :=
    relTriple_post_mono h (fun _ _ hp => hp.1)
  exact relTriple_map hweak

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

/-- Relational transport corollary of `OracleComp.run'_simulateQ_eq_of_query_map_eq`
(`SimSemantics/StateProjection.lean`): under the same per-step projection hypothesis, the two
output distributions are related by equality. -/
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
  relTriple_eqRel_of_eq
    (OracleComp.run'_simulateQ_eq_of_query_map_eq impl₁ impl₂ proj hproj oa s)

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

/-! ## "Identical until bad" with an output bad flag

These variants record the bad event in the **output** state of each oracle step (not the input).
The state has shape `σ × Bool` with the second component a monotone bad flag, and the two
implementations may disagree on the very step that flips the flag. The standard pointwise
agreement hypothesis of `tvDist_simulateQ_le_probEvent_bad{,_dist}` is too strong here: at the
firing step, the input is non-bad but the outputs already differ. The output-bad pattern is the
exact shape of `QueryImpl.withProgramming` (which sets `bad := true` only on policy-firing
steps) and the `programming_collision_bound` argument that builds on it. -/

open scoped Classical in
private lemma probOutput_simulateQ_run_eq_of_not_output_bad
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) :
    Pr[= (x, (s, false)) | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[= (x, (s, false)) | (simulateQ impl₂ oa).run (s₀, false)] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp only [simulateQ_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨u, ⟨s', b⟩⟩
    cases b with
    | true =>
      have h₁ : Pr[= (x, (s, false)) | (simulateQ impl₁ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_bad impl₁ (fun p : σ × Bool => p.2 = true)
          h_mono₁ (oa u) (s', true) rfl x (s, false) (by simp)
      have h₂ : Pr[= (x, (s, false)) | (simulateQ impl₂ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ (fun p : σ × Bool => p.2 = true)
          h_mono₂ (oa u) (s', true) rfl x (s, false) (by simp)
      simp [h₁, h₂]
    | false =>
      rw [h_agree_good t s₀ u s', ih u s']

open scoped Classical in
private lemma probEvent_output_bad_eq
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₂ oa).run (s₀, false)] := by
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h₁ := probEvent_compl sim₁ (fun z : α × σ × Bool => z.2.2 = true)
  have h₂ := probEvent_compl sim₂ (fun z : α × σ × Bool => z.2.2 = true)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h₁ h₂
  have h_not_eq :
      Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    refine tsum_congr ?_
    rintro ⟨a, s, b⟩
    by_cases hb : b = true
    · simp [hb]
    · have hb' : b = false := by cases b <;> simp_all
      subst hb'
      simpa using
        probOutput_simulateQ_run_eq_of_not_output_bad impl₁ impl₂ h_agree_good
          h_mono₁ h_mono₂ oa s₀ a s
  have hne₁ : Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top probEvent_le_one
  calc Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁]
      = 1 - Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] := by
        rw [← h₁]; exact (ENNReal.add_sub_cancel_right hne₁).symm
    _ = 1 - Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by rw [h_not_eq]
    _ = Pr[fun z : α × σ × Bool => z.2.2 = true | sim₂] := by
        rw [← h₂]; exact ENNReal.add_sub_cancel_right
          (ne_top_of_le_ne_top one_ne_top probEvent_le_one)

/-- "Identical until bad" with the bad flag tracked at the **output** of each oracle step.
TV-distance between two state-extended simulations is bounded by the probability of the flag
firing in the run of `impl₁`.

Compared to `tvDist_simulateQ_le_probEvent_bad{,_dist}`, this version weakens the
agreement hypothesis: the two implementations need only agree on **non-bad output transitions**
from non-bad input states. They may disagree arbitrarily on the very step that flips the flag.

Both implementations must satisfy bad-input monotonicity: once `b = true` in the input state of
a step, every reachable output also has `b = true`. -/
theorem tvDist_simulateQ_le_probEvent_output_bad
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  classical
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h_eq : ∀ (z : α × σ × Bool), ¬(z.2.2 = true) → Pr[= z | sim₁] = Pr[= z | sim₂] := by
    rintro ⟨x, s, b⟩ hb
    have hb' : b = false := by cases b <;> simp_all
    subst hb'
    exact probOutput_simulateQ_run_eq_of_not_output_bad impl₁ impl₂ h_agree_good
      h_mono₁ h_mono₂ oa s₀ x s
  have h_event_eq :
      Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => z.2.2 = true | sim₂] :=
    probEvent_output_bad_eq impl₁ impl₂ h_agree_good h_mono₁ h_mono₂ oa s₀
  have h_tv_joint :
      tvDist sim₁ sim₂ ≤ Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal :=
    tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂)
      (fun z : α × σ × Bool => z.2.2 = true) h_eq h_event_eq
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist sim₁ sim₂ := by
    simpa [sim₁, sim₂, StateT.run'] using
      (tvDist_map_le (m := OracleComp spec) (α := α × σ × Bool) (β := α) Prod.fst sim₁ sim₂)
  exact le_trans h_map h_tv_joint

/-- Ergonomic wrapper of `tvDist_simulateQ_le_probEvent_output_bad` for the very common case
where the underlying oracle implementations live in `StateT σ (OracleComp spec)` and have been
*lifted* to `StateT (σ × Bool) (OracleComp spec)` by attaching a bad flag.

This is the exact shape consumed by the `QueryImpl.withProgramming` collision-bound argument:
the impls agree on `(s, false)` input *modulo* the rare programming-fired step, and the bound
is the probability of any policy hit during the run. -/
theorem identical_until_bad_with_flag
    {σ : Type} {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec)))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
  tvDist_simulateQ_le_probEvent_output_bad impl₁ impl₂ oa s₀ h_agree_good h_mono₁ h_mono₂

/-! ## ε-perturbed "identical until bad" with output bad flag

These lemmas generalize `tvDist_simulateQ_le_probEvent_output_bad` from EXACT agreement on
the no-bad path to ε-CLOSE agreement: the per-step TV distance between the two oracle
implementations may be at most `ε` (instead of zero) on the no-bad path. Combined with a
query bound `q` on the computation, the total bound becomes `q*ε + Pr[bad]`.

The standard "identical until bad" bound (`Pr[bad]`) is recovered as the special case `ε = 0`.

**Application**: HVZK simulation in Fiat-Shamir, where the simulated transcript is only
`ε`-close to the real transcript per query (not exactly equal), but a "programming
collision" event captures the catastrophic failure mode (collision between programmed hash
entries). The total reduction loss is `qS·ε + Pr[collision]`. -/

section IdenticalUntilBadEpsilon

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [spec'.Fintype] [spec'.Inhabited]
variable {α : Type} {σ : Type}

omit [spec'.Fintype] [spec'.Inhabited] in
/-- "Bad propagation": starting from a bad state, every output of the simulation has the
bad flag set. This generalizes the per-step `h_mono` hypothesis to the full simulation. -/
private lemma mem_support_simulateQ_run_of_bad
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((simulateQ impl oa).run p), z.2.2 = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hp
  | query_bind t cont ih =>
      intro z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion,
        exists_prop] at hz
      obtain ⟨⟨u, p'⟩, h_mem, h_z⟩ := hz
      have hp' : p'.2 = true := h_mono t p hp (u, p') h_mem
      exact ih u p' hp' z h_z

/-- Under bad-monotonicity, a simulation started from a bad state has bad output probability
exactly `1` (using `OracleComp.HasEvalPMF` to ensure no failure mass). -/
private lemma probEvent_simulateQ_run_bad_eq_one_of_bad
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) :
    Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl oa).run p] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp, ?_⟩
  exact mem_support_simulateQ_run_of_bad impl h_mono oa p hp

/-! ### ε-perturbed identical-until-bad: helper lemmas (in dependency order) -/

/-- Bound `∑' z, p_z.toReal * tvDist (f₁ z) (f₂ z)` by `c + Pr[bad | mx >>= f₁]`,
given that each summand is bounded by `p_z * (c + Pr[bad | f₁ z])`. The constant `c`
is intended to be `(q - 1) · ε` from the inductive hypothesis. -/
private theorem tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad
    {β : Type} (mx : OracleComp spec' β) (f₁ f₂ : β → OracleComp spec' (α × σ × Bool))
    {c : ℝ} (hc : 0 ≤ c)
    (h_summand_le : ∀ z : β,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤
        Pr[= z | mx].toReal * (c +
          Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal)) :
    (∑' z : β, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
      ≤ c + Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁].toReal := by
  have h_p_sum_le_one : (∑' z : β, Pr[= z | mx]) ≤ 1 := tsum_probOutput_le_one
  have h_p_sum_ne_top : (∑' z : β, Pr[= z | mx]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top h_p_sum_le_one
  have h_p_summable : Summable (fun z : β => Pr[= z | mx].toReal) :=
    ENNReal.summable_toReal h_p_sum_ne_top
  have h_lhs_summand_nn : ∀ z : β, 0 ≤ Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    fun z => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have h_lhs_summand_le : ∀ z : β,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤ Pr[= z | mx].toReal :=
    fun z => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have h_lhs_summable : Summable
      (fun z : β => Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) :=
    Summable.of_nonneg_of_le h_lhs_summand_nn h_lhs_summand_le h_p_summable
  have h_b_z_le_one : ∀ z : β,
      Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal ≤ 1 := fun z => by
    simpa using ENNReal.toReal_mono one_ne_top probEvent_le_one
  have h_rhs_summand_nn : ∀ z : β, 0 ≤ Pr[= z | mx].toReal *
      (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) :=
    fun z => mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg hc ENNReal.toReal_nonneg)
  have h_rhs_summand_le : ∀ z : β,
      Pr[= z | mx].toReal * (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) ≤
      Pr[= z | mx].toReal * (c + 1) := fun z => by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    linarith [h_b_z_le_one z]
  have h_rhs_summable : Summable (fun z : β => Pr[= z | mx].toReal *
      (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal)) :=
    Summable.of_nonneg_of_le h_rhs_summand_nn h_rhs_summand_le
      (h_p_summable.mul_right (c + 1))
  have h_le_rhs :
      (∑' z : β, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
        ≤ ∑' z : β, Pr[= z | mx].toReal *
          (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) :=
    Summable.tsum_le_tsum h_summand_le h_lhs_summable h_rhs_summable
  refine le_trans h_le_rhs ?_
  have h_distrib_summable_a : Summable
      (fun z : β => Pr[= z | mx].toReal * c) :=
    h_p_summable.mul_right _
  have h_distrib_summable_b : Summable
      (fun z : β => Pr[= z | mx].toReal *
        Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) :=
    Summable.of_nonneg_of_le
      (fun z => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun z => mul_le_of_le_one_right ENNReal.toReal_nonneg (h_b_z_le_one z))
      h_p_summable
  have h_split :
      (∑' z : β, Pr[= z | mx].toReal *
        (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal))
        = (∑' z : β, Pr[= z | mx].toReal * c) +
          (∑' z : β, Pr[= z | mx].toReal *
            Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) := by
    rw [← Summable.tsum_add h_distrib_summable_a h_distrib_summable_b]
    refine tsum_congr fun z => ?_
    ring
  rw [h_split]
  have h_first_sum :
      (∑' z : β, Pr[= z | mx].toReal * c) = c := by
    rw [tsum_mul_right]
    have h_one : (∑' z : β, Pr[= z | mx].toReal) = 1 := by
      rw [show (∑' z : β, Pr[= z | mx].toReal) = ((∑' z : β, Pr[= z | mx])).toReal from
        (ENNReal.tsum_toReal_eq fun z => by
          have h := probOutput_le_one (mx := mx) (x := z)
          exact ne_top_of_le_ne_top one_ne_top h).symm]
      rw [HasEvalPMF.tsum_probOutput_eq_one]
      simp
    rw [h_one, one_mul]
  have h_second_sum :
      (∑' z : β, Pr[= z | mx].toReal *
        Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal)
        = Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁].toReal := by
    have h_term_ne_top : ∀ z : β, Pr[= z | mx] *
        Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] ≠ ⊤ := fun z => by
      have h₁ : Pr[= z | mx] ≤ 1 := probOutput_le_one
      have h₂ : Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] ≤ 1 := probEvent_le_one
      have h_le : Pr[= z | mx] * Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] ≤ 1 :=
        mul_le_one' h₁ h₂
      exact ne_top_of_le_ne_top one_ne_top h_le
    rw [show
      Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] =
        ∑' z : β, Pr[= z | mx] *
          Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] from
        probEvent_bind_eq_tsum mx f₁ _,
      ENNReal.tsum_toReal_eq h_term_ne_top]
    refine tsum_congr fun z => ?_
    exact ENNReal.toReal_mul.symm
  rw [h_first_sum, h_second_sum]

/-- The `query_bind` (`p.2 = false`) inductive step: given the per-continuation IH bound
(parameterized by `q - 1`), combine the triangle inequality, the two `tvDist_bind_*_le`
bounds, and the algebraic distribution to get the `q · ε + Pr[bad]` bound. -/
private theorem tvDist_simulateQ_run_query_bind_le
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_step_tv : ∀ (t : spec.Domain) (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    {q : ℕ} (hq_pos : 0 < q)
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p')
        ≤ ↑(q - 1) * ε + Pr[ fun w : α × σ × Bool => w.2.2 = true |
            (simulateQ impl₁ (cont u)).run p'].toReal)
    (s : σ) :
    tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false))
      ≤ ↑q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ (query t >>= cont)).run (s, false)].toReal := by
  set sim₁ : OracleComp spec' (α × σ × Bool) :=
    (simulateQ impl₁ (query t >>= cont)).run (s, false) with hsim₁_def
  set sim₂ : OracleComp spec' (α × σ × Bool) :=
    (simulateQ impl₂ (query t >>= cont)).run (s, false) with hsim₂_def
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  set my : OracleComp spec' (spec.Range t × σ × Bool) := (impl₂ t).run (s, false) with hmy_def
  have hsim₁_eq : sim₁ = mx >>= f₁ := by
    simp [hsim₁_def, hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : sim₂ = my >>= f₂ := by
    simp [hsim₂_def, hmy_def, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  set mid : OracleComp spec' (α × σ × Bool) := mx >>= f₂ with hmid_def
  have h_tri : tvDist sim₁ sim₂ ≤ tvDist sim₁ mid + tvDist mid sim₂ :=
    tvDist_triangle _ _ _
  have h_second : tvDist mid sim₂ ≤ ε := by
    rw [hmid_def, hsim₂_eq]
    exact le_trans (tvDist_bind_right_le _ _ _) (h_step_tv t s)
  have h_first_raw :
      tvDist sim₁ mid ≤ ∑' z : spec.Range t × σ × Bool,
        Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) := by
    rw [hsim₁_eq, hmid_def]
    exact tvDist_bind_left_le _ _ _
  have h_summand_le : ∀ z : spec.Range t × σ × Bool,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤
        Pr[= z | mx].toReal * (↑(q - 1) * ε + Pr[fun w : α × σ × Bool => w.2.2 = true |
            f₁ z].toReal) := fun z => by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa [hf₁_def, hf₂_def] using ih z.1 z.2
  have h_const_nonneg : (0 : ℝ) ≤ ↑(q - 1) * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have h_first :
      tvDist sim₁ mid ≤ ↑(q - 1) * ε +
        Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal := by
    refine le_trans h_first_raw ?_
    have h_helper := tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad
      (mx := mx) (f₁ := f₁) (f₂ := f₂) (c := ↑(q - 1) * ε) h_const_nonneg h_summand_le
    rw [hsim₁_eq]
    exact h_helper
  have hq_arith : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    have h1 : 1 ≤ q := hq_pos
    have h2 : ((q - 1 : ℕ) + 1 : ℕ) = q := Nat.sub_add_cancel h1
    have h3 : (((q - 1 : ℕ) + 1 : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast h2
    simpa using h3
  calc tvDist sim₁ sim₂
      ≤ tvDist sim₁ mid + tvDist mid sim₂ := h_tri
    _ ≤ (↑(q - 1) * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal) + ε :=
        add_le_add h_first h_second
    _ = (↑(q - 1) + 1) * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal := by
        ring
    _ = ↑q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal := by
        rw [hq_arith]

/-- Auxiliary inductive lemma for `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad`. Bounds
the TV distance on the **joint** (state-included) distribution, for arbitrary starting state
`p` (whether the bad flag is set or not).

The proof inducts on `oa`:
- `pure x`: both simulations equal `pure (x, p)`, so `tvDist = 0` and the RHS is non-negative.
- `query t >>= cont`: case on `p.2`.
  - `true`: by bad-monotonicity, `Pr[bad | sim₁] = 1`, and `tvDist ≤ 1` always.
  - `false`: see `tvDist_simulateQ_run_query_bind_le`. -/
private theorem tvDist_simulateQ_run_le_qeps_plus_probEvent_output_bad_aux
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_step_tv : ∀ (t : spec.Domain) (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {q : ℕ}
    (h_qb : OracleComp.IsTotalQueryBound oa q) (p : σ × Bool) :
    tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p)
      ≤ q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run p].toReal := by
  induction oa using OracleComp.inductionOn generalizing q p with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) ENNReal.toReal_nonneg
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true =>
          have h_bad₁ : Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, true)] = 1 :=
            probEvent_simulateQ_run_bad_eq_one_of_bad impl₁ h_mono₁
              (query t >>= cont) (s, true) rfl
          have h_tv_le_one :
              tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true)) ≤ 1 :=
            tvDist_le_one _ _
          have h_target_ge_one :
              (1 : ℝ) ≤ ↑q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
                (simulateQ impl₁ (query t >>= cont)).run (s, true)].toReal := by
            rw [h_bad₁]
            simp only [ENNReal.toReal_one]
            have hqε : (0 : ℝ) ≤ ↑q * ε := mul_nonneg (Nat.cast_nonneg _) hε
            linarith
          exact le_trans h_tv_le_one h_target_ge_one
      | false =>
          have hq_pos : 0 < q := h_qb.1
          have hq_cont : ∀ u, OracleComp.IsTotalQueryBound (cont u) (q - 1) := h_qb.2
          exact tvDist_simulateQ_run_query_bind_le impl₁ impl₂ hε h_step_tv t cont hq_pos
            (fun u p' => ih u (hq_cont u) p') s

/-- **ε-perturbed identical-until-bad with output bad flag.**

If two stateful oracle implementations are ε-CLOSE in TV distance per step on the no-bad
path (instead of exactly equal as in `tvDist_simulateQ_le_probEvent_output_bad`), and the
computation makes at most `q` queries, then the TV distance between the two simulations
is bounded by `q*ε + Pr[bad]`.

Only `impl₁` requires bad-flag monotonicity (since the bound uses `Pr[bad | sim₁]`); the
"true" branch in the inductive proof exploits monotonicity to push `Pr[bad | sim₁] = 1`
which dominates the trivial `tvDist ≤ 1` bound.

The `ε = 0` case recovers the existing identical-until-bad bound (modulo the upgraded
agreement hypothesis from definitional equality to TV-distance equality, which is
equivalent for distributions over the same type). -/
theorem tvDist_simulateQ_le_qeps_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_step_tv : ∀ (t : spec.Domain) (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {q : ℕ}
    (h_qb : OracleComp.IsTotalQueryBound oa q) (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  have h_joint :
      tvDist ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false))
        ≤ q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ oa).run (s₀, false)].toReal :=
    tvDist_simulateQ_run_le_qeps_plus_probEvent_output_bad_aux
      impl₁ impl₂ hε h_step_tv h_mono₁ oa h_qb (s₀, false)
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist ((simulateQ impl₁ oa).run (s₀, false))
            ((simulateQ impl₂ oa).run (s₀, false)) := by
    simpa [StateT.run'] using
      (tvDist_map_le (m := OracleComp spec') (α := α × σ × Bool) (β := α) Prod.fst
        ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false)))
  exact le_trans h_map h_joint

end IdenticalUntilBadEpsilon

/-! ### Selective ε-perturbed identical-until-bad

A refinement of `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad` where the per-step ε
bound applies only to a designated subset `S` of queries (the "costly" or "perturbed"
queries), and the impls are pointwise equal on the complement (the "free" queries). The
bound counts only the S-queries, giving a tight `qS · ε` instead of `q_total · ε`.

This is essential for cryptographic reductions where, e.g., signing-oracle queries are
ε-close to a simulator (HVZK guarantee) but uniform / RO queries are exactly equal (both
sides forward through the same RO cache). Direct application of the uniform-ε lemma would
give `(qS + qH) · ε`, but for tight bounds we want `qS · ε`. -/

section IdenticalUntilBadEpsilonSelective

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [spec'.Fintype] [spec'.Inhabited]
variable {α : Type} {σ : Type}

/-- The `query_bind` step for a "free" query (impls pointwise equal on the no-bad branch).
The budget `qS` is preserved (no decrement), since a free query doesn't count toward the
S-query bound. -/
private theorem tvDist_simulateQ_run_free_query_bind_le
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (t : spec.Domain) (h_step_eq : ∀ (p : σ × Bool), (impl₁ t).run p = (impl₂ t).run p)
    (cont : spec.Range t → OracleComp spec α) {qS : ℕ}
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p')
        ≤ ↑qS * ε + Pr[ fun w : α × σ × Bool => w.2.2 = true |
            (simulateQ impl₁ (cont u)).run p'].toReal)
    (s : σ) :
    tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false))
      ≤ ↑qS * ε + Pr[ fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ (query t >>= cont)).run (s, false)].toReal := by
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  have hmy_eq : (impl₂ t).run (s, false) = mx := (h_step_eq (s, false)).symm
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  have hsim₁_eq : (simulateQ impl₁ (query t >>= cont)).run (s, false) = mx >>= f₁ := by
    simp [hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : (simulateQ impl₂ (query t >>= cont)).run (s, false) = mx >>= f₂ := by
    simp [hmy_eq, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have h_bd : tvDist (mx >>= f₁) (mx >>= f₂)
      ≤ ∑' z : spec.Range t × σ × Bool, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    tvDist_bind_left_le _ _ _
  have h_summand_le : ∀ z : spec.Range t × σ × Bool,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤
        Pr[= z | mx].toReal * (↑qS * ε + Pr[fun w : α × σ × Bool => w.2.2 = true |
            f₁ z].toReal) := fun z => by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa [hf₁_def, hf₂_def] using ih z.1 z.2
  have h_qSε_nonneg : (0 : ℝ) ≤ ↑qS * ε := mul_nonneg (Nat.cast_nonneg _) hε
  rw [hsim₁_eq, hsim₂_eq]
  exact le_trans h_bd
    (tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad
      (mx := mx) (f₁ := f₁) (f₂ := f₂) (c := ↑qS * ε) h_qSε_nonneg h_summand_le)

/-- Auxiliary inductive lemma for the selective ε-perturbed bound. Inducts on `oa` and
case-splits each query on whether it's in the costly set `S` (existing per-step argument
with budget decrement) or free (`tvDist_simulateQ_run_free_query_bind_le` with budget
preserved). -/
private theorem tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad_aux
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (p : σ × Bool) :
    tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p)
      ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run p].toReal := by
  -- Construct a global per-step bound `tvDist ≤ ε` that holds for ALL queries:
  -- for S-queries by `h_step_tv_S`, for non-S-queries since the impls are pointwise equal.
  have h_step_tv_global : ∀ (t' : ι) (s' : σ),
      tvDist ((impl₁ t').run (s', false)) ((impl₂ t').run (s', false)) ≤ ε := by
    intro t' s'
    by_cases hSt' : S t'
    · exact h_step_tv_S t' hSt' s'
    · rw [h_step_eq_nS t' hSt' (s', false), tvDist_self]; exact hε
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) ENNReal.toReal_nonneg
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true =>
          have h_bad₁ : Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, true)] = 1 :=
            probEvent_simulateQ_run_bad_eq_one_of_bad impl₁ h_mono₁
              (query t >>= cont) (s, true) rfl
          have h_tv_le_one :
              tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true)) ≤ 1 :=
            tvDist_le_one _ _
          have h_target_ge_one :
              (1 : ℝ) ≤ ↑qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
                (simulateQ impl₁ (query t >>= cont)).run (s, true)].toReal := by
            rw [h_bad₁]
            simp only [ENNReal.toReal_one]
            have hqε : (0 : ℝ) ≤ ↑qS * ε := mul_nonneg (Nat.cast_nonneg _) hε
            linarith
          exact le_trans h_tv_le_one h_target_ge_one
      | false =>
          rw [isQueryBound_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : S t
          · -- Costly query: use the existing helper with budget `qS`, decrementing to `qS - 1`.
            simp only [hSt, if_true] at h_can h_cont
            have hqS_pos : 0 < qS := h_can
            exact tvDist_simulateQ_run_query_bind_le impl₁ impl₂ hε h_step_tv_global
              t cont hqS_pos
              (fun u p' => ih u (h_cont u) p') s
          · -- Free query: impls equal here; preserve the `qS` budget through the recursion.
            simp only [hSt, if_false] at h_can h_cont
            exact tvDist_simulateQ_run_free_query_bind_le impl₁ impl₂ hε t
              (h_step_eq_nS t hSt) cont
              (fun u p' => ih u (h_cont u) p') s

/-- **Selective ε-perturbed identical-until-bad with output bad flag.**

Like `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad`, but the per-step ε bound
applies only to queries `t` satisfying a designated predicate `S` (the "costly" queries),
and the impls are pointwise equal on `¬ S` (the "free" queries). The bound counts only
the S-queries (via `IsQueryBound` parameterized to decrement only on S), giving the tight
`qS · ε` instead of the trivial `q_total · ε` from the uniform-ε lemma.

The intended use is for cryptographic reductions: e.g., for Fiat-Shamir signing-oracle
swaps, the "costly" queries are signing queries (HVZK gives per-query ε bound) and the
"free" queries are the underlying spec queries (uniform sampling and RO caching, where
both sides forward through the same `baseSim`). -/
theorem tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run (s₀, false))
        ((simulateQ impl₂ oa).run (s₀, false))
      ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
  tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad_aux
    impl₁ impl₂ hε S h_step_tv_S h_step_eq_nS h_mono₁ oa h_qb (s₀, false)

/-- **Selective ε-perturbed identical-until-bad with output bad flag.**

Like `tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad`, but projected to the
computation output via `StateT.run'`. -/
theorem tvDist_simulateQ_le_qSeps_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  have h_joint :
      tvDist ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false))
        ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ oa).run (s₀, false)].toReal :=
    tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad
      impl₁ impl₂ hε S h_step_tv_S h_step_eq_nS h_mono₁ oa h_qb s₀
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist ((simulateQ impl₁ oa).run (s₀, false))
            ((simulateQ impl₂ oa).run (s₀, false)) := by
    simpa [StateT.run'] using
      (tvDist_map_le (m := OracleComp spec') (α := α × σ × Bool) (β := α) Prod.fst
        ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false)))
  exact le_trans h_map h_joint

end IdenticalUntilBadEpsilonSelective

/-! ### State-dep ε-perturbed identical-until-bad

A further refinement of `tvDist_simulateQ_le_qSeps_plus_probEvent_output_bad` where the
per-step ε bound is allowed to depend on the **input state** `s : σ` to the impl. The
bound on `tvDist` is then expressed as the **expected sum** of `ε s` over the trace of
S-queries fired during the simulation, captured by the recursive function `expectedSCost`.

This is essential for cryptographic reductions where the per-step gap depends on a varying
state quantity (e.g., for Fiat-Shamir signing-oracle swaps the gap is
`ζ_zk + |s.cache| · β`, growing with cache size, with no uniform constant ε).
The constant-ε lemma `tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad` is a
corollary (see Phase A2).

To sidestep summability obligations, `expectedSCost` is valued in `ℝ≥0∞` and the bridge
lemma is stated in `ℝ≥0∞` via `ENNReal.ofReal (tvDist …)`. A real-valued corollary
`tvDist_…_toReal_…` is provided for users that supply a finiteness witness for
`expectedSCost`. -/

section IdenticalUntilBadEpsilonStateDep

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [spec'.Fintype] [spec'.Inhabited]
variable {α : Type} {σ : Type}

/-- Per-`query_bind` step of `expectedSCost`. Given the impl, the costly-query
predicate `S`, the per-state cost `ε`, the query symbol `t`, and the IH continuation
`k : Range t → ℕ → (σ × Bool) → ℝ≥0∞`, returns the expected cost contributed by
performing the query `t` from state `p` with budget `qS`:

* if the bad flag is set in `p`, return `0` (the `Pr[bad]` term swallows the deficit);
* if `t` is a free query (`¬ S t`), forward through the impl with budget unchanged;
* if `t` is a costly query and the budget is exhausted, return `0` (vacuous via
  `IsQueryBound`);
* if `t` is a costly query with positive budget, pay `ε p.1` immediately, then forward
  through the impl with budget decremented to `qS - 1`. -/
noncomputable def expectedSCostStep
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (p : σ × Bool) : ℝ≥0∞ :=
  if p.2 then 0
  else
    if S t then
      if 0 < qS then
        ε p.1 + ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl t).run (p.1, false)] * k z.1 (qS - 1) z.2
      else 0
    else
      ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (p.1, false)] * k z.1 qS z.2

/-- Recursive expected sum-of-`ε(state)` over the S-queries fired during
`(simulateQ impl oa).run p`. Defined by recursion on `oa` via `OracleComp.construct`. -/
noncomputable def expectedSCost
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) :
    {α : Type} → OracleComp spec α → ℕ → (σ × Bool) → ℝ≥0∞ :=
  fun {_} oa => OracleComp.construct
    (C := fun _ => ℕ → (σ × Bool) → ℝ≥0∞)
    (fun _ _ _ => 0)
    (fun t _ ih => expectedSCostStep impl S ε t ih)
    oa

@[simp]
lemma expectedSCost_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (x : α)
    (qS : ℕ) (p : σ × Bool) :
    expectedSCost impl S ε (pure x : OracleComp spec α) qS p = 0 := rfl

lemma expectedSCost_query_bind
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    (qS : ℕ) (p : σ × Bool) :
    expectedSCost impl S ε (query t >>= cont) qS p =
      expectedSCostStep impl S ε t (fun u => expectedSCost impl S ε (cont u)) qS p := rfl

lemma expectedSCost_bind_eq_of_right_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    {β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (hzero : ∀ x qS p, expectedSCost impl S ε (ob x) qS p = 0)
    (qS : ℕ) (p : σ × Bool) :
    expectedSCost impl S ε (oa >>= ob) qS p =
      expectedSCost impl S ε oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x =>
      simp [hzero x qS p]
  | query_bind t cont ih =>
      simp only [bind_assoc]
      rw [expectedSCost_query_bind, expectedSCost_query_bind]
      congr
      funext u qS' p'
      exact ih u qS' p'

@[simp]
lemma expectedSCostStep_bad_eq_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) :
    expectedSCostStep impl S ε t k qS (s, true) = 0 := by
  simp [expectedSCostStep]

@[simp]
lemma expectedSCost_bad_eq_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (oa : OracleComp spec α) (qS : ℕ) (s : σ) :
    expectedSCost impl S ε oa qS (s, true) = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact expectedSCost_pure impl S ε x qS (s, true)
  | query_bind t cont _ =>
      rw [expectedSCost_query_bind, expectedSCostStep_bad_eq_zero]

lemma expectedSCostStep_costly_pos
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) (hS : S t) (hqS : 0 < qS) :
    expectedSCostStep impl S ε t k qS (s, false) =
      ε s + ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (s, false)] * k z.1 (qS - 1) z.2 := by
  simp [expectedSCostStep, hS, hqS]

lemma expectedSCostStep_free
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) (hS : ¬ S t) :
    expectedSCostStep impl S ε t k qS (s, false) =
      ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (s, false)] * k z.1 qS z.2 := by
  simp [expectedSCostStep, hS]

/-! #### Pointwise monotonicity of `expectedSCost` in `ε`

If `ε ≤ ε'` pointwise (as functions `σ → ℝ≥0∞`), then
`expectedSCost impl S ε oa qS p ≤ expectedSCost impl S ε' oa qS p`.
The analogous monotonicity in the continuation `k` (for
`expectedSCostStep`) is the step-level lemma, used in the inductive
step of `expectedSCost_mono`. These lemmas are used to bound a
state-dependent ε by a constant upper bound so the constant-ε bound
`expectedSCost_const_le_qS_mul` applies. -/

lemma expectedSCostStep_mono
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (hε : ∀ s, ε s ≤ ε' s)
    (t : spec.Domain) {k k' : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞}
    (hk : ∀ u qS p, k u qS p ≤ k' u qS p)
    (qS : ℕ) (p : σ × Bool) :
    expectedSCostStep impl S ε t k qS p ≤ expectedSCostStep impl S ε' t k' qS p := by
  rcases p with ⟨s, b⟩
  cases b with
  | true => simp [expectedSCostStep]
  | false =>
      by_cases hSt : S t
      · by_cases hqS : 0 < qS
        · rw [expectedSCostStep_costly_pos impl S ε t k qS s hSt hqS,
              expectedSCostStep_costly_pos impl S ε' t k' qS s hSt hqS]
          gcongr with z
          · exact hε s
          · exact hk z.1 (qS - 1) z.2
        · simp [expectedSCostStep, hSt, hqS]
      · rw [expectedSCostStep_free impl S ε t k qS s hSt,
            expectedSCostStep_free impl S ε' t k' qS s hSt]
        gcongr with z
        exact hk z.1 qS z.2

theorem expectedSCost_mono
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (hε : ∀ s, ε s ≤ ε' s)
    (oa : OracleComp spec α) (qS : ℕ) (p : σ × Bool) :
    expectedSCost impl S ε oa qS p ≤ expectedSCost impl S ε' oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      rw [expectedSCost_query_bind, expectedSCost_query_bind]
      exact expectedSCostStep_mono impl S hε t
        (fun u qS' p' => ih u qS' p') qS p

/-! #### Invariant support congruence for `expectedSCost` -/

/-- If two per-state cost functions agree on an invariant and the real handler preserves
that invariant from no-bad states, then `expectedSCost` is insensitive to their values on
unreachable states.

The input hypothesis is phrased as `p.2 = false → Inv p.1` so that bad states remain
vacuous: `expectedSCost` is definitionally zero once the bad flag is set. -/
theorem expectedSCost_eq_of_inv
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (Inv : σ → Prop)
    (hε : ∀ s, Inv s → ε s = ε' s)
    (h_pres : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false → Inv p.1 →
      ∀ z ∈ support ((impl t).run p), Inv z.2.1)
    (oa : OracleComp spec α) (qS : ℕ) (p : σ × Bool)
    (hp : p.2 = false → Inv p.1) :
    expectedSCost impl S ε oa qS p = expectedSCost impl S ε' oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true => simp [expectedSCost_bad_eq_zero]
      | false =>
          have hInv : Inv s := hp rfl
          by_cases hSt : S t
          · by_cases hqS : 0 < qS
            · rw [expectedSCost_query_bind, expectedSCost_query_bind,
                expectedSCostStep_costly_pos impl S ε t
                  (fun u => expectedSCost impl S ε (cont u)) qS s hSt hqS,
                expectedSCostStep_costly_pos impl S ε' t
                  (fun u => expectedSCost impl S ε' (cont u)) qS s hSt hqS,
                hε s hInv]
              congr 1
              refine tsum_congr fun z => ?_
              by_cases hz : z ∈ support ((impl t).run (s, false))
              · rw [ih z.1 (qS := qS - 1) (p := z.2)]
                intro _
                exact h_pres t (s, false) rfl hInv z hz
              · have hprob :
                    Pr[= z | (impl t).run (s, false)] = 0 :=
                  probOutput_eq_zero_of_not_mem_support hz
                rw [hprob, zero_mul, zero_mul]
            · simp [expectedSCost_query_bind, expectedSCostStep, hSt, hqS]
          · rw [expectedSCost_query_bind, expectedSCost_query_bind,
              expectedSCostStep_free impl S ε t
                (fun u => expectedSCost impl S ε (cont u)) qS s hSt,
              expectedSCostStep_free impl S ε' t
                (fun u => expectedSCost impl S ε' (cont u)) qS s hSt]
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ support ((impl t).run (s, false))
            · rw [ih z.1 (qS := qS) (p := z.2)]
              intro _
              exact h_pres t (s, false) rfl hInv z hz
            · have hprob :
                  Pr[= z | (impl t).run (s, false)] = 0 :=
                probOutput_eq_zero_of_not_mem_support hz
              rw [hprob, zero_mul, zero_mul]

/-! #### Helper lemma: per-summand IH bound implies the bind-sum bound -/

/-- Sum bound for the inductive step: from a per-summand `ofReal (tvDist) ≤ cost z + Pr[bad]`
IH, conclude that `ofReal (∑' z, Pr[=z|mx].toReal · tvDist (f₁ z) (f₂ z))` is bounded by
`(∑' z, Pr[=z|mx] · cost z) + Pr[bad | mx >>= f₁]`. The state-dep analogue of
`tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad`, replacing the constant `c` by a
per-summand `cost z : ℝ≥0∞`. -/
private lemma tsum_probOutput_mul_ofReal_tvDist_le_tsum_cost_plus_probEvent_bad
    {γ : Type} (mx : OracleComp spec' γ) (f₁ f₂ : γ → OracleComp spec' (α × σ × Bool))
    (cost : γ → ℝ≥0∞)
    (h_summand_le : ∀ z : γ,
      ENNReal.ofReal (tvDist (f₁ z) (f₂ z)) ≤
        cost z + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z]) :
    ENNReal.ofReal (∑' z, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
      ≤ (∑' z, Pr[= z | mx] * cost z)
        + Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] := by
  have h_p_sum_le_one : (∑' z : γ, Pr[= z | mx]) ≤ 1 := tsum_probOutput_le_one
  have h_p_sum_ne_top : (∑' z : γ, Pr[= z | mx]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top h_p_sum_le_one
  have h_p_summable : Summable (fun z : γ => Pr[= z | mx].toReal) :=
    ENNReal.summable_toReal h_p_sum_ne_top
  have h_lhs_summand_nn : ∀ z : γ,
      0 ≤ Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    fun z => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have h_lhs_summand_le : ∀ z : γ,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤ Pr[= z | mx].toReal :=
    fun z => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have h_lhs_summable : Summable
      (fun z : γ => Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) :=
    Summable.of_nonneg_of_le h_lhs_summand_nn h_lhs_summand_le h_p_summable
  have h_p_ne_top : ∀ z : γ, Pr[= z | mx] ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top one_ne_top probOutput_le_one
  have h_summand_eq : ∀ z : γ,
      ENNReal.ofReal (Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) =
        Pr[= z | mx] * ENNReal.ofReal (tvDist (f₁ z) (f₂ z)) := fun z => by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (h_p_ne_top z)]
  have h_ofreal_tsum :
      ENNReal.ofReal (∑' z, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
        = ∑' z, Pr[= z | mx] * ENNReal.ofReal (tvDist (f₁ z) (f₂ z)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg h_lhs_summand_nn h_lhs_summable]
    exact tsum_congr h_summand_eq
  rw [h_ofreal_tsum]
  calc
    (∑' z : γ, Pr[= z | mx] * ENNReal.ofReal (tvDist (f₁ z) (f₂ z)))
      ≤ ∑' z : γ, Pr[= z | mx] *
          (cost z + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z]) :=
        ENNReal.tsum_le_tsum fun z => by gcongr; exact h_summand_le z
    _ = (∑' z : γ, Pr[= z | mx] * cost z) +
          ∑' z : γ, Pr[= z | mx] *
            Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun z => ?_
        rw [mul_add]
    _ = (∑' z : γ, Pr[= z | mx] * cost z) +
          Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] := by
        rw [← probEvent_bind_eq_tsum mx f₁]

/-! #### Per-step inductive helpers -/

/-- The `query_bind` step for a costly S-query (`S t ∧ 0 < qS`), state-dep ε version.
Combines triangle inequality through the coupled mid-distribution `mx >>= f₂` with
`tvDist_bind_left_le` + the helper lemma to push the IH through the bind. -/
private theorem ofReal_tvDist_simulateQ_run_costly_query_bind_le_expectedSCost
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε s)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    {qS : ℕ} (hS : S t) (hqS : 0 < qS)
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      ENNReal.ofReal (tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p'))
        ≤ expectedSCost impl₁ S ε (cont u) (qS - 1) p'
          + Pr[fun w : α × σ × Bool => w.2.2 = true |
              (simulateQ impl₁ (cont u)).run p'])
    (s : σ) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      ≤ expectedSCost impl₁ S ε (query t >>= cont) qS (s, false)
        + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  set my : OracleComp spec' (spec.Range t × σ × Bool) := (impl₂ t).run (s, false) with hmy_def
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  have hsim₁_eq : (simulateQ impl₁ (query t >>= cont)).run (s, false) = mx >>= f₁ := by
    simp [hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : (simulateQ impl₂ (query t >>= cont)).run (s, false) = my >>= f₂ := by
    simp [hmy_def, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  set sim₁ : OracleComp spec' (α × σ × Bool) := mx >>= f₁ with hsim₁_def
  set sim₂ : OracleComp spec' (α × σ × Bool) := my >>= f₂ with hsim₂_def
  set mid : OracleComp spec' (α × σ × Bool) := mx >>= f₂ with hmid_def
  have h_tri_real : tvDist sim₁ sim₂ ≤ tvDist sim₁ mid + tvDist mid sim₂ :=
    tvDist_triangle _ _ _
  have h_first_real : tvDist sim₁ mid ≤ ∑' z : spec.Range t × σ × Bool,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) := by
    rw [hsim₁_def, hmid_def]
    exact tvDist_bind_left_le _ _ _
  have h_second_real : tvDist mid sim₂ ≤ tvDist mx my := by
    rw [hmid_def, hsim₂_def]
    exact tvDist_bind_right_le _ _ _
  have h_tri :
      ENNReal.ofReal (tvDist sim₁ sim₂) ≤
        ENNReal.ofReal (tvDist sim₁ mid) + ENNReal.ofReal (tvDist mid sim₂) := by
    refine le_trans (ENNReal.ofReal_le_ofReal h_tri_real) ?_
    rw [ENNReal.ofReal_add (tvDist_nonneg _ _) (tvDist_nonneg _ _)]
  have h_second :
      ENNReal.ofReal (tvDist mid sim₂) ≤ ε s :=
    le_trans (ENNReal.ofReal_le_ofReal h_second_real)
      (le_trans (by rw [hmx_def, hmy_def]) (h_step_tv_S t hS s))
  have h_first :
      ENNReal.ofReal (tvDist sim₁ mid) ≤
        (∑' z : spec.Range t × σ × Bool,
          Pr[= z | mx] * expectedSCost impl₁ S ε (cont z.1) (qS - 1) z.2)
        + Pr[fun w : α × σ × Bool => w.2.2 = true | sim₁] := by
    refine le_trans (ENNReal.ofReal_le_ofReal h_first_real) ?_
    have hfsim₁ : sim₁ = mx >>= f₁ := hsim₁_def
    rw [hfsim₁]
    refine tsum_probOutput_mul_ofReal_tvDist_le_tsum_cost_plus_probEvent_bad
      (mx := mx) (f₁ := f₁) (f₂ := f₂)
      (cost := fun z => expectedSCost impl₁ S ε (cont z.1) (qS - 1) z.2)
      (fun z => ?_)
    simpa [hf₁_def, hf₂_def] using ih z.1 z.2
  have h_recurse :
      expectedSCost impl₁ S ε (query t >>= cont) qS (s, false) =
        ε s + ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl₁ t).run (s, false)] *
            expectedSCost impl₁ S ε (cont z.1) (qS - 1) z.2 := by
    rw [expectedSCost_query_bind, expectedSCostStep_costly_pos _ _ _ _ _ _ _ hS hqS]
  have h_sim₁_eq_again : sim₁ = (simulateQ impl₁ (query t >>= cont)).run (s, false) :=
    hsim₁_eq.symm
  calc
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      = ENNReal.ofReal (tvDist sim₁ sim₂) := by rw [hsim₁_eq, hsim₂_eq]
    _ ≤ ENNReal.ofReal (tvDist sim₁ mid) + ENNReal.ofReal (tvDist mid sim₂) := h_tri
    _ ≤ ((∑' z : spec.Range t × σ × Bool,
            Pr[= z | mx] * expectedSCost impl₁ S ε (cont z.1) (qS - 1) z.2)
          + Pr[fun w : α × σ × Bool => w.2.2 = true | sim₁])
          + ε s := add_le_add h_first h_second
    _ = (ε s + ∑' z : spec.Range t × σ × Bool,
              Pr[= z | mx] * expectedSCost impl₁ S ε (cont z.1) (qS - 1) z.2)
          + Pr[fun w : α × σ × Bool => w.2.2 = true | sim₁] := by
        rw [add_assoc, add_comm (Pr[fun w : α × σ × Bool => w.2.2 = true | sim₁]) (ε s),
            ← add_assoc, add_comm (∑' _, _) (ε s)]
    _ = expectedSCost impl₁ S ε (query t >>= cont) qS (s, false)
          + Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
        rw [h_recurse, ← hmx_def, h_sim₁_eq_again]

/-- The `query_bind` step for a free (non-S) query, state-dep ε version. The impls are
pointwise equal at this query, so the only contribution is from the IH; the budget `qS`
is preserved (no decrement). -/
private theorem ofReal_tvDist_simulateQ_run_free_query_bind_le_expectedSCost
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (h_step_eq_nS : ∀ (t : spec.Domain), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    {qS : ℕ} (hS : ¬ S t)
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      ENNReal.ofReal (tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p'))
        ≤ expectedSCost impl₁ S ε (cont u) qS p'
          + Pr[fun w : α × σ × Bool => w.2.2 = true |
              (simulateQ impl₁ (cont u)).run p'])
    (s : σ) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      ≤ expectedSCost impl₁ S ε (query t >>= cont) qS (s, false)
        + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  have hmy_eq : (impl₂ t).run (s, false) = mx := (h_step_eq_nS t hS (s, false)).symm
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  have hsim₁_eq : (simulateQ impl₁ (query t >>= cont)).run (s, false) = mx >>= f₁ := by
    simp [hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : (simulateQ impl₂ (query t >>= cont)).run (s, false) = mx >>= f₂ := by
    simp [hmy_eq, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have h_bd_real : tvDist (mx >>= f₁) (mx >>= f₂)
      ≤ ∑' z : spec.Range t × σ × Bool, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    tvDist_bind_left_le _ _ _
  have h_recurse :
      expectedSCost impl₁ S ε (query t >>= cont) qS (s, false) =
        ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl₁ t).run (s, false)] *
            expectedSCost impl₁ S ε (cont z.1) qS z.2 := by
    rw [expectedSCost_query_bind, expectedSCostStep_free _ _ _ _ _ _ _ hS]
  calc
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      = ENNReal.ofReal (tvDist (mx >>= f₁) (mx >>= f₂)) := by rw [hsim₁_eq, hsim₂_eq]
    _ ≤ ENNReal.ofReal
          (∑' z : spec.Range t × σ × Bool, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) :=
        ENNReal.ofReal_le_ofReal h_bd_real
    _ ≤ (∑' z : spec.Range t × σ × Bool,
            Pr[= z | mx] * expectedSCost impl₁ S ε (cont z.1) qS z.2)
          + Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] := by
        refine tsum_probOutput_mul_ofReal_tvDist_le_tsum_cost_plus_probEvent_bad
          (mx := mx) (f₁ := f₁) (f₂ := f₂)
          (cost := fun z => expectedSCost impl₁ S ε (cont z.1) qS z.2)
          (fun z => ?_)
        simpa [hf₁_def, hf₂_def] using ih z.1 z.2
    _ = expectedSCost impl₁ S ε (query t >>= cont) qS (s, false)
          + Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
        rw [h_recurse, ← hmx_def, ← hsim₁_eq]

/-! #### Inductive auxiliary lemma -/

/-- Auxiliary inductive lemma for the state-dep ε-perturbed bound. Inducts on `oa` and
case-splits each query on whether it's in the costly set `S` (decrement budget, charge
`ε s`) or free (no decrement, no charge). The bad-flag-true branch dominates the trivial
`tvDist ≤ 1` bound via `Pr[bad | sim₁] = 1`, so `expectedSCost = 0` is enough there. -/
private theorem ofReal_tvDist_simulateQ_run_le_expectedSCost_plus_probEvent_output_bad_aux
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : spec.Domain), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (p : σ × Bool) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p))
      ≤ expectedSCost impl₁ S ε oa qS p
        + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run p] := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self, ENNReal.ofReal_zero]
      exact zero_le _
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true =>
          have h_bad₁ : Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, true)] = 1 :=
            probEvent_simulateQ_run_bad_eq_one_of_bad impl₁ h_mono₁
              (query t >>= cont) (s, true) rfl
          have h_tv_le_one_real :
              tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true)) ≤ 1 :=
            tvDist_le_one _ _
          have h_lhs_le_one :
              ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true))) ≤ 1 := by
            calc ENNReal.ofReal _
                ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_tv_le_one_real
              _ = 1 := ENNReal.ofReal_one
          have h_cost_zero :
              expectedSCost impl₁ S ε (query t >>= cont) qS (s, true) = 0 :=
            expectedSCost_bad_eq_zero impl₁ S ε (query t >>= cont) qS s
          rw [h_cost_zero, zero_add, h_bad₁]
          exact h_lhs_le_one
      | false =>
          rw [isQueryBound_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : S t
          · simp only [hSt, if_true] at h_can h_cont
            have hqS_pos : 0 < qS := h_can
            exact ofReal_tvDist_simulateQ_run_costly_query_bind_le_expectedSCost
              impl₁ impl₂ S ε h_step_tv_S t cont hSt hqS_pos
              (fun u p' => ih u (h_cont u) p') s
          · simp only [hSt, if_false] at h_can h_cont
            exact ofReal_tvDist_simulateQ_run_free_query_bind_le_expectedSCost
              impl₁ impl₂ S ε h_step_eq_nS t cont hSt
              (fun u p' => ih u (h_cont u) p') s

/-! #### Public bridge lemmas -/

/-- **State-dep ε-perturbed identical-until-bad with output bad flag (joint state).**

Like `tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad`, but the per-step ε bound
is allowed to depend on the input state `s : σ` to the impl. The `qS · ε` term is replaced
by the **expected cumulative ε-cost** over the trace of S-queries fired during simulation,
captured by the recursive function `expectedSCost`.

Statement is in `ℝ≥0∞` to sidestep summability obligations on the cost trace; users that
supply a finiteness witness for `expectedSCost` can recover a real-valued statement via
`ENNReal.toReal`. -/
theorem ofReal_tvDist_simulateQ_run_le_expectedSCost_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : spec.Domain), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (p : σ × Bool) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p))
      ≤ expectedSCost impl₁ S ε oa qS p
        + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run p] :=
  ofReal_tvDist_simulateQ_run_le_expectedSCost_plus_probEvent_output_bad_aux
    impl₁ impl₂ S ε h_step_tv_S h_step_eq_nS h_mono₁ oa h_qb p

/-- **State-dep ε-perturbed identical-until-bad with output bad flag (projected output).**

Composing the joint-state lemma with the projection `Prod.fst : α × σ × Bool → α`, which
can only decrease TV distance (data-processing inequality `tvDist_map_le`). -/
theorem ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : spec.Domain), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (s₀ : σ) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false)))
      ≤ expectedSCost impl₁ S ε oa qS (s₀, false)
        + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ oa).run (s₀, false)] := by
  have h_joint :
      ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run (s₀, false))
          ((simulateQ impl₂ oa).run (s₀, false)))
        ≤ expectedSCost impl₁ S ε oa qS (s₀, false)
          + Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ oa).run (s₀, false)] :=
    ofReal_tvDist_simulateQ_run_le_expectedSCost_plus_probEvent_output_bad
      impl₁ impl₂ S ε h_step_tv_S h_step_eq_nS h_mono₁ oa h_qb (s₀, false)
  have h_map_real :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist ((simulateQ impl₁ oa).run (s₀, false))
            ((simulateQ impl₂ oa).run (s₀, false)) := by
    simpa [StateT.run'] using
      (tvDist_map_le (m := OracleComp spec') (α := α × σ × Bool) (β := α) Prod.fst
        ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false)))
  exact le_trans (ENNReal.ofReal_le_ofReal h_map_real) h_joint

/-! #### Constant-ε corollary (Phase A2 regression)

Specializing `expectedSCost` to a constant cost function `fun _ => ε` and using `IsQueryBound`
to bound the number of S-queries, the cumulative cost is dominated by `qS · ε`. Combined
with the state-dep main lemma this re-derives the selective constant-ε bound
in `ENNReal` form. -/

lemma expectedSCost_const_le_qS_mul
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : ℝ≥0∞)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (p : σ × Bool) :
    expectedSCost impl S (fun _ => ε) oa qS p ≤ qS * ε := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true => simp [expectedSCost_bad_eq_zero]
      | false =>
          rw [isQueryBound_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : S t
          · simp only [hSt, if_true] at h_can h_cont
            have hqS_pos : 0 < qS := h_can
            rw [expectedSCost_query_bind,
                expectedSCostStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
            have h_tsum_le : (∑' z : spec.Range t × σ × Bool,
                Pr[= z | (impl t).run (s, false)] *
                  expectedSCost impl S (fun _ => ε) (cont z.1) (qS - 1) z.2)
                ≤ (qS - 1 : ℕ) * ε := by
              calc (∑' z : spec.Range t × σ × Bool,
                    Pr[= z | (impl t).run (s, false)] *
                      expectedSCost impl S (fun _ => ε) (cont z.1) (qS - 1) z.2)
                  ≤ ∑' z : spec.Range t × σ × Bool,
                      Pr[= z | (impl t).run (s, false)] * ((qS - 1 : ℕ) * ε) :=
                    ENNReal.tsum_le_tsum fun z => by
                      gcongr
                      exact ih z.1 (qS := qS - 1) (h_cont z.1) z.2
                _ = (∑' z : spec.Range t × σ × Bool,
                        Pr[= z | (impl t).run (s, false)]) * ((qS - 1 : ℕ) * ε) :=
                    ENNReal.tsum_mul_right
                _ ≤ 1 * ((qS - 1 : ℕ) * ε) := by
                    gcongr
                    exact tsum_probOutput_le_one
                _ = (qS - 1 : ℕ) * ε := one_mul _
            have h_main : ε +
                  (∑' z : spec.Range t × σ × Bool,
                    Pr[= z | (impl t).run (s, false)] *
                      expectedSCost impl S (fun _ => ε) (cont z.1) (qS - 1) z.2)
                ≤ (qS : ℕ) * ε := by
              calc ε + (∑' z : spec.Range t × σ × Bool,
                    Pr[= z | (impl t).run (s, false)] *
                      expectedSCost impl S (fun _ => ε) (cont z.1) (qS - 1) z.2)
                  ≤ ε + ((qS - 1 : ℕ) * ε) := by
                    gcongr
                _ = ((qS - 1 : ℕ) + 1) * ε := by
                    rw [add_mul, one_mul, add_comm]
                _ = (qS : ℕ) * ε := by
                    congr 2
                    have : (qS - 1) + 1 = qS := Nat.sub_add_cancel hqS_pos
                    exact_mod_cast this
            exact h_main
          · simp only [hSt, if_false] at h_can h_cont
            rw [expectedSCost_query_bind,
                expectedSCostStep_free _ _ _ _ _ _ _ hSt]
            calc (∑' z : spec.Range t × σ × Bool,
                  Pr[= z | (impl t).run (s, false)] *
                    expectedSCost impl S (fun _ => ε) (cont z.1) qS z.2)
                ≤ ∑' z : spec.Range t × σ × Bool,
                    Pr[= z | (impl t).run (s, false)] * ((qS : ℕ) * ε) :=
                  ENNReal.tsum_le_tsum fun z => by
                    gcongr
                    exact ih z.1 (qS := qS) (h_cont z.1) z.2
              _ = (∑' z : spec.Range t × σ × Bool,
                      Pr[= z | (impl t).run (s, false)]) * ((qS : ℕ) * ε) :=
                  ENNReal.tsum_mul_right
              _ ≤ 1 * ((qS : ℕ) * ε) := by
                  gcongr
                  exact tsum_probOutput_le_one
              _ = (qS : ℕ) * ε := one_mul _

/-- **Constant-ε version of the bridge as a corollary of the state-dep version.**

This is the ENNReal-form analogue of the existing real-valued
`tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad`. It demonstrates that
the state-dep version subsumes the constant-ε version: instantiate
`ε := fun _ => ENNReal.ofReal ε_const` and bound `expectedSCost` by
`qS * ENNReal.ofReal ε_const`. -/
theorem ofReal_tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ε : ℝ≥0∞)
    (S : spec.Domain → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε)
    (h_step_eq_nS : ∀ (t : spec.Domain), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound oa qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b))
    (p : σ × Bool) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p))
      ≤ qS * ε
        + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run p] := by
  have h_step_tv_S' : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)))
        ≤ (fun _ : σ => ε) s := h_step_tv_S
  refine le_trans
    (ofReal_tvDist_simulateQ_run_le_expectedSCost_plus_probEvent_output_bad
      impl₁ impl₂ S (fun _ => ε) h_step_tv_S' h_step_eq_nS h_mono₁ oa h_qb p) ?_
  gcongr
  exact expectedSCost_const_le_qS_mul impl₁ S ε oa h_qb p

end IdenticalUntilBadEpsilonStateDep

end OracleComp.ProgramLogic.Relational
