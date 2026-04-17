/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.FromUnary
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Unary.HandlerSpecs

/-!
# Lifting `Std.Do` handler triples to relational triples

This file generalizes the unary-to-relational bridge in
`Relational.FromUnary` from pure `OracleComp` computations to *stateful
handlers*. It bridges the gap between

* `Std.Do.Triple` specs for `QueryImpl spec (StateT σ (OracleComp spec'))`,
  produced by `mvcgen` and registered via `@[spec]` (e.g.
  `cachingOracle_triple`, `seededOracle_triple`, `loggingOracle_triple`),
  and
* `RelTriple` couplings on the `.run` distributions of those handlers,
  consumed by `relTriple_simulateQ_run` for whole-program reasoning.

## Main results

* `relTriple_run_of_triple` — *per-call lift*: two unary `Std.Do.Triple`s
  on `StateT σᵢ (OracleComp specᵢ)` give a `RelTriple` on the products
  of the two `.run` distributions, with the relational postcondition the
  pairwise conjunction of the unary postconditions. This is the stateful
  analogue of `relTriple_prod_of_triple`.
* `relTriple_simulateQ_run_of_triples` — *whole-program lift*: combines
  per-call unary triples on two simulator handlers with a synchronization
  condition relating their postconditions, yielding a `RelTriple` for the
  entire `simulateQ`-driven simulation.
* `relTriple_simulateQ_run_of_impl_eq_triple` — *identical-up-to-invariant
  lift*: takes a unary invariant-preservation `Std.Do.Triple` on one
  handler plus pointwise-equality-on-Inv with the other, and yields an
  `EqRel` whole-program coupling. This is the direct bridge from the
  `mvcgen` proof style to the support-based
  `relTriple_simulateQ_run_of_impl_eq_preservesInv`.

The `hsync` argument is what bridges product (independent) reasoning to
the synchronized coupling expected by `relTriple_simulateQ_run`: even if
the underlying unary triples are independent, an external sync argument
(determinism of the handler, agreement of random choices, etc.) is needed
to upgrade pairwise postconditions to output equality plus a state
invariant.

The whole-program lift fixes `OracleSpec.{0, 0}` because the unary
`triple_stateT_iff_forall_support` bridge in
`VCVio.ProgramLogic.Unary.HandlerSpecs` is stated at that universe.
-/

open ENNReal OracleSpec OracleComp
open Std.Do

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {σ₁ σ₂ α β : Type}

/-! ### Per-call lifts (one transformer layer) -/

/-- Per-call lift from two unary `Std.Do.Triple`s to a relational product
coupling on the `.run` distributions.

Each triple's postcondition is interpreted as a property of the
`(value, final_state)` pair; the relational postcondition is the
pairwise conjunction. This is the stateful generalization of
`relTriple_prod_of_triple`. -/
theorem relTriple_run_of_triple
    (mx₁ : StateT σ₁ (OracleComp spec₁) α)
    (mx₂ : StateT σ₂ (OracleComp spec₂) β)
    (s₁ : σ₁) (s₂ : σ₂)
    (P₁ : σ₁ → Prop) (P₂ : σ₂ → Prop)
    (Q₁ : α → σ₁ → Prop) (Q₂ : β → σ₂ → Prop)
    (hP₁ : P₁ s₁) (hP₂ : P₂ s₂)
    (h₁ : Std.Do.Triple mx₁
      (spred(fun s => ⌜P₁ s⌝))
      (⇓a s' => ⌜Q₁ a s'⌝))
    (h₂ : Std.Do.Triple mx₂
      (spred(fun s => ⌜P₂ s⌝))
      (⇓b s' => ⌜Q₂ b s'⌝)) :
    RelTriple (mx₁.run s₁) (mx₂.run s₂)
      (fun p₁ p₂ => Q₁ p₁.1 p₁.2 ∧ Q₂ p₂.1 p₂.2) := by
  rw [OracleComp.ProgramLogic.StdDo.triple_stateT_iff_forall_support] at h₁ h₂
  refine relTriple_prod
    (P := fun (p : α × σ₁) => Q₁ p.1 p.2)
    (Q := fun (p : β × σ₂) => Q₂ p.1 p.2)
    ?_ ?_
  · rintro ⟨a, s'⟩ hmem
    exact h₁ s₁ hP₁ a s' hmem
  · rintro ⟨b, s'⟩ hmem
    exact h₂ s₂ hP₂ b s' hmem

/-- `WriterT` analogue of `relTriple_run_of_triple`.

Two unary `Std.Do.Triple`s on `WriterT ωᵢ (OracleComp specᵢ)` lift to a
product coupling on the `(value, accumulated_log)` pairs of the underlying
`OracleComp`. The starting log of each side is fixed at `s₁ : ω₁` and
`s₂ : ω₂` and the postconditions are read at `Q₁ a (s₁ ++ w)` /
`Q₂ b (s₂ ++ w)` where `w` is the writer increment produced by the run.

The starting logs default to `∅` for the typical `WriterT.run` call but
are kept arbitrary so the lemma composes cleanly with prefix-style log
specs (e.g. `loggingOracle`'s `log' = log₀ ++ [⟨t, v⟩]`). -/
theorem relTriple_run_writerT_of_triple
    {ω₁ ω₂ : Type}
    [EmptyCollection ω₁] [Append ω₁] [LawfulAppend ω₁]
    [EmptyCollection ω₂] [Append ω₂] [LawfulAppend ω₂]
    (mx₁ : WriterT ω₁ (OracleComp spec₁) α)
    (mx₂ : WriterT ω₂ (OracleComp spec₂) β)
    (s₁ : ω₁) (s₂ : ω₂)
    (P₁ : ω₁ → Prop) (P₂ : ω₂ → Prop)
    (Q₁ : α → ω₁ → Prop) (Q₂ : β → ω₂ → Prop)
    (hP₁ : P₁ s₁) (hP₂ : P₂ s₂)
    (h₁ : Std.Do.Triple mx₁
      (spred(fun s => ⌜P₁ s⌝))
      (⇓a s' => ⌜Q₁ a s'⌝))
    (h₂ : Std.Do.Triple mx₂
      (spred(fun s => ⌜P₂ s⌝))
      (⇓b s' => ⌜Q₂ b s'⌝)) :
    RelTriple mx₁.run mx₂.run
      (fun p₁ p₂ => Q₁ p₁.1 (s₁ ++ p₁.2) ∧ Q₂ p₂.1 (s₂ ++ p₂.2)) := by
  rw [OracleComp.ProgramLogic.StdDo.triple_writerT_iff_forall_support] at h₁ h₂
  refine relTriple_prod
    (P := fun (p : α × ω₁) => Q₁ p.1 (s₁ ++ p.2))
    (Q := fun (p : β × ω₂) => Q₂ p.1 (s₂ ++ p.2))
    ?_ ?_
  · rintro ⟨a, w⟩ hmem
    exact h₁ s₁ hP₁ a w hmem
  · rintro ⟨b, w⟩ hmem
    exact h₂ s₂ hP₂ b w hmem

/-- Whole-program handler lift: given matching unary handler triples on
two simulators with parametric pre/postconditions and a synchronization
condition relating the postconditions, derive a `RelTriple` on the entire
`simulateQ` outputs.

The unary triples are quantified over the *initial* handler state; their
postconditions may depend on it. The synchronization condition `hsync`
extracts output equality and the state-relation invariant from a paired
instance of the two unary postconditions, which is exactly the bridge
needed by `relTriple_simulateQ_run`. -/
theorem relTriple_simulateQ_run_of_triples
    {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (Q₁ : ∀ (t : spec.Domain), σ₁ → spec.Range t → σ₁ → Prop)
    (Q₂ : ∀ (t : spec.Domain), σ₂ → spec.Range t → σ₂ → Prop)
    (h₁ : ∀ (t : spec.Domain) (s : σ₁), Std.Do.Triple
      (impl₁ t : StateT σ₁ (OracleComp spec₁) (spec.Range t))
      (spred(fun s' => ⌜s' = s⌝))
      (⇓a s' => ⌜Q₁ t s a s'⌝))
    (h₂ : ∀ (t : spec.Domain) (s : σ₂), Std.Do.Triple
      (impl₂ t : StateT σ₂ (OracleComp spec₂) (spec.Range t))
      (spred(fun s' => ⌜s' = s⌝))
      (⇓a s' => ⌜Q₂ t s a s'⌝))
    (hsync : ∀ (t : spec.Domain) (s₁' : σ₁) (s₂' : σ₂),
      R_state s₁' s₂' →
      ∀ a₁ s₁'' a₂ s₂'',
        Q₁ t s₁' a₁ s₁'' → Q₂ t s₂' a₂ s₂'' →
          a₁ = a₂ ∧ R_state s₁'' s₂'')
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run s₁)
      ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2) := by
  refine relTriple_simulateQ_run impl₁ impl₂ R_state oa ?_ s₁ s₂ hs
  intro t s₁' s₂' hs'
  have hcombine := relTriple_run_of_triple
    (mx₁ := impl₁ t) (mx₂ := impl₂ t)
    (s₁ := s₁') (s₂ := s₂')
    (P₁ := fun s => s = s₁') (P₂ := fun s => s = s₂')
    (Q₁ := Q₁ t s₁') (Q₂ := Q₂ t s₂')
    rfl rfl (h₁ t s₁') (h₂ t s₂')
  refine relTriple_post_mono hcombine ?_
  rintro ⟨a₁, s₁''⟩ ⟨a₂, s₂''⟩ ⟨hQ₁, hQ₂⟩
  exact hsync t s₁' s₂' hs' a₁ s₁'' a₂ s₂'' hQ₁ hQ₂

/-- Output-projection variant of `relTriple_simulateQ_run_of_triples`.

Drops the final state from both sides, leaving only a relational equality
on the return values. This is the canonical shape needed for probability
transport (via `probOutput_eq_of_relTriple_eqRel`), matching
`relTriple_simulateQ_run'` at the handler-triple layer. -/
theorem relTriple_simulateQ_run'_of_triples
    {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (Q₁ : ∀ (t : spec.Domain), σ₁ → spec.Range t → σ₁ → Prop)
    (Q₂ : ∀ (t : spec.Domain), σ₂ → spec.Range t → σ₂ → Prop)
    (h₁ : ∀ (t : spec.Domain) (s : σ₁), Std.Do.Triple
      (impl₁ t : StateT σ₁ (OracleComp spec₁) (spec.Range t))
      (spred(fun s' => ⌜s' = s⌝))
      (⇓a s' => ⌜Q₁ t s a s'⌝))
    (h₂ : ∀ (t : spec.Domain) (s : σ₂), Std.Do.Triple
      (impl₂ t : StateT σ₂ (OracleComp spec₂) (spec.Range t))
      (spred(fun s' => ⌜s' = s⌝))
      (⇓a s' => ⌜Q₂ t s a s'⌝))
    (hsync : ∀ (t : spec.Domain) (s₁' : σ₁) (s₂' : σ₂),
      R_state s₁' s₂' →
      ∀ a₁ s₁'' a₂ s₂'',
        Q₁ t s₁' a₁ s₁'' → Q₂ t s₂' a₂ s₂'' →
          a₁ = a₂ ∧ R_state s₁'' s₂'')
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run' s₁)
      ((simulateQ impl₂ oa).run' s₂)
      (EqRel α) := by
  have hfull := relTriple_simulateQ_run_of_triples
    impl₁ impl₂ R_state oa Q₁ Q₂ h₁ h₂ hsync s₁ s₂ hs
  have hweak : RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => (EqRel α) p₁.1 p₂.1) := by
    apply relTriple_post_mono hfull
    intro _ _ hp; exact hp.1
  exact relTriple_map hweak

/-! ### Bridge to support-based simulation lemmas

The lemmas below convert `Std.Do.Triple` invariant specs produced by
`mvcgen` into the `support`-based hypotheses that the existing
`Relational/SimulateQ.lean` infrastructure consumes. They're the
recommended entry point from the `mvcgen` proof style into whole-program
relational reasoning. -/

/-- Convert a unary `Std.Do.Triple` invariant-preservation spec into the
`support`-based preservation hypothesis consumed by
`relTriple_simulateQ_run_of_impl_eq_preservesInv` and friends.

The `mvcgen` proof style produces invariant-preservation specs as
`Std.Do.Triple` judgments; most of the existing `SimulateQ.lean`
relational infrastructure is phrased in terms of `support`. This lemma
is the direct translator, lifting over `triple_stateT_iff_forall_support`. -/
theorem support_preservesInv_of_triple
    {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
    {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (Inv : σ → Prop)
    (h : ∀ (t : spec.Domain), Std.Do.Triple
      (impl t : StateT σ (OracleComp spec₁) (spec.Range t))
      (spred(fun s' => ⌜Inv s'⌝))
      (⇓_ s' => ⌜Inv s'⌝)) :
    ∀ (t : spec.Domain) (s : σ), Inv s →
      ∀ z ∈ support ((impl t).run s), Inv z.2 := by
  intro t s hs z hz
  have htriple := h t
  rw [OracleComp.ProgramLogic.StdDo.triple_stateT_iff_forall_support] at htriple
  rcases z with ⟨a, s'⟩
  exact htriple s hs a s' hz

/-- Whole-program equality coupling when two handlers agree pointwise on
an invariant `Inv` and the target handler preserves `Inv`. This is the
`Std.Do.Triple`-fronted version of
`relTriple_simulateQ_run_of_impl_eq_preservesInv`: the preservation
hypothesis is supplied via `mvcgen`-style `Std.Do.Triple`s rather than a
`support`-based quantifier. -/
theorem relTriple_simulateQ_run_of_impl_eq_triple
    {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
    {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (oa : OracleComp spec α)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain), Std.Do.Triple
      (impl₂ t : StateT σ ProbComp (spec.Range t))
      (spred(fun s' => ⌜Inv s'⌝))
      (⇓_ s' => ⌜Inv s'⌝))
    (s : σ) (hs : Inv s) :
    RelTriple
      ((simulateQ impl₁ oa).run s)
      ((simulateQ impl₂ oa).run s)
      (EqRel (α × σ)) :=
  relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
    impl₁ impl₂ Inv oa himpl_eq
    (support_preservesInv_of_triple (spec₁ := unifSpec)
      (σ := σ) (impl := impl₂) (Inv := Inv) hpres₂)
    s hs

/-! ## Smoke tests -/

section SmokeTests

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
variable [DecidableEq ι]

/-- Smoke test: independent product coupling for two `cachingOracle` runs
on possibly different initial caches. The cache-monotonicity invariant
holds on each side via `cachingOracle_triple`; the output values are not
synced (caching is non-deterministic). -/
private example
    (t : spec.Domain) (cache_a cache_b : QueryCache spec) :
    RelTriple
      ((cachingOracle t :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t)).run cache_a)
      ((cachingOracle t :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t)).run cache_b)
      (fun p₁ p₂ =>
        (cache_a ≤ p₁.2 ∧ p₁.2 t = some p₁.1) ∧
        (cache_b ≤ p₂.2 ∧ p₂.2 t = some p₂.1)) :=
  relTriple_run_of_triple
    (mx₁ := cachingOracle t) (mx₂ := cachingOracle t)
    (s₁ := cache_a) (s₂ := cache_b)
    (P₁ := fun cache => cache_a ≤ cache)
    (P₂ := fun cache => cache_b ≤ cache)
    (Q₁ := fun v cache' => cache_a ≤ cache' ∧ cache' t = some v)
    (Q₂ := fun v cache' => cache_b ≤ cache' ∧ cache' t = some v)
    (hP₁ := le_refl _) (hP₂ := le_refl _)
    (h₁ := OracleComp.ProgramLogic.StdDo.cachingOracle_triple t cache_a)
    (h₂ := OracleComp.ProgramLogic.StdDo.cachingOracle_triple t cache_b)

/-- Smoke test: synchronized coupling for two `seededOracle` runs starting
from the same seed `seed₀` with `seed₀ t = u :: us`. By
`seededOracle_triple_of_cons`, both runs deterministically pop the head
value, so the output values and post-states coincide. -/
private example
    (t : spec.Domain) (u : spec.Range t) (us : List (spec.Range t))
    (seed₀ : QuerySeed spec) (h : seed₀ t = u :: us) :
    RelTriple
      ((seededOracle t :
        StateT (QuerySeed spec) (OracleComp spec) (spec.Range t)).run seed₀)
      ((seededOracle t :
        StateT (QuerySeed spec) (OracleComp spec) (spec.Range t)).run seed₀)
      (fun p₁ p₂ => p₁ = p₂) := by
  refine relTriple_post_mono
    (relTriple_run_of_triple
      (mx₁ := seededOracle t) (mx₂ := seededOracle t)
      (s₁ := seed₀) (s₂ := seed₀)
      (P₁ := fun seed => seed = seed₀) (P₂ := fun seed => seed = seed₀)
      (Q₁ := fun v seed' => v = u ∧ seed' = Function.update seed₀ t us)
      (Q₂ := fun v seed' => v = u ∧ seed' = Function.update seed₀ t us)
      rfl rfl
      (OracleComp.ProgramLogic.StdDo.seededOracle_triple_of_cons t u us seed₀ h)
      (OracleComp.ProgramLogic.StdDo.seededOracle_triple_of_cons t u us seed₀ h))
    ?_
  rintro ⟨v₁, seed₁'⟩ ⟨v₂, seed₂'⟩ ⟨⟨hv₁, hseed₁'⟩, ⟨hv₂, hseed₂'⟩⟩
  exact Prod.ext (hv₁.trans hv₂.symm) (hseed₁'.trans hseed₂'.symm)

/-- Smoke test: independent product coupling for two `loggingOracle` runs.
The log-extension postcondition (`log' = log₀ ++ [⟨t, v⟩]`) holds on each
side via `loggingOracle_triple`; the output values are not synced
(`loggingOracle` makes a fresh live query on every call). -/
private example
    (t : spec.Domain) (log_a log_b : QueryLog spec) :
    RelTriple
      (loggingOracle t :
        WriterT (QueryLog spec) (OracleComp spec) (spec.Range t)).run
      (loggingOracle t :
        WriterT (QueryLog spec) (OracleComp spec) (spec.Range t)).run
      (fun p₁ p₂ =>
        log_a ++ p₁.2 = log_a ++ [⟨t, p₁.1⟩] ∧
        log_b ++ p₂.2 = log_b ++ [⟨t, p₂.1⟩]) := by
  refine relTriple_run_writerT_of_triple
    (mx₁ := (loggingOracle t : WriterT _ (OracleComp spec) _))
    (mx₂ := (loggingOracle t : WriterT _ (OracleComp spec) _))
    (s₁ := log_a) (s₂ := log_b)
    (P₁ := fun log => log = log_a) (P₂ := fun log => log = log_b)
    (Q₁ := fun v log' => log' = log_a ++ [⟨t, v⟩])
    (Q₂ := fun v log' => log' = log_b ++ [⟨t, v⟩])
    rfl rfl ?_ ?_
  · exact OracleComp.ProgramLogic.StdDo.loggingOracle_triple t log_a
  · exact OracleComp.ProgramLogic.StdDo.loggingOracle_triple t log_b

end SmokeTests

end OracleComp.ProgramLogic.Relational
