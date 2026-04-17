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

/-- `Monoid`-variant of `relTriple_run_writerT_of_triple`.

For `WriterT ωᵢ (OracleComp specᵢ)` with `[Monoid ωᵢ]`, two unary
`Std.Do.Triple`s lift to a product coupling on the `(value,
accumulated_log)` pairs where each postcondition is read at
`Q₁ a (s₁ * w)` / `Q₂ b (s₂ * w)` (monoid multiplication). Used by
`countingOracle` / `costOracle` reasoning. -/
theorem relTriple_run_writerT_of_triple_monoid
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
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
      (fun p₁ p₂ => Q₁ p₁.1 (s₁ * p₁.2) ∧ Q₂ p₂.1 (s₂ * p₂.2)) := by
  rw [OracleComp.ProgramLogic.StdDo.triple_writerT_iff_forall_support_monoid] at h₁ h₂
  refine relTriple_prod
    (P := fun (p : α × ω₁) => Q₁ p.1 (s₁ * p.2))
    (Q := fun (p : β × ω₂) => Q₂ p.1 (s₂ * p.2))
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

/-- `WriterT` analogue of `relTriple_simulateQ_run_of_triples` (monoid variant).

Given matching unary `Std.Do.Triple` specs for two `WriterT`-based
handlers, a monoid-congruent writer relation `R_writer` (via `hR_one` and
`hR_mul`), and a synchronization condition on per-query postconditions,
derive a whole-program `RelTriple` on the full `(output, writer)` outputs
of the two simulations.

The per-query triples are specialized to starting writer `1`
(which corresponds to `WriterT.run`-style entry); their postconditions
are evaluated at the resulting step writer. Typical instantiations are
`countingOracle_triple` and `costOracle_triple` with `qc₀ = 0` /
`s₀ = 1`. -/
theorem relTriple_simulateQ_run_writerT_of_triples
    {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec₂)))
    (R_writer : ω₁ → ω₂ → Prop)
    (hR_one : R_writer 1 1)
    (hR_mul : ∀ w₁ w₁' w₂ w₂', R_writer w₁ w₂ → R_writer w₁' w₂' →
      R_writer (w₁ * w₁') (w₂ * w₂'))
    (oa : OracleComp spec α)
    (Q₁ : ∀ (t : spec.Domain), spec.Range t → ω₁ → Prop)
    (Q₂ : ∀ (t : spec.Domain), spec.Range t → ω₂ → Prop)
    (h₁ : ∀ (t : spec.Domain), Std.Do.Triple
      (impl₁ t : WriterT ω₁ (OracleComp spec₁) (spec.Range t))
      (spred(fun s => ⌜s = 1⌝))
      (⇓a s' => ⌜Q₁ t a s'⌝))
    (h₂ : ∀ (t : spec.Domain), Std.Do.Triple
      (impl₂ t : WriterT ω₂ (OracleComp spec₂) (spec.Range t))
      (spred(fun s => ⌜s = 1⌝))
      (⇓a s' => ⌜Q₂ t a s'⌝))
    (hsync : ∀ (t : spec.Domain) a₁ w₁ a₂ w₂,
      Q₁ t a₁ w₁ → Q₂ t a₂ w₂ → a₁ = a₂ ∧ R_writer w₁ w₂) :
    RelTriple
      (simulateQ impl₁ oa).run
      (simulateQ impl₂ oa).run
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2) := by
  refine relTriple_simulateQ_run_writerT
    impl₁ impl₂ R_writer hR_one hR_mul oa ?_
  intro t
  have hcombine := relTriple_run_writerT_of_triple_monoid
    (mx₁ := impl₁ t) (mx₂ := impl₂ t)
    (s₁ := (1 : ω₁)) (s₂ := (1 : ω₂))
    (P₁ := fun s => s = 1) (P₂ := fun s => s = 1)
    (Q₁ := Q₁ t) (Q₂ := Q₂ t)
    rfl rfl (h₁ t) (h₂ t)
  refine relTriple_post_mono hcombine ?_
  rintro ⟨a₁, w₁⟩ ⟨a₂, w₂⟩ ⟨hQ₁, hQ₂⟩
  rw [one_mul] at hQ₁ hQ₂
  exact hsync t a₁ w₁ a₂ w₂ hQ₁ hQ₂

/-- Output-projection variant of `relTriple_simulateQ_run_writerT_of_triples`.

Drops the writer component, leaving only `EqRel α` on outputs. -/
theorem relTriple_simulateQ_run_writerT'_of_triples
    {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec₂)))
    (R_writer : ω₁ → ω₂ → Prop)
    (hR_one : R_writer 1 1)
    (hR_mul : ∀ w₁ w₁' w₂ w₂', R_writer w₁ w₂ → R_writer w₁' w₂' →
      R_writer (w₁ * w₁') (w₂ * w₂'))
    (oa : OracleComp spec α)
    (Q₁ : ∀ (t : spec.Domain), spec.Range t → ω₁ → Prop)
    (Q₂ : ∀ (t : spec.Domain), spec.Range t → ω₂ → Prop)
    (h₁ : ∀ (t : spec.Domain), Std.Do.Triple
      (impl₁ t : WriterT ω₁ (OracleComp spec₁) (spec.Range t))
      (spred(fun s => ⌜s = 1⌝))
      (⇓a s' => ⌜Q₁ t a s'⌝))
    (h₂ : ∀ (t : spec.Domain), Std.Do.Triple
      (impl₂ t : WriterT ω₂ (OracleComp spec₂) (spec.Range t))
      (spred(fun s => ⌜s = 1⌝))
      (⇓a s' => ⌜Q₂ t a s'⌝))
    (hsync : ∀ (t : spec.Domain) a₁ w₁ a₂ w₂,
      Q₁ t a₁ w₁ → Q₂ t a₂ w₂ → a₁ = a₂ ∧ R_writer w₁ w₂) :
    RelTriple
      (Prod.fst <$> (simulateQ impl₁ oa).run)
      (Prod.fst <$> (simulateQ impl₂ oa).run)
      (EqRel α) := by
  have hfull := relTriple_simulateQ_run_writerT_of_triples
    impl₁ impl₂ R_writer hR_one hR_mul oa Q₁ Q₂ h₁ h₂ hsync
  have hweak : RelTriple (simulateQ impl₁ oa).run (simulateQ impl₂ oa).run
      (fun p₁ p₂ => (EqRel α) p₁.1 p₂.1) :=
    relTriple_post_mono hfull (fun _ _ hp => hp.1)
  exact relTriple_map hweak

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

/-- Smoke test: independent product coupling for two `countingOracle`
runs. Each side's count increments by `QueryCount.single t` via
`countingOracle_triple`; the returned values are not synced (fresh
`query` on each side). -/
private example
    (t : spec.Domain) (qc_a qc_b : QueryCount ι) :
    RelTriple
      (countingOracle t :
        WriterT (QueryCount ι) (OracleComp spec) (spec.Range t)).run
      (countingOracle t :
        WriterT (QueryCount ι) (OracleComp spec) (spec.Range t)).run
      (fun p₁ p₂ =>
        (qc_a : QueryCount ι) + p₁.2 = qc_a + QueryCount.single t ∧
        (qc_b : QueryCount ι) + p₂.2 = qc_b + QueryCount.single t) := by
  have hmul : ∀ x y : QueryCount ι,
      (@HMul.hMul (QueryCount ι) (QueryCount ι) (QueryCount ι)
        (@instHMul _ (Monoid.toMulOneClass.toMul)) x y) = x + y := fun _ _ => rfl
  refine relTriple_post_mono
    (relTriple_run_writerT_of_triple_monoid
      (mx₁ := (countingOracle t : WriterT _ (OracleComp spec) _))
      (mx₂ := (countingOracle t : WriterT _ (OracleComp spec) _))
      (s₁ := qc_a) (s₂ := qc_b)
      (P₁ := fun qc => qc = qc_a) (P₂ := fun qc => qc = qc_b)
      (Q₁ := fun _v qc' => qc' = qc_a + QueryCount.single t)
      (Q₂ := fun _v qc' => qc' = qc_b + QueryCount.single t)
      rfl rfl
      (OracleComp.ProgramLogic.StdDo.countingOracle_triple t qc_a)
      (OracleComp.ProgramLogic.StdDo.countingOracle_triple t qc_b))
    ?_
  rintro ⟨_, w₁⟩ ⟨_, w₂⟩ ⟨h₁, h₂⟩
  exact ⟨(hmul qc_a w₁).symm.trans h₁, (hmul qc_b w₂).symm.trans h₂⟩

/-- Smoke test: independent product coupling for two `costOracle` runs
with the same cost function `costFn`. Each side's accumulator multiplies
by `costFn t` via `costOracle_triple`; values are not synced. -/
private example {ω : Type} [Monoid ω]
    (costFn : spec.Domain → ω) (t : spec.Domain) (s_a s_b : ω) :
    RelTriple
      (costOracle costFn t : WriterT ω (OracleComp spec) (spec.Range t)).run
      (costOracle costFn t : WriterT ω (OracleComp spec) (spec.Range t)).run
      (fun p₁ p₂ =>
        s_a * p₁.2 = s_a * costFn t ∧
        s_b * p₂.2 = s_b * costFn t) := by
  refine relTriple_run_writerT_of_triple_monoid
    (mx₁ := (costOracle costFn t : WriterT _ (OracleComp spec) _))
    (mx₂ := (costOracle costFn t : WriterT _ (OracleComp spec) _))
    (s₁ := s_a) (s₂ := s_b)
    (P₁ := fun s => s = s_a) (P₂ := fun s => s = s_b)
    (Q₁ := fun _v s' => s' = s_a * costFn t)
    (Q₂ := fun _v s' => s' = s_b * costFn t)
    rfl rfl ?_ ?_
  · exact OracleComp.ProgramLogic.StdDo.costOracle_triple costFn t s_a
  · exact OracleComp.ProgramLogic.StdDo.costOracle_triple costFn t s_b

/-! ### Whole-program `WriterT` smoke tests -/

/-- Smoke test: two `countingOracle` simulations on the same program `oa`
agree on outputs and on accumulated counts under the diagonal coupling.
Uses `relTriple_simulateQ_run_writerT` with `R_writer = Eq`, which is
trivially reflexive and closed under the monoid operation. The per-query
triple is supplied by `relTriple_refl`. -/
private example {α : Type} (oa : OracleComp spec α) :
    RelTriple
      (simulateQ
        (countingOracle :
          QueryImpl spec (WriterT (QueryCount ι) (OracleComp spec))) oa).run
      (simulateQ
        (countingOracle :
          QueryImpl spec (WriterT (QueryCount ι) (OracleComp spec))) oa).run
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) := by
  refine relTriple_simulateQ_run_writerT
    (impl₁ := countingOracle) (impl₂ := countingOracle)
    (R_writer := fun (w₁ w₂ : QueryCount ι) => w₁ = w₂)
    rfl (by rintro _ _ _ _ rfl rfl; rfl) oa ?_
  intro t
  refine relTriple_post_mono
    (relTriple_refl (spec₁ := spec)
      (oa := (countingOracle t :
        WriterT (QueryCount ι) (OracleComp spec) (spec.Range t)).run)) ?_
  rintro ⟨a, w⟩ ⟨b, w'⟩ heq
  simp only [EqRel, Prod.mk.injEq] at heq
  exact heq

/-- Smoke test: two `costOracle` simulations on the same program `oa`
with the same cost function agree on outputs and on accumulated costs
under the diagonal coupling. -/
private example {ω : Type} [Monoid ω]
    (costFn : spec.Domain → ω) {α : Type} (oa : OracleComp spec α) :
    RelTriple
      (simulateQ
        (costOracle costFn :
          QueryImpl spec (WriterT ω (OracleComp spec))) oa).run
      (simulateQ
        (costOracle costFn :
          QueryImpl spec (WriterT ω (OracleComp spec))) oa).run
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) := by
  refine relTriple_simulateQ_run_writerT
    (impl₁ := costOracle costFn) (impl₂ := costOracle costFn)
    (R_writer := fun (w₁ w₂ : ω) => w₁ = w₂)
    rfl (by rintro _ _ _ _ rfl rfl; rfl) oa ?_
  intro t
  refine relTriple_post_mono
    (relTriple_refl (spec₁ := spec)
      (oa := (costOracle costFn t :
        WriterT ω (OracleComp spec) (spec.Range t)).run)) ?_
  rintro ⟨a, w⟩ ⟨b, w'⟩ heq
  simp only [EqRel, Prod.mk.injEq] at heq
  exact heq

end SmokeTests

end OracleComp.ProgramLogic.Relational
