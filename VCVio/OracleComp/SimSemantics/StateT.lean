/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Query Implementations with State Monads

This file gives lemmas about `QueryImpl spec m` when `m` is something like `StateT σ n`.

TODO: should generalize things to `MonadState` once laws for it exist.
-/

universe u v w

open OracleSpec

namespace QueryImpl

/-- Push an outer oracle interpretation through the base monad of a
`StateT`-valued query implementation. -/
noncomputable def stateTMapBase {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁))) :
    QueryImpl spec₀ (StateT σ m) := fun t =>
  StateT.mk fun s => simulateQ outer ((inner t).run s)

/-- Running a `StateT` handler and then interpreting its base oracle
computations is the same as first mapping the handler's base through the
outer interpreter. -/
theorem simulateQ_stateTMapBase_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run s) =
      (simulateQ (outer.stateTMapBase inner) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
      simp only [simulateQ_bind, StateT.run_bind]
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, stateTMapBase]
      refine bind_congr fun z => ?_
      exact ih z.1 z.2

/-- Output-only corollary of `simulateQ_stateTMapBase_run`. -/
theorem simulateQ_stateTMapBase_run' {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run' s) =
      (simulateQ (outer.stateTMapBase inner) oa).run' s := by
  change simulateQ outer (Prod.fst <$> (simulateQ inner oa).run s) = _
  rw [simulateQ_map, simulateQ_stateTMapBase_run]
  rfl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of state monads for
two different contexts `σ₁` and `σ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `σ₁ × σ₂` state. -/
def prodStateT {ι₁ ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type _ → Type _} [Functor m] {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec₁ (StateT σ₁ m))
    (impl₂ : QueryImpl spec₂ (StateT σ₂ m)) :
    QueryImpl (spec₁ + spec₂) (StateT (σ₁ × σ₂) m)
  | .inl t => StateT.mk fun | (s₁, s₂) => Prod.map id (·, s₂) <$> (impl₁ t).run s₁
  | .inr t => StateT.mk fun | (s₁, s₂) => Prod.map id (s₁, ·) <$> (impl₂ t).run s₂

/-- Indexed version of `QueryImpl.prodStateT`. Note that `m` cannot vary with `t`.
dtumad: The `Function.update` thing is nice but forces `DecidableEq`. -/
def piStateT {τ : Type} [DecidableEq τ] {ι : τ → Type _}
    {spec : (t : τ) → OracleSpec (ι t)}
    {m : Type _ → Type _} [Monad m] {σ : τ → Type _}
    (impl : (t : τ) → QueryImpl (spec t) (StateT (σ t) m)) :
    QueryImpl (OracleSpec.sigma spec) (StateT ((t : τ) → σ t) m)
  | ⟨t, q⟩ => StateT.mk fun s => Prod.map id (Function.update s t) <$> (impl t q).run (s t)

/-- Lift a stateful query implementation to a `(state × Bool)`-stateful version that threads
the boolean (bad) flag unchanged. The output value and updated state come from the
underlying `impl`; the second `Bool` component is preserved verbatim across each query. -/
def withBadFlag {ι : Type _} {spec : OracleSpec ι}
    {m : Type _ → Type _} [Functor m] {σ : Type _}
    (impl : QueryImpl spec (StateT σ m)) :
    QueryImpl spec (StateT (σ × Bool) m) := fun t =>
  StateT.mk fun | (s, b) => Prod.map id (·, b) <$> (impl t).run s

/-- Lift a stateful query implementation to a `(state × Bool)`-stateful version that OR-updates
the boolean (bad) flag with a predicate `f` evaluated on the pre-state and produced output.
The flag is monotone: if it was already `true`, it stays `true`. -/
def withBadUpdate {ι : Type _} {spec : OracleSpec ι}
    {m : Type _ → Type _} [Functor m] {σ : Type _}
    (impl : QueryImpl spec (StateT σ m))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool) :
    QueryImpl spec (StateT (σ × Bool) m) := fun t =>
  StateT.mk fun | (s, b) => (fun (vs : spec.Range t × σ) => (vs.1, vs.2, b || f t s vs.1)) <$>
    (impl t).run s

/-- Run-shape of `withBadFlag`: the lifted implementation maps the underlying run by tagging
each `(value, state)` pair with the unchanged bad flag `b`. -/
@[simp] lemma withBadFlag_apply_run {ι : Type _} {spec : OracleSpec ι}
    {m : Type _ → Type _} [Functor m] {σ : Type _}
    (impl : QueryImpl spec (StateT σ m)) (t : spec.Domain) (s : σ) (b : Bool) :
    (impl.withBadFlag t).run (s, b) =
      (fun (vs : spec.Range t × σ) => (vs.1, vs.2, b)) <$> (impl t).run s := rfl

/-- Run-shape of `withBadUpdate`: the lifted implementation maps the underlying run by
appending the OR-updated bad flag `b || f t s vs.1`. -/
@[simp] lemma withBadUpdate_apply_run {ι : Type _} {spec : OracleSpec ι}
    {m : Type _ → Type _} [Functor m] {σ : Type _}
    (impl : QueryImpl spec (StateT σ m))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool)
    (t : spec.Domain) (s : σ) (b : Bool) :
    (impl.withBadUpdate f t).run (s, b) =
      (fun (vs : spec.Range t × σ) =>
        (vs.1, vs.2, b || f t s vs.1)) <$> (impl t).run s := rfl

end QueryImpl

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  {σ : Type u} (so : QueryImpl spec (StateT σ m))

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma StateT_run_simulateQ_eq_map_run'_simulateQ {α} [Subsingleton σ]
    (oa : OracleComp spec α) (s s' : σ) :
    (simulateQ so oa).run s = (·, s') <$> (simulateQ so oa).run' s := by
  have : (fun x : α × σ ↦ (x.1, s')) = id :=
    funext fun (x, s) ↦ Prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, Subsingleton.elim _ _⟩
  simp [this]

lemma StateT_run'_simulateQ_eq_self {α} (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ t s, (so t).run' s = query t)
    (oa : OracleComp spec α) (s : σ) : (simulateQ so oa).run' s = oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
      intro s
      simp at ih
      have := congr_arg (· >>= oa) (h t s)
      simpa [ih] using this

omit [LawfulMonad m] in
lemma liftM_run_StateT {α : Type u} (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = x >>= fun a => pure (a, s) :=
  StateT.run_lift x s

end OracleComp
