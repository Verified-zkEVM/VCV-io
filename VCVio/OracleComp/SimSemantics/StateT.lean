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
noncomputable def mapStateTBase {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁))) :
    QueryImpl spec₀ (StateT σ m) := fun t =>
  StateT.mk fun s => simulateQ outer ((inner t).run s)

/-- Running a `StateT` handler and then interpreting its base oracle
computations is the same as first mapping the handler's base through the
outer interpreter. -/
theorem simulateQ_mapStateTBase_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run s) =
      (simulateQ (outer.mapStateTBase inner) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
      simp only [simulateQ_bind, StateT.run_bind]
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, mapStateTBase]
      refine bind_congr fun z => ?_
      exact ih z.1 z.2

/-- Output-only corollary of `simulateQ_mapStateTBase_run`. -/
theorem simulateQ_mapStateTBase_run' {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run' s) =
      (simulateQ (outer.mapStateTBase inner) oa).run' s := by
  change simulateQ outer (Prod.fst <$> (simulateQ inner oa).run s) = _
  rw [simulateQ_map, simulateQ_mapStateTBase_run]
  rfl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of state monads for
two different contexts `σ₁` and `σ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `σ₁ × σ₂` state. -/
def parallelStateT {ι₁ ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type _ → Type _} [Functor m] {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec₁ (StateT σ₁ m))
    (impl₂ : QueryImpl spec₂ (StateT σ₂ m)) :
    QueryImpl (spec₁ + spec₂) (StateT (σ₁ × σ₂) m)
  | .inl t => StateT.mk fun | (s₁, s₂) => Prod.map id (·, s₂) <$> (impl₁ t).run s₁
  | .inr t => StateT.mk fun | (s₁, s₂) => Prod.map id (s₁, ·) <$> (impl₂ t).run s₂

/-- Reassociate a nested state transformer into one product state.

The outer state is the first component of the product; the inner/base state is
the second component. This is the state-transformer analogue of reassociating
handler stacks into an explicit joint state before applying projection lemmas. -/
def flattenStateT {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] {σ τ : Type u}
    (impl : QueryImpl spec (StateT σ (StateT τ m))) :
    QueryImpl spec (StateT (σ × τ) m) := fun t =>
  StateT.mk fun (s, q) => do
    let ((u, s'), q') ← (impl t).run s |>.run q
    pure (u, (s', q'))

@[simp] theorem flattenStateT_liftTarget_apply_run {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ τ : Type u}
    (impl : QueryImpl spec (StateT τ m)) (t : spec.Domain) (s : σ) (q : τ) :
    ((impl.liftTarget (StateT σ (StateT τ m))).flattenStateT t).run (s, q) =
      (fun y : spec.Range t × τ => (y.1, (s, y.2))) <$> (impl t).run q := by
  simp [flattenStateT, QueryImpl.liftTarget_apply, StateT.run_bind,
    StateT.run_monadLift, map_eq_bind_pure_comp]

/-- Indexed version of `QueryImpl.parallelStateT`. Note that `m` cannot vary with `t`.
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

variable {τ : Type u}

/-- Running a computation under a flattened nested-state implementation is the
same as running the original nested computation and reassociating the final
states into a product. -/
theorem simulateQ_flattenStateT_run
    (impl : QueryImpl spec (StateT σ (StateT τ m)))
    {α : Type u} (oa : OracleComp spec α) (s : σ) (q : τ) :
    (simulateQ impl.flattenStateT oa).run (s, q) =
      (do
        let ((a, s'), q') ← (simulateQ impl oa).run s |>.run q
        pure (a, (s', q')) : m (α × (σ × τ))) := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t k ih =>
      suffices
          ((impl t).run s).run q >>= (fun x =>
            (simulateQ impl.flattenStateT (k x.1.1)).run (x.1.2, x.2)) =
          ((impl t).run s).run q >>= fun x =>
            (fun y : (α × σ) × τ => (y.1.1, (y.1.2, y.2))) <$>
              ((simulateQ impl (k x.1.1)).run x.1.2).run x.2 by
        simpa [simulateQ_bind, simulateQ_query, QueryImpl.flattenStateT,
          StateT.run_bind, map_eq_bind_pure_comp, bind_assoc] using this
      refine bind_congr (m := m) fun x => ?_
      rcases x with ⟨⟨u, s'⟩, q'⟩
      simpa [map_eq_bind_pure_comp] using ih u s' q'

/-- Output-only corollary of `simulateQ_flattenStateT_run`. -/
theorem simulateQ_flattenStateT_run'
    (impl : QueryImpl spec (StateT σ (StateT τ m)))
    {α : Type u} (oa : OracleComp spec α) (s : σ) (q : τ) :
    (simulateQ impl.flattenStateT oa).run' (s, q) =
      (Prod.fst <$> (simulateQ impl oa).run s).run' q := by
  rw [StateT.run'_eq, simulateQ_flattenStateT_run]
  simp [StateT.run'_eq, Functor.map_map]

/-- Running an adversary-side `StateT` handler under an outer stateful
interpreter produces the same distribution as the flattened product-state
handler, up to reassociating `((output, localState), outerState)` and
`(output, (localState, outerState))`. -/
theorem simulateQ_mapStateTBase_run_eq_map_flattenStateT
    {ι₀ ι₁ : Type _} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ τ : Type u}
    (outer : QueryImpl spec₁ (StateT τ m))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) (q : τ) :
    (simulateQ outer ((simulateQ inner oa).run s)).run q =
      (fun z : α × (σ × τ) => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (outer.mapStateTBase inner).flattenStateT oa).run (s, q) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, simulateQ_flattenStateT_run]
  simp [Functor.map_map]

end OracleComp
