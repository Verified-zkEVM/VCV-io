/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbComp
import ToMathlib.Control.StateT

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
      (simulateQ (outer.mapStateTBase inner) oa).run s :=
  simulateQ_StateT_compose inner outer (outer.mapStateTBase inner) (fun _ _ => rfl) oa s

/-- Output-only corollary of `simulateQ_mapStateTBase_run`. -/
theorem simulateQ_mapStateTBase_run' {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run' s) =
      (simulateQ (outer.mapStateTBase inner) oa).run' s := by
  simp [simulateQ_mapStateTBase_run]

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
  StateT.mk fun (s, q) =>
    (fun ((u, s'), q') => (u, (s', q'))) <$> ((impl t).run s |>.run q)

@[simp] theorem flattenStateT_liftTarget_apply_run {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ τ : Type u}
    (impl : QueryImpl spec (StateT τ m)) (t : spec.Domain) (s : σ) (q : τ) :
    ((impl.liftTarget (StateT σ (StateT τ m))).flattenStateT t).run (s, q) =
      (fun y : spec.Range t × τ => (y.1, (s, y.2))) <$> (impl t).run q := by
  simp [flattenStateT]

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
  StateT.mk fun | (s, b) => (fun (v, s') => (v, s', b || f t s v)) <$> (impl t).run s

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
  simp [show (fun x : α × σ => (x.1, s')) = id from
    funext fun x => Prod.ext rfl (Subsingleton.elim _ _)]

/-- If a `StateT` implementation passes every query through unchanged after discarding state
(`(so t).run' s = query t`), then simulating a computation and projecting out the final state
recovers the original computation. -/
lemma StateT_run'_simulateQ_eq_self {α} (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ t s, (so t).run' s = query t)
    (oa : OracleComp spec α) (s : σ) : (simulateQ so oa).run' s = oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [StateT.run'_eq] at ih
    simpa [ih] using congr_arg (· >>= oa) (h t s)

omit [LawfulMonad m] in
/-- Running a base-monad action lifted into `StateT σ m` threads the state `s` through
unchanged, pairing it with the produced value. -/
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
  induction oa using OracleComp.inductionOn generalizing s q <;>
    simp_all [QueryImpl.flattenStateT]

/-- Output-only corollary of `simulateQ_flattenStateT_run`. -/
theorem simulateQ_flattenStateT_run'
    (impl : QueryImpl spec (StateT σ (StateT τ m)))
    {α : Type u} (oa : OracleComp spec α) (s : σ) (q : τ) :
    (simulateQ impl.flattenStateT oa).run' (s, q) =
      (Prod.fst <$> (simulateQ impl oa).run s).run' q := by
  simp [simulateQ_flattenStateT_run]

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
  simp [QueryImpl.simulateQ_mapStateTBase_run, simulateQ_flattenStateT_run]

end OracleComp

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

open Option ENNReal BigOperators
open scoped OracleSpec.PrimitiveQuery

section simulateQ_evalDist

variable [IsUniformSpec spec]

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
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind]
    rw [@map_bind (OracleComp spec), evalDist_bind]
    simp_rw [← StateT.run'_eq, ih]
    rw [← evalDist_bind, ← bind_map_left Prod.fst, ← StateT.run'_eq, evalDist_bind, h t s]
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
  probOutput_congr rfl (evalDist_simulateQ_run'_eq_evalDist so h s oa)

/-- Corollary for `probEvent`: stateful simulation preserves event probabilities. -/
lemma probEvent_simulateQ_run'_eq {σ τ : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec.Domain) (s : σ),
      𝒟[(so t).run' s] = OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (s : σ) (oa : OracleComp spec τ) (p : τ → Prop) :
    Pr[ p | (simulateQ so oa).run' s] = Pr[ p | oa] :=
  probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_simulateQ_run'_eq_evalDist so h s oa)

/-- If two stateful oracle implementations agree on the post-`run` distribution of every
query (`𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s]`), then simulating any computation through
either yields the same distribution on the run. -/
lemma evalDist_simulateQ_run_congr
    {ι' : Type} {spec' : OracleSpec ι'} {σ α : Type}
    (impl₁ impl₂ : QueryImpl spec' (StateT σ (OracleComp spec)))
    (h : ∀ (t : spec'.Domain) (s : σ),
      𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    (comp : OracleComp spec' α) (s : σ) :
    𝒟[(simulateQ impl₁ comp).run s] =
      𝒟[(simulateQ impl₂ comp).run s] := by
  induction comp using OracleComp.inductionOn generalizing s <;> simp_all

@[deprecated (since := "2026-06-25")]
alias evalDist_simulateQ_run_eq_of_impl_evalDist_eq := evalDist_simulateQ_run_congr

end simulateQ_evalDist

section support_simulateQ_StateT

variable {α : Type w} [IsUniformSpec spec]

omit [IsUniformSpec spec] in
/-- Simulating an `OracleComp` through a stateful implementation in monad `m` can only shrink the
support: any output reachable after simulation was already reachable in the original computation
(where oracle queries may return any value). This is the support-level analogue of
`evalDist_simulateQ_run'_eq_evalDist`. -/
theorem support_simulateQ_run'_subset
    {n : Type w → Type _} [Monad n] [LawfulMonad n] [MonadLiftT n SetM] [LawfulMonadLiftT n SetM]
    {σ : Type w}
    (impl : QueryImpl spec (StateT σ n))
    (oa : OracleComp spec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind, Set.mem_image, Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨⟨a, s'⟩, ⟨⟨u, s''⟩, -, hsupp⟩, rfl⟩ := hx
    refine ⟨u, mem_support_query t u, ih u s'' ?_⟩
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hsupp

end support_simulateQ_StateT

end OracleComp

section probEventSimulateQ

open OracleComp

/-- `run'`-level corollary of `simulateQ_bind_map_eq_of_body`: if the two bodies of a bind agree
under `simulateQ` up to a pure post-map `f`, then so do the `run'`s of the simulated binds from
any initial state. -/
lemma StateT.run'_simulateQ_bind_map_eq_of_body
    {ι : Type} {σ α β γ : Type} {spec : OracleSpec ι}
    {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl spec (StateT σ n))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β) (s : σ)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    (simulateQ impl (oa >>= body₁)).run' s =
      f <$> (simulateQ impl (oa >>= body₂)).run' s := by
  rw [← StateT.run'_map']
  exact congrArg (fun mx : StateT σ n β => mx.run' s)
    (simulateQ_bind_map_eq_of_body impl oa body₁ body₂ f hBody)

/-- If all outputs of the original `OracleComp` are successful (`some`) and satisfy `P`, then
the simulated `OptionT`-wrapped computation satisfies `P` with probability one. The success
hypothesis is at the level of the *original* computation's support, which bounds the simulated
support by `support_simulateQ_run'_subset`. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk ((simulateQ impl oa).run' s₀)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    have hfail : Pr[⊥ | (simulateQ impl oa).run' s₀] = 0 :=
      probFailure_eq_zero
    rw [hfail, _root_.zero_add]
    exact probOutput_eq_zero_of_not_mem_support fun hnone =>
      let hnone' := support_simulateQ_run'_subset impl oa s₀ hnone
      let ⟨_, hsome, _⟩ := h none hnone'
      by cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s₀ hx)
    cases ha
    exact hP

/-- Bind-prefixed variant of `OptionT.probEvent_eq_one_of_simulateQ_support`: the simulated
`OptionT` computation may sample its initial state `s₀` from an arbitrary `ProbComp σ`. Since
`support_simulateQ_run'_subset` bounds the support uniformly in `s₀`, the support hypothesis
`h` (independent of `s₀`) still discharges both the never-fail and all-outputs-`P`
obligations. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support_bind
    {ι σ α : Type} {spec : OracleSpec ι}
    (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk (do let s ← init; (simulateQ impl oa).run' s)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- The simulated computation never fails: for every sampled state `s`, the run' has no `none`
    -- in its support (it is bounded by `support oa`, which contains no `none` by `h`).
    rw [OptionT.probFailure_eq, OptionT.run_mk, add_eq_zero]
    refine ⟨probFailure_eq_zero, ?_⟩
    refine probOutput_eq_zero_of_not_mem_support fun hnone => ?_
    rw [mem_support_bind_iff] at hnone
    obtain ⟨s, _, hnone⟩ := hnone
    obtain ⟨_, hsome, _⟩ := h none (support_simulateQ_run'_subset impl oa s hnone)
    cases hsome
  · -- Every successful output satisfies `P`: peel the `init` bind, then bound the support.
    intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s hx)
    cases ha
    exact hP

/-- Properties of `Option`-valued outputs of an underlying `OracleComp` propagate to elements
in the support of the simulated, run, and `OptionT`-wrapped version. -/
lemma OptionT.aux_mem_support_simulateQ_run'
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∀ a, x = some a → P a)
    {x : α} (hx : x ∈ support (OptionT.mk ((simulateQ impl oa).run' s₀))) : P x := by
  rw [OptionT.mem_support_iff] at hx
  exact h (some x) (support_simulateQ_run'_subset impl oa s₀ hx) x rfl

end probEventSimulateQ
