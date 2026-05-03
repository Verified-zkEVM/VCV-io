/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.EvalDist

/-!
# Basic Constructions of Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.

## `preInsert` and `postInsert`

The two main building blocks for instrumented `QueryImpl` values are `preInsert` and
`postInsert`. Both take a base `QueryImpl spec m` and a per-query side effect, and produce
a new `QueryImpl spec n` that wraps the base with that side effect:

* `preInsert  so nx` runs `nx t` *before* the handler `so t`. The side effect happens
  unconditionally, including when the handler later fails.
* `postInsert so nx` runs `nx t u` *after* the handler returns response `u`, so the side
  effect can depend on the response and is skipped when the handler fails.

Both come with a complete generic theory, parametric in a projection
`proj : ∀ {γ}, n γ → m γ` that strips the instrumentation: `proj_simulateQ_preInsert`,
`probFailure_proj_simulateQ_preInsert`, `NeverFail_proj_simulateQ_preInsert_iff`,
`evalDist_proj_simulateQ_preInsert`, `probOutput_proj_simulateQ_preInsert`,
`support_proj_simulateQ_preInsert`, `finSupport_proj_simulateQ_preInsert`, and the
induction principle `simulateQ_preInsert.induct` (with `postInsert` analogues). Query-bound
transfer through these wrappers lives in `QueryTracking/QueryBound.lean`.

Most of the wrappers in `QueryTracking/` (`withTraceBefore`, `withTrace`,
`withTraceAppendBefore`, `withTraceAppend`, `withCost`, `withCounting`, `withAddCost`,
`withUnitCost`, `withLogging`, `appendInputLog`) bottom out at these combinators. New
instrumentation should follow the same pattern when its shape is "for each query, run a
side effect and delegate" — wrappers whose control flow is conditional on external state
or the would-be response (cache-on-hit, seed fallback, budget gating) genuinely need a
custom `QueryImpl` and stay outside this hierarchy.
-/

open OracleSpec OracleComp Prod Sum

universe u v w

namespace QueryImpl

section compose

variable {m : Type u → Type v} [Monad m]
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α β γ : Type u}

/-- Given an implementation of `spec` in terms of a new set of oracles `spec'`,
and an implementation of `spec'` in terms of arbitrary `m`, implement `spec` in terms of `m`. -/
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m :=
  fun t => simulateQ so' (so t)

infixl : 65 " ∘ₛ " => QueryImpl.compose

@[simp]
lemma apply_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : (so' ∘ₛ so) t = simulateQ so' (so t) := rfl

@[simp]
lemma simulateQ_compose [LawfulMonad m] (so' : QueryImpl spec' m)
    (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) : simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

@[simp]
lemma compose_id' [LawfulMonad m] (so : QueryImpl spec m) :
    so ∘ₛ QueryImpl.id' spec = so := by ext x; simp

end compose

section insertPre

variable {m : Type u → Type v}
    {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι} {α β γ : Type u}

/-- Given monads `m` and `n` with `MonadLiftT m n`, an implementation of `spec` in `m`,
and a computation `nx` in `n` for each query input, construct a new implementation
`QueryImpl.preInsert so nx` that calls `nx` on every query before the actual substitution `so`.
Note that `nx` is expected to have some side-effects, it's actual result is discarded. -/
def preInsert (so : QueryImpl spec m) (nx : spec.Domain → n α) :
    QueryImpl spec n :=
  fun t => nx t *> liftM (so t)

variable (so : QueryImpl spec m) (nx : spec.Domain → n α)

@[simp, grind =]
lemma preInsert_apply [LawfulMonad n] (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (t : spec.Domain) :
    so.preInsert nx t = (do let _ ← nx t; liftM (so t)) := by
  simp [preInsert, seqRight_eq, monad_norm]

/-- One-step characterisation of `simulateQ (preInsert so nx)` on a single query. -/
lemma simulateQ_preInsert_query [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (t : spec.Domain) :
    simulateQ (so.preInsert nx) (query t) = (do let _ ← nx t; liftM (so t)) := by
  simp

/-- Induction principle for `proj (simulateQ (so.preInsert nx) oa)` parametric in a
motive `OracleComp spec β → m β → Prop`. The recursion structure of
`proj_simulateQ_preInsert` is exposed as two cases mirroring `OracleComp.inductionOn`:
in `pure x` the projected term reduces to `pure x`, and in `query t >>= k` it reduces
to `so t >>= k'` for some continuation `k' u = proj (simulateQ (so.preInsert nx) (k u))`.
Tagged `@[elab_as_elim]` so it is usable as `induction oa using simulateQ_preInsert.induct`. -/
@[elab_as_elim]
lemma simulateQ_preInsert.induct [Monad m] [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    {motive : OracleComp spec β → m β → Prop}
    (h_pure : ∀ (x : β), motive (pure x : OracleComp spec β) (pure x))
    (h_query_bind : ∀ (t : spec.Domain) (k : spec.Range t → OracleComp spec β)
        (k' : spec.Range t → m β),
        (∀ u, motive (k u) (k' u)) → motive (query t >>= k) (so t >>= k'))
    (oa : OracleComp spec β) :
    motive oa (proj (simulateQ (so.preInsert nx) oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rw [simulateQ_pure, hproj_pure]
      exact h_pure x
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_spec_query, hproj_bind, hproj_apply]
      exact h_query_bind t k _ ih

/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `preInsert so nx` and projecting back recovers `simulateQ so`. The proof
is the canonical use of `simulateQ_preInsert.induct`: the parametric motive is instantiated
to the equality with `simulateQ so oa`, leaving trivial cases. -/
lemma proj_simulateQ_preInsert [Monad m] [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.preInsert nx) oa) = simulateQ so oa := by
  induction oa using simulateQ_preInsert.induct so nx proj hproj_pure hproj_bind hproj_apply with
  | h_pure x => rfl
  | h_query_bind t k k' ih =>
      simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
      exact bind_congr ih

/-- A `preInsert` instrumentation preserves failure probability for any base monad with
`HasEvalSPMF`, given the projection bundle and its compatibility with failure probabilities. -/
lemma probFailure_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    Pr[⊥ | proj (simulateQ (so.preInsert nx) oa)] = Pr[⊥ | simulateQ so oa] := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_preInsert`. -/
lemma neverFail_proj_simulateQ_preInsert_iff [Monad m]
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.preInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-- When `nx` is constantly `pure x`, `preInsert so nx` is the lift of `so` and the
resulting simulation equals the lifted underlying simulation. Generic analogue of the
`run_simulateQ_withTraceBefore_const_one` no-op identity. -/
lemma simulateQ_preInsert_const_pure [Monad m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    (so : QueryImpl spec m) (x : α) (oa : OracleComp spec β) :
    simulateQ (so.preInsert (fun _ => (pure x : n α))) oa = liftM (simulateQ so oa) := by
  have h : so.preInsert (fun _ => (pure x : n α)) = so.liftTarget n := by
    funext t; simp
  rw [h, simulateQ_liftTarget]

/-! #### `evalDist` / `probOutput` / `support` bridges for `preInsert` -/

lemma evalDist_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    𝒟[proj (simulateQ (so.preInsert nx) oa)] = 𝒟[simulateQ so oa] := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma probOutput_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) (x : β) :
    Pr[= x | proj (simulateQ (so.preInsert nx) oa)] = Pr[= x | simulateQ so oa] := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma support_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    support (proj (simulateQ (so.preInsert nx) oa)) = support (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma finSupport_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m] [HasEvalFinset m] [DecidableEq β]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    finSupport (proj (simulateQ (so.preInsert nx) oa)) = finSupport (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]

end insertPre

section insertPost

variable {m : Type u → Type v} [Monad m]
    {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι}

/-- Given monads `m` and `n` with `MonadLiftT m n`, an implementation of `spec` in `m`,
and a computation `nx` in `n` for each query output, construct a new implementation
`QueryImpl.postInsert so nx` that calls `nx` on on the result of each substitution.
Note that `nx` is expected to have some side-effects, it's actual result is discarded. -/
def postInsert (so : QueryImpl spec m) {α} (nx : (t : spec.Domain) → spec.Range t → n α) :
    QueryImpl spec n :=
  fun t => do let u ← liftM (so t); let _ ← nx t u; return u

variable {α β : Type u}

omit [Monad m] in
@[simp, grind =]
lemma postInsert_apply (so : QueryImpl spec m)
    (nx : (t : spec.Domain) → spec.Range t → n α) (t : spec.Domain) :
    so.postInsert nx t = (do let u ← liftM (so t); let _ ← nx t u; return u) := rfl

omit [Monad m] in
/-- One-step characterisation of `simulateQ (postInsert so nx)` on a single query. -/
lemma simulateQ_postInsert_query [LawfulMonad n]
    (so : QueryImpl spec m)
    (nx : (t : spec.Domain) → spec.Range t → n α) (t : spec.Domain) :
    simulateQ (so.postInsert nx) (query t) =
      (do let u ← liftM (so t); let _ ← nx t u; return u) := by
  simp

/-- Induction principle for `proj (simulateQ (so.postInsert nx) oa)` parametric in a
motive `OracleComp spec β → m β → Prop`. The recursion structure of
`proj_simulateQ_postInsert` is exposed as two cases mirroring `OracleComp.inductionOn`:
in `pure x` the projected term reduces to `pure x`, and in `query t >>= k` it reduces
to `so t >>= k'` for some continuation `k' u = proj (simulateQ (so.postInsert nx) (k u))`.
Tagged `@[elab_as_elim]` so it is usable as `induction oa using simulateQ_postInsert.induct`. -/
@[elab_as_elim]
lemma simulateQ_postInsert.induct [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    {motive : OracleComp spec β → m β → Prop}
    (h_pure : ∀ (x : β), motive (pure x : OracleComp spec β) (pure x))
    (h_query_bind : ∀ (t : spec.Domain) (k : spec.Range t → OracleComp spec β)
        (k' : spec.Range t → m β),
        (∀ u, motive (k u) (k' u)) → motive (query t >>= k) (so t >>= k'))
    (oa : OracleComp spec β) :
    motive oa (proj (simulateQ (so.postInsert nx) oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rw [simulateQ_pure, hproj_pure]
      exact h_pure x
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_spec_query, hproj_bind, hproj_apply]
      exact h_query_bind t k _ ih

/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `postInsert so nx` and projecting back recovers `simulateQ so`. The proof
is the canonical use of `simulateQ_postInsert.induct`: the parametric motive is instantiated
to the equality with `simulateQ so oa`, leaving trivial cases. -/
lemma proj_simulateQ_postInsert [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.postInsert nx) oa) = simulateQ so oa := by
  induction oa using simulateQ_postInsert.induct so nx proj hproj_pure hproj_bind hproj_apply with
  | h_pure x => rfl
  | h_query_bind t k k' ih =>
      simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
      exact bind_congr ih

/-- A `postInsert` instrumentation preserves failure probability for any base monad with
`HasEvalSPMF`, given the projection bundle and its compatibility with failure probabilities. -/
lemma probFailure_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    Pr[⊥ | proj (simulateQ (so.postInsert nx) oa)] = Pr[⊥ | simulateQ so oa] := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_postInsert`. -/
lemma neverFail_proj_simulateQ_postInsert_iff
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.postInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

/-- When `nx` is constantly `pure x`, `postInsert so nx` is the lift of `so` and the
resulting simulation equals the lifted underlying simulation. Generic analogue of the
`run_simulateQ_withTrace_const_one` no-op identity. -/
lemma simulateQ_postInsert_const_pure
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    (so : QueryImpl spec m) (x : α) (oa : OracleComp spec β) :
    simulateQ (so.postInsert (fun _ _ => (pure x : n α))) oa = liftM (simulateQ so oa) := by
  have h : so.postInsert (fun _ _ => (pure x : n α)) = so.liftTarget n := by
    funext t
    change (do let u ← liftM (so t); let _ ← (pure x : n α); return u) = liftM (so t)
    simp [bind_pure]
  rw [h, simulateQ_liftTarget]

/-! #### `evalDist` / `probOutput` / `support` bridges for `postInsert` -/

lemma evalDist_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    𝒟[proj (simulateQ (so.postInsert nx) oa)] = 𝒟[simulateQ so oa] := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma probOutput_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) (x : β) :
    Pr[= x | proj (simulateQ (so.postInsert nx) oa)] = Pr[= x | simulateQ so oa] := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma support_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    support (proj (simulateQ (so.postInsert nx) oa)) = support (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

lemma finSupport_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m] [HasEvalFinset m] [DecidableEq β]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    finSupport (proj (simulateQ (so.postInsert nx) oa)) = finSupport (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]

end insertPost

end QueryImpl
