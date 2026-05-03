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
lemma preInsert_apply [LawfulMonad n] (so : QueryImpl spec m) (nx : spec.Domain → n α) (t : spec.Domain) :
    so.preInsert nx t = (do let _ ← nx t; liftM (so t)) := by
  simp [preInsert, seqRight_eq, monad_norm]

/-- One-step characterisation of `simulateQ (preInsert so nx)` on a single query. -/
lemma simulateQ_preInsert_query [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (t : spec.Domain) :
    simulateQ (so.preInsert nx) (query t) = (do let _ ← nx t; liftM (so t)) := by
  simp

/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `preInsert so nx` and projecting back recovers `simulateQ so`. -/
lemma proj_simulateQ_preInsert [Monad m] [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.preInsert nx) oa) = simulateQ so oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rw [simulateQ_pure, simulateQ_pure, hproj_pure]
  | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [hproj_bind, hproj_apply]
      exact bind_congr fun u => ih u

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

/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `postInsert so nx` and projecting back recovers `simulateQ so`. -/
lemma proj_simulateQ_postInsert [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.postInsert nx) oa) = simulateQ so oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rw [simulateQ_pure, simulateQ_pure, hproj_pure]
  | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [hproj_bind, hproj_apply]
      exact bind_congr fun u => ih u

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
