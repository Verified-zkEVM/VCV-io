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

variable {ι} {spec : OracleSpec ι} {α β γ : Type u}
variable {ι' : Type} {spec' : OracleSpec ι'} {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Given an implementation of `spec` in terms of a new set of oracles `spec'`,
and an implementation of `spec'` in terms of arbitrary `m`, implement `spec` in terms of `m`. -/
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m :=
  fun t => simulateQ so' (so t)

infixl : 65 " ∘ₛ " => QueryImpl.compose

omit [LawfulMonad m] in
@[simp]
lemma apply_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : (so' ∘ₛ so) t = simulateQ so' (so t) := rfl

@[simp]
lemma simulateQ_compose (so' : QueryImpl spec' m)
    (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) : simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

end compose

section insertPre

variable {m : Type u → Type v} [Monad m]
    {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι}

/-- Given monads `m` and `n` with `MonadLiftT m n`, an implementation of `spec` in `m`,
and a computation `nx` in `n` for each query input, construct a new implementation
`QueryImpl.preInsert so nx` that calls `nx` on every query before the actual substitution `so`.
Note that `nx` is expected to have some side-effects, it's actual result is discarded. -/
def preInsert (so : QueryImpl spec m) {α} (nx : spec.Domain → n α) :
    QueryImpl spec n :=
  fun t => do let _ ← nx t; liftM (so t)

variable {α β : Type u}

omit [Monad m] in
@[simp, grind =]
lemma preInsert_apply (so : QueryImpl spec m) (nx : spec.Domain → n α) (t : spec.Domain) :
    so.preInsert nx t = (do let _ ← nx t; liftM (so t)) := rfl

/-- One-step characterisation of `simulateQ (preInsert so nx)` on a single query. -/
lemma simulateQ_preInsert_query (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (t : spec.Domain) :
    simulateQ (so.preInsert nx) (query t) = (do let _ ← nx t; liftM (so t)) := by
  sorry

/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `preInsert so nx` and projecting back recovers `simulateQ so`. -/
lemma proj_simulateQ_preInsert [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.preInsert nx) oa) = simulateQ so oa := by
  sorry

/-- A `preInsert` instrumentation preserves failure probability for any base monad with
`HasEvalSPMF`, given the projection bundle and its compatibility with failure probabilities. -/
lemma probFailure_proj_simulateQ_preInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    Pr[⊥ | proj (simulateQ (so.preInsert nx) oa)] = Pr[⊥ | simulateQ so oa] := by
  sorry

/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_preInsert`. -/
lemma neverFail_proj_simulateQ_preInsert_iff
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.preInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  sorry

/-- When `nx` is constantly `pure x`, `preInsert so nx` is the lift of `so` and the
resulting simulation equals the lifted underlying simulation. Generic analogue of the
`run_simulateQ_withTraceBefore_const_one` no-op identity. -/
lemma simulateQ_preInsert_const_pure
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    (so : QueryImpl spec m) (x : α) (oa : OracleComp spec β) :
    simulateQ (so.preInsert (fun _ => (pure x : n α))) oa = liftM (simulateQ so oa) := by
  sorry

/-! #### `evalDist` / `probOutput` / `support` bridges for `preInsert` -/

lemma evalDist_proj_simulateQ_preInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    𝒟[proj (simulateQ (so.preInsert nx) oa)] = 𝒟[simulateQ so oa] := by
  sorry

lemma probOutput_proj_simulateQ_preInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) (x : β) :
    Pr[= x | proj (simulateQ (so.preInsert nx) oa)] = Pr[= x | simulateQ so oa] := by
  sorry

lemma support_proj_simulateQ_preInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    support (proj (simulateQ (so.preInsert nx) oa)) = support (simulateQ so oa) := by
  sorry

lemma finSupport_proj_simulateQ_preInsert
    [LawfulMonad m] [LawfulMonad n] [HasEvalSPMF m] [HasEvalFinset m] [DecidableEq β]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    finSupport (proj (simulateQ (so.preInsert nx) oa)) = finSupport (simulateQ so oa) := by
  sorry

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

/-- One-step characterisation of `simulateQ (postInsert so nx)` on a single query. -/
lemma simulateQ_postInsert_query (so : QueryImpl spec m)
    (nx : (t : spec.Domain) → spec.Range t → n α) (t : spec.Domain) :
    simulateQ (so.postInsert nx) (query t) =
      (do let u ← liftM (so t); let _ ← nx t u; return u) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- When `nx` is constantly `pure x`, `postInsert so nx` is the lift of `so` and the
resulting simulation equals the lifted underlying simulation. Generic analogue of the
`run_simulateQ_withTrace_const_one` no-op identity. -/
lemma simulateQ_postInsert_const_pure
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    (so : QueryImpl spec m) (x : α) (oa : OracleComp spec β) :
    simulateQ (so.postInsert (fun _ _ => (pure x : n α))) oa = liftM (simulateQ so oa) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end insertPost

end QueryImpl

variable {ι} {spec : OracleSpec ι} {α β γ : Type u}

/-- Given that the output type of all oracles has a `SampleableType` instance, replace all queries
with uniformly random responses by calling the corresponding `uniformSample` at each query. -/
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t

namespace uniformSampleImpl

variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} [∀ i, SampleableType (spec₀.Range i)]

@[simp]
lemma evalDist_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) :
    𝒟[simulateQ uniformSampleImpl oa] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h, uniformSampleImpl]

@[simp]
lemma probOutput_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (x : α) :
    Pr[= x | simulateQ uniformSampleImpl oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ oa)) x

@[simp]
lemma probEvent_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (p : α → Prop) :
    Pr[ p | simulateQ uniformSampleImpl oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_simulateQ]

@[simp]
lemma support_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) :
    support (simulateQ uniformSampleImpl oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h, uniformSampleImpl]

@[simp]
lemma finSupport_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    [DecidableEq α] (oa : OracleComp spec₀ α) :
    finSupport (simulateQ uniformSampleImpl oa) = finSupport oa := by
  simp [finSupport_eq_iff_support_eq_coe]

end uniformSampleImpl
