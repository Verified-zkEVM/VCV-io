/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# Caching Queries Made by a Computation

This file defines a modifier `QueryImpl.withCaching` that modifies a query implementation to
cache results to return to the same query in the future.

We also define `cachingOracle`, which caches queries to the oracles in `spec`,
querying fresh values from `spec` if no cached value exists.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a query implementation to cache previous call and return that output in the future. -/
def withCaching (so : QueryImpl spec m) : QueryImpl spec (StateT spec.QueryCache m) :=
  fun t => do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)

@[simp] lemma withCaching_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCaching t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

section CacheMonotonicity

variable [spec.DecidableEq]

omit [spec.DecidableEq] in
/-- Running `withCaching` at state `cache` produces a result whose cache is `≥ cache`.
On a cache hit the state is unchanged; on a miss a single entry is added. -/
lemma withCaching_cache_le [LawfulMonad m] [HasEvalSet m]
    (so : QueryImpl spec m) (t : spec.Domain) (cache₀ : QueryCache spec)
    (z) (hz : z ∈ support ((so.withCaching t).run cache₀)) :
    cache₀ ≤ z.2 := by
  simp only [withCaching_apply, StateT.run_bind] at hz
  have hget : (get : StateT spec.QueryCache m spec.QueryCache).run cache₀ =
      pure (cache₀, cache₀) := rfl
  rw [hget, pure_bind] at hz
  cases ht : cache₀ t with
  | some u =>
    simp only [ht] at hz
    have hrun : (pure u : StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        pure (u, cache₀) := rfl
    rw [hrun] at hz
    simp at hz; rw [hz]
  | none =>
    simp only [ht, StateT.run_bind] at hz
    have hlift : (liftM (so t) : StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        so t >>= fun v => pure (v, cache₀) := by
      show StateT.lift (so t) cache₀ = _; rfl
    rw [hlift, bind_assoc] at hz
    simp only [pure_bind] at hz
    rcases (mem_support_bind_iff _ _ _).1 hz with ⟨v, _, hmod⟩
    have : (modifyGet fun c => (v, QueryCache.cacheQuery c t v) :
        StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        pure (v, cache₀.cacheQuery t v) := rfl
    rw [this] at hmod
    simp at hmod
    rw [hmod]
    exact QueryCache.le_cacheQuery cache₀ ht

/-- `withCaching` preserves the invariant `(cache₀ ≤ ·)` (the cache only grows). -/
lemma PreservesInv.withCaching_le {ι₀ : Type} {spec₀ : OracleSpec.{0,0} ι₀}
    [DecidableEq ι₀] [spec₀.DecidableEq]
    (so : QueryImpl spec₀ ProbComp) (cache₀ : QueryCache spec₀) :
    QueryImpl.PreservesInv (so.withCaching) (cache₀ ≤ ·) :=
  fun t cache hle z hz => le_trans hle (withCaching_cache_le so t cache z hz)

end CacheMonotonicity

end QueryImpl

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCaching

namespace cachingOracle

lemma apply_eq (t : spec.Domain) : cachingOracle t =
  (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← query t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

@[simp]
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0,0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    Pr[⊥ | (simulateQ (cachingOracle (spec := spec₀)) oa).run cache] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0,0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    NeverFail ((simulateQ (cachingOracle (spec := spec₀)) oa).run cache) ↔ NeverFail oa := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    HasEvalPMF.probFailure_eq_zero, HasEvalPMF.probFailure_eq_zero]

end cachingOracle
