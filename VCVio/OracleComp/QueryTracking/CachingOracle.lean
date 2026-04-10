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
    simp only [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
  | none =>
    simp only [ht, StateT.run_bind] at hz
    have hlift : (liftM (so t) : StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        so t >>= fun v => pure (v, cache₀) := rfl
    rw [hlift, bind_assoc] at hz
    simp only [pure_bind] at hz
    rcases (mem_support_bind_iff _ _ _).1 hz with ⟨v, _, hmod⟩
    have : (modifyGet fun c => (v, QueryCache.cacheQuery c t v) :
        StateT spec.QueryCache m (spec.Range t)).run cache₀ =
        pure (v, cache₀.cacheQuery t v) := rfl
    rw [this] at hmod
    simp only [support_pure, Set.mem_singleton_iff] at hmod
    rw [hmod]
    exact QueryCache.le_cacheQuery cache₀ ht

/-- `withCaching` preserves the invariant `(cache₀ ≤ ·)` (the cache only grows). -/
lemma PreservesInv.withCaching_le {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
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
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    Pr[⊥ | (simulateQ (cachingOracle (spec := spec₀)) oa).run cache] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    NeverFail ((simulateQ (cachingOracle (spec := spec₀)) oa).run cache) ↔ NeverFail oa := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    HasEvalPMF.probFailure_eq_zero, HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma simulateQ_query (t : spec.Domain) :
    simulateQ cachingOracle (liftM (query t)) = cachingOracle t := by
  simp [_root_.simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]

end cachingOracle

namespace OracleComp

variable [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

omit [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- `simulateQ cachingOracle` only grows the cache: for any `oa`, if
`z ∈ support ((simulateQ cachingOracle oa).run cache₀)` then `cache₀ ≤ z.2`. -/
theorem simulateQ_cachingOracle_cache_le {α : Type u}
    (oa : OracleComp spec α) (cache₀ : QueryCache spec)
    (z : α × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle oa).run cache₀)) :
    cache₀ ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
      simp only [StateT.run, simulateQ_pure] at hmem
      rw [hmem]
  | query_bind t mx ih =>
      simp only [simulateQ_query_bind, StateT.run_bind] at hmem
      rw [support_bind] at hmem
      simp only [Set.mem_iUnion] at hmem
      obtain ⟨⟨u, cache_mid⟩, hmid, hrest⟩ := hmem
      have hle_mid : cache₀ ≤ cache_mid := by
        simp only [liftM, MonadLiftT.monadLift] at hmid
        unfold cachingOracle at hmid
        exact QueryImpl.withCaching_cache_le _ _ cache₀ _ hmid
      exact le_trans hle_mid (ih _ cache_mid z hrest)

omit [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- After running `cachingOracle` on a single query at `t`, the resulting cache
maps `t` to the returned value. -/
theorem cachingOracle_query_caches (t : spec.Domain)
    (cache₀ : QueryCache spec)
    (v : spec.Range t) (cache₁ : QueryCache spec)
    (hmem : (v, cache₁) ∈ support ((cachingOracle t).run cache₀)) :
    cache₁ t = some v := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hc : cache₀ t with
  | some u =>
    simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact hc
  | none =>
    simp only [hc, StateT.run_bind] at hmem
    rw [show (liftM (query t) :
        StateT (QueryCache spec) (OracleComp spec) _).run cache₀ =
        ((liftM (query t) : OracleComp _ _) >>= fun u =>
          pure (u, cache₀)) from rfl] at hmem
    rw [bind_assoc] at hmem; simp only [pure_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨u, _, hmem⟩ := hmem
    simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact QueryCache.cacheQuery_self cache₀ t v

end OracleComp
