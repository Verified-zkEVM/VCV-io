/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Caching Queries Made by a Computation

This file defines a modifier `QueryImpl.withCaching` that modifies a query implementation to
cache results to return to the same query in the future.

We also define a plain caching oracle and random oracles as special cases of this.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a query implementation to cache previous call and return that output in the future. -/
def withCaching (so : QueryImpl spec m) : QueryImpl spec (StateT spec.QueryCache m) where
  impl | query i t => do match (← get) i t with
    | Option.some u => return u
    | Option.none =>
        let u ← so.impl (query i t)
        modifyGet fun cache => (u, cache.cacheQuery i t u)

@[simp] lemma withCaching_apply {α} (so : QueryImpl spec m) (q : OracleQuery spec α) :
    so.withCaching.impl q = match q with | query i t => (do match (← get) i t with
      | Option.some u => return u
      | Option.none =>
          let u ← so.impl (query i t)
          modifyGet fun cache => (u, cache.cacheQuery i t u)) := rfl

end QueryImpl

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  idOracle.withCaching

namespace cachingOracle

lemma apply_eq {α} (q : OracleQuery spec α) : cachingOracle.impl q =
  match q with | query i t => (do match (← get) i t with
    | Option.some u => return u
    | Option.none =>
        let u ← query i t
        modifyGet fun cache => (u, cache.cacheQuery i t u)) := rfl

end cachingOracle

-- NOTE: need to change universe levels b/c `unifSpec` doesn't use `pNat`.
variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

/-- Random Oracle implemented as a uniform selection oracle with caching -/
@[inline, reducible] def randomOracle [(i : ι) → SelectableType (spec.range i)] :
    QueryImpl spec (StateT spec.QueryCache (OracleComp unifSpec)) :=
  unifOracle.withCaching

namespace randOracle

variable [(i : ι) → SelectableType (spec.range i)]

lemma apply_eq {α} (q : OracleQuery spec α) : randomOracle.impl q =
    match q with | query i t => (do match (← get) i t with
      | Option.some u => return u
      | Option.none =>
          let u ←$ᵗ (spec.range i)
          modifyGet fun cache => (u, cache.cacheQuery i t u)) := rfl

/--
If a cache results from a run of a single randomOracle query,
then it is a supercache of the preexisting cache
-/
theorem subcache_of_mem_randomOracle_impl_query_run_support
    -- Parameters of the query
    (i : ι) (t : (spec).domain i) (a : spec.range i)
    -- Preexisting and resulting caches
    (preexisting_cache resulting_cache : (spec).QueryCache)
    (h_mem : (a, resulting_cache) ∈
        ((randomOracle.impl (query i t)).run preexisting_cache).support) :
    preexisting_cache ⊆ resulting_cache := by
  simp [OracleSpec.QueryCache.subcache_def]
  intros i' input output h
  simp_all only [QueryImpl.withCaching_apply, unifOracle.apply_eq, StateT.run_bind, StateT.run_get,
    pure_bind]
  set result := preexisting_cache i t with h'
  clear_value result
  cases result with
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
      StateT.run_modifyGet, Functor.map_map, support_map, support_uniformOfFintype, Set.image_univ,
      Set.mem_range, Prod.mk.injEq, exists_eq_left] at h_mem
    subst h_mem
    simp only [QueryCache.cacheQuery_eq_ite_ite, h]
    by_cases h_i'_eq_i : i' = i
    · subst h_i'_eq_i -- odd that this is needed with grind immediately after
      grind
    simp [h_i'_eq_i]
  | some val =>
    simp_all only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]

/--
If a cache results from any run of a randomOracle computation,
then it is a supercache of the preexisting cache
-/
theorem subcache_of_mem_support {α β : Type} [DecidableEq α] [SelectableType α]
    (comp : OracleComp (spec) β)
    (preexisting_cache resulting_cache : (spec).QueryCache) (b : β)
    (h_mem :
      ((b, resulting_cache) ∈ ((simulateQ randomOracle comp).run preexisting_cache).support)
    ) :
     preexisting_cache ⊆ resulting_cache := by
  induction comp using OracleComp.inductionOn generalizing b preexisting_cache resulting_cache with
  | pure x =>
    simp [OracleSpec.QueryCache.subcache_def]
    simp_all
  | query_bind i t oa ih =>
    simp_all only [simulateQ_bind, StateT.run_bind, Function.comp_apply, support_bind,
      Set.mem_iUnion, exists_prop, Prod.exists]
    rcases h_mem with
      ⟨a, cache, h1, h2⟩
    specialize ih a cache resulting_cache b h2
    have : preexisting_cache ⊆ cache := by
      clear ih h2 b resulting_cache
      apply subcache_of_mem_randomOracle_impl_query_run_support i t a
      simp_all only [simulateQ_query, QueryImpl.withCaching_apply, unifOracle.apply_eq,
        StateT.run_bind, StateT.run_get, pure_bind]
    exact subset_trans this ih
  | failure =>
    simp_all only [simulateQ_failure, StateT.run_failure, support_failure, Set.mem_empty_iff_false]

end randOracle
