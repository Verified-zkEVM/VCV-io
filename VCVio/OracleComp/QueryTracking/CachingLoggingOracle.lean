/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.StateProjection

/-!
# Combined Caching + Logging Handlers

This file packages the concrete "cache plus append-log" handlers that are
useful in proof developments but should live below `ProgramLogic`.

`QueryImpl.withCachingTraceAppend` is the generic transformer: it threads a
`QueryCache spec × ω` state, reuses cached answers on hits, falls back to the
underlying implementation on misses, and appends a response-dependent trace to
the second state component after every query.

`QueryImpl.withCachingLogging` and `OracleSpec.cachingLoggingOracle` are the
canonical specializations to `QueryLog spec`.
-/

open OracleComp OracleSpec

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m] [DecidableEq ι] [spec.DecidableEq]
variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Cache responses in the first state component and append a response-dependent
trace to the second state component after every query.

On a cache hit, the underlying handler is not consulted; the cached answer is
returned directly and the trace still records the observed `(query, response)`
pair. On a cache miss, the underlying handler supplies the answer, which is then
installed in the cache before the trace is appended. -/
def withCachingTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (StateT (QueryCache spec × ω) m) :=
  fun t => do
    let (cache, trace) ← get
    match cache t with
    | some u =>
        modifyGet fun _ => (u, (cache, trace ++ traceFn t u))
    | none =>
        let u ← so t
        modifyGet fun _ => (u, (cache.cacheQuery t u, trace ++ traceFn t u))

omit [spec.DecidableEq] [EmptyCollection ω] in
@[simp, grind =]
lemma withCachingTraceAppend_apply (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (t : spec.Domain) :
    so.withCachingTraceAppend traceFn t = (do
      let (cache, trace) ← get
      match cache t with
      | some u =>
          modifyGet fun _ => (u, (cache, trace ++ traceFn t u))
      | none =>
          let u ← so t
          modifyGet fun _ => (u, (cache.cacheQuery t u, trace ++ traceFn t u))) := rfl

/-- Specialization of `withCachingTraceAppend` to the canonical query log
`QueryLog spec`. -/
def withCachingLogging (so : QueryImpl spec m) :
    QueryImpl spec (StateT (QueryCache spec × QueryLog spec) m) :=
  so.withCachingTraceAppend (fun t u => [⟨t, u⟩])

omit [spec.DecidableEq] in
@[simp, grind =]
lemma withCachingLogging_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCachingLogging t = (do
      let (cache, trace) ← get
      match cache t with
      | some u =>
          modifyGet fun _ => (u, (cache, trace ++ [⟨t, u⟩]))
      | none =>
          let u ← so t
          modifyGet fun _ => (u, (cache.cacheQuery t u, trace ++ [⟨t, u⟩]))) := rfl

end QueryImpl

/-- Canonical combined caching + logging oracle over `OracleComp spec`. -/
def OracleSpec.cachingLoggingOracle [DecidableEq ι] [spec.DecidableEq] :
    QueryImpl spec (StateT (QueryCache spec × QueryLog spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCachingLogging

namespace cachingLoggingOracle

variable [DecidableEq ι] [spec.DecidableEq]

@[simp]
lemma apply_eq (t : spec.Domain) :
    cachingLoggingOracle t = (do
      let (cache, trace) ← get
      match cache t with
      | some u =>
          modifyGet fun _ => (u, (cache, trace ++ [⟨t, u⟩]))
      | none =>
          let u ← query t
          modifyGet fun _ => (u, (cache.cacheQuery t u, trace ++ [⟨t, u⟩]))) := rfl

/-- Projecting away the log component recovers the ordinary caching semantics. -/
theorem fst_map_run_simulateQ {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    Prod.map id Prod.fst <$> (simulateQ cachingLoggingOracle oa).run s =
      (simulateQ cachingOracle oa).run s.1 := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := cachingLoggingOracle) (impl₂ := cachingOracle)
    (proj := Prod.fst) ?_ oa s
  intro t ⟨cache, trace⟩
  cases hcache : cache t with
  | some u =>
      simp [apply_eq, hcache]
  | none =>
      simp only [apply_eq, cachingOracle.apply_eq, StateT.run_bind,
        StateT.run_get, pure_bind, hcache, StateT.run_monadLift, map_bind,
        bind_assoc]
      refine bind_congr fun u => ?_
      simp

/-- Output-only projection corollary of `fst_map_run_simulateQ`. -/
@[simp]
theorem run'_simulateQ_eq {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    (simulateQ cachingLoggingOracle oa).run' s =
      (simulateQ cachingOracle oa).run' s.1 := by
  have hrun := fst_map_run_simulateQ oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

end cachingLoggingOracle
