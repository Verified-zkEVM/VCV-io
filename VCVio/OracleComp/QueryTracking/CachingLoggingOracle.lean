/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.LoggingOracle

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

@[expose] public section

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
  withCachingAux
    (fun t u _ trace => trace ++ traceFn t u)
    (fun t _ trace => (fun u => (u, trace ++ traceFn t u)) <$> so t)

omit [spec.DecidableEq] [EmptyCollection ω] in
@[simp, grind =]
lemma withCachingTraceAppend_apply (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (t : spec.Domain) :
    so.withCachingTraceAppend traceFn t =
      StateT.mk fun s => match s.1 t with
      | some u => pure (u, (s.1, s.2 ++ traceFn t u))
      | none => (fun p : spec.Range t × ω => (p.1, (s.1.cacheQuery t p.1, p.2))) <$>
          ((fun u => (u, s.2 ++ traceFn t u)) <$> so t) := rfl

/-- Specialization of `withCachingTraceAppend` to the canonical query log
`QueryLog spec`. -/
def withCachingLogging (so : QueryImpl spec m) :
    QueryImpl spec (StateT (QueryCache spec × QueryLog spec) m) :=
  so.withCachingTraceAppend (fun t u => [⟨t, u⟩])

omit [spec.DecidableEq] in
@[simp, grind =]
lemma withCachingLogging_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCachingLogging t =
      StateT.mk fun s => match s.1 t with
      | some u => pure (u, (s.1, s.2 ++ [⟨t, u⟩]))
      | none => (fun p : spec.Range t × QueryLog spec =>
          (p.1, (s.1.cacheQuery t p.1, p.2))) <$>
          ((fun u => (u, s.2 ++ [⟨t, u⟩])) <$> so t) := rfl

/-! ### Forward-direction query bounds for `withCachingTraceAppend`

The trace overlay does not change the underlying query count, so the `withCaching` bounds
transfer through `withCachingAux_run_proj_eq` via `isQueryBound_iff_of_map_eq`. -/

variable {α : Type u} {ι' : Type u} {spec' : OracleSpec ι'}

omit [Monad m] [spec.DecidableEq] [EmptyCollection ω] in
private lemma _root_.QueryImpl.withCachingTraceAppend_run_proj_eq
    {ι₂ : Type u} {spec₂ : OracleSpec ι₂}
    (so : QueryImpl spec (OracleComp spec₂))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (oa : OracleComp spec α) (s : QueryCache spec × ω) :
    Prod.map id Prod.fst <$> (simulateQ (so.withCachingTraceAppend traceFn) oa).run s =
      (simulateQ so.withCaching oa).run s.1 :=
  QueryImpl.withCachingAux_run_proj_eq so _ _
    (fun _ _ _ => by simp [Functor.map_map]) oa s.1 s.2

omit [Monad m] [spec.DecidableEq] in
omit [EmptyCollection ω] in
theorem isTotalQueryBound_run_simulateQ_withCachingTraceAppend
    (so : QueryImpl spec (OracleComp spec))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {oa : OracleComp spec α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n)
    (hstep : ∀ t, OracleComp.IsTotalQueryBound (so t) 1)
    (s : QueryCache spec × ω) :
    OracleComp.IsTotalQueryBound
      ((simulateQ (so.withCachingTraceAppend traceFn) oa).run s) n :=
  (OracleComp.isQueryBound_iff_of_map_eq
      (QueryImpl.withCachingTraceAppend_run_proj_eq so traceFn oa s) _ _).mpr
    (OracleComp.IsTotalQueryBound.simulateQ_run_withCaching so h hstep s.1)

omit [Monad m] [spec.DecidableEq] in
omit [EmptyCollection ω] in
theorem isQueryBoundP_run_simulateQ_withCachingTraceAppend
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {oa : OracleComp spec α}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → OracleComp.IsQueryBoundP (so t) q 1)
    (hstep_np : ∀ t, ¬ p t → OracleComp.IsQueryBoundP (so t) q 0)
    (s : QueryCache spec × ω) :
    OracleComp.IsQueryBoundP
      ((simulateQ (so.withCachingTraceAppend traceFn) oa).run s) q n :=
  (OracleComp.isQueryBoundP_iff_of_map_eq
      (QueryImpl.withCachingTraceAppend_run_proj_eq so traceFn oa s)).mpr
    (OracleComp.IsQueryBoundP.simulateQ_run_withCaching so h hstep_p hstep_np s.1)

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
          let u ← (HasQuery.query t : OracleComp spec _)
          modifyGet fun _ => (u, (cache.cacheQuery t u, trace ++ [⟨t, u⟩]))) := by
  ext s
  rw [cachingLoggingOracle, QueryImpl.withCachingLogging, QueryImpl.withCachingTraceAppend,
    QueryImpl.withCachingAux_apply]
  cases hcache : s.1 t <;> simp [hcache]

/-- Cache hit: return the stored response and append it to the query log. -/
lemma run_some {t : spec.Domain} {cache : QueryCache spec} {trace : QueryLog spec}
    {u : spec.Range t} (h : cache t = some u) :
    (cachingLoggingOracle t).run (cache, trace) =
      pure (u, (cache, trace ++ [⟨t, u⟩])) := by
  rw [apply_eq]
  simp [h]

/-- Cache miss: issue the underlying query, cache its response, and append it to the query log. -/
lemma run_none {t : spec.Domain} {cache : QueryCache spec} {trace : QueryLog spec}
    (h : cache t = none) :
    (cachingLoggingOracle t).run (cache, trace) =
      (fun u => (u, (cache.cacheQuery t u, trace ++ [⟨t, u⟩]))) <$>
        (query t : OracleComp spec _) := by
  rw [apply_eq]
  simp [h, monad_norm]

/-- Running the combined caching-and-logging handler is equivalent to first adding the
writer-style query log and then interpreting the resulting computation through the caching
handler. The explicit state rearrangement also appends the newly produced log to an arbitrary
initial trace, so the statement composes across phases. -/
theorem run_simulateQ_eq_map_run_simulateQ_withQueryLog {α : Type u}
    (oa : OracleComp spec α) (cache₀ : QueryCache spec) (trace₀ : QueryLog spec) :
    (simulateQ cachingLoggingOracle oa).run (cache₀, trace₀) =
      (fun z : (α × QueryLog spec) × QueryCache spec =>
        (z.1.1, (z.2, trace₀ ++ z.1.2))) <$>
        (simulateQ cachingOracle oa.withQueryLog).run cache₀ := by
  change (simulateQ cachingLoggingOracle oa).run (cache₀, trace₀) =
    (fun z : (α × QueryLog spec) × QueryCache spec =>
      (z.1.1, (z.2, trace₀ ++ z.1.2))) <$>
      (simulateQ cachingOracle (simulateQ loggingOracle oa).run).run cache₀
  induction oa using OracleComp.inductionOn generalizing cache₀ trace₀ with
  | pure x => simp
  | query_bind t mx ih =>
      rw [OracleComp.run_simulateQ_query_bind]
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind]
      rw [OracleComp.run_simulateQ_query_bind]
      cases hcache : cache₀ t with
      | none =>
          rw [run_none hcache, cachingOracle.run_none hcache]
          simp [ih, List.append_assoc, monad_norm]
      | some u =>
          rw [run_some hcache, cachingOracle.run_some hcache]
          simp [ih, List.append_assoc, monad_norm]

/-- Projecting away the log component recovers the ordinary caching semantics. -/
theorem fst_map_run_simulateQ {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    Prod.map id Prod.fst <$> (simulateQ cachingLoggingOracle oa).run s =
      (simulateQ cachingOracle oa).run s.1 := by
  exact QueryImpl.withCachingTraceAppend_run_proj_eq
    (QueryImpl.ofLift spec (OracleComp spec)) (fun t u => [⟨t, u⟩]) oa s

/-- Output-only projection corollary of `fst_map_run_simulateQ`. -/
theorem run'_simulateQ_eq {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    (simulateQ cachingLoggingOracle oa).run' s =
      (simulateQ cachingOracle oa).run' s.1 := by
  have hmap := congrArg (fun p => Prod.fst <$> p) (fst_map_run_simulateQ oa s)
  rw [StateT.run', StateT.run']
  change (fun a => id a.1) <$> (simulateQ cachingLoggingOracle oa).run s =
    Prod.fst <$> (simulateQ cachingOracle oa).run s.1
  simpa only [Functor.map_map, Function.comp_def, Prod.map] using hmap

/-! ### Forward-direction query bounds

The log overlay does not change the underlying query count, so the `cachingOracle` bounds
transfer through `fst_map_run_simulateQ` via `isQueryBound_iff_of_map_eq`. -/

theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq]
    {α : Type} {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.cachingLoggingOracle oa).run s) n :=
  (OracleComp.isQueryBound_iff_of_map_eq (fst_map_run_simulateQ oa s) _ _).mpr
    (cachingOracle.isTotalQueryBound_run_simulateQ h s.1)

theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq]
    {α : Type} {oa : OracleComp spec₀ α} {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.cachingLoggingOracle oa).run s) p n :=
  (OracleComp.isQueryBoundP_iff_of_map_eq (fst_map_run_simulateQ oa s)).mpr
    (cachingOracle.isQueryBoundP_run_simulateQ h s.1)

theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.cachingLoggingOracle oa).run s) qb :=
  (OracleComp.isPerIndexQueryBound_iff_of_map_eq (fst_map_run_simulateQ oa s)).mpr
    (cachingOracle.isPerIndexQueryBound_run_simulateQ h s.1)

end cachingLoggingOracle

/-! ## Cache and log coherence -/

namespace OracleSpec.QueryCache
variable {ι Y : Type}
/-- Appending a response already present in the cache preserves log consistency. -/
theorem log_consistent_append (cache : (ι →ₒ Y).QueryCache) (log : (ι →ₒ Y).QueryLog)
    (t : ι) (value : Y) (hlookup : cache t = some value)
    (hlog : ∀ entry ∈ log, cache entry.1 = some entry.2) :
    ∀ entry ∈ log ++ [⟨t, value⟩], cache entry.1 = some entry.2 := by
  intro entry hentry
  rcases List.mem_append.mp hentry with hentry | hentry
  · exact hlog entry hentry
  · obtain rfl := List.mem_singleton.mp hentry
    exact hlookup

/-- Caching a fresh response and appending it preserves log consistency. -/
theorem log_consistent_cacheQuery_append [DecidableEq ι] (cache : (ι →ₒ Y).QueryCache)
    (log : (ι →ₒ Y).QueryLog) (t : ι) (value : Y) (hnone : cache t = none)
    (hlog : ∀ entry ∈ log, cache entry.1 = some entry.2) :
    ∀ entry ∈ log ++ [⟨t, value⟩], (cache.cacheQuery t value) entry.1 = some entry.2 := by
  apply log_consistent_append _ _ t value (cacheQuery_self ..)
  intro entry hentry
  exact le_cacheQuery cache hnone (hlog entry hentry)

/-- Appending entries preserves coverage of every cached response by the log. -/
theorem cache_covered_append (cache : (ι →ₒ Y).QueryCache)
    (log extra : (ι →ₒ Y).QueryLog)
    (hlog : ∀ input output, cache input = some output →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = output) :
    ∀ input output, cache input = some output →
      ∃ entry ∈ log ++ extra, entry.1 = input ∧ entry.2 = output := by
  intro input output hcached
  obtain ⟨entry, hentry, hi, ho⟩ := hlog input output hcached
  exact ⟨entry, List.mem_append_left _ hentry, hi, ho⟩

/-- The extended log covers every response in an updated cache. -/
theorem cache_covered_cacheQuery_append [DecidableEq ι] (cache : (ι →ₒ Y).QueryCache)
    (log : (ι →ₒ Y).QueryLog) (t : ι) (value : Y)
    (hlog : ∀ input output, cache input = some output →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = output) :
    ∀ input output, (cache.cacheQuery t value) input = some output →
      ∃ entry ∈ log ++ [⟨t, value⟩], entry.1 = input ∧ entry.2 = output := by
  intro input output hcached
  by_cases hi : input = t
  · subst input
    rw [cacheQuery_self] at hcached
    obtain rfl := Option.some.inj hcached
    exact ⟨⟨t, value⟩, by simp, rfl, rfl⟩
  · rw [cacheQuery_of_ne cache value hi] at hcached
    exact cache_covered_append cache log _ hlog input output hcached

/-- Inserting one response increases a finite cache-domain bound by at most one. -/
theorem domain_bound_cacheQuery [DecidableEq ι] (cache : (ι →ₒ Y).QueryCache) (t : ι) (value : Y)
    (bound : ℕ) (hbound : ∃ keys : Finset ι, keys.card ≤ bound ∧
      ∀ input, cache input ≠ none → input ∈ keys) :
    ∃ keys : Finset ι, keys.card ≤ bound + 1 ∧
      ∀ input, (cache.cacheQuery t value) input ≠ none → input ∈ keys := by
  obtain ⟨keys, hcard, hmem⟩ := hbound
  refine ⟨insert t keys, (Finset.card_insert_le t keys).trans (by omega), ?_⟩
  intro input hinput
  by_cases hi : input = t
  · exact hi ▸ Finset.mem_insert_self _ _
  · rw [cacheQuery_of_ne cache value hi] at hinput
    exact Finset.mem_insert_of_mem (hmem input hinput)
end OracleSpec.QueryCache
