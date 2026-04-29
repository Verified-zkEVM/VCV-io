/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle

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
          ((fun u => (u, s.2 ++ [⟨t, u⟩])) <$> so t) := by
  simp [withCachingLogging, withCachingTraceAppend_apply]

/-! ### Forward-direction query bounds for `withCachingTraceAppend`

The trace overlay does not change the underlying query count, so the `withCaching` bounds
transfer through `withCachingAux_run_proj_eq` via `isQueryBound_iff_of_map_eq`. -/

variable {α : Type u} {ι' : Type u} {spec' : OracleSpec ι'}

omit [Monad m] [spec.DecidableEq] in
private lemma _root_.QueryImpl.withCachingTraceAppend_run_proj_eq
    {ι₂ : Type u} {spec₂ : OracleSpec ι₂} [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec₂))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (oa : OracleComp spec α) (s : QueryCache spec × ω) :
    Prod.map id Prod.fst <$> (simulateQ (so.withCachingTraceAppend traceFn) oa).run s =
      (simulateQ so.withCaching oa).run s.1 :=
  QueryImpl.withCachingAux_run_proj_eq so _ _
    (by intro t cache q; simp [Functor.map_map]) oa s.1 s.2

omit [Monad m] [spec.DecidableEq] in
theorem isTotalQueryBound_run_simulateQ_withCachingTraceAppend
    [LawfulAppend ω]
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
theorem isQueryBoundP_run_simulateQ_withCachingTraceAppend
    [LawfulAppend ω]
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
  cases hcache : s.1 t with
  | some u =>
      simp [hcache]
  | none =>
      simp [hcache, StateT.run_bind, StateT.run_monadLift, Functor.map_map]

/-- Projecting away the log component recovers the ordinary caching semantics. -/
theorem fst_map_run_simulateQ {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    Prod.map id Prod.fst <$> (simulateQ cachingLoggingOracle oa).run s =
      (simulateQ cachingOracle oa).run s.1 := by
  simpa [cachingLoggingOracle, QueryImpl.withCachingLogging, QueryImpl.withCachingTraceAppend,
    cachingOracle] using
    (QueryImpl.withCachingAux_run_proj_eq
      (base := QueryImpl.ofLift spec (OracleComp spec))
      (hit := fun t u _ trace => trace ++ [⟨t, u⟩])
      (miss := fun t _ trace => (fun u => (u, trace ++ [⟨t, u⟩])) <$>
        (QueryImpl.ofLift spec (OracleComp spec) t))
      (hmiss := by
        intro t cache trace
        simp [Functor.map_map])
      (oa := oa) (cache := s.1) (q := s.2))

/-- Output-only projection corollary of `fst_map_run_simulateQ`. -/
@[simp]
theorem run'_simulateQ_eq {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    (simulateQ cachingLoggingOracle oa).run' s =
      (simulateQ cachingOracle oa).run' s.1 := by
  have hrun := fst_map_run_simulateQ oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

/-! ### Forward-direction query bounds

The log overlay does not change the underlying query count, so the `cachingOracle` bounds
transfer through `fst_map_run_simulateQ` via `isQueryBound_iff_of_map_eq`. -/

theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] {α : Type}
    {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.cachingLoggingOracle oa).run s) n :=
  (OracleComp.isQueryBound_iff_of_map_eq (fst_map_run_simulateQ oa s) _ _).mpr
    (cachingOracle.isTotalQueryBound_run_simulateQ h s.1)

theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] {α : Type}
    {oa : OracleComp spec₀ α} {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.cachingLoggingOracle oa).run s) p n :=
  (OracleComp.isQueryBoundP_iff_of_map_eq (fst_map_run_simulateQ oa s)).mpr
    (cachingOracle.isQueryBoundP_run_simulateQ h s.1)

theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] {α : Type}
    {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.cachingLoggingOracle oa).run s) qb :=
  (OracleComp.isPerIndexQueryBound_iff_of_map_eq (fst_map_run_simulateQ oa s)).mpr
    (cachingOracle.isPerIndexQueryBound_run_simulateQ h s.1)

end cachingLoggingOracle
