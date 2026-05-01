/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.SimSemantics.PreservesInv
import VCVio.OracleComp.SimSemantics.StateProjection

/-!
# Caching Queries Made by a Computation

This file defines a modifier `QueryImpl.withCaching` that modifies a query implementation to
cache results to return to the same query in the future.

We also define `cachingOracle`, which caches queries to the oracles in `spec`,
querying fresh values from `spec` if no cached value exists.
-/

open OracleComp OracleSpec

universe u v w

open scoped OracleSpec.PrimitiveQuery

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

lemma withCaching_run_some [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {cache : spec.QueryCache} {u : spec.Range t} (hcache : cache t = some u) :
    (so.withCaching t).run cache = pure (u, cache) := by
  simp only [withCaching_apply, StateT.run_bind]
  rw [show (get : StateT spec.QueryCache m spec.QueryCache).run cache =
      pure (cache, cache) from rfl, pure_bind]
  simp [hcache]

lemma withCaching_run_none [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {cache : spec.QueryCache} (hcache : cache t = none) :
    (so.withCaching t).run cache =
      (fun u => (u, cache.cacheQuery t u)) <$> so t := by
  simp only [withCaching_apply, StateT.run_bind]
  rw [show (get : StateT spec.QueryCache m spec.QueryCache).run cache =
      pure (cache, cache) from rfl, pure_bind]
  simp [hcache, StateT.run_bind, StateT.run_monadLift, bind_pure_comp]

/-! ## Caching with auxiliary state -/

section CachingAux

variable {Q : Type w} {m' : Type (max u w) → Type v} [Monad m']

/-- Cache responses while threading an auxiliary state component.

The cache is consulted first. On a hit, the cached response is returned and the auxiliary state is
updated by `hit`. On a miss, `miss` produces both the response and the next auxiliary state; the
response is then installed in the cache. -/
def withCachingAux
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m' (spec.Range t × Q)) :
    QueryImpl spec (StateT (spec.QueryCache × Q) m') :=
  fun t => StateT.mk fun s =>
    match s with
    | (cache, q) =>
        match cache t with
        | some u => pure (u, (cache, hit t u cache q))
        | none => (fun p : spec.Range t × Q => (p.1, (cache.cacheQuery t p.1, p.2))) <$>
            miss t cache q

@[simp, grind =]
lemma withCachingAux_apply
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m' (spec.Range t × Q))
    (t : spec.Domain) (s : spec.QueryCache × Q) :
    (withCachingAux (spec := spec) hit miss t).run s =
      (match s.1 t with
      | some u => pure (u, (s.1, hit t u s.1 s.2))
      | none =>
          (fun p : spec.Range t × Q => (p.1, (s.1.cacheQuery t p.1, p.2))) <$>
            miss t s.1 s.2) := by
  cases s
  rfl

end CachingAux

section CacheAuxProjection

variable {Q : Type u}
variable [LawfulMonad m]

/-- Projecting away the auxiliary state of `withCachingAux` recovers ordinary caching whenever
the miss handler has the same output marginal as the base implementation. -/
theorem withCachingAux_run_proj_eq
    (base : QueryImpl spec m)
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m (spec.Range t × Q))
    (hmiss : ∀ t cache q, Prod.fst <$> miss t cache q = base t)
    {α : Type u} (oa : OracleComp spec α) (cache : spec.QueryCache) (q : Q) :
    Prod.map id Prod.fst <$> (simulateQ (withCachingAux hit miss) oa).run (cache, q) =
      (simulateQ base.withCaching oa).run cache := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := withCachingAux hit miss) (impl₂ := base.withCaching)
    (proj := Prod.fst) ?_ oa (cache, q)
  intro t ⟨cache', q'⟩
  cases hcache : cache' t with
  | some u =>
      rw [withCachingAux_apply, withCaching_run_some base hcache]
      simp [hcache]
  | none =>
      rw [withCachingAux_apply, withCaching_run_none base hcache]
      simp only [hcache, Functor.map_map]
      change (fun p : spec.Range t × Q => (p.1, cache'.cacheQuery t p.1)) <$>
          miss t cache' q' =
        (fun u => (u, cache'.cacheQuery t u)) <$> base t
      rw [← hmiss t cache' q', Functor.map_map]

/-- Output-only corollary of `withCachingAux_run_proj_eq`. -/
theorem withCachingAux_run'_eq
    (base : QueryImpl spec m)
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m (spec.Range t × Q))
    (hmiss : ∀ t cache q, Prod.fst <$> miss t cache q = base t)
    {α : Type u} (oa : OracleComp spec α) (cache : spec.QueryCache) (q : Q) :
    (simulateQ (withCachingAux hit miss) oa).run' (cache, q) =
      (simulateQ base.withCaching oa).run' cache := by
  have h := withCachingAux_run_proj_eq base hit miss hmiss oa cache q
  have hmap := congrArg (fun p => Prod.fst <$> p) h
  simpa [StateT.run'] using hmap

end CacheAuxProjection

section CachingAuxInvariant

variable {Q : Type w} {m' : Type (max u w) → Type v} [Monad m'] [LawfulMonad m']
  [HasEvalSet m']

/-- One-step invariant preservation for the auxiliary component of `withCachingAux`. -/
theorem withCachingAux_aux_inv_of_mem
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m' (spec.Range t × Q))
    (inv : Q → Prop)
    (hhit : ∀ t u cache q, inv q → inv (hit t u cache q))
    (hmiss : ∀ t cache q, inv q → ∀ p ∈ support (miss t cache q), inv p.2)
    {t : spec.Domain} {cache : spec.QueryCache} {q : Q}
    {z : spec.Range t × spec.QueryCache × Q}
    (hq : inv q) (hz : z ∈ support ((withCachingAux hit miss t).run (cache, q))) :
    inv z.2.2 := by
  rw [withCachingAux_apply] at hz
  cases hcache : cache t with
  | some u =>
      simp only [hcache, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hhit t u cache q hq
  | none =>
      simp only [hcache] at hz
      rw [support_map] at hz
      rcases hz with ⟨p, hp, hz⟩
      rw [← hz]
      exact hmiss t cache q hq p hp

end CachingAuxInvariant

/-- A `withCachingAux` handler preserves an invariant on its auxiliary component when both hit and
miss auxiliary updates preserve it. -/
theorem PreservesInv.withCachingAux_aux
    {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀} {Q₀ : Type}
    (hit : (t : spec₀.Domain) → spec₀.Range t → spec₀.QueryCache → Q₀ → Q₀)
    (miss : (t : spec₀.Domain) → spec₀.QueryCache → Q₀ → ProbComp (spec₀.Range t × Q₀))
    (inv : Q₀ → Prop)
    (hhit : ∀ t u cache q, inv q → inv (hit t u cache q))
    (hmiss : ∀ t cache q, inv q → ∀ p ∈ support (miss t cache q), inv p.2) :
    QueryImpl.PreservesInv (withCachingAux hit miss)
      (fun s : spec₀.QueryCache × Q₀ => inv s.2) := by
  intro t ⟨cache, q⟩ hq z hz
  exact withCachingAux_aux_inv_of_mem hit miss inv hhit hmiss hq hz

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
    simp only [hlift, monad_norm] at hz
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

/-! ## Forward query bounds for `withCaching`

A wrapped step makes ≤ 1 underlying query (zero on a hit, one on a miss), so any bound on
`so t` transfers to `(so.withCaching t).run cache`. -/

section QueryBound

variable {ι' : Type u} {spec' : OracleSpec ι'}

lemma isQueryBoundP_run_withCaching
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    {p : ι' → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP (so t) p n) (cache : spec.QueryCache) :
    OracleComp.IsQueryBoundP ((so.withCaching t).run cache) p n := by
  cases hcache : cache t with
  | none =>
      rw [withCaching_run_none _ hcache]
      exact (OracleComp.isQueryBoundP_map_iff (p := p) _ _ _).mpr h
  | some u =>
      rw [withCaching_run_some _ hcache]
      trivial

lemma isTotalQueryBound_run_withCaching
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain) {n : ℕ}
    (h : OracleComp.IsTotalQueryBound (so t) n) (cache : spec.QueryCache) :
    OracleComp.IsTotalQueryBound ((so.withCaching t).run cache) n := by
  cases hcache : cache t with
  | none =>
      rw [withCaching_run_none _ hcache]
      exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).mpr h
  | some u =>
      rw [withCaching_run_some _ hcache]
      trivial

lemma isPerIndexQueryBound_run_withCaching
    (so : QueryImpl spec (OracleComp spec)) (t : spec.Domain) {qb : ι → ℕ}
    (h : OracleComp.IsPerIndexQueryBound (so t) qb) (cache : spec.QueryCache) :
    OracleComp.IsPerIndexQueryBound ((so.withCaching t).run cache) qb := by
  cases hcache : cache t with
  | none =>
      rw [withCaching_run_none _ hcache]
      exact (OracleComp.isPerIndexQueryBound_map_iff _ _ _).mpr h
  | some u =>
      rw [withCaching_run_some _ hcache]
      trivial

end QueryBound

end QueryImpl

/-! ### Parametric `simulateQ` lifts for `withCaching` -/

namespace OracleComp

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
  {ι' : Type u} {spec' : OracleSpec ι'} {α : Type u}

theorem IsQueryBoundP.simulateQ_run_withCaching
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    (so : QueryImpl spec (OracleComp spec'))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → IsQueryBoundP (so t) q 1)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (so t) q 0)
    (cache : spec.QueryCache) :
    IsQueryBoundP ((simulateQ so.withCaching oa).run cache) q n :=
  IsQueryBoundP.simulateQ_run_of_step h
    (fun t hp s' => QueryImpl.isQueryBoundP_run_withCaching so t (hstep_p t hp) s')
    (fun t hnp s' => QueryImpl.isQueryBoundP_run_withCaching so t (hstep_np t hnp) s')
    cache

theorem IsTotalQueryBound.simulateQ_run_withCaching
    (so : QueryImpl spec (OracleComp spec'))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t, IsTotalQueryBound (so t) 1)
    (cache : spec.QueryCache) :
    IsTotalQueryBound ((simulateQ so.withCaching oa).run cache) n :=
  IsTotalQueryBound.simulateQ_run_of_step h
    (fun t s' => QueryImpl.isTotalQueryBound_run_withCaching so t (hstep t) s')
    cache

theorem IsPerIndexQueryBound.simulateQ_run_withCaching
    (so : QueryImpl spec (OracleComp spec))
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep : ∀ t, IsPerIndexQueryBound (so t) (Function.update 0 t 1))
    (cache : spec.QueryCache) :
    IsPerIndexQueryBound ((simulateQ so.withCaching oa).run cache) qb :=
  IsPerIndexQueryBound.simulateQ_run_of_uniform_step h
    (fun t s' => QueryImpl.isPerIndexQueryBound_run_withCaching so t (hstep t) s')
    cache

end OracleComp

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def OracleSpec.cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCaching

namespace cachingOracle

/-- Definitional unfold of `cachingOracle` as caching wrapped around the lifting handler. -/
lemma eq_withCaching :
    (spec.cachingOracle : QueryImpl spec (StateT spec.QueryCache (OracleComp spec))) =
      (QueryImpl.ofLift spec (OracleComp spec)).withCaching := rfl

lemma apply_eq (t : spec.Domain) : cachingOracle t =
    (do match (← get) t with
      | Option.some u => return u
      | Option.none =>
          let u ← query t
          modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

/-- Cache hit: `cachingOracle t` returns the stored value without an underlying query. -/
lemma run_some {t : spec.Domain} {cache : spec.QueryCache} {u : spec.Range t}
    (h : cache t = some u) : (cachingOracle t).run cache = pure (u, cache) :=
  QueryImpl.withCaching_run_some _ h

/-- Cache miss: `cachingOracle t` issues a single underlying `query t` and stores it. -/
lemma run_none {t : spec.Domain} {cache : spec.QueryCache} (h : cache t = none) :
    (cachingOracle t).run cache =
      (fun u => (u, cache.cacheQuery t u)) <$> (liftM (query t) : OracleComp spec _) := by
  rw [eq_withCaching, QueryImpl.withCaching_run_none _ h, QueryImpl.ofLift_apply]

/-- Trivially true via `probFailure_eq_zero` since both sides are `OracleComp` computations.
A generic `withCaching` version for arbitrary base monads would require a separate argument
because caching changes the oracle semantics (cache hits skip the underlying oracle call). -/
@[simp]
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    Pr[⊥ | (simulateQ spec₀.cachingOracle oa).run cache] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/-- Trivially true via `probFailure_eq_zero`; see `probFailure_run_simulateQ`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    NeverFail ((simulateQ spec₀.cachingOracle oa).run cache) ↔ NeverFail oa := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    HasEvalPMF.probFailure_eq_zero, HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma simulateQ_query (t : spec.Domain) :
    simulateQ cachingOracle (liftM (query t)) = cachingOracle t := by
  simp [_root_.simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]

/-! ### Forward query bounds for `cachingOracle`

Forward only — the reverse fails because cache hits strictly reduce the simulated count. -/

theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n) (cache : spec₀.QueryCache) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.cachingOracle oa).run cache) n := by
  rw [eq_withCaching]
  exact OracleComp.IsTotalQueryBound.simulateQ_run_withCaching _ h
    (fun t => (OracleComp.isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) cache

theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {oa : OracleComp spec₀ α} {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n) (cache : spec₀.QueryCache) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.cachingOracle oa).run cache) p n := by
  rw [eq_withCaching]
  exact OracleComp.IsQueryBoundP.simulateQ_run_withCaching _ h
    (fun t _ => (OracleComp.isQueryBoundP_query_iff p t 1).mpr (fun _ => Nat.one_pos))
    (fun t hnp => (OracleComp.isQueryBoundP_query_iff p t 0).mpr (fun hpt => absurd hpt hnp))
    cache

theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb) (cache : spec₀.QueryCache) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.cachingOracle oa).run cache) qb := by
  rw [eq_withCaching]
  refine OracleComp.IsPerIndexQueryBound.simulateQ_run_withCaching _ h ?_ cache
  intro t
  rw [QueryImpl.ofLift_apply]
  exact (OracleComp.isPerIndexQueryBound_query_iff t (Function.update 0 t 1)).mpr (by
    simp [Function.update_self])

end cachingOracle

section withCacheOverlay

/-- Run an `OracleComp` with a `QueryCache` as a priority layer over the real oracle.
Cached entries are returned directly (no oracle query), misses fall through to the real
oracle and get cached for subsequent lookups within the same computation.

This is the fundamental "programmable random oracle" primitive: pre-fill the cache with
programmed entries, then run the computation. Concretely:

  `withCacheOverlay cache oa = StateT.run' (simulateQ cachingOracle oa) cache`

Key properties:
- `withCacheOverlay ∅ oa` deduplicates queries but is otherwise equivalent to `oa`.
- `withCacheOverlay cache (query t)` returns `v` without an external query when
  `cache t = some v`, and queries the real oracle when `cache t = none`.

The cache-parametric runtime built on top of this combinator lives in
`VCVio.CryptoFoundations.FiatShamir.Sigma` as `FiatShamir.runtimeWithCache cache`, with
`FiatShamir.runtime` defined as `runtimeWithCache ∅`. -/
def OracleSpec.withCacheOverlay {α : Type u} (cache : spec.QueryCache) (oa : OracleComp spec α) :
    OracleComp spec α :=
  StateT.run' (simulateQ spec.cachingOracle oa) cache

@[simp]
lemma withCacheOverlay_pure {α : Type u} (cache : spec.QueryCache) (a : α) :
    withCacheOverlay cache (pure a : OracleComp spec α) = pure a := by
  change Prod.fst <$> (pure (a, cache) : OracleComp spec _) = _; simp

lemma withCacheOverlay_bind {α β : Type u} (cache : spec.QueryCache)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    withCacheOverlay cache (oa >>= ob) =
      ((simulateQ cachingOracle oa).run cache >>= fun p =>
        withCacheOverlay p.2 (ob p.1)) := by
  simp only [withCacheOverlay, simulateQ_bind, StateT.run']
  change Prod.fst <$> (((simulateQ cachingOracle oa >>=
    fun x => simulateQ cachingOracle (ob x)) :
      StateT (QueryCache spec) (OracleComp spec) β).run cache) = _
  rw [StateT.run_bind, map_bind]
  refine bind_congr fun p => ?_
  rfl

lemma withCacheOverlay_map {α β : Type u} (cache : spec.QueryCache)
    (f : α → β) (oa : OracleComp spec α) :
    withCacheOverlay cache (f <$> oa) = f <$> withCacheOverlay cache oa := by
  rw [map_eq_bind_pure_comp, withCacheOverlay_bind]
  simp [withCacheOverlay]

lemma withCacheOverlay_bind_pure {α β : Type u} (cache : spec.QueryCache)
    (oa : OracleComp spec α) (f : α → β) :
    withCacheOverlay cache (oa >>= fun x => pure (f x)) =
      f <$> withCacheOverlay cache oa := by
  change withCacheOverlay cache (f <$> oa) = f <$> withCacheOverlay cache oa
  exact withCacheOverlay_map cache f oa

private lemma fst_map_cachingOracle_run_some (cache : spec.QueryCache) (t : spec.Domain)
    (v : spec.Range t) (hv : cache t = some v) :
    Prod.fst <$> (cachingOracle t).run cache = pure v := by
  unfold cachingOracle QueryImpl.withCaching QueryImpl.ofLift
  simp only [StateT.run_bind,
    show (get : StateT spec.QueryCache (OracleComp spec) _).run cache =
      (pure (cache, cache) : OracleComp spec _) from rfl, pure_bind, hv,
    show (pure v : StateT spec.QueryCache (OracleComp spec) _).run cache =
      (pure (v, cache) : OracleComp spec _) from rfl, map_pure]

private lemma fst_map_cachingOracle_run_none (cache : spec.QueryCache) (t : spec.Domain)
    (hv : cache t = none) :
    Prod.fst <$> (cachingOracle t).run cache =
      (query t : OracleComp spec (spec.Range t)) := by
  unfold cachingOracle QueryImpl.withCaching QueryImpl.ofLift
  simp only [StateT.run_bind,
    show (get : StateT spec.QueryCache (OracleComp spec) _).run cache =
      (pure (cache, cache) : OracleComp spec _) from rfl, pure_bind, hv,
    show (liftM (query t : OracleComp spec _) :
        StateT _ (OracleComp spec) _).run cache =
      ((query t : OracleComp spec _) >>= fun u => pure (u, cache)) from rfl,
    bind_assoc, pure_bind,
    show ∀ u, (modifyGet (fun c : QueryCache spec => (u, c.cacheQuery t u)) :
        StateT _ (OracleComp spec) _).run cache =
      (pure (u, cache.cacheQuery t u) : OracleComp spec _) from fun _ => rfl,
    map_bind, map_pure, bind_pure]

lemma withCacheOverlay_query_hit (cache : spec.QueryCache) (t : spec.Domain)
    (v : spec.Range t) (hv : cache t = some v) :
    withCacheOverlay cache (query t : OracleComp spec (spec.Range t)) = pure v := by
  change Prod.fst <$> (simulateQ cachingOracle
    (query t : OracleComp spec (spec.Range t))).run cache = _
  rw [cachingOracle.simulateQ_query, fst_map_cachingOracle_run_some cache t v hv]

lemma withCacheOverlay_query_miss (cache : spec.QueryCache) (t : spec.Domain)
    (hv : cache t = none) :
    withCacheOverlay cache (query t : OracleComp spec (spec.Range t)) = query t := by
  change Prod.fst <$> (simulateQ cachingOracle
    (query t : OracleComp spec (spec.Range t))).run cache = _
  rw [cachingOracle.simulateQ_query, fst_map_cachingOracle_run_none cache t hv]

end withCacheOverlay

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
    simp only [monad_norm] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨u, _, hmem⟩ := hmem
    simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact QueryCache.cacheQuery_self cache₀ t v

end OracleComp
