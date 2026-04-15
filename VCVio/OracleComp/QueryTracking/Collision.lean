/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.EvalDist

/-!
# ROM Collision Infrastructure

Collision predicates on `QueryLog` and `QueryCache`, together with structural
lemmas relating log entries and cache entries when running `loggingOracle`
inside `cachingOracle`.

## Main declarations

* `OracleComp.LogHasCollision`: two log entries at distinct positions with
  distinct inputs but `HEq`-equal outputs.
* `OracleComp.CacheHasCollision`: two distinct cache inputs map to the same output.
* `OracleComp.cache_lookup_eq_of_noCollision`: in a collision-free cache,
  a value determines at most one query input.
* `OracleComp.log_entry_in_cache_and_mono`: every log entry ends up in the
  cache, and the cache is monotone.
* `OracleComp.cache_entry_in_log_or_initial`: every new cache entry has a
  corresponding log entry.
-/

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-! ## Collision Predicates -/

/-- A query log has a collision: two entries at distinct positions with
distinct inputs but HEq-equal outputs. -/
def LogHasCollision (log : QueryLog spec) : Prop :=
  ∃ (i j : Fin log.length), i ≠ j ∧
    log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2

/-- A cache has a collision: two distinct inputs map to the same output. -/
def CacheHasCollision (cache : QueryCache spec) : Prop :=
  ∃ (t₁ t₂ : spec.Domain) (u₁ : spec.Range t₁) (u₂ : spec.Range t₂),
    t₁ ≠ t₂ ∧ cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ HEq u₁ u₂

omit [DecidableEq ι] [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- In a collision-free cache, a value determines at most one query input. -/
lemma cache_lookup_eq_of_noCollision
    {cache : QueryCache spec}
    {t₀ t₁ : spec.Domain} {v : spec.Range t₀}
    (hno : ¬ CacheHasCollision cache)
    (h₀ : cache t₀ = some v)
    (h₁ : ∃ v' : spec.Range t₁, cache t₁ = some v' ∧ HEq v' v) :
    t₀ = t₁ := by
  rcases h₁ with ⟨v', hcache₁, hv'⟩
  by_contra hne
  exact hno ⟨t₀, t₁, v, v', hne, h₀, hcache₁, hv'.symm⟩

/-! ## Log entries are cached after logging inside caching -/

omit [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- When running `loggingOracle` inside `cachingOracle`, every log entry ends up in the cache.

We prove two properties simultaneously by induction:
1. Every log entry is in the final cache.
2. The initial cache is a subset of the final cache (monotonicity).

The proof works by induction on `oa`. The `pure` case is trivial (empty log).
For `query t >>= mx`: the logging oracle decomposes as
`query t >>= fun u => map (prepend ⟨t,u⟩) ...`,
and `cachingOracle` caches the query result `u` at `t`. By the IH applied to `mx u`,
all sub-log entries are in the final cache, and cache monotonicity ensures `t ↦ u` persists. -/
theorem log_entry_in_cache_and_mono {α : Type}
    (oa : OracleComp spec α)
    (cache₀ : QueryCache spec)
    (z : (α × QueryLog spec) × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle
        ((simulateQ loggingOracle oa).run)).run cache₀)) :
    (∀ entry ∈ z.1.2, z.2 entry.1 = some entry.2) ∧ cache₀ ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    simp only [simulateQ_pure] at hmem
    change z ∈ support (pure ((a, ([] : QueryLog spec)), cache₀)) at hmem
    rw [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨fun _ h => ?_, le_refl _⟩; simp at h
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at hmem
    rw [show simulateQ cachingOracle
          ((query t : OracleComp spec _) >>= fun u =>
            (fun p : α × QueryLog spec =>
                (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                  :: p.2))
              <$> (simulateQ loggingOracle (mx u)).run) =
          ((cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                    :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) :
            StateT (QueryCache spec) (OracleComp spec) _)
        from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query]] at hmem
    have hbind_rw : (cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                    :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run) :
            StateT (QueryCache spec) (OracleComp spec) _) =
          (cachingOracle t >>= fun u =>
            StateT.map
              (fun p : α × QueryLog spec =>
                (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                  :: p.2))
              (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
      congr 1; ext u s
      simp only [StateT.map, StateT.run, map_eq_bind_pure_comp, simulateQ_bind,
        simulateQ_pure, Function.comp_def]
      rfl
    rw [hbind_rw] at hmem
    rw [StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hu_mem, hmem⟩ := hmem
    have hu_mem' : (u, cache_mid) ∈ support ((cachingOracle (spec := spec) t).run cache₀) := by
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem ⊢
      exact hu_mem
    have hcache_mid_entry : cache_mid t = some u := by
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem
      cases hc : cache₀ t with
      | some v =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hu_mem; exact hc
      | none =>
        simp only [hc, StateT.run_bind, StateT.run_modifyGet] at hu_mem
        rw [support_bind] at hu_mem; simp only [Set.mem_iUnion] at hu_mem
        obtain ⟨w, _, hmem_w⟩ := hu_mem
        rw [support_pure, Set.mem_singleton_iff] at hmem_w
        have h1 : u = w.1 := congr_arg Prod.fst hmem_w
        have h2 : cache_mid = w.2.cacheQuery t w.1 := congr_arg Prod.snd hmem_w
        subst h1; rw [h2]
        exact QueryCache.cacheQuery_self w.2 t w.1
    have hcache₀_le_mid : cache₀ ≤ cache_mid := by
      unfold cachingOracle at hu_mem'
      exact QueryImpl.withCaching_cache_le
        (QueryImpl.ofLift spec (OracleComp spec)) t cache₀ (u, cache_mid) hu_mem'
    change z ∈ support ((StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid) at hmem
    rw [show (StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid =
      (fun zz : (α × QueryLog spec) × QueryCache spec =>
        ((zz.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zz.1.2), zz.2)) <$>
      ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache_mid)
      from by simp only [StateT.map, StateT.run, map_eq_bind_pure_comp,
        Function.comp_def]] at hmem
    rw [support_map] at hmem
    obtain ⟨⟨⟨x', log'⟩, cache_final⟩, hmem_cont, heq⟩ := hmem
    have hz : z =
        ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'),
          cache_final) := heq.symm
    rw [hz]
    have ⟨ih_entries, ih_mono⟩ := ih u cache_mid ((x', log'), cache_final) hmem_cont
    exact ⟨fun entry hentry => by
      cases hentry with
      | head => exact ih_mono hcache_mid_entry
      | tail _ hentry' => exact ih_entries entry hentry',
      le_trans hcache₀_le_mid ih_mono⟩

omit [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] in
/-- **Converse of `log_entry_in_cache_and_mono`**: when running `loggingOracle` inside
`cachingOracle`, every cache entry that was not in the initial cache has a corresponding
log entry. Combined with `log_entry_in_cache_and_mono`, this shows that (starting from `∅`)
the cache entries and log entries have the same set of `(input, output)` pairs.

Proof by structural induction on `oa`, mirroring `log_entry_in_cache_and_mono`. -/
theorem cache_entry_in_log_or_initial {α : Type}
    (oa : OracleComp spec α)
    (cache₀ : QueryCache spec)
    (z : (α × QueryLog spec) × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle
        ((simulateQ loggingOracle oa).run)).run cache₀)) :
    ∀ (t₀ : spec.Domain) (v : spec.Range t₀),
      z.2 t₀ = some v → cache₀ t₀ = some v ∨
        ∃ entry ∈ z.1.2, entry.1 = t₀ ∧ HEq entry.2 v := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    simp only [simulateQ_pure] at hmem
    change z ∈ support (pure ((a, ([] : QueryLog spec)), cache₀)) at hmem
    rw [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    intro t₀ v hcache
    exact Or.inl hcache
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at hmem
    rw [show simulateQ cachingOracle
          ((query t : OracleComp spec _) >>= fun u =>
            (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              <$> (simulateQ loggingOracle (mx u)).run) =
          ((cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                    :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) :
            StateT (QueryCache spec) (OracleComp spec) _)
        from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query]] at hmem
    have hbind_rw : (cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec =>
                  (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                    :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run) :
            StateT (QueryCache spec) (OracleComp spec) _) =
          (cachingOracle t >>= fun u =>
            StateT.map
              (fun p : α × QueryLog spec =>
                (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)
                  :: p.2))
              (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
      congr 1; ext u s
      simp only [StateT.map, StateT.run, map_eq_bind_pure_comp, simulateQ_bind,
        simulateQ_pure, Function.comp_def]
      rfl
    rw [hbind_rw] at hmem
    rw [StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hu_mem, hmem⟩ := hmem
    have hcache_mid_entry : cache_mid t = some u := by
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem
      cases hc : cache₀ t with
      | some v =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hu_mem; exact hc
      | none =>
        simp only [hc, StateT.run_bind, StateT.run_modifyGet] at hu_mem
        rw [support_bind] at hu_mem; simp only [Set.mem_iUnion] at hu_mem
        obtain ⟨w, _, hmem_w⟩ := hu_mem
        rw [support_pure, Set.mem_singleton_iff] at hmem_w
        have h1 : u = w.1 := congr_arg Prod.fst hmem_w
        have h2 : cache_mid = w.2.cacheQuery t w.1 := congr_arg Prod.snd hmem_w
        subst h1; rw [h2]
        exact QueryCache.cacheQuery_self w.2 t w.1
    have hcache₀_le_mid : cache₀ ≤ cache_mid := by
      have hu_mem' : (u, cache_mid) ∈ support ((cachingOracle (spec := spec) t).run cache₀) := by
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem ⊢
        exact hu_mem
      unfold cachingOracle at hu_mem'
      exact QueryImpl.withCaching_cache_le
        (QueryImpl.ofLift spec (OracleComp spec)) t cache₀ (u, cache_mid) hu_mem'
    change z ∈ support ((StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid) at hmem
    rw [show (StateT.map
      (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
      (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid =
      (fun zz : (α × QueryLog spec) × QueryCache spec =>
        ((zz.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zz.1.2), zz.2)) <$>
      ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache_mid)
      from by simp only [StateT.map, StateT.run, map_eq_bind_pure_comp,
        Function.comp_def]] at hmem
    rw [support_map] at hmem
    obtain ⟨⟨⟨x', log'⟩, cache_final⟩, hmem_cont, heq⟩ := hmem
    have hz : z =
        ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'),
          cache_final) := heq.symm
    rw [hz]
    have hcache_mid_eq : ∀ t₀ : spec.Domain, t₀ ≠ t → cache_mid t₀ = cache₀ t₀ := by
      intro t₀ hne
      have hu_mem' : (u, cache_mid) ∈ support ((cachingOracle (spec := spec) t).run cache₀) := by
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem ⊢
        exact hu_mem
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem'
      cases hc : cache₀ t with
      | some w =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem'
        have := (Prod.mk.inj hu_mem').2; rw [this]
      | none =>
        simp only [hc, StateT.run_bind] at hu_mem'
        change (u, cache_mid) ∈ support
          ((liftM (query t) : StateT _ (OracleComp spec) _).run cache₀ >>= fun p =>
            ((modifyGet fun cache => (p.1, QueryCache.cacheQuery cache t p.1) :
              StateT (QueryCache spec) (OracleComp spec) _).run p.2)) at hu_mem'
        rw [support_bind] at hu_mem'; simp only [Set.mem_iUnion] at hu_mem'
        obtain ⟨⟨r, s⟩, hrs, hfinal⟩ := hu_mem'
        simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hfinal
        have hcm : cache_mid = s.cacheQuery t r := congr_arg Prod.snd hfinal
        simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
          StateT.run, StateT.lift] at hrs
        rw [support_bind] at hrs; simp only [Set.mem_iUnion] at hrs
        obtain ⟨q, _, hq⟩ := hrs
        rw [support_pure, Set.mem_singleton_iff] at hq
        have hs : s = cache₀ := congr_arg Prod.snd hq
        rw [hcm, hs, QueryCache.cacheQuery_of_ne _ _ hne]
    intro t₀ v hcache_final
    have ih_result := ih u cache_mid ((x', log'), cache_final) hmem_cont t₀ v hcache_final
    rcases ih_result with h_in_mid | ⟨entry, hentry, hentry_eq, hentry_heq⟩
    · by_cases ht₀ : t₀ = t
      · subst ht₀
        rw [hcache_mid_entry] at h_in_mid; cases h_in_mid
        exact Or.inr ⟨⟨t₀, _⟩, List.Mem.head _, rfl, HEq.rfl⟩
      · rw [hcache_mid_eq t₀ ht₀] at h_in_mid
        exact Or.inl h_in_mid
    · exact Or.inr ⟨entry, List.Mem.tail _ hentry, hentry_eq, hentry_heq⟩

end OracleComp
