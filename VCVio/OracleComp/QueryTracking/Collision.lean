/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound

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

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}

/-! ## Collision Predicates -/

/-- A query log has a collision: two entries at distinct positions with
distinct inputs but HEq-equal outputs. -/
def LogHasCollision (log : QueryLog spec) : Prop :=
  ∃ (i j : Fin log.length), i ≠ j ∧ log[i].1 ≠ log[j].1 ∧ HEq log[i].2 log[j].2

omit [DecidableEq ι] in
/-- Value-form constructor for `LogHasCollision`: any two distinct log entries with
`HEq`-equal outputs (note: distinctness forces distinct inputs when outputs match) witness
a collision. -/
lemma LogHasCollision.of_mem {log : QueryLog spec}
    {q1 q2 : (i : ι) × spec.Range i}
    (hne : q1 ≠ q2) (hm1 : q1 ∈ log) (hm2 : q2 ∈ log) (hresp : HEq q1.2 q2.2) :
    LogHasCollision log := by
  rcases List.mem_iff_getElem.mp hm1 with ⟨i, hi, hgi⟩
  rcases List.mem_iff_getElem.mp hm2 with ⟨j, hj, hgj⟩
  have hgi' : log[(⟨i, hi⟩ : Fin log.length)] = q1 := hgi
  have hgj' : log[(⟨j, hj⟩ : Fin log.length)] = q2 := hgj
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩, fun heq => hne (hgi' ▸ hgj' ▸ congrArg (log[·]) heq),
    fun h => hne (Sigma.ext (hgi' ▸ hgj' ▸ h) hresp), hgi' ▸ hgj' ▸ hresp⟩

omit [DecidableEq ι] in
/-- `LogHasCollision` is monotone under log inclusion (member-wise). -/
lemma LogHasCollision.mono {log₁ log₂ : QueryLog spec}
    (h_sub : ∀ q, q ∈ log₁ → q ∈ log₂) :
    LogHasCollision log₁ → LogHasCollision log₂ := by
  rintro ⟨i, j, hij, h_inp, h_out⟩
  exact .of_mem (fun h => h_inp (congrArg Sigma.fst h))
    (h_sub _ (List.getElem_mem _)) (h_sub _ (List.getElem_mem _)) h_out

/-- A cache has a collision: two distinct inputs map to the same output. -/
def CacheHasCollision (cache : QueryCache spec) : Prop :=
  ∃ (t₁ t₂ : spec.Domain) (u₁ : spec.Range t₁) (u₂ : spec.Range t₂),
    t₁ ≠ t₂ ∧ cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ HEq u₁ u₂

omit [DecidableEq ι] in
/-- In a collision-free cache, a value determines at most one query input. -/
lemma cache_lookup_eq_of_noCollision
    {cache : QueryCache spec}
    {t₀ t₁ : spec.Domain} {v : spec.Range t₀}
    (hno : ¬ CacheHasCollision cache)
    (h₀ : cache t₀ = some v)
    (h₁ : ∃ v' : spec.Range t₁, cache t₁ = some v' ∧ HEq v' v) :
    t₀ = t₁ := by
  grind [CacheHasCollision]

/-! ## Log entries are cached after logging inside caching -/

/-- Structural decomposition of the `query t >>= mx` step when running `loggingOracle` inside
`cachingOracle`: a result `z` of the whole computation arises by first caching the query value
`u` at `t` (yielding `cache_mid` with `cache_mid t = some u`, `cache₀ ≤ cache_mid`, and
`cache_mid` agreeing with `cache₀` away from `t`), then running the continuation `mx u` from
`cache_mid` to a state `zc`, with `z` obtained from `zc` by prepending the log entry `⟨t, u⟩`.
Shared `query_bind` skeleton for the induction in `log_entry_in_cache_and_mono` and
`cache_entry_in_log_or_initial`. -/
private lemma exists_cont_of_run_simulateQ_query_bind {α : Type}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α)
    (cache₀ : QueryCache spec) (z : (α × QueryLog spec) × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle
        ((simulateQ loggingOracle (liftM (query t) >>= mx)).run)).run cache₀)) :
    ∃ (u : spec.Range t) (cache_mid : QueryCache spec)
        (zc : (α × QueryLog spec) × QueryCache spec),
      cache₀ ≤ cache_mid ∧ cache_mid t = some u ∧
        (∀ t₀ : spec.Domain, t₀ ≠ t → cache_mid t₀ = cache₀ t₀) ∧
        zc ∈ support ((simulateQ cachingOracle
            ((simulateQ loggingOracle (mx u)).run)).run cache_mid) ∧
        z = ((zc.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zc.1.2), zc.2) := by
  rw [run_simulateQ_loggingOracle_query_bind] at hmem
  rw [show simulateQ cachingOracle
        ((query t : OracleComp spec _) >>= fun u =>
          (fun p : α × QueryLog spec =>
              (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) ::
                p.2))
            <$> (simulateQ loggingOracle (mx u)).run) =
        ((cachingOracle t >>= fun u =>
          simulateQ cachingOracle
            ((fun p : α × QueryLog spec =>
                (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) ::
                  p.2))
              <$> (simulateQ loggingOracle (mx u)).run)) :
          StateT (QueryCache spec) (OracleComp spec) _)
      from by simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.withCaching_apply, QueryImpl.ofLift_apply, map_bind,
        id_map, simulateQ_map, bind_assoc]] at hmem
  rw [show (cachingOracle t >>= fun u =>
          simulateQ cachingOracle
            ((fun p : α × QueryLog spec =>
                (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) ::
                  p.2))
              <$> (simulateQ loggingOracle (mx u)).run) :
          StateT (QueryCache spec) (OracleComp spec) _) =
        (cachingOracle t >>= fun u =>
          StateT.map
            (fun p : α × QueryLog spec =>
              (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) ::
                p.2))
            (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)))
      from by
        congr 1; ext u s
        simp only [StateT.map, StateT.run, map_eq_bind_pure_comp, simulateQ_bind,
          simulateQ_pure, Function.comp_def]
        rfl] at hmem
  rw [StateT.run_bind, support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
  obtain ⟨⟨u, cache_mid⟩, hu_mem, hmem⟩ := hmem
  change z ∈ support ((StateT.map
    (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
    (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid) at hmem
  rw [show (StateT.map
    (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
    (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))).run cache_mid =
    (fun zz : (α × QueryLog spec) × QueryCache spec =>
      ((zz.1.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: zz.1.2), zz.2)) <$>
    ((simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run)).run cache_mid)
    from by simp only [StateT.map, StateT.run, monad_norm,
      Function.comp_def]] at hmem
  rw [support_map] at hmem
  obtain ⟨zc, hmem_cont, heq⟩ := hmem
  have hne_eq : ∀ t₀ : spec.Domain, t₀ ≠ t → cache_mid t₀ = cache₀ t₀ := by
    intro t₀ hne
    cases hc : cache₀ t with
    | some w =>
      rw [cachingOracle.run_some hc, support_pure, Set.mem_singleton_iff] at hu_mem
      rw [(Prod.mk.inj hu_mem).2]
    | none =>
      rw [cachingOracle.run_none hc, support_map] at hu_mem
      obtain ⟨w, _, hw⟩ := hu_mem
      rw [← (Prod.mk.inj hw).2, QueryCache.cacheQuery_of_ne _ _ hne]
  exact ⟨u, cache_mid, zc,
    QueryImpl.withCaching_cache_le
      (QueryImpl.ofLift spec (OracleComp spec)) t cache₀ (u, cache_mid) hu_mem,
    cachingOracle_query_caches t cache₀ u cache_mid hu_mem, hne_eq, hmem_cont, heq.symm⟩

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
    exact ⟨by simp, le_refl _⟩
  | query_bind t mx ih =>
    obtain ⟨u, cache_mid, ⟨⟨x', log'⟩, cache_final⟩,
      hcache₀_le_mid, hcache_mid_entry, _, hmem_cont, rfl⟩ :=
      exists_cont_of_run_simulateQ_query_bind t mx cache₀ z hmem
    obtain ⟨ih_entries, ih_mono⟩ := ih u cache_mid ((x', log'), cache_final) hmem_cont
    exact ⟨fun entry hentry => by
      cases hentry with
      | head => exact ih_mono hcache_mid_entry
      | tail _ hentry' => exact ih_entries entry hentry',
      le_trans hcache₀_le_mid ih_mono⟩

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
    obtain ⟨u, cache_mid, ⟨⟨x', log'⟩, cache_final⟩,
      _, hcache_mid_entry, hcache_mid_eq, hmem_cont, rfl⟩ :=
      exists_cont_of_run_simulateQ_query_bind t mx cache₀ z hmem
    intro t₀ v hcache_final
    rcases ih u cache_mid ((x', log'), cache_final) hmem_cont t₀ v hcache_final with
      h_in_mid | ⟨entry, hentry, hentry_eq, hentry_heq⟩
    · by_cases ht₀ : t₀ = t
      · subst ht₀
        rw [hcache_mid_entry] at h_in_mid; cases h_in_mid
        exact Or.inr ⟨⟨t₀, _⟩, List.Mem.head _, rfl, HEq.rfl⟩
      · exact Or.inl (hcache_mid_eq t₀ ht₀ ▸ h_in_mid)
    · exact Or.inr ⟨entry, List.Mem.tail _ hentry, hentry_eq, hentry_heq⟩

end OracleComp
