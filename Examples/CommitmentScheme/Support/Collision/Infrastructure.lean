/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import Examples.CommitmentScheme.Support.QueryBound
import VCVio.OracleComp.EvalDist

/-!
# ROM Collision Infrastructure

Collision predicates, Gauss sum arithmetic, logging oracle decomposition,
query bound preservation through `loggingOracle`, and cache monotonicity lemmas.

## TODO: upstream candidates

- `gauss_sum_inv_le`, `gauss_sum_inv_eq` → `VCVio/ToMathlib/` or `VCVio/Prelude/`
- `IsTotalQueryBound.of_perIndex` → `VCVio/OracleComp/QueryTracking/`
- `isTotalQueryBound_run_simulateQ_loggingOracle_iff` → `VCVio/OracleComp/QueryTracking/`
- `log_length_le_of_mem_support_run_simulateQ` → `VCVio/OracleComp/QueryTracking/`
- `simulateQ_cachingOracle_cache_le` → `VCVio/OracleComp/QueryTracking/`
-/

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0,0} ι}
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

/-! ## Gauss Sum Arithmetic -/

-- 1+2+...+(n-1) = n*(n-1)/2
/-- The Gauss sum `∑_{k=0}^{n-1} k/N ≤ n²/(2N)`, the arithmetic core of the birthday bound. -/
lemma gauss_sum_inv_le (n : ℕ) (N : ℝ≥0∞) (_hN : 0 < N) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ ≤
      (n ^ 2 : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  -- Key inequality in ℕ: 2 * ∑_{k<n} k = n*(n-1) ≤ n^2
  have hnat : 2 * (∑ k ∈ range n, k) ≤ n ^ 2 := by
    have := Finset.sum_range_id_mul_two n; nlinarith [Nat.sub_le n 1]
  -- Lift to ENNReal
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num,
      show (n : ℝ≥0∞) ^ 2 = ((n ^ 2 : ℕ) : ℝ≥0∞) from by push_cast; ring,
      ← Nat.cast_mul]
    exact_mod_cast hnat
  -- From 2 * sum ≤ n^2, derive sum ≤ n^2 / 2
  have hle : (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
    rwa [mul_comm]
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      ≤ ((n : ℝ≥0∞) ^ 2 / 2) * N⁻¹ := mul_le_mul_left hle N⁻¹
    _ = (n : ℝ≥0∞) ^ 2 / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

/-- Tight Gauss sum: `∑_{k=0}^{n-1} k/N ≤ n*(n-1)/(2N)`. -/
lemma gauss_sum_inv_eq (n : ℕ) (N : ℝ≥0∞) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ =
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  have hnat : (∑ k ∈ range n, k) * 2 = n * (n - 1) :=
    Finset.sum_range_id_mul_two n
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
    congr 1; omega
  have heq : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 := by
    rw [ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    exact henn
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 * N⁻¹ := by rw [heq]
    _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

/-- Updating one index and summing gives sum minus one. -/
/-- Per-index bound implies total bound (sum over indices). -/
theorem IsTotalQueryBound.of_perIndex [Fintype ι] {α : Type}
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => exact trivial
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    rw [isTotalQueryBound_query_bind_iff]
    have hpos : 0 < ∑ i, qb i :=
      Nat.lt_of_lt_of_le h.1 (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))
    refine ⟨hpos, fun u => ?_⟩
    rw [← sum_update_pred h.1]
    exact ih u (h.2 u)

/-! ## Logging Oracle Run Decomposition -/

/-- When running `loggingOracle` on `query t >>= mx`, the result decomposes as:
a uniform draw `u` from `Range t`, followed by prepending `⟨t, u⟩` to the sub-log. -/
lemma run_simulateQ_loggingOracle_query_bind {α : Type}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp spec _) >>= fun u =>
        (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def, Function.comp]

/-! ## IsTotalQueryBound preservation through loggingOracle -/

/-- `loggingOracle` preserves `IsTotalQueryBound`: the query structure of
`(simulateQ loggingOracle oa).run` is identical to that of `oa` (each query passes through
unchanged, with only the WriterT log being appended).

Proof by structural induction on `oa`. The pure case is trivial; the query_bind case
uses `run_simulateQ_loggingOracle_query_bind` to decompose, then `isQueryBound_map_iff`
to strip the log-prepend map, and finally the inductive hypothesis. -/
theorem isTotalQueryBound_run_simulateQ_loggingOracle_iff {α : Type}
    (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ loggingOracle oa).run) n ↔
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
    constructor <;> intro _ <;> trivial
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    rw [isTotalQueryBound_query_bind_iff, isTotalQueryBound_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun u =>
      (isQueryBound_map_iff _ _ _ _ _).trans (ih u (n - 1))

/-- A total query bound controls the length of every `loggingOracle` trace in support:
if `oa` makes at most `n` queries, then every support point of
`(simulateQ loggingOracle oa).run` has log length at most `n`. -/
theorem log_length_le_of_mem_support_run_simulateQ {α : Type}
    {oa : OracleComp spec α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    {z : α × QueryLog spec}
    (hz : z ∈ support ((simulateQ loggingOracle oa).run)) :
    z.2.length ≤ n := by
  suffices h : ∀ (β : Type) (ob : OracleComp spec β) (m : ℕ),
      IsTotalQueryBound ob m → ∀ z ∈ support ((simulateQ loggingOracle ob).run),
      z.2.length ≤ m from
    h α oa n hbound z hz
  intro β ob m hm
  induction ob using OracleComp.inductionOn generalizing m with
  | pure x =>
      intro z hz
      simp [simulateQ_pure] at hz
      subst hz
      simp
  | query_bind t mx ih =>
      intro z hz
      rw [isTotalQueryBound_query_bind_iff] at hm
      obtain ⟨hpos, hrest⟩ := hm
      simp only [simulateQ_bind, simulateQ_query] at hz
      rw [show ((query t).cont <$> loggingOracle (query t).input >>=
        fun x => simulateQ loggingOracle (mx x) :
        WriterT (QueryLog spec) (OracleComp spec) β).run =
        ((query t).cont <$> loggingOracle (query t).input).run >>=
        fun p => Prod.map id (p.2 ++ ·) <$>
          (simulateQ loggingOracle (mx p.1)).run
        from WriterT.run_bind' _ _] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hqu_log : qu.2.length = 1 := by
        simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query] at hqu
        have hrun : (loggingOracle (spec := spec) t).run =
            (query t : OracleComp spec _) >>= fun u =>
              pure (u, [⟨t, u⟩]) := by
          simp [loggingOracle, QueryImpl.withLogging_apply,
            WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
            map_pure, Prod.map]
        rw [hrun] at hqu
        simp only [support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff] at hqu
        obtain ⟨u, _, rfl⟩ := hqu
        simp
      have hz'_len : z'.2.length ≤ m - 1 :=
        ih qu.1 (m - 1) (hrest qu.1) z' hz'
      have hm : 1 + (m - 1) = m := by omega
      simpa [List.length_append, hqu_log, hm] using Nat.add_le_add_left hz'_len 1

/-! ## Log entries are cached after logging inside caching -/

/-- When running `loggingOracle` inside `cachingOracle`, every log entry ends up in the cache.

We prove two properties simultaneously by induction:
1. Every log entry is in the final cache.
2. The initial cache is a subset of the final cache (monotonicity).

The proof works by induction on `oa`. The `pure` case is trivial (empty log).
For `query t >>= mx`: the logging oracle decomposes as `query t >>= fun u => map (prepend ⟨t,u⟩) ...`,
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
    -- (simulateQ cachingOracle (pure (a, []))).run cache₀ = pure ((a, []), cache₀)
    change z ∈ support (pure ((a, ([] : QueryLog spec)), cache₀)) at hmem
    rw [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨fun _ h => ?_, le_refl _⟩; simp at h
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at hmem
    -- After logging decomposition, the inner computation is:
    --   query t >>= fun u => (fun p => (p.1, ⟨t,u⟩ :: p.2)) <$> (sim loggingOracle (mx u)).run
    -- simulateQ cachingOracle on (query t >>= ...) unfolds via simulateQ_query_bind
    rw [show simulateQ cachingOracle
          ((query t : OracleComp spec _) >>= fun u =>
            (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              <$> (simulateQ loggingOracle (mx u)).run) =
          ((cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) :
            StateT (QueryCache spec) (OracleComp spec) _)
        from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query]] at hmem
    -- simulateQ cachingOracle (f <$> oa) = f <$> simulateQ cachingOracle oa
    -- Rewrite inside the bind: simulateQ cachingOracle (f <$> oa) = StateT.map f (simulateQ cachingOracle oa)
    have hbind_rw : (cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run) :
            StateT (QueryCache spec) (OracleComp spec) _) =
          (cachingOracle t >>= fun u =>
            StateT.map
              (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
      congr 1; ext u s
      simp only [StateT.map, StateT.run, StateT.bind, map_eq_bind_pure_comp,
        simulateQ_bind, simulateQ_pure, Function.comp_def, bind_assoc, pure_bind]
      rfl
    rw [hbind_rw] at hmem
    rw [StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hu_mem, hmem⟩ := hmem
    -- Prove cache_mid has entry at t and cache₀ ≤ cache_mid
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
        simp only [hc, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet] at hu_mem
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
    -- Continuation: StateT.run of (f <$> simulateQ cachingOracle ...) at cache_mid
    -- This maps the result to prepend ⟨t, u⟩ to the log
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
    have hz : z = ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'), cache_final) := heq.symm
    rw [hz]
    -- Apply IH to get properties of log' and cache_final
    have ⟨ih_entries, ih_mono⟩ := ih u cache_mid ((x', log'), cache_final) hmem_cont
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
    rw [run_simulateQ_loggingOracle_query_bind] at hmem
    rw [show simulateQ cachingOracle
          ((query t : OracleComp spec _) >>= fun u =>
            (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              <$> (simulateQ loggingOracle (mx u)).run) =
          ((cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run)) :
            StateT (QueryCache spec) (OracleComp spec) _)
        from by simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query]] at hmem
    have hbind_rw : (cachingOracle t >>= fun u =>
            simulateQ cachingOracle
              ((fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
                <$> (simulateQ loggingOracle (mx u)).run) :
            StateT (QueryCache spec) (OracleComp spec) _) =
          (cachingOracle t >>= fun u =>
            StateT.map
              (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
              (simulateQ cachingOracle ((simulateQ loggingOracle (mx u)).run))) := by
      congr 1; ext u s
      simp only [StateT.map, StateT.run, StateT.bind, map_eq_bind_pure_comp,
        simulateQ_bind, simulateQ_pure, Function.comp_def, bind_assoc, pure_bind]
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
        simp only [hc, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet] at hu_mem
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
    -- Continuation
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
    have hz : z = ((x', (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: log'), cache_final) := heq.symm
    rw [hz]
    -- We need: cache_mid t₀ = cache₀ t₀ for t₀ ≠ t
    -- cachingOracle at t only modifies cache at index t: either cache_mid = cache₀ (hit)
    -- or cache_mid = cache₀.cacheQuery t u (miss). In both cases, unchanged at t₀ ≠ t.
    have hcache_mid_eq : ∀ t₀ : spec.Domain, t₀ ≠ t → cache_mid t₀ = cache₀ t₀ := by
      intro t₀ hne
      -- Derive: cache_mid = cache₀ or cache_mid = cache₀.cacheQuery t u
      have hu_mem' : (u, cache_mid) ∈ support ((cachingOracle (spec := spec) t).run cache₀) := by
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem ⊢
        exact hu_mem
      simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hu_mem'
      cases hc : cache₀ t with
      | some w =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu_mem'
        have := (Prod.mk.inj hu_mem').2; rw [this]
      | none =>
        -- In the miss case, cachingOracle draws a fresh value and caches it.
        -- The resulting cache is cache₀.cacheQuery t (fresh value).
        -- After the simp, hu_mem' has the form involving modifyGet.
        -- We use QueryImpl.withCaching_cache_le and the cacheQuery structure.
        -- cache_mid ≤ cache₀.cacheQuery t u because the only modification is at t
        -- Actually, let's just derive from withCaching behavior:
        -- (u, cache_mid) is in support of (withCaching (ofLift ...) t).run cache₀
        -- In the none case, cache_mid = cache₀.cacheQuery t u
        -- We know cache₀ t = none, so cacheQuery only adds at t
        simp only [hc, StateT.run_bind] at hu_mem'
        -- After simp, hu_mem' involves the lift/modifyGet pattern
        -- Use: cache_mid t₀ = cache₀ t₀ because cacheQuery only modifies at t
        -- Direct approach: show cache_mid = cache₀.cacheQuery t u
        -- from the support membership, then use cacheQuery_of_ne
        -- hu_mem' is now in the miss case. Extract cache_mid structure.
        -- The do block is definitionally equal to a bind.
        change (u, cache_mid) ∈ support
          ((liftM (query t) : StateT _ (OracleComp spec) _).run cache₀ >>= fun p =>
            ((modifyGet fun cache => (p.1, QueryCache.cacheQuery cache t p.1) :
              StateT (QueryCache spec) (OracleComp spec) _).run p.2)) at hu_mem'
        rw [support_bind] at hu_mem'; simp only [Set.mem_iUnion] at hu_mem'
        obtain ⟨⟨r, s⟩, hrs, hfinal⟩ := hu_mem'
        simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hfinal
        have hru : u = r := congr_arg Prod.fst hfinal
        have hcm : cache_mid = s.cacheQuery t r := congr_arg Prod.snd hfinal
        -- s comes from (liftM (query t)).run cache₀, so s = cache₀
        simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
          StateT.run, StateT.lift] at hrs
        rw [support_bind] at hrs; simp only [Set.mem_iUnion] at hrs
        obtain ⟨q, _, hq⟩ := hrs
        rw [support_pure, Set.mem_singleton_iff] at hq
        have hs : s = cache₀ := congr_arg Prod.snd hq
        rw [hcm, hs, QueryCache.cacheQuery_of_ne _ _ hne]
    intro t₀ v hcache_final
    -- Apply IH
    have ih_result := ih u cache_mid ((x', log'), cache_final) hmem_cont t₀ v hcache_final
    rcases ih_result with h_in_mid | ⟨entry, hentry, hentry_eq, hentry_heq⟩
    · -- v was in cache_mid. Was it in cache₀?
      by_cases ht₀ : t₀ = t
      · -- cache_mid t = some u, and cache_mid t₀ = some v with t₀ = t, so v = u
        subst ht₀
        rw [hcache_mid_entry] at h_in_mid; cases h_in_mid
        -- The log entry ⟨t₀, v⟩ is at the head (t₀ = t, v = u)
        exact Or.inr ⟨⟨t₀, _⟩, List.Mem.head _, rfl, HEq.rfl⟩
      · -- t₀ ≠ t: cache_mid t₀ = cache₀ t₀
        rw [hcache_mid_eq t₀ ht₀] at h_in_mid
        exact Or.inl h_in_mid
    · exact Or.inr ⟨entry, List.Mem.tail _ hentry, hentry_eq, hentry_heq⟩

/-- `simulateQ cachingOracle` only grows the cache: for any `oa`, if
`z ∈ support ((simulateQ cachingOracle oa).run cache₀)` then `cache₀ ≤ z.2`. -/
theorem simulateQ_cachingOracle_cache_le {α : Type}
    (oa : OracleComp spec α) (cache₀ : QueryCache spec)
    (z : α × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle oa).run cache₀)) :
    cache₀ ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
    simp [simulateQ_pure, StateT.run] at hmem
    rw [hmem]
  | query_bind t mx ih =>
    simp only [simulateQ_query_bind, StateT.run_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨u, cache_mid⟩, hmid, hrest⟩ := hmem
    have hle_mid : cache₀ ≤ cache_mid := by
      -- The first step is (liftM (cachingOracle t)).run cache₀
      -- which is cachingOracle applied at t — cache only grows
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.run_bind, StateT.run_get, pure_bind] at hmid
      unfold cachingOracle at hmid
      exact QueryImpl.withCaching_cache_le _ _ cache₀ _ hmid
    exact le_trans hle_mid (ih _ cache_mid z hrest)

end OracleComp
