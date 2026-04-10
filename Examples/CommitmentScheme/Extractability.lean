/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Common

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]
/-! ## 2. Extractability

**Textbook (Lemma cm-extractability)**: There exists a deterministic extractor E
such that for every `t`-query two-phase adversary A = (A_commit, A_open):
  Pr[Check^H(c,m,s) = 1 ∧ E(c, trace) ≠ (m,s)] ≤ ½ · t² / |C|

The extractor E scans the commit-phase query-answer trace for an entry
whose answer matches the commitment c. -/

/-- An extractability adversary with two phases. -/
structure ExtractAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- Commit phase: produces a commitment and auxiliary state (with oracle access). -/
  commit : OracleComp (CMOracle M S C) (C × AUX)
  /-- Open phase: given auxiliary state, produces an opening `(m, s)` (with oracle access). -/
  open_ : AUX → OracleComp (CMOracle M S C) (M × S)
  /-- Commit-phase query bound. -/
  t₁ : ℕ
  /-- Open-phase query bound. -/
  t₂ : ℕ
  /-- Total queries bounded by `t`. -/
  totalBound : t₁ + t₂ ≤ t
  /-- Query bound for the commit phase. -/
  commitBound : IsTotalQueryBound commit t₁
  /-- Query bound for the open phase. -/
  openBound : ∀ aux, IsTotalQueryBound (open_ aux) t₂

/-- The extractor: scan the query-answer trace for a pair whose answer matches `cm`. -/
def CMExtract (cm : C) (tr : QueryLog (CMOracle M S C)) : Option (M × S) :=
  match tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => some entry.1
  | none => none

/-- The extractability game in the random oracle model, parameterized by an extractor `E`.

Phase 1 (commit): Run `A.commit` with a logging oracle layered on top
  (to capture the trace), all within `cachingOracle`.
Phase 2 (open): Run `A.open_` with the same oracle (shared cache).
Verification: Query `H(m, s)` and compare to `cm`.
Extraction: Apply `E` to the commitment and commit-phase trace.

Win: Check passes AND (extractor found nothing OR found a different opening). -/
def extractabilityGame {AUX : Type} {t : ℕ}
    (E : C → QueryLog (CMOracle M S C) → Option (M × S))
    (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) (Bool × QueryCache (CMOracle M S C)) :=
  (simulateQ cachingOracle (do
    -- Phase 1: commit with logging to get trace
    let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
    -- Phase 2: open
    let (m, s) ← A.open_ aux
    -- Verify: query H(m,s) using the same oracle
    let c ← query (spec := CMOracle M S C) (m, s)
    -- Extract from the commit-phase trace
    let extracted := E cm tr
    return (match extracted with
      | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
      | none => (c == cm)))).run ∅

variable {AUX : Type}

/-- The inner oracle computation of the extractability game (before `simulateQ`). -/
private def extractabilityInner {AUX : Type} {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) Bool := do
  let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
  let (m, s) ← A.open_ aux
  let c ← query (spec := CMOracle M S C) (m, s)
  let extracted := CMExtract cm tr
  return (match extracted with
    | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
    | none => (c == cm))

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- The extractability game equals `simulateQ cachingOracle` on `extractabilityInner`. -/
private lemma extractabilityGame_eq {t : ℕ} (A : ExtractAdversary M S C AUX t) :
    extractabilityGame CMExtract A =
    (simulateQ cachingOracle (extractabilityInner A)).run ∅ := rfl

/-- Tagged inner computation: returns `(win, isNoneCase)` where `isNoneCase = true`
iff the extractor found no matching entry in the commit trace.

This decomposition allows separate handling of the two win cases:
- `some` case (`win ∧ ¬isNoneCase`): implies cache collision (pointwise)
- `none` case (`win ∧ isNoneCase`): requires probabilistic bound -/
private def extractabilityInner_tagged {AUX : Type} {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    OracleComp (CMOracle M S C) (Bool × Bool) := do
  let ((cm, aux), tr) ← (simulateQ loggingOracle A.commit).run
  let (m, s) ← A.open_ aux
  let c ← query (spec := CMOracle M S C) (m, s)
  let extracted := CMExtract cm tr
  return (match extracted with
    | some (m', s') => ((c == cm) && decide ((m', s') ≠ (m, s)), false)
    | none => ((c == cm), true))

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- The untagged inner computation is the first projection of the tagged one. -/
private lemma extractabilityInner_eq_fst_tagged {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    extractabilityInner A = Prod.fst <$> extractabilityInner_tagged A := by
  simp only [extractabilityInner, extractabilityInner_tagged, map_eq_bind_pure_comp,
    bind_assoc, Function.comp, pure_bind]
  congr 1; ext ⟨⟨cm, aux⟩, tr⟩
  congr 1; ext ⟨m, s⟩
  congr 1; ext c
  simp only [CMExtract]
  cases tr.find? (fun entry => decide (entry.2 = cm)) with
  | some entry => simp
  | none => simp

/- The some-case win (extractor found a different opening) implies cache collision.

When `CMExtract` finds an entry `(m', s')` in the commit trace with `H(m', s') = cm`,
and verification gives `H(m, s) = cm` with `(m', s') ≠ (m, s)`, both distinct inputs
map to `cm` in the final cache. -/
omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
private lemma extractability_someWin_implies_collision {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    ∀ z ∈ support ((simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅),
      z.1.1 = true → z.1.2 = false → CacheHasCollision z.2 := by
  intro z hz hwin hsome
  simp only [extractabilityInner_tagged, simulateQ_bind, simulateQ_pure] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨⟨cm, aux⟩, tr⟩, cache₁⟩, hmem₁, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨m, s⟩, cache₂⟩, hmem₂, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, cache₃⟩, hmem₃, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz] at hwin hsome ⊢
  -- cache₃ has entry at (m, s) with value c
  rw [cachingOracle.simulateQ_query] at hmem₃
  have hcache₃ : cache₃ (m, s) = some c :=
    cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
  -- Cache monotonicity: cache₂ ≤ cache₃
  have hcache_mono₂₃ : cache₂ ≤ cache₃ := by
    have hmem₃_co : (c, cache₃) ∈ support
        ((cachingOracle (spec := CMOracle M S C) (m, s)).run cache₂) := hmem₃
    unfold cachingOracle at hmem₃_co
    exact QueryImpl.withCaching_cache_le
      (QueryImpl.ofLift (CMOracle M S C) (OracleComp (CMOracle M S C)))
      (m, s) cache₂ (c, cache₃) hmem₃_co
  -- The tag tells us this is the some case
  unfold CMExtract at hwin hsome
  cases hfind : (tr.find? (fun entry => decide (entry.2 = cm))) with
  | none => simp [hfind] at hsome
  | some entry =>
    simp only [hfind] at hwin
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
    obtain ⟨hceq, hne⟩ := hwin
    -- entry.2 = cm by the find? predicate
    have hentry_cm : entry.2 = cm := by
      have hfound := List.find?_some hfind
      simp only [decide_eq_true_eq] at hfound
      exact hfound
    -- entry is in the log tr
    have hentry_mem : entry ∈ tr := List.mem_of_find?_eq_some hfind
    -- Log entries are in cache₁ (via log_entry_in_cache_and_mono)
    have hlog_cache := (OracleComp.log_entry_in_cache_and_mono A.commit ∅
      (((cm, aux), tr), cache₁) hmem₁).1
    have hcache₁_entry : cache₁ entry.1 = some entry.2 :=
      hlog_cache entry hentry_mem
    -- cache₁ ≤ cache₂ (simulateQ cachingOracle on open_ only grows cache)
    have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
      simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
    -- cache₃ entry.1 = some entry.2 (by monotonicity chain cache₁ ≤ cache₂ ≤ cache₃)
    have hcache₃_entry : cache₃ entry.1 = some entry.2 :=
      hcache_mono₂₃ (hcache_mono₁₂ hcache₁_entry)
    -- Collision: entry.1 and (m,s) both map to cm in cache₃
    exact ⟨entry.1, (m, s), entry.2, c, hne, hcache₃_entry, hcache₃,
      heq_of_eq (by rw [hentry_cm, hceq])⟩

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] in
/-- `IsTotalQueryBound` for the extractability game's inner computation.

The inner computation consists of:
1. `(simulateQ loggingOracle A.commit).run` — `t₁` queries (loggingOracle passes through)
2. `A.open_ aux` — `t₂` queries
3. `query (m, s)` — 1 verification query

Total: `t₁ + t₂ + 1 ≤ t + 1`.

The proof uses `isTotalQueryBound_run_simulateQ_loggingOracle_iff` (logging preserves
query bounds) and `isTotalQueryBound_bind` (composition through dependent bind). -/
private lemma extractabilityInner_totalBound [Finite C] {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    IsTotalQueryBound (extractabilityInner A) (t + 1) := by
  haveI : Fintype C := Fintype.ofFinite C
  -- extractabilityInner A =
  --   (simulateQ loggingOracle A.commit).run >>= fun ((cm, aux), tr) =>
  --     A.open_ aux >>= fun (m, s) =>
  --       query (m, s) >>= fun c => pure (...)
  -- Query budget: t₁ (commit) + t₂ (open) + 1 (verify) ≤ t + 1
  -- Step 1: (simulateQ loggingOracle A.commit).run has bound t₁
  have h1 : IsTotalQueryBound ((simulateQ loggingOracle A.commit).run) A.t₁ :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff A.commit A.t₁).mpr A.commitBound
  -- Step 2: A.open_ aux has bound t₂ for all aux
  -- Step 3: query (m, s) >>= pure (...) has bound 1
  -- Combine via isTotalQueryBound_bind
  have hbind :
      IsTotalQueryBound
        (((simulateQ loggingOracle A.commit).run) >>= fun
          | ((cm, aux), tr) =>
              A.open_ aux >>= fun (m, s) =>
                query (spec := CMOracle M S C) (m, s) >>= fun c =>
                  have extracted : Option (M × S) := CMExtract cm tr
                  pure
                    (match extracted with
                    | some (m', s') => c == cm && decide ((m', s') ≠ (m, s))
                    | none => c == cm))
        (A.t₁ + (A.t₂ + 1)) := by
    apply isTotalQueryBound_bind h1
    intro ⟨⟨cm, aux⟩, tr⟩
    apply isTotalQueryBound_bind (A.openBound aux)
    intro ⟨m, s⟩
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  exact hbind.mono (by
    have := A.totalBound
    omega)

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] in
/-- The tagged inner computation has the same query bound as the untagged one. -/
private lemma extractabilityInner_tagged_totalBound [Finite C] {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    IsTotalQueryBound (extractabilityInner_tagged A) (t + 1) := by
  haveI : Fintype C := Fintype.ofFinite C
  have h := extractabilityInner_totalBound A
  rw [extractabilityInner_eq_fst_tagged] at h
  rwa [show IsTotalQueryBound (Prod.fst <$> extractabilityInner_tagged A) (t + 1) ↔
    IsTotalQueryBound (extractabilityInner_tagged A) (t + 1) from
    isQueryBound_map_iff _ _ _ _ _] at h

/- The some-case win event on the tagged game implies cache collision.

Wraps `extractability_someWin_implies_collision` for use with `probEvent_mono`. -/
omit [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
private lemma extractability_someWin_le_collision {t : ℕ}
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1.1 = true ∧ z.1.2 = false |
      (simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅] ≤
    Pr[fun z => CacheHasCollision z.2 |
      (simulateQ cachingOracle (extractabilityInner_tagged A)).run ∅] :=
  probEvent_mono fun z hz ⟨hwin, hsome⟩ =>
    extractability_someWin_implies_collision A z hz hwin hsome

/-- Textbook arithmetic: if `t₁ + t₂ ≤ t` and `t ≥ 3`, then
`t₁(t₁-1) + 2t₂ ≤ t(t-1)`. -/
private lemma extractability_num_le
    {t t₁ t₂ : ℕ} (ht : 3 ≤ t) (hbound : t₁ + t₂ ≤ t) :
    t₁ * (t₁ - 1) + 2 * t₂ ≤ t * (t - 1) := by
  have ht₁_le : t₁ ≤ t := by omega
  have ht₂_le : t₂ ≤ t - t₁ := Nat.le_sub_of_add_le' hbound
  have htwo : 2 ≤ t - 1 := by omega
  calc
    t₁ * (t₁ - 1) + 2 * t₂ ≤ t₁ * (t₁ - 1) + 2 * (t - t₁) := by
      gcongr
    _ ≤ t₁ * (t - 1) + (t - 1) * (t - t₁) := by
      apply add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ht₁_le 1)
      · simpa [Nat.mul_comm] using Nat.mul_le_mul_right (t - t₁) htwo
    _ = t * (t - 1) := by
      rw [Nat.mul_comm (t - 1) (t - t₁), ← Nat.add_mul, Nat.add_sub_of_le ht₁_le]

/-- The post-commit/open extractability computation for a fixed commit outcome. -/
private def extractabilityRestOa {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    (cm : C) (aux : AUX) (tr : QueryLog (CMOracle M S C)) :
    OracleComp (CMOracle M S C) Bool :=
  A.open_ aux >>= fun (m, s) =>
    (liftM (query (spec := CMOracle M S C) (m, s))) >>= fun c =>
    let extracted := CMExtract cm tr
    pure (match extracted with
      | some (m', s') => (c == cm) && decide ((m', s') ≠ (m, s))
      | none => (c == cm))

set_option maxHeartbeats 400000 in
/- Under a collision-free commit cache, any extractability win must create a fresh
post-commit cache entry equal to the commitment value. -/
omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
private lemma extractability_rest_win_implies_fresh_cm {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    {cm : C} {aux : AUX} {tr : QueryLog (CMOracle M S C)}
    {cache₁ : QueryCache (CMOracle M S C)}
    (hx : (((cm, aux), tr), cache₁) ∈
      support ((simulateQ cachingOracle ((simulateQ loggingOracle A.commit).run)).run ∅))
    (hno : ¬ CacheHasCollision cache₁) :
  ∀ z ∈ support ((simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁),
      z.1 = true →
      ∃ t₀ : (CMOracle M S C).Domain, ∃ v : (CMOracle M S C).Range t₀,
        z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v cm := by
  intro z hz hwin
  unfold extractabilityRestOa at hz
  rw [simulateQ_bind] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨m, s⟩, cache₂⟩, hmem₂, hz⟩ := hz
  rw [simulateQ_bind] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, cache₃⟩, hmem₃, hz⟩ := hz
  rw [hz] at hwin
  unfold CMExtract at hwin
  cases hfind : tr.find? (fun entry => decide (entry.2 = cm)) with
  | none =>
      simp only [hfind, beq_iff_eq] at hwin
      have hc_eq : c = cm := hwin
      rw [cachingOracle.simulateQ_query] at hmem₃
      have hcache₃ : cache₃ (m, s) = some c :=
        cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
      have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
        simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
      have hcache₁_none : cache₁ (m, s) = none := by
        by_contra h
        push_neg at h
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
        have hno_cm : ∀ (t₀ : (CMOracle M S C).Domain) (v' : (CMOracle M S C).Range t₀),
            cache₁ t₀ = some v' → ¬HEq v' cm := by
          intro t₀ v' hcache₁ hheq
          have hlog := cache_entry_in_log_or_initial A.commit ∅
            (((cm, aux), tr), cache₁) hx
          have h' := hlog t₀ v' hcache₁
          rcases h' with h_empty | ⟨entry, hentry_mem, _, hentry_heq⟩
          · exact absurd h_empty (by simp)
          · have hentry_cm : entry.2 = cm := eq_of_heq (hentry_heq.trans hheq)
            have hfound : (tr.find? (fun e => decide (e.2 = cm))).isSome = true := by
              rw [List.find?_isSome]
              exact ⟨entry, hentry_mem, by simp [hentry_cm]⟩
            simp [hfind] at hfound
        have hcache₂_ms := hcache_mono₁₂ hv
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get,
          pure_bind, hcache₂_ms, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem₃
        have hcv : c = v := (Prod.mk.inj hmem₃).1
        exact hno_cm (m, s) v hv (heq_of_eq (hcv ▸ hc_eq))
      have hcache_final_eq : z.2 = cache₃ := congr_arg (·.2) hz
      rw [hcache_final_eq]
      exact ⟨(m, s), c, hcache₃, hcache₁_none, heq_of_eq hc_eq⟩
  | some entry =>
      simp only [hfind, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
      obtain ⟨hc_eq, hne⟩ := hwin
      rw [cachingOracle.simulateQ_query] at hmem₃
      have hcache₃ : cache₃ (m, s) = some c :=
        cachingOracle_query_caches (m, s) cache₂ c cache₃ hmem₃
      have hcache_mono₁₂ : cache₁ ≤ cache₂ :=
        simulateQ_cachingOracle_cache_le (A.open_ aux) cache₁ _ hmem₂
      have hentry_cm : entry.2 = cm := by
        have hfound := List.find?_some hfind
        simpa only [decide_eq_true_eq] using hfound
      have hentry_mem : entry ∈ tr := List.mem_of_find?_eq_some hfind
      have hlog_cache := (OracleComp.log_entry_in_cache_and_mono A.commit ∅
        (((cm, aux), tr), cache₁) hx).1
      have hcache₁_entry : cache₁ entry.1 = some entry.2 :=
        hlog_cache entry hentry_mem
      have hcache₁_none : cache₁ (m, s) = none := by
        by_contra h
        push_neg at h
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
        have hcache₂_ms := hcache_mono₁₂ hv
        simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get,
          pure_bind, hcache₂_ms, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem₃
        have hcv : c = v := (Prod.mk.inj hmem₃).1
        have hv_entry : v = entry.2 := by
          rw [← hcv, hc_eq, ← hentry_cm]
        have hcache₁_ms : cache₁ (m, s) = some entry.2 := by
          simpa [hv_entry] using hv
        have hsame : entry.1 = (m, s) :=
          cache_lookup_eq_of_noCollision hno hcache₁_entry
            ⟨entry.2, hcache₁_ms, HEq.rfl⟩
        exact hne hsame
      have hcache_final_eq : z.2 = cache₃ := congr_arg (·.2) hz
      rw [hcache_final_eq]
      exact ⟨(m, s), c, hcache₃, hcache₁_none, heq_of_eq hc_eq⟩

/- Winning the extractability rest-game implies a fresh cache entry matching `cm`. -/
omit [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
private lemma extractability_rest_win_le_exists_fresh {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    (cm : C) (aux : AUX) (tr : QueryLog (CMOracle M S C))
    (cache₁ : QueryCache (CMOracle M S C))
    (hx : (((cm, aux), tr), cache₁) ∈
      support ((simulateQ cachingOracle ((simulateQ loggingOracle A.commit).run)).run ∅))
    (hno : ¬ CacheHasCollision cache₁) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁] ≤
    Pr[fun z => ∃ t₀ : (CMOracle M S C).Domain, ∃ v : (CMOracle M S C).Range t₀,
          z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v cm |
        (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁] :=
  probEvent_mono fun z hz hwin =>
    extractability_rest_win_implies_fresh_cm A hx hno z hz hwin

/- Conditioned on a collision-free commit trace, the later extractability failure
probability is bounded by the fresh-hit term `(t₂ + 1) / |C|`. -/
omit [Fintype M] [Fintype S] in
private lemma extractability_rest_noCollision_le_inv {t : ℕ}
    (A : ExtractAdversary M S C AUX t)
    (cm : C) (aux : AUX) (tr : QueryLog (CMOracle M S C))
    (cache₁ : QueryCache (CMOracle M S C))
    (hx : (((cm, aux), tr), cache₁) ∈
      support ((simulateQ cachingOracle ((simulateQ loggingOracle A.commit).run)).run ∅))
    (hno : ¬ CacheHasCollision cache₁) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁] ≤
      (↑(A.t₂ + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
  have hrest_bound : IsTotalQueryBound
      (extractabilityRestOa A cm aux tr) (A.t₂ + 1) := by
    apply isTotalQueryBound_bind (A.openBound aux)
    intro ⟨m, s⟩
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  calc
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁]
      ≤ Pr[fun z => ∃ t₀ : (CMOracle M S C).Domain, ∃ v : (CMOracle M S C).Range t₀,
            z.2 t₀ = some v ∧ cache₁ t₀ = none ∧ HEq v cm |
          (simulateQ cachingOracle (extractabilityRestOa A cm aux tr)).run cache₁] :=
          extractability_rest_win_le_exists_fresh A cm aux tr cache₁ hx hno
    _ ≤ (↑(A.t₂ + 1) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ :=
      OracleComp.probEvent_cache_has_value_le_of_noCollision
        (oa := extractabilityRestOa A cm aux tr)
        (n := A.t₂ + 1) hrest_bound (fun _ => le_refl _)
        cm cache₁ hno

/- The extraction error decomposes into collision in commit trace plus fresh query
matching `cm`. The commit trace has `≤ t₁` entries (birthday bound `t₁(t₁-1)/(2|C|)`),
and the open+verify phase has `≤ t₂+1` fresh queries matching `cm` (`(t₂+1)/|C|`).
Maximizing `t₁(t₁-1)/2 + t₂ + 1` over `t₁+t₂ ≤ t` gives `max{t+1, t(t-1)/2+1}`.
For `t ≥ 3` this is `t(t-1)/2+1`, yielding `(t(t-1)+2)/(2|C|)`. -/
omit [Fintype M] [Fintype S] in
private lemma extractability_win_le_textbook_bound {t : ℕ} (ht : 3 ≤ t)
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1 = true | extractabilityGame CMExtract A] ≤
    ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
    (Fintype.card C : ℝ≥0∞)⁻¹ := by
  let commitPart := (simulateQ loggingOracle A.commit).run
  let restPart := fun (x : (C × AUX) × QueryLog (CMOracle M S C)) =>
    let ((cm, aux), tr) := x
    extractabilityRestOa A cm aux tr
  have hdecomp : extractabilityInner A = commitPart >>= restPart := by
    simp [extractabilityInner, commitPart, restPart, extractabilityRestOa]
  have hcommit_bound : IsTotalQueryBound commitPart A.t₁ :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff A.commit A.t₁).mpr A.commitBound
  have hmain :
      Pr[fun z => z.1 = true |
        (simulateQ cachingOracle commitPart).run ∅ >>= fun x =>
          (simulateQ cachingOracle (restPart x.1)).run x.2] ≤
        ((A.t₁ * (A.t₁ - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
        ((A.t₂ + 1 : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
    simpa [not_not] using
      (probEvent_bind_le_add
        (mx := (simulateQ cachingOracle commitPart).run ∅)
        (my := fun x => (simulateQ cachingOracle (restPart x.1)).run x.2)
        (p := fun x => ¬ CacheHasCollision x.2)
        (q := fun z => z.1 ≠ true)
        (ε₁ := ((A.t₁ * (A.t₁ - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C))
        (ε₂ := ((A.t₂ + 1 : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹)
        (by
          simpa using
            (probEvent_cacheCollision_le_birthday_total_tight commitPart A.t₁
              hcommit_bound Fintype.card_pos (fun _ => le_refl _)))
        (by
          rintro ⟨⟨⟨cm, aux⟩, tr⟩, cache₁⟩ hx hno
          simpa [restPart, extractabilityRestOa] using
            extractability_rest_noCollision_le_inv A cm aux tr cache₁ hx hno))
  rw [extractabilityGame_eq, hdecomp, simulateQ_bind, StateT.run_bind]
  calc
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle commitPart).run ∅ >>= fun x =>
        (simulateQ cachingOracle (restPart x.1)).run x.2]
      ≤ ((A.t₁ * (A.t₁ - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
          ((A.t₂ + 1 : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := hmain
    _ = ((A.t₁ * (A.t₁ - 1) + 2 * (A.t₂ + 1) : ℕ) : ℝ≥0∞) /
          (2 * Fintype.card C) := by
          simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            add_div_two_mul_nat (A.t₁ * (A.t₁ - 1)) (A.t₂ + 1) (Fintype.card C)
    _ ≤ ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
          have hnat :
              A.t₁ * (A.t₁ - 1) + 2 * (A.t₂ + 1) ≤ t * (t - 1) + 2 := by
            simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              Nat.add_le_add_right (extractability_num_le ht A.totalBound) 2
          gcongr
    _ = ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
          (Fintype.card C : ℝ≥0∞)⁻¹ := by
          symm
          simpa [Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            add_div_two_mul_nat (t * (t - 1)) 1 (Fintype.card C)

/- **Extractability theorem (Lemma cm-extractability)**: for `t ≥ 3`,
`Pr[win] ≤ (t(t-1)+2) / (2|C|)`. Combines the case-split decomposition
`extractability_win_le_textbook_bound` with arithmetic. -/
omit [Fintype M] [Fintype S] in
theorem extractability_bound {t : ℕ} (ht : 3 ≤ t)
    (A : ExtractAdversary M S C AUX t) :
    Pr[fun z => z.1 = true | extractabilityGame CMExtract A] ≤
    ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
  calc Pr[fun z => z.1 = true | extractabilityGame CMExtract A]
      ≤ ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
        (Fintype.card C : ℝ≥0∞)⁻¹ := extractability_win_le_textbook_bound ht A
    _ = ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
        have h := add_div_two_mul_nat (t * (t - 1)) 1 (Fintype.card C)
        simp only [Nat.cast_one, one_mul, Nat.mul_one] at h
        exact h
