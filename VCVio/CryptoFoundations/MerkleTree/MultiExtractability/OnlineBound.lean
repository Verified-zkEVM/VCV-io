/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Potential
import VCVio.OracleComp.QueryTracking.Collision
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# Predictable Online-Target Bound

This module proves the single-phase stopping-time estimate needed by stateful Merkle extraction.
During an adaptive phase, the caller supplies a finite target set computed from the phase's fixed
control state and the log *before* the next fresh random-oracle response is sampled. The fixed
control state is captured by the target closure; a phase-ending terminal theorem may record a new
checkpoint and recursively start the next phase. A miss is pessimistically declared bad when it
either creates a cache collision or lands in that predictable set. Cached queries consume syntax
budget but create no new random sample and therefore incur no local bad-event charge.

The caller also supplies a good-state invariant. It is propagated only through cache hits and
fresh noncollision/non-target misses, and is handed to the terminal theorem. This is what permits
an outer induction over sequential checkpoint phases without forgetting that no earlier online
hit occurred. The organization is deliberately stronger than proving only a final-log target
bound: future targets may depend on the response currently being sampled, so using them at the
current step would be circular.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Query Y X R C : Type}

/-- Run a prefix with an explicit phase-local query log, then choose a proof-only accounting
continuation from its output and the resulting cumulative log.  This computation is used only for
query accounting; the executable stopping theorem continues to run `adaptivePrefixRunFrom`. -/
def loggedAccountingBind
    (prefixComp : OracleComp (Query →ₒ Y) X)
    (initialLog : (Query →ₒ Y).QueryLog)
    (continuation : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C) :
    OracleComp (Query →ₒ Y) C :=
  prefixComp.withQueryLog >>= fun result =>
    continuation result.1 (initialLog ++ result.2)

@[simp]
theorem loggedAccountingBind_pure (x : X) (log : (Query →ₒ Y).QueryLog)
    (continuation : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C) :
    loggedAccountingBind (pure x) log continuation = continuation x log := by
  simp [loggedAccountingBind]

theorem loggedAccountingBind_query_bind
    (query : Query) (next : Y → OracleComp (Query →ₒ Y) X)
    (log : (Query →ₒ Y).QueryLog)
    (continuation : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C) :
    loggedAccountingBind
        ((liftM ((Query →ₒ Y).query query) : OracleComp (Query →ₒ Y) Y) >>= next)
        log continuation =
      (liftM ((Query →ₒ Y).query query) : OracleComp (Query →ₒ Y) Y) >>= fun response =>
        loggedAccountingBind (next response) (log ++ [⟨query, response⟩]) continuation := by
  simp only [loggedAccountingBind, OracleComp.withQueryLog_bind, withQueryLog_query,
    bind_assoc, pure_bind, map_eq_pure_bind, Prod.map, id_eq, List.append_assoc]

/-- Ignoring the recorded log in the accounting continuation recovers ordinary bind accounting. -/
theorem isTotalQueryBound_loggedAccountingBind_const_iff
    (prefixComp : OracleComp (Query →ₒ Y) X)
    (log : (Query →ₒ Y).QueryLog)
    (continuation : X → OracleComp (Query →ₒ Y) C) (budget : ℕ) :
    IsTotalQueryBound
      (loggedAccountingBind prefixComp log (fun x _ => continuation x)) budget ↔
        IsTotalQueryBound (prefixComp >>= continuation) budget := by
  induction prefixComp using OracleComp.inductionOn generalizing budget log with
  | pure x => simp
  | query_bind query next ih =>
      rw [loggedAccountingBind_query_bind, bind_assoc,
        isTotalQueryBound_query_bind_iff, isTotalQueryBound_query_bind_iff]
      exact and_congr_right fun _ => forall_congr' fun response => ih response _ _

/-- **Online predictable-target adaptive-prefix bound.**

The target set may change with the accumulated log, but its cardinality must be bounded from the
pre-query cache/log invariants. The proof treats a target hit as an unrestricted bad branch; hence
the conclusion applies to any terminal event whose good branches satisfy the recursive/terminal
hypotheses, without requiring the execution to expose an explicit monitoring flag. -/
theorem probEvent_onlineAdaptivePrefixRunFrom_logged_le
    [DecidableEq Query] [DecidableEq Y] [Finite Y] [Inhabited Y]
    [IsUniformSpec (Query →ₒ Y)]
    (suffix : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) R)
    (continuation : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C)
    (win : R → Prop)
    (targets : (Query →ₒ Y).QueryLog → Finset Y)
    (Good : (Query →ₒ Y).QueryCache → (Query →ₒ Y).QueryLog → Prop)
    (nodeBudget checkpointCount overhead : ℕ)
    (prefixComp : OracleComp (Query →ₒ Y) X)
    (remaining cached : ℕ)
    (log : (Query →ₒ Y).QueryLog)
    (hbound : IsTotalQueryBound
      (loggedAccountingBind prefixComp log continuation) remaining)
    (cache : (Query →ₒ Y).QueryCache)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hgood : Good cache log)
    (hgoodHit : ∀ (currentCache : (Query →ₒ Y).QueryCache)
        (currentLog : (Query →ₒ Y).QueryLog) query response,
      Good currentCache currentLog → currentCache query = some response →
      (∀ input value, currentCache input = some value →
        ∃ entry ∈ currentLog, entry.1 = input ∧ entry.2 = value) →
      Good currentCache (currentLog ++ [⟨query, response⟩]))
    (hgoodMiss : ∀ (currentCache : (Query →ₒ Y).QueryCache)
        (currentLog : (Query →ₒ Y).QueryLog) query response,
      Good currentCache currentLog → currentCache query = none →
      ¬ CacheHasCollision (currentCache.cacheQuery query response) →
      response ∉ targets currentLog →
      Good (currentCache.cacheQuery query response)
        (currentLog ++ [⟨query, response⟩]))
    (htargetBound : ∀ (currentCached : ℕ)
        (currentCache : (Query →ₒ Y).QueryCache)
        (currentLog : (Query →ₒ Y).QueryLog),
      (∃ keys : Finset Query, keys.card ≤ currentCached ∧
        ∀ input, currentCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ currentLog, currentCache entry.1 = some entry.2) →
      (∀ input value, currentCache input = some value →
        ∃ entry ∈ currentLog, entry.1 = input ∧ entry.2 = value) →
      Good currentCache currentLog →
      (targets currentLog).card ≤
        sharedExtractedLabelCountBound nodeBudget checkpointCount currentCached)
    (hterminal : ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (Query →ₒ Y).QueryCache)
        (terminalLog : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x terminalLog) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      Good terminalCache terminalLog →
      Pr[ fun z => win z.1 | (simulateQ (Query →ₒ Y).cachingOracle
          (suffix x terminalLog)).run terminalCache] ≤
        (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
          terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[fun z => win z.1 |
      adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
        suffix prefixComp cache log] ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
        remaining cached : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  let cardY := (Nat.card Y : ENNReal)
  induction prefixComp using OracleComp.inductionOn generalizing remaining cached cache log with
  | pure x =>
      simpa only [adaptivePrefixRunFrom, simulateQ_pure, StateT.run_pure, pure_bind] using
        hterminal x remaining cached cache log (by simpa using hbound)
        hno hcacheBound hlogCache hcacheLog hgood
  | query_bind query next ih =>
      have hqueryBound : IsTotalQueryBound
          ((liftM ((Query →ₒ Y).query query) : OracleComp (Query →ₒ Y) _) >>=
            fun response =>
            loggedAccountingBind (next response) (log ++ [⟨query, response⟩])
              continuation) remaining := by
        rw [← loggedAccountingBind_query_bind]
        exact hbound
      rw [isTotalQueryBound_query_bind_iff] at hqueryBound
      obtain ⟨hremaining, hnext⟩ := hqueryBound
      by_cases hhit : ∃ response, cache query = some response
      · obtain ⟨response, hresponse⟩ := hhit
        have hrun : adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
            suffix ((liftM ((Query →ₒ Y).query query) :
              OracleComp (Query →ₒ Y) _) >>= next) cache log =
            adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
              suffix (next response) cache (log ++ [⟨query, response⟩]) := by
          simp only [adaptivePrefixRunFrom, OracleComp.run_simulateQ_query_bind,
            cachingLoggingOracle.run_some hresponse, pure_bind]
        rw [hrun]
        have hlogCache' : ∀ entry ∈ log ++ [⟨query, response⟩],
            cache entry.1 = some entry.2 := by
          intro entry hentry
          rw [List.mem_append] at hentry
          rcases hentry with hentry | hentry
          · exact hlogCache entry hentry
          · rw [List.mem_singleton] at hentry
            subst entry
            exact hresponse
        have hcacheLog' : ∀ input output, cache input = some output →
            ∃ entry ∈ log ++ [⟨query, response⟩],
              entry.1 = input ∧ entry.2 = output := by
          intro input output hcached
          obtain ⟨entry, hentry, hi, ho⟩ := hcacheLog input output hcached
          exact ⟨entry, List.mem_append_left _ hentry, hi, ho⟩
        have hrec := ih response (remaining := remaining - 1) (cached := cached)
          (hnext response) (cache := cache) (log := log ++ [⟨query, response⟩])
          hno hcacheBound hlogCache' hcacheLog'
          (hgoodHit cache log query response hgood hresponse hcacheLog)
        refine hrec.trans ?_
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast multiCheckpointErrorNumerator_hit_le
            nodeBudget checkpointCount overhead remaining cached
        · exact zero_le
      · push Not at hhit
        have hnone : cache query = none := Option.eq_none_iff_forall_ne_some.mpr hhit
        have hrun : adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
            suffix ((liftM ((Query →ₒ Y).query query) :
              OracleComp (Query →ₒ Y) _) >>= next) cache log =
            (liftM ((Query →ₒ Y).query query) :
              OracleComp (Query →ₒ Y) _) >>= fun response =>
              adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
                suffix (next response) (cache.cacheQuery query response)
                (log ++ [⟨query, response⟩]) := by
          simp only [adaptivePrefixRunFrom, OracleComp.run_simulateQ_query_bind,
            cachingLoggingOracle.run_none hnone]
          rfl
        rw [hrun]
        have hbad : Pr[fun response =>
            CacheHasCollision (cache.cacheQuery query response) ∨
              response ∈ targets log |
            (liftM ((Query →ₒ Y).query query) : OracleComp (Query →ₒ Y) _)] ≤
              ((cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached : ℕ) :
                ENNReal) * cardY⁻¹ := by
          classical
          let _ : Fintype Y := OracleSpec.instFintypeRangeOfFintype query
          have htargets := htargetBound cached cache log hcacheBound hlogCache hcacheLog hgood
          obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
          rw [probEvent_query]
          have hcollision := (OracleComp.card_responses_creating_cacheCollision_le
            (t := query) hno hkeysMem).trans hkeysCard
          have horCard :
              (Finset.univ.filter fun response : Y =>
                CacheHasCollision (cache.cacheQuery query response) ∨
                  response ∈ targets log).card ≤
                cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached := by
            calc
              _ ≤ (Finset.univ.filter fun response : Y =>
                      CacheHasCollision (cache.cacheQuery query response)).card +
                    (Finset.univ.filter fun response : Y =>
                      response ∈ targets log).card := by
                  refine (Finset.card_mono (b :=
                      (Finset.univ.filter fun response : Y =>
                        CacheHasCollision (cache.cacheQuery query response)) ∪
                      (Finset.univ.filter fun response : Y =>
                        response ∈ targets log)) ?_).trans
                    (Finset.card_union_le _ _)
                  intro response hresponse
                  simpa using hresponse
              _ ≤ cached + (targets log).card := by
                  exact Nat.add_le_add hcollision (by
                    have heq : (Finset.univ.filter fun response : Y =>
                        response ∈ targets log) = targets log := by ext; simp
                    exact le_of_eq (congrArg Finset.card heq))
              _ ≤ cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached :=
                Nat.add_le_add_left htargets cached
          have hcard :
              @Fintype.card ((Query →ₒ Y).Range query)
                  (OracleSpec.instFintypeRangeOfFintype query) = Nat.card Y := by
            calc
              @Fintype.card ((Query →ₒ Y).Range query)
                  (OracleSpec.instFintypeRangeOfFintype query) =
                  Nat.card ((Query →ₒ Y).Range query) :=
                    (@Nat.card_eq_fintype_card ((Query →ₒ Y).Range query)
                      (OracleSpec.instFintypeRangeOfFintype query)).symm
              _ = Nat.card Y := Nat.card_congr (Equiv.refl Y)
          calc
            ((Finset.univ.filter fun response : Y =>
                CacheHasCollision (cache.cacheQuery query response) ∨
                  response ∈ targets log).card : ENNReal) /
                @Fintype.card ((Query →ₒ Y).Range query)
                  (OracleSpec.instFintypeRangeOfFintype query)
              ≤ ((cached + sharedExtractedLabelCountBound nodeBudget checkpointCount
                    cached : ℕ) : ENNReal) /
                  @Fintype.card ((Query →ₒ Y).Range query)
                    (OracleSpec.instFintypeRangeOfFintype query) :=
                ENNReal.div_le_div_right (by exact_mod_cast horCard) _
            _ = ((cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached : ℕ) :
                  ENNReal) * cardY⁻¹ := by
              rw [hcard, ENNReal.div_eq_inv_mul, mul_comm]
        have hcontinuation : ∀ response ∈ support
            (liftM ((Query →ₒ Y).query query) : OracleComp (Query →ₒ Y) _),
            ¬ (CacheHasCollision (cache.cacheQuery query response) ∨
              response ∈ targets log) →
            Pr[fun z => win z.1 |
              adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
                suffix (next response) (cache.cacheQuery query response)
                (log ++ [⟨query, response⟩])] ≤
              (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
                (remaining - 1) (cached + 1) : ENNReal) * cardY⁻¹ := by
          intro response _ hsafe
          have hcacheBound' : ∃ keys : Finset Query, keys.card ≤ cached + 1 ∧
              ∀ input, (cache.cacheQuery query response) input ≠ none →
                input ∈ keys := by
            obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
            refine ⟨insert query keys, (Finset.card_insert_le query keys).trans (by omega), ?_⟩
            intro input hinput
            by_cases hi : input = query
            · exact hi ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne cache response hi] at hinput
              exact Finset.mem_insert_of_mem (hkeysMem input hinput)
          have hlogCache' : ∀ entry ∈ log ++ [⟨query, response⟩],
              (cache.cacheQuery query response) entry.1 = some entry.2 := by
            rintro ⟨input, output⟩ hentry
            rw [List.mem_append] at hentry
            rcases hentry with hentry | hentry
            · by_cases hi : input = query
              · subst input
                have := hlogCache ⟨query, output⟩ hentry
                simp [hnone] at this
              · rw [QueryCache.cacheQuery_of_ne cache response hi]
                exact hlogCache ⟨input, output⟩ hentry
            · rw [List.mem_singleton] at hentry
              have hinput : input = query := congrArg Sigma.fst hentry
              subst input
              have houtput : output = response := eq_of_heq (Sigma.mk.inj_iff.mp hentry).2
              subst output
              exact QueryCache.cacheQuery_self cache query response
          have hcacheLog' : ∀ input output,
              (cache.cacheQuery query response) input = some output →
              ∃ entry ∈ log ++ [⟨query, response⟩],
                entry.1 = input ∧ entry.2 = output := by
            intro input output hcached
            by_cases hi : input = query
            · subst input
              rw [QueryCache.cacheQuery_self] at hcached
              obtain rfl := Option.some.inj hcached
              exact ⟨⟨query, response⟩, by simp, rfl, rfl⟩
            · rw [QueryCache.cacheQuery_of_ne cache response hi] at hcached
              obtain ⟨entry, hentry, heqInput, heqOutput⟩ :=
                hcacheLog input output hcached
              exact ⟨entry, List.mem_append_left _ hentry, heqInput, heqOutput⟩
          have hrec := ih response (remaining := remaining - 1) (cached := cached + 1)
            (hnext response) (cache := cache.cacheQuery query response)
            (log := log ++ [⟨query, response⟩]) (not_or.mp hsafe).1
              hcacheBound' hlogCache' hcacheLog'
              (hgoodMiss cache log query response hgood hnone
                (not_or.mp hsafe).1 (not_or.mp hsafe).2)
          exact hrec
        have hcombined := probEvent_bind_le_add
          (mx := (liftM ((Query →ₒ Y).query query) : OracleComp (Query →ₒ Y) _))
          (my := fun response => adaptivePrefixRunFrom
            (ι := Query) (Y := Y) (X := X) (R := R) suffix (next response)
            (cache.cacheQuery query response) (log ++ [⟨query, response⟩]))
          (p := fun response =>
            ¬ (CacheHasCollision (cache.cacheQuery query response) ∨
              response ∈ targets log))
          (q := fun z => ¬ win z.1)
          (ε₁ :=
            ((cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached : ℕ) :
                ENNReal) * cardY⁻¹)
          (ε₂ := (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
            (remaining - 1) (cached + 1) : ENNReal) * cardY⁻¹)
          (by simpa only [not_not] using hbad)
          (by simpa only [not_not] using hcontinuation)
        simp only [not_not] at hcombined
        refine hcombined.trans ?_
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast multiCheckpointErrorNumerator_miss_le
            nodeBudget checkpointCount overhead remaining cached hremaining
        · exact zero_le

/-- Specialization where structural accounting does not depend on the accumulated log. -/
theorem probEvent_onlineAdaptivePrefixRunFrom_le
    [DecidableEq Query] [DecidableEq Y] [Finite Y] [Inhabited Y]
    [IsUniformSpec (Query →ₒ Y)]
    (suffix : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) R)
    (continuation : X → OracleComp (Query →ₒ Y) C)
    (win : R → Prop)
    (targets : (Query →ₒ Y).QueryLog → Finset Y)
    (Good : (Query →ₒ Y).QueryCache → (Query →ₒ Y).QueryLog → Prop)
    (nodeBudget checkpointCount overhead : ℕ)
    (prefixComp : OracleComp (Query →ₒ Y) X)
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (Query →ₒ Y).QueryCache)
    (log : (Query →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hgood : Good cache log)
    (hgoodHit : ∀ (currentCache : (Query →ₒ Y).QueryCache)
        (currentLog : (Query →ₒ Y).QueryLog) query response,
      Good currentCache currentLog → currentCache query = some response →
      (∀ input value, currentCache input = some value →
        ∃ entry ∈ currentLog, entry.1 = input ∧ entry.2 = value) →
      Good currentCache (currentLog ++ [⟨query, response⟩]))
    (hgoodMiss : ∀ (currentCache : (Query →ₒ Y).QueryCache)
        (currentLog : (Query →ₒ Y).QueryLog) query response,
      Good currentCache currentLog → currentCache query = none →
      ¬ CacheHasCollision (currentCache.cacheQuery query response) →
      response ∉ targets currentLog →
      Good (currentCache.cacheQuery query response)
        (currentLog ++ [⟨query, response⟩]))
    (htargetBound : ∀ (currentCached : ℕ)
        (currentCache : (Query →ₒ Y).QueryCache)
        (currentLog : (Query →ₒ Y).QueryLog),
      (∃ keys : Finset Query, keys.card ≤ currentCached ∧
        ∀ input, currentCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ currentLog, currentCache entry.1 = some entry.2) →
      (∀ input value, currentCache input = some value →
        ∃ entry ∈ currentLog, entry.1 = input ∧ entry.2 = value) →
      Good currentCache currentLog →
      (targets currentLog).card ≤
        sharedExtractedLabelCountBound nodeBudget checkpointCount currentCached)
    (hterminal : ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (Query →ₒ Y).QueryCache)
        (terminalLog : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      Good terminalCache terminalLog →
      Pr[ fun z => win z.1 | (simulateQ (Query →ₒ Y).cachingOracle
          (suffix x terminalLog)).run terminalCache] ≤
        (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
          terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[fun z => win z.1 |
      adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R)
        suffix prefixComp cache log] ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
        remaining cached : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  apply probEvent_onlineAdaptivePrefixRunFrom_logged_le suffix
    (fun x _ => continuation x) win targets Good nodeBudget checkpointCount overhead
    prefixComp remaining cached log
  · exact (isTotalQueryBound_loggedAccountingBind_const_iff
      prefixComp log continuation remaining).2 hbound
  · exact hno
  · exact hcacheBound
  · exact hlogCache
  · exact hcacheLog
  · exact hgood
  · exact hgoodHit
  · exact hgoodMiss
  · exact htargetBound
  · exact hterminal

end MerkleTreeMultiExtractability
