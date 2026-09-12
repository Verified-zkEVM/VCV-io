/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.CachingLoggingOracle
public import VCVio.OracleComp.QueryTracking.Collision
public import VCVio.EvalDist.Monad.Measure
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# Adaptive-prefix bounds for shared random oracles

This module isolates the stopping-time argument used by transcript extractors. A computation has
an adaptive prefix, whose completed query log determines a later suffix. Both phases run against
one lazy random function. The proof inducts on the still-running prefix rather than conditioning on
its realized query count.

For `m` remaining prefix-plus-continuation queries, `k` populated cache keys, and `c` future
prefix cache misses, the potential is

`c * k + choose(c, 2) + targetCount (k + c) * (m - c + overhead)`.

The first two terms pay for collisions introduced by the adaptive prefix. The last term is supplied
by a caller-specific terminal theorem, normally a finite-target fresh-hit bound for the suffix.
`targetCount` can describe how many distinct values a transcript extractor can expose from a cache
of a given size. This separation keeps Merkle-specific extraction invariants out of the generic
random-oracle stopping argument.

The theorem currently lives in `Type` because the birthday-bound primitive
`card_responses_creating_cacheCollision_le` is specialized to `OracleSpec.{0, 0}`. Lifting that
infrastructure to independent universes is deferred; the restriction is inherited rather than
mathematical.
-/

@[expose] public section

open OracleSpec OracleComp MeasureTheory

namespace OracleComp

variable {ι Y X R C : Type}

/-- Error energy after `prefixMisses` further fresh inputs in an adaptive prefix. -/
def adaptivePrefixEnergy (targetCount : ℕ → ℕ) (overhead remaining cached prefixMisses : ℕ) : ℕ :=
  prefixMisses * cached + prefixMisses.choose 2 +
    targetCount (cached + prefixMisses) * (remaining - prefixMisses + overhead)

/-- Maximum adaptive-prefix energy over every possible number of future cache misses. -/
def adaptivePrefixPotential (targetCount : ℕ → ℕ) (overhead remaining cached : ℕ) : ℕ :=
  (Finset.range (remaining + 1)).sup fun prefixMisses =>
    adaptivePrefixEnergy targetCount overhead remaining cached prefixMisses

private lemma adaptivePrefixEnergy_zero
    (targetCount : ℕ → ℕ) (overhead remaining cached : ℕ) :
    adaptivePrefixEnergy targetCount overhead remaining cached 0 =
      targetCount cached * (remaining + overhead) := by
  simp [adaptivePrefixEnergy]

private lemma adaptivePrefixEnergy_hit_le
    (targetCount : ℕ → ℕ) (overhead remaining cached prefixMisses : ℕ) :
    adaptivePrefixEnergy targetCount overhead (remaining - 1) cached prefixMisses ≤
      adaptivePrefixEnergy targetCount overhead remaining cached prefixMisses := by
  unfold adaptivePrefixEnergy
  gcongr
  omega

private lemma adaptivePrefixEnergy_miss_eq
    (targetCount : ℕ → ℕ) (overhead remaining cached prefixMisses : ℕ)
    (hprefix : prefixMisses < remaining) :
    cached + adaptivePrefixEnergy targetCount overhead (remaining - 1) (cached + 1)
        prefixMisses =
      adaptivePrefixEnergy targetCount overhead remaining cached (prefixMisses + 1) := by
  have htarget : cached + 1 + prefixMisses = cached + (prefixMisses + 1) := by omega
  have hremaining : remaining - 1 - prefixMisses = remaining - (prefixMisses + 1) := by omega
  have hchoose : (prefixMisses + 1).choose 2 =
      prefixMisses + prefixMisses.choose 2 := by
    rw [show prefixMisses + 1 = prefixMisses.succ by omega, Nat.choose_succ_succ]
    simp
  unfold adaptivePrefixEnergy
  rw [htarget, hremaining, hchoose]
  simp only [Nat.mul_succ, Nat.succ_mul]
  omega

private lemma adaptivePrefixPotential_terminal_le
    (targetCount : ℕ → ℕ) (overhead remaining cached : ℕ) :
    targetCount cached * (remaining + overhead) ≤
      adaptivePrefixPotential targetCount overhead remaining cached := by
  rw [← adaptivePrefixEnergy_zero]
  exact Finset.le_sup (by simp)

private lemma adaptivePrefixPotential_hit_le
    (targetCount : ℕ → ℕ) (overhead remaining cached : ℕ) :
    adaptivePrefixPotential targetCount overhead (remaining - 1) cached ≤
      adaptivePrefixPotential targetCount overhead remaining cached := by
  unfold adaptivePrefixPotential
  apply Finset.sup_le
  intro prefixMisses hprefix
  apply (adaptivePrefixEnergy_hit_le targetCount overhead remaining cached prefixMisses).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hprefix ⊢
  omega

private lemma adaptivePrefixPotential_miss_le
    (targetCount : ℕ → ℕ) (overhead remaining cached : ℕ) (hremaining : 0 < remaining) :
    cached + adaptivePrefixPotential targetCount overhead (remaining - 1) (cached + 1) ≤
      adaptivePrefixPotential targetCount overhead remaining cached := by
  unfold adaptivePrefixPotential
  rw [Finset.add_sup (by simp)]
  apply Finset.sup_le
  intro prefixMisses hprefix
  rw [adaptivePrefixEnergy_miss_eq targetCount overhead remaining cached prefixMisses
    (by
      simp only [Finset.mem_range] at hprefix
      omega)]
  apply Finset.le_sup
  simp only [Finset.mem_range] at hprefix ⊢
  omega

/-- Execute a still-running adaptive prefix with a combined cache/log state, then run the
caller-supplied suffix from the resulting state. -/
def adaptivePrefixRunFrom
    [DecidableEq ι] [DecidableEq Y]
    (suffix : X → (ι →ₒ Y).QueryLog → OracleComp (ι →ₒ Y) R)
    (prefixComp : OracleComp (ι →ₒ Y) X)
    (cache : (ι →ₒ Y).QueryCache)
    (log : (ι →ₒ Y).QueryLog) :
    OracleComp (ι →ₒ Y) (R × (ι →ₒ Y).QueryCache) :=
  (simulateQ (ι →ₒ Y).cachingLoggingOracle prefixComp).run (cache, log) >>= fun z =>
    (simulateQ (ι →ₒ Y).cachingOracle (suffix z.1 z.2.2)).run z.2.1

/-- **Adaptive-prefix shared-ROM bound.**

The prefix and its abstract continuation have total query bound `remaining`. The terminal
hypothesis supplies the caller-specific bound once the prefix stops, under the exact cache/log
invariants maintained by `cachingLoggingOracle`. The conclusion is valid even when the prefix
adaptively decides when to stop and repeats cached queries. -/
theorem measure_adaptivePrefixRunFrom_le
    [DecidableEq ι] [DecidableEq Y] [Finite Y]
    [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [MeasurableSpace (R × (ι →ₒ Y).QueryCache)]
    [EvalDistSemantics (OracleComp (ι →ₒ Y))]
    [LawfulEvalDistSemantics (OracleComp (ι →ₒ Y))]
    (hquery : ∀ t : ι, 𝒟[(liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)] =
      ProbabilityTheory.uniformOn Set.univ)
    (suffix : X → (ι →ₒ Y).QueryLog → OracleComp (ι →ₒ Y) R)
    (continuation : X → OracleComp (ι →ₒ Y) C)
    (win : R → Prop)
    (hwin : MeasurableSet {z : R × (ι →ₒ Y).QueryCache | win z.1})
    (targetCount : ℕ → ℕ) (overhead : ℕ)
    (prefixComp : OracleComp (ι →ₒ Y) X)
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (ι →ₒ Y).QueryCache)
    (log : (ι →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset ι, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hterminal : ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (ι →ₒ Y).QueryCache)
        (terminalLog : (ι →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset ι, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      𝒟[(simulateQ (ι →ₒ Y).cachingOracle
          (suffix x terminalLog)).run terminalCache] {z | win z.1} ≤
        ((targetCount terminalCached * (terminalRemaining + overhead) : ℕ) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹) :
    𝒟[adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R)
        suffix prefixComp cache log] {z | win z.1} ≤
      (adaptivePrefixPotential targetCount overhead remaining cached : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  let C := (Nat.card Y : ENNReal)
  induction prefixComp using OracleComp.inductionOn generalizing remaining cached cache log with
  | pure x =>
      have hsuffix := hterminal x remaining cached cache log (by simpa using hbound)
        hno hcacheBound hlogCache hcacheLog
      simp only [adaptivePrefixRunFrom, simulateQ_pure, StateT.run_pure, pure_bind]
      refine hsuffix.trans ?_
      change ((targetCount cached * (remaining + overhead) : ℕ) : ENNReal) * C⁻¹ ≤
        (adaptivePrefixPotential targetCount overhead remaining cached : ENNReal) * C⁻¹
      gcongr
      exact adaptivePrefixPotential_terminal_le targetCount overhead remaining cached
  | query_bind t next ih =>
      have hqueryBound : IsTotalQueryBound
          ((liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) _) >>= fun u =>
            next u >>= continuation) remaining := by
        simpa only [bind_assoc] using hbound
      rw [isTotalQueryBound_query_bind_iff] at hqueryBound
      obtain ⟨hremaining, hnext⟩ := hqueryBound
      by_cases hhit : ∃ value, cache t = some value
      · obtain ⟨value, hvalue⟩ := hhit
        have hrun : adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R) suffix
            ((liftM ((ι →ₒ Y).query t) :
              OracleComp (ι →ₒ Y) _) >>= next) cache log =
            adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R)
              suffix (next value) cache (log ++ [⟨t, value⟩]) := by
          simp only [adaptivePrefixRunFrom, OracleComp.run_simulateQ_query_bind,
            cachingLoggingOracle.run_some hvalue, pure_bind]
        rw [hrun]
        have hlogCache' : ∀ entry ∈ log ++ [⟨t, value⟩],
            cache entry.1 = some entry.2 := by
          exact QueryCache.log_consistent_append cache log t value hvalue hlogCache
        have hcacheLog' : ∀ input output, cache input = some output →
            ∃ entry ∈ log ++ [⟨t, value⟩], entry.1 = input ∧ entry.2 = output := by
          exact QueryCache.cache_covered_append cache log _ hcacheLog
        have hrec := ih value (remaining := remaining - 1) (cached := cached)
          (hnext value) (cache := cache) (log := log ++ [⟨t, value⟩])
          hno hcacheBound hlogCache' hcacheLog'
        refine hrec.trans ?_
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast adaptivePrefixPotential_hit_le
            targetCount overhead remaining cached
        · exact zero_le
      · push Not at hhit
        have hnone : cache t = none := Option.eq_none_iff_forall_ne_some.mpr hhit
        have hrun : adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R) suffix
            ((liftM ((ι →ₒ Y).query t) :
              OracleComp (ι →ₒ Y) _) >>= next) cache log =
            (liftM ((ι →ₒ Y).query t) :
              OracleComp (ι →ₒ Y) _) >>= fun value =>
              adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R)
                suffix (next value) (cache.cacheQuery t value)
                (log ++ [⟨t, value⟩]) := by
          simp only [adaptivePrefixRunFrom, OracleComp.run_simulateQ_query_bind,
            cachingLoggingOracle.run_none hnone]
          rfl
        rw [hrun]
        have hcollision : 𝒟[(liftM ((ι →ₒ Y).query t) :
              OracleComp (ι →ₒ Y) _)] {value | CacheHasCollision (cache.cacheQuery t value)} ≤
              (cached : ENNReal) * C⁻¹ := by
          classical
          let : Fintype Y := Fintype.ofFinite Y
          obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
          rw [hquery, ProbabilityTheory.uniformOn_univ_apply_setOf]
          have hbad := (OracleComp.card_responses_creating_cacheCollision_le
            (t := t) hno hkeysMem).trans hkeysCard
          calc
            _ ≤ (cached : ENNReal) / Fintype.card Y :=
              ENNReal.div_le_div_right (by exact_mod_cast hbad) _
            _ = (cached : ENNReal) * C⁻¹ := by
              rw [← Nat.card_eq_fintype_card, ENNReal.div_eq_inv_mul, mul_comm]
        have hcontinuation : ∀ value,
            ¬ CacheHasCollision (cache.cacheQuery t value) →
            𝒟[adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R)
                suffix (next value) (cache.cacheQuery t value)
                (log ++ [⟨t, value⟩])] {z | win z.1} ≤
              (adaptivePrefixPotential targetCount overhead
                (remaining - 1) (cached + 1) : ENNReal) * C⁻¹ := by
          intro value hno'
          have hcacheBound' : ∃ keys : Finset ι, keys.card ≤ cached + 1 ∧
              ∀ input, (cache.cacheQuery t value) input ≠ none → input ∈ keys := by
            exact QueryCache.domain_bound_cacheQuery cache t value cached hcacheBound
          have hlogCache' : ∀ entry ∈ log ++ [⟨t, value⟩],
              (cache.cacheQuery t value) entry.1 = some entry.2 := by
            exact QueryCache.log_consistent_cacheQuery_append cache log t value hnone hlogCache
          have hcacheLog' : ∀ input output,
              (cache.cacheQuery t value) input = some output →
              ∃ entry ∈ log ++ [⟨t, value⟩], entry.1 = input ∧ entry.2 = output := by
            exact QueryCache.cache_covered_cacheQuery_append cache log t value hcacheLog
          have hrec := ih value (remaining := remaining - 1) (cached := cached + 1)
            (hnext value) (cache := cache.cacheQuery t value)
            (log := log ++ [⟨t, value⟩]) hno' hcacheBound' hlogCache' hcacheLog'
          exact hrec
        have hcombined := evalDist_bind_apply_le_add_of_bad
          (mx := (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y))
          (f := fun value : Y => adaptivePrefixRunFrom
            (ι := ι) (Y := Y) (X := X) (R := R) suffix (next value)
            (cache.cacheQuery t value) (log ++ [⟨t, value⟩]))
          Measurable.of_discrete (bad := {value | CacheHasCollision (cache.cacheQuery t value)})
          MeasurableSet.of_discrete hwin hcollision (fun value hsafe => hcontinuation value hsafe)
        refine hcombined.trans ?_
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast adaptivePrefixPotential_miss_le
            targetCount overhead remaining cached hremaining
        · exact zero_le

/-- The adaptive-prefix measure bound read through the discrete probability notation. -/
theorem probEvent_adaptivePrefixRunFrom_le
    [DecidableEq ι] [DecidableEq Y] [Finite Y] [Inhabited Y]
    [IsUniformSpec (ι →ₒ Y)]
    (suffix : X → (ι →ₒ Y).QueryLog → OracleComp (ι →ₒ Y) R)
    (continuation : X → OracleComp (ι →ₒ Y) C)
    (win : R → Prop) (targetCount : ℕ → ℕ) (overhead : ℕ)
    (prefixComp : OracleComp (ι →ₒ Y) X)
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (ι →ₒ Y).QueryCache)
    (log : (ι →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset ι, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hterminal : ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (ι →ₒ Y).QueryCache)
        (terminalLog : (ι →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset ι, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      Pr[ fun z => win z.1 | (simulateQ (ι →ₒ Y).cachingOracle
          (suffix x terminalLog)).run terminalCache] ≤
        ((targetCount terminalCached * (terminalRemaining + overhead) : ℕ) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹) :
    Pr[fun z => win z.1 |
      adaptivePrefixRunFrom (ι := ι) (Y := Y) (X := X) (R := R)
        suffix prefixComp cache log] ≤
      (adaptivePrefixPotential targetCount overhead remaining cached : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  classical
  let : MeasurableSpace Y := ⊤
  let : MeasurableSpace (R × (ι →ₒ Y).QueryCache) := ⊤
  rw [← evalDist_apply_setOf]
  refine measure_adaptivePrefixRunFrom_le (hquery := ?_) suffix continuation win
    MeasurableSet.of_discrete targetCount overhead prefixComp remaining cached hbound
    cache log hno hcacheBound hlogCache hcacheLog ?_
  · intro t
    let : Fintype Y := Fintype.ofFinite Y
    apply MeasureTheory.Measure.ext_of_singleton
    intro y
    rw [evalDist_apply_singleton, probOutput_query, ProbabilityTheory.uniformOn_univ,
      MeasureTheory.Measure.count_singleton, one_div]
    simp only [← Nat.card_eq_fintype_card]
  · intro x terminalRemaining terminalCached terminalCache terminalLog hq hn hb hl hc
    simpa only [evalDist_apply_setOf] using
      hterminal x terminalRemaining terminalCached terminalCache terminalLog hq hn hb hl hc

end OracleComp
