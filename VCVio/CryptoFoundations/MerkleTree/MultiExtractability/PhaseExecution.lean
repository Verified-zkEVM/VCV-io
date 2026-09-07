/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.PhaseBound
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Sequential

/-!
# Execution Bridge for One Sequential Commitment Phase

`probEvent_stablePhaseRunFrom_le` exposes a raw commitment computation through the combined
caching/logging interpreter. The executable sequential runner instead uses `withQueryLog` inside
the oracle syntax and records the returned phase-local suffix. This module proves that the two
views are equal when the interpreter's initial cumulative log is the extractor state's log.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y S R : Type}

/-- Generic execution bridge: exposing an adaptive prefix through the combined cache/log handler
is exactly the executable `withQueryLog` prefix followed by a suffix receiving the accumulated
log.  This theorem is useful both for commitment phases and for the terminal opening phase. -/
theorem adaptivePrefixRunFrom_eq_withQueryLog
    [DecidableEq Query] [DecidableEq Y]
    (prefixComp : OracleComp (Query →ₒ Y) S)
    (suffix : S → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) R)
    (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog) :
    adaptivePrefixRunFrom suffix prefixComp cache log =
      (simulateQ (Query →ₒ Y).cachingOracle
        (prefixComp.withQueryLog >>= fun phaseResult =>
          suffix phaseResult.1 (log ++ phaseResult.2))).run cache := by
  unfold adaptivePrefixRunFrom
  rw [cachingLoggingOracle.run_simulateQ_eq_map_run_simulateQ_withQueryLog]
  simp only [StateT.run_bind, simulateQ_bind]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [pure_bind, Function.comp_apply]

/-- Executable `withQueryLog` form of the stable online phase theorem.  The abstract continuation
is used only for structural query accounting; `suffix` is the computation actually executed
after the logged prefix. -/
theorem probEvent_withQueryLog_stablePhase_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (prefixComp : OracleComp (Query →ₒ Y) S)
    (suffix : S → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) R)
    {C : Type} (continuation : S → OracleComp (Query →ₒ Y) C)
    (win : R → Prop) (nodeBudget checkpointCount overhead remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt view log)
    (hnodeBudget : state.totalNodeBudget ≤ nodeBudget)
    (hcheckpointCount : state.checkpoints.length ≤ checkpointCount)
    (hterminal : ∀ (x : S) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (Query →ₒ Y).QueryCache)
        (terminalLog : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view terminalLog →
      Pr[ fun z => win z.1 | (simulateQ (Query →ₒ Y).cachingOracle
          (suffix x terminalLog)).run terminalCache] ≤
        (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
          terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (prefixComp.withQueryLog >>= fun phaseResult =>
          suffix phaseResult.1 (log ++ phaseResult.2))).run cache] ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead remaining cached :
        ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  rw [← adaptivePrefixRunFrom_eq_withQueryLog prefixComp suffix cache log]
  exact probEvent_stablePhaseRunFrom_le view state suffix continuation win
    nodeBudget checkpointCount overhead prefixComp remaining cached hbound cache log
    hno hcacheBound hlogCache hcacheLog hstable hnodeBudget hcheckpointCount hterminal

/-- A raw commitment phase followed by cumulative-log recording has exactly the same cached
semantics as the executable `withQueryLog` phase followed by suffix recording. -/
theorem adaptivePrefixRunFrom_commit_eq
    [DecidableEq Query] [DecidableEq Y]
    {config : Configuration Cfg Address}
    (extractorState : ExtractorState Cfg Query Address Y config)
    (commit : OracleComp (Query →ₒ Y) (Cfg × Y × S))
    (rest : (Cfg × Y × S) → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (cache : (Query →ₒ Y).QueryCache) :
    adaptivePrefixRunFrom
        (fun output cumulativeLog =>
          rest output (extractorState.recordCumulative output.1 cumulativeLog output.2.1))
        commit cache extractorState.cumulativeLog =
      (simulateQ (Query →ₒ Y).cachingOracle
        (commit.withQueryLog >>= fun phaseResult =>
          rest phaseResult.1
            (extractorState.record phaseResult.1.1 phaseResult.2 phaseResult.1.2.1))).run
        cache := by
  unfold adaptivePrefixRunFrom
  rw [cachingLoggingOracle.run_simulateQ_eq_map_run_simulateQ_withQueryLog]
  simp only [StateT.run_bind, simulateQ_bind]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [pure_bind, Function.comp_apply]
  apply bind_congr
  intro phaseResult
  obtain ⟨⟨output, phaseLog⟩, nextCache⟩ := phaseResult
  rw [ExtractorState.recordCumulative_append]

end MerkleTreeMultiExtractability
