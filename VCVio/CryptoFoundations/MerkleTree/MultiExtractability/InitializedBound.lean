/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.SequentialBound

/-!
# Initialized Sequential Merkle Bounds

This module initializes the stateful stopping theorem at the empty cache, log, and extractor
history. The finite-maximum numerator is obtained from a single bound on the complete adversarial
execution.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y R C : Type}

/-- Run a fixed commitment prefix from the canonical private and extractor states, then execute
the terminal computation supplied by the caller. -/
def SequentialCommitter.runFromEmptyThen
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R) : OracleComp (Query →ₒ Y) R :=
  committer.runCommitmentsThen rounds 0 committer.initialState ExtractorState.empty finish

/-- Empty-state specialization of the global-budget sequential theorem.

The single hypothesis at `queryBound` accounts for every commitment phase and the final
log-dependent accounting computation. The executable runner still ends in the independent
`finish`, and the empty initial cache turns the safe potential into the finite-max numerator. -/
theorem SequentialCommitter.probEvent_runFromEmptyThen_logged_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (config : Configuration Cfg Address)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (accountingFinish : committer.State → ExtractorState Cfg Query Address Y config →
      (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C)
    (win : R → Prop)
    (nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hfinish : ∀ privateState
        (state : ExtractorState Cfg Query Address Y config)
        (terminalRemaining terminalCached : ℕ)
        (cache : (Query →ₒ Y).QueryCache)
        (log : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (accountingFinish privateState state log) terminalRemaining →
      state.cumulativeLog = log →
      ¬ CacheHasCollision cache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, cache input ≠ none → input ∈ keys) →
      (∀ entry ∈ log, cache entry.1 = some entry.2) →
      (∀ input value, cache input = some value →
        ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view log →
      state.totalNodeBudget ≤ nodeBudget →
      state.checkpoints.length ≤ checkpointCount →
      Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle (finish privateState state)).run cache] ≤
        (multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
          terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹)
    (rounds queryBound : ℕ)
    (hbound : IsTotalQueryBound
      (committer.runCommitmentsThenAccounting accountingFinish rounds 0
        committer.initialState
        (ExtractorState.empty : ExtractorState Cfg Query Address Y config) []) queryBound)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runFromEmptyThen config rounds finish)).run ∅] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  have hraw := committer.probEvent_runCommitmentsThen_logged_le view finish accountingFinish win
    nodeBudget checkpointCount verifierOverhead perCheckpoint hconfig hfinish
    rounds 0 committer.initialState
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
    (∅ : (Query →ₒ Y).QueryCache) [] queryBound 0 hbound rfl
    (by
      rintro ⟨_, _, _, _, _, hcached, _, _⟩
      simp at hcached)
    ⟨∅, by simp, fun input hinput => (hinput (by simp)).elim⟩
    (by simp) (by simp) (ExtractorState.stableAt_empty view config [])
    (by simpa [ExtractorState.totalNodeBudget, nodeBudgetOfCheckpoints] using hnodes)
    (by simpa using hcheckpoints)
  simpa [SequentialCommitter.runFromEmptyThen, multiCheckpointROMErrorNumerator] using hraw

end MerkleTreeMultiExtractability
