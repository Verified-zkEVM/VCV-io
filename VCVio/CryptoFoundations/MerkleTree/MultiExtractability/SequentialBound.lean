/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.PhaseExecution
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.ResourceBounds

/-!
# Sequential Composition of Stateful Merkle Phases

This module composes the one-phase predictable-target theorem across a fixed number of commitment
rounds. One global query bound covers a proof-only runner that mirrors the commitment phases and
ends in a log-dependent accounting computation.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y R C : Type}

/-- Run a sequential commitment suffix and then a caller-supplied terminal computation. -/
def SequentialCommitter.runCommitmentsThen
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address}
    (rounds firstRound : ℕ) (privateState : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R) : OracleComp (Query →ₒ Y) R := do
  let (finalPrivateState, finalExtractorState) ←
    committer.runCommitments rounds firstRound privateState extractorState
  finish finalPrivateState finalExtractorState

/-- Proof-only structural accounting for a sequential commitment suffix.

The commitment prefix is identical to `runCommitmentsThen`. At every boundary, the accumulated
query log selects the accounting computation for the remaining suffix. The final
`accountingFinish` need not be the executable `finish`: it exists solely to expose the residual
query budget used by the stopping theorem. -/
def SequentialCommitter.runCommitmentsThenAccounting
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address}
    (accountingFinish : committer.State → ExtractorState Cfg Query Address Y config →
      (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C) :
    (rounds firstRound : ℕ) → committer.State →
      ExtractorState Cfg Query Address Y config → (Query →ₒ Y).QueryLog →
      OracleComp (Query →ₒ Y) C
  | 0, _, privateState, extractorState, log =>
      accountingFinish privateState extractorState log
  | rounds + 1, firstRound, privateState, extractorState, log =>
      loggedAccountingBind (committer.commit firstRound privateState) log fun output terminalLog =>
        committer.runCommitmentsThenAccounting accountingFinish rounds (firstRound + 1)
          output.2.2
          (extractorState.recordCumulative output.1 terminalLog output.2.1) terminalLog

/-- When the accounting finish agrees with an executable finish at the extractor state's own
cumulative log, the proof-only accounting runner is extensionally the executable runner.  This
bridge lets a whole-program query bound be stated on the ordinary adversary syntax while the
stopping proof internally follows branch-specific residual budgets. -/
theorem SequentialCommitter.runCommitmentsThenAccounting_eq_runCommitmentsThen
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address}
    (accountingFinish : committer.State → ExtractorState Cfg Query Address Y config →
      (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C)
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) C)
    (hfinish : ∀ privateState extractorState,
      accountingFinish privateState extractorState extractorState.cumulativeLog =
        finish privateState extractorState)
    (rounds firstRound : ℕ) (privateState : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (log : (Query →ₒ Y).QueryLog)
    (hlog : extractorState.cumulativeLog = log) :
    committer.runCommitmentsThenAccounting accountingFinish rounds firstRound privateState
        extractorState log =
      committer.runCommitmentsThen rounds firstRound privateState extractorState finish := by
  induction rounds generalizing firstRound privateState extractorState log with
  | zero =>
      simp only [SequentialCommitter.runCommitmentsThenAccounting,
        SequentialCommitter.runCommitmentsThen, SequentialCommitter.runCommitments,
        pure_bind]
      rw [← hlog, hfinish]
  | succ rounds ih =>
      simp only [SequentialCommitter.runCommitmentsThenAccounting,
        SequentialCommitter.runCommitmentsThen, SequentialCommitter.runCommitments,
        loggedAccountingBind, bind_assoc]
      apply bind_congr
      rintro ⟨⟨tag, root, nextPrivateState⟩, phaseLog⟩
      rw [← hlog, ExtractorState.recordCumulative_append]
      exact ih (firstRound + 1) nextPrivateState
        (extractorState.record tag phaseLog root)
        (extractorState.cumulativeLog ++ phaseLog) rfl

/-- Exact adversarial query budget for `rounds` consecutive commitment phases beginning at
`firstRound`, allowing a different public budget at every round. -/
def commitmentQueryBudget (phaseBudget : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | rounds + 1, firstRound =>
      phaseBudget firstRound + commitmentQueryBudget phaseBudget rounds (firstRound + 1)

/-- A constant phase schedule has total budget `rounds * phaseBudget`. -/
@[simp]
theorem commitmentQueryBudget_const (phaseBudget rounds firstRound : ℕ) :
    commitmentQueryBudget (fun _ => phaseBudget) rounds firstRound = rounds * phaseBudget := by
  induction rounds generalizing firstRound with
  | zero => simp [commitmentQueryBudget]
  | succ rounds ih =>
      simp [commitmentQueryBudget, ih, Nat.succ_mul, Nat.add_comm]

/-- Public per-round bounds imply the corresponding exact whole-run bound. -/
theorem SequentialCommitter.runCommitments_isTotalQueryBound_schedule
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address}
    (phaseQueryBound : ℕ → ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (committer.commit round privateState) (phaseQueryBound round)) :
    ∀ rounds firstRound privateState
      (extractorState : ExtractorState Cfg Query Address Y config),
      IsTotalQueryBound
        (committer.runCommitments rounds firstRound privateState extractorState)
        (commitmentQueryBudget phaseQueryBound rounds firstRound) := by
  intro rounds
  induction rounds with
  | zero =>
      intro firstRound privateState extractorState
      trivial
  | succ rounds ih =>
      intro firstRound privateState extractorState
      simp only [SequentialCommitter.runCommitments, commitmentQueryBudget]
      apply isTotalQueryBound_bind
      · exact (isTotalQueryBound_withQueryLog_iff
          (committer.commit firstRound privateState) (phaseQueryBound firstRound)).2
          (hcommit firstRound privateState)
      · rintro ⟨⟨tag, root, nextPrivateState⟩, phaseLog⟩
        exact ih (firstRound + 1) nextPrivateState
          (extractorState.record tag phaseLog root)

/-- **Global-budget sequential predictable-target composition theorem.**

One total query bound covers the complete proof-only accounting runner. The induction decomposes
that bound at each commitment phase and passes the actual residual bound to the next phase. The
executable computation remains `runCommitmentsThen` with the caller's independent `finish`. -/
theorem SequentialCommitter.probEvent_runCommitmentsThen_logged_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (accountingFinish : committer.State → ExtractorState Cfg Query Address Y config →
      (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C)
    (win : R → Prop)
    (nodeBudget checkpointCount verifierOverhead : ℕ)
    (perCheckpoint : ℕ)
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
    (rounds firstRound : ℕ) (privateState : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache)
    (log : (Query →ₒ Y).QueryLog)
    (remaining cachedBound : ℕ)
    (hbound : IsTotalQueryBound
      (committer.runCommitmentsThenAccounting accountingFinish rounds firstRound privateState
        extractorState log) remaining)
    (hstateLog : extractorState.cumulativeLog = log)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query,
      keys.card ≤ cachedBound ∧
        ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : extractorState.StableAt view log)
    (hnodes : extractorState.totalNodeBudget + rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : extractorState.checkpoints.length + rounds ≤ checkpointCount) :
    Pr[ fun z => win z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (committer.runCommitmentsThen rounds firstRound privateState extractorState finish)).run
          cache] ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        remaining cachedBound : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  induction rounds generalizing firstRound privateState extractorState cache log remaining
      cachedBound with
  | zero =>
      have hnodes0 : extractorState.totalNodeBudget ≤ nodeBudget := by simpa using hnodes
      have hcheckpoints0 : extractorState.checkpoints.length ≤ checkpointCount := by
        simpa using hcheckpoints
      have hterminal := hfinish privateState extractorState remaining cachedBound cache log
        (by simpa [SequentialCommitter.runCommitmentsThenAccounting] using hbound)
        hstateLog hno hcacheBound hlogCache hcacheLog hstable hnodes0 hcheckpoints0
      simpa [SequentialCommitter.runCommitmentsThen] using hterminal
  | succ rounds ih =>
      subst log
      unfold SequentialCommitter.runCommitmentsThen
      simp only [SequentialCommitter.runCommitments]
      rw [bind_assoc]
      change Pr[ fun z => win z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          ((committer.commit firstRound privateState).withQueryLog >>= fun phaseResult =>
            committer.runCommitmentsThen rounds (firstRound + 1) phaseResult.1.2.2
              (extractorState.record phaseResult.1.1 phaseResult.2 phaseResult.1.2.1)
              finish)).run cache] ≤ _
      rw [← adaptivePrefixRunFrom_commit_eq extractorState
        (committer.commit firstRound privateState)
        (fun output nextExtractorState =>
          committer.runCommitmentsThen rounds (firstRound + 1) output.2.2
            nextExtractorState finish) cache]
      apply probEvent_stablePhaseRunFrom_logged_le view extractorState
        (fun output currentLog =>
          committer.runCommitmentsThen rounds (firstRound + 1) output.2.2
            (extractorState.recordCumulative output.1 currentLog output.2.1) finish)
        (fun output currentLog =>
          committer.runCommitmentsThenAccounting accountingFinish rounds (firstRound + 1)
            output.2.2
            (extractorState.recordCumulative output.1 currentLog output.2.1) currentLog)
        win nodeBudget checkpointCount verifierOverhead
        (committer.commit firstRound privateState) remaining cachedBound
        extractorState.cumulativeLog
      · simpa only [SequentialCommitter.runCommitmentsThenAccounting] using hbound
      · exact hno
      · exact hcacheBound
      · exact hlogCache
      · exact hcacheLog
      · exact hstable
      · omega
      · omega
      · intro output terminalRemaining terminalCached terminalCache terminalLog
          hrest hno' hcacheBound' hlogCache' hcacheLog' hstable'
        obtain ⟨tag, root, nextPrivateState⟩ := output
        refine ih (firstRound := firstRound + 1) (privateState := nextPrivateState)
          (extractorState := extractorState.recordCumulative tag terminalLog root)
          (cache := terminalCache) (log := terminalLog)
          (remaining := terminalRemaining) (cachedBound := terminalCached)
          hrest (ExtractorState.recordCumulative_cumulativeLog _ _ _ _)
          hno' hcacheBound' hlogCache' hcacheLog'
          (hstable'.recordCumulative view tag terminalLog root) ?_ ?_
        · rw [ExtractorState.totalNodeBudget_recordCumulative]
          have htag := hconfig tag
          simp only [Nat.add_mul, one_mul] at hnodes
          omega
        · simp only [ExtractorState.recordCumulative_checkpoints, List.length_append,
            List.length_singleton]
          omega

end MerkleTreeMultiExtractability
