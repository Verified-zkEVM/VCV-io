/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Stateful
public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Sequential Merkle commitment phases

This module runs an adaptive sequence of Merkle commitment phases while recording one extractor
checkpoint after every emitted root.  Each phase receives the previous phase's private state, may
make homogeneous oracle queries, and selects its next configuration tag adaptively.

`runCommitments` is itself one `OracleComp`.  Calling `withQueryLog` around each phase records only
that phase's query segment; it does not evaluate the phase or install a fresh oracle.  A later game
can therefore interpret the complete runner through one caching random-oracle implementation and
obtain the shared-ROM semantics required by multi-extractability.

This layer deliberately stops before the terminal opening phase.  The opening verifier determines
what auxiliary state and dependent opening claims it needs, and owns the accepted/rejected bit.
Likewise, no query bound or probability statement is attached to this executable runner.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleSpec OracleComp

variable {Cfg Query Y Address S : Type}

/-- Adaptive commitment strategy used by the multi-extractability experiment. -/
structure SequentialCommitter (Cfg Query Y : Type) where
  /-- Private state threaded between commitment phases. -/
  State : Type
  /-- Initial state before the first commitment. -/
  initialState : State
  /-- Phase `round` emits a configuration tag and claimed root, then returns its next state. -/
  commit : (round : ℕ) → State → OracleComp (Query →ₒ Y) (Cfg × Y × State)

/-- Execute `rounds` commitment phases from an explicit round number, state, and extractor state.

The explicit `firstRound` parameter lets a surrounding game resume a sequence without renumbering
the adversary's phase input. -/
def SequentialCommitter.runCommitments
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} :
    (rounds firstRound : ℕ) → committer.State →
      ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y)
        (committer.State × ExtractorState Cfg Query Address Y config)
  | 0, _, state, extractorState => pure (state, extractorState)
  | rounds + 1, firstRound, state, extractorState => do
      let ((tag, root, nextState), phaseLog) ←
        (committer.commit firstRound state).withQueryLog
      committer.runCommitments rounds (firstRound + 1) nextState
        (extractorState.record tag phaseLog root)

/-- Execute a fixed number of commitments from the committer's initial state and an empty
extractor history. -/
def SequentialCommitter.runFromEmpty
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ) :
    OracleComp (Query →ₒ Y)
      (committer.State × ExtractorState Cfg Query Address Y config) :=
  committer.runCommitments rounds 0 committer.initialState ExtractorState.empty

@[simp]
theorem SequentialCommitter.runCommitments_zero
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (firstRound : ℕ) (state : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    committer.runCommitments 0 firstRound state extractorState =
      pure (state, extractorState) := rfl

/-- Every supported execution of the sequential runner preserves the checkpoint-prefix invariant.

This gives the random-oracle game an executable preservation theorem for
`ExtractorState.CheckpointLogsPrefixCumulativeLog`. -/
theorem SequentialCommitter.runCommitments_preserves_checkpointLogsPrefixCumulativeLog
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (rounds firstRound : ℕ)
    (state : committer.State) (extractorState : ExtractorState Cfg Query Address Y config)
    (hstate : extractorState.CheckpointLogsPrefixCumulativeLog)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support
      (committer.runCommitments rounds firstRound state extractorState)) :
    result.2.CheckpointLogsPrefixCumulativeLog := by
  induction rounds generalizing firstRound state extractorState result with
  | zero =>
      simp only [SequentialCommitter.runCommitments, mem_support_pure_iff] at hresult
      subst result
      exact hstate
  | succ rounds ih =>
      simp only [SequentialCommitter.runCommitments, mem_support_bind_iff] at hresult
      obtain ⟨phaseResult, _hphase, hrest⟩ := hresult
      obtain ⟨⟨tag, root, nextState⟩, phaseLog⟩ := phaseResult
      exact ih (firstRound + 1) nextState (extractorState.record tag phaseLog root)
        (ExtractorState.CheckpointLogsPrefixCumulativeLog.record hstate tag phaseLog root)
        result hrest

/-- Every supported run from the canonical empty state has prefix-ordered checkpoint logs. -/
theorem SequentialCommitter.runFromEmpty_checkpointLogsPrefixCumulativeLog
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support (committer.runFromEmpty config rounds)) :
    result.2.CheckpointLogsPrefixCumulativeLog :=
  committer.runCommitments_preserves_checkpointLogsPrefixCumulativeLog rounds 0
    committer.initialState
    ExtractorState.empty ExtractorState.checkpointLogsPrefixCumulativeLog_empty result hresult

/-- Support-wise accounting for a sequential commitment run.

The result has exactly one new checkpoint per phase, and its cumulative log extends the initial
log.  The prefix conclusion is the decomposition statement used by later stopping-time proofs: it
is equivalent to the existence of a suffix whose append to the initial log is the final log. -/
theorem SequentialCommitter.runCommitments_accounting
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (rounds firstRound : ℕ)
    (state : committer.State) (extractorState : ExtractorState Cfg Query Address Y config)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support
      (committer.runCommitments rounds firstRound state extractorState)) :
    result.2.checkpoints.length = extractorState.checkpoints.length + rounds ∧
      extractorState.cumulativeLog <+: result.2.cumulativeLog := by
  induction rounds generalizing firstRound state extractorState result with
  | zero =>
      simp only [SequentialCommitter.runCommitments, mem_support_pure_iff] at hresult
      subst result
      exact ⟨by simp, List.prefix_rfl⟩
  | succ rounds ih =>
      simp only [SequentialCommitter.runCommitments, mem_support_bind_iff] at hresult
      obtain ⟨phaseResult, _hphase, hrest⟩ := hresult
      obtain ⟨⟨tag, root, nextState⟩, phaseLog⟩ := phaseResult
      have haccount := ih (firstRound + 1) nextState
        (extractorState.record tag phaseLog root) result hrest
      constructor
      · calc
          result.2.checkpoints.length =
              (extractorState.record tag phaseLog root).checkpoints.length + rounds := haccount.1
          _ = (extractorState.checkpoints.length + 1) + rounds := by
            rw [ExtractorState.record_checkpoints_length]
          _ = extractorState.checkpoints.length + (rounds + 1) := by omega
      · exact (List.prefix_append extractorState.cumulativeLog phaseLog).trans haccount.2

/-- A supported sequential run adds exactly `rounds` checkpoints. -/
theorem SequentialCommitter.runCommitments_checkpoint_count
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (rounds firstRound : ℕ)
    (state : committer.State) (extractorState : ExtractorState Cfg Query Address Y config)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support
      (committer.runCommitments rounds firstRound state extractorState)) :
    result.2.checkpoints.length = extractorState.checkpoints.length + rounds :=
  (committer.runCommitments_accounting rounds firstRound state extractorState result hresult).1

/-- The terminal commitment log decomposes as the initial log followed by a phase suffix. -/
theorem SequentialCommitter.runCommitments_cumulativeLog_prefix
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (rounds firstRound : ℕ)
    (state : committer.State) (extractorState : ExtractorState Cfg Query Address Y config)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support
      (committer.runCommitments rounds firstRound state extractorState)) :
    extractorState.cumulativeLog <+: result.2.cumulativeLog :=
  (committer.runCommitments_accounting rounds firstRound state extractorState result hresult).2

/-- A supported run from the empty history records exactly the requested number of commitments. -/
theorem SequentialCommitter.runFromEmpty_checkpoint_count
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support (committer.runFromEmpty config rounds)) :
    result.2.checkpoints.length = rounds := by
  simpa [SequentialCommitter.runFromEmpty] using
    committer.runCommitments_checkpoint_count rounds 0 committer.initialState
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config) result hresult

/-- The pure state transition used after observing one phase output and its local query log. -/
def ExtractorState.recordCommitmentOutput {config : Configuration Cfg Address}
    (extractorState : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y)
    (output : Cfg × Y × S) : ExtractorState Cfg Query Address Y config :=
  extractorState.record output.1 phaseLog output.2.1

@[simp]
theorem ExtractorState.recordCommitmentOutput_cumulativeLog
    {config : Configuration Cfg Address}
    (extractorState : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y)
    (output : Cfg × Y × S) :
    (extractorState.recordCommitmentOutput phaseLog output).cumulativeLog =
      extractorState.cumulativeLog ++ phaseLog := rfl

end MerkleTreeMultiExtractability
