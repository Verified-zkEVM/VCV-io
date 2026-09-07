/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Endgame
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.InitializedBound
public import VCVio.OracleComp.QueryTracking.Unpredictability

/-!
# Strong Multi-Extractability Bound

This module connects the generic sequential stopping theorem to the executable stateful game.
One whole-adversary query predicate controls every commitment and opening query. Honest batch
verification is charged separately through its structural query bound.
-/

@[expose] public section

open OracleSpec OracleComp
open BinaryTree InductiveMerkleTree

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y : Type}

/-- Terminal opening production, honest verification, and transcript assembly. -/
def Adversary.terminalExecution [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) := do
  let (claims, terminalSuffix) ←
    (adversary.opening privateState extractorState).withQueryLog
  let attempts ← verifyOpeningClaims model claims
  return { extractorState, attempts, terminalSuffix }

/-- The executable inner game is the initialized sequential runner followed by
`terminalExecution`. -/
theorem extractabilityInner_eq_runFromEmptyThen [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    extractabilityInner model config rounds adversary =
      adversary.committer.runFromEmptyThen config rounds
        (adversary.terminalExecution model) := rfl

/-- Proof-only terminal computation used to account exactly the adversary's opening work while
excluding honest verification. The cumulative log argument is intentionally ignored here: it is
needed by the generic residual runner to select continuations, while the adversary already
receives the equivalent extractor state. -/
def Adversary.openingAccountingFinish
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (_log : (Query →ₒ Y).QueryLog) : OracleComp (Query →ₒ Y) Unit := do
  let _claims ← adversary.opening privateState extractorState
  pure ()

/-- The residual accounting runner is exactly the previously exposed whole-adversary prefix
program. Consequently, clients state one ordinary global query bound and never mention the
proof-only logged runner. -/
theorem Adversary.runCommitmentsThenAccounting_opening_eq_prefixProgram
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) (rounds : ℕ) :
    adversary.committer.runCommitmentsThenAccounting adversary.openingAccountingFinish
        rounds 0 adversary.committer.initialState
        (ExtractorState.empty : ExtractorState Cfg Query Address Y config) [] =
      adversary.prefixProgram rounds := by
  rw [adversary.committer.runCommitmentsThenAccounting_eq_runCommitmentsThen
    adversary.openingAccountingFinish
    (fun privateState extractorState => do
      let _claims ← adversary.opening privateState extractorState
      pure ()) (by intros; rfl) rounds 0 adversary.committer.initialState
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config) [] rfl]
  rfl

/-- Pointwise query accounting for the executable terminal phase.  The opening computation uses
the supplied residual adversarial budget; honest verification contributes only its separately
justified support-wise overhead. Query logging itself is resource-transparent. -/
theorem Adversary.terminalExecution_isTotalQueryBound_of_opening
    [DecidableEq Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (openingBound verifierBound : ℕ)
    (hopening : IsTotalQueryBound
      (adversary.opening privateState extractorState) openingBound)
    (hverifier : adversary.HasVerifierQueryBound verifierBound) :
    IsTotalQueryBound (adversary.terminalExecution model privateState extractorState)
      (openingBound + verifierBound) := by
  unfold Adversary.terminalExecution
  apply isTotalQueryBound_bind_of_mem_support
      (prefixBound := openingBound) (suffixBound := verifierBound)
  · exact (isTotalQueryBound_withQueryLog_iff
      (adversary.opening privateState extractorState) openingBound).2
      hopening
  · rintro ⟨claims, terminalSuffix⟩ hclaimsLogged
    have hclaims : claims ∈ support (adversary.opening privateState extractorState) := by
      have hmapped : claims ∈ support
          (Prod.fst <$> (adversary.opening privateState extractorState).withQueryLog) := by
        rw [support_map]
        exact ⟨(claims, terminalSuffix), hclaimsLogged, rfl⟩
      change claims ∈ support (Prod.fst <$> (simulateQ
        (Query →ₒ Y).loggingOracle
        (adversary.opening privateState extractorState)).run) at hmapped
      simpa using hmapped
    exact isTotalQueryBound_bind
      (n₁ := verifierBound) (n₂ := 0)
      ((verifyOpeningClaims_isTotalQueryBound model claims).mono
        (hverifier privateState extractorState claims hclaims))
      fun _ => trivial

/-- Uniform specialization of pointwise terminal accounting. -/
theorem Adversary.terminalExecution_isTotalQueryBound
    [DecidableEq Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (openingBound verifierBound : ℕ)
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) openingBound)
    (hverifier : adversary.HasVerifierQueryBound verifierBound) :
    ∀ privateState extractorState,
      IsTotalQueryBound (adversary.terminalExecution model privateState extractorState)
        (openingBound + verifierBound) := by
  intro privateState extractorState
  exact adversary.terminalExecution_isTotalQueryBound_of_opening model privateState
    extractorState openingBound verifierBound (hopening privateState extractorState) hverifier

/-- Deterministic terminal reduction needed for the concrete ROM estimate.  Every strong failure
must add, under a previously empty complete-query key, one value that was already live in the
checkpoint extractor at the beginning of the terminal phase. -/
private def Adversary.TerminalFreshTargetProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache),
    state.cumulativeLog = log →
    ¬ CacheHasCollision cache →
    (∀ entry ∈ log, cache entry.1 = some entry.2) →
    (∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
    state.StableAt model.view log →
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    Transcript.HasAnyCheckpointExtractionDisagreement model z.1 →
    ∃ target ∈ state.liveTargetSet model.view log,
      MerkleTreeExtractability.CacheAddsValue cache z.2 target

/-- Cache/log facts preserved by terminal execution. -/
private def Adversary.TerminalTraceInvariant
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache),
    state.cumulativeLog = log →
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    z.1.extractorState = state ∧ cache ≤ z.2 ∧
      ∀ entry ∈ z.1.terminalSuffix, z.2 entry.1 = some entry.2

/-- The remaining Merkle-specific endgame obligation after terminal checkpoint evolution is
handled generically: under final stability, an accepted opening disagreement adds a fresh value
from the immutable checkpoint target set. -/
private def Adversary.TerminalAcceptedFreshProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache),
    state.cumulativeLog = log →
    ¬ CacheHasCollision cache →
    (∀ entry ∈ log, cache entry.1 = some entry.2) →
    (∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
    state.StableAt model.view log →
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    state.StableAt model.view (log ++ z.1.terminalSuffix) →
    HasAcceptedOpeningDisagreement model.view state z.1.attempts →
    ∃ target ∈ state.targetSet model.view,
      MerkleTreeExtractability.CacheAddsValue cache z.2 target

/-- Support-level evidence expected from honest batch verification: every accepted disagreeing
attempt exposes the generated selected path consumed by the deterministic extraction kernel. -/
private def Adversary.TerminalOpeningEvidenceProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (cache : (Query →ₒ Y).QueryCache)
      (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache)
      tag (attempt : EvaluatedOpeningClaim Query Y config tag),
    z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache) →
    (⟨tag, attempt⟩ : AnyEvaluatedOpeningClaim Cfg Query Address Y config) ∈ z.1.attempts →
    (⟨tag, attempt.checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
      state.checkpoints →
    AcceptedOpeningDisagreement model.view attempt →
    Nonempty (OpeningKernelEvidence model attempt z.2)

/-- A supported terminal execution retains the complete cache-level batch run for every accepted
attempt selected from its result list.  This is the generic support bridge used before applying
the pure selected-path disagreement theorem. -/
private theorem Adversary.batchProofEvaluatesInCache_of_terminalExecution_support
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (state : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache)
    (z : Transcript Cfg Query Address Y config × (Query →ₒ Y).QueryCache)
    (hz : z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
      (adversary.terminalExecution model privateState state)).run cache))
    (tag : Cfg) (attempt : EvaluatedOpeningClaim Query Y config tag)
    (hmem :
      (⟨tag, attempt⟩ : AnyEvaluatedOpeningClaim Cfg Query Address Y config) ∈ z.1.attempts)
    (haccepted : attempt.accepted = true) :
    MerkleTreeBatchExtractability.BatchProofEvaluatesInCache model (config.addressKey tag) z.2
      attempt.opening.values attempt.opening.proof attempt.checkpoint.root := by
  unfold Adversary.terminalExecution at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨claims, terminalSuffix⟩, cacheOpening⟩, hopening, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨attempts, cacheFinal⟩, hverify, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst z
  exact batchProofEvaluatesInCache_of_mem_support_verifyOpeningClaims model claims cacheOpening
    cacheFinal attempts hverify tag attempt hmem haccepted

/-- Reverse whole-structure disagreement at a checkpoint is exactly the explicit selected-values
or pruned-proof disagreement consumed by the batch path kernel.  The selector is definitionally
shared, so the dependent payload equalities are the only two possible equality obligations. -/
private theorem AcceptedOpeningDisagreement.toOpeningDisagreesWithTree
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    {attempt : EvaluatedOpeningClaim Query Y config tag}
    (hdisagreement : AcceptedOpeningDisagreement model.view attempt) :
    MerkleTreeBatchExtractability.OpeningDisagreesWithTree attempt.opening
      (Checkpoint.extractedTree model.view attempt.checkpoint) := by
  rcases attempt with ⟨checkpoint, ⟨selector, values, proof⟩, accepted⟩
  simp only [AcceptedOpeningDisagreement] at hdisagreement
  by_contra hnot
  simp only [MerkleTreeBatchExtractability.OpeningDisagreesWithTree, not_or] at hnot
  apply hdisagreement.2
  simp only [Checkpoint.extractedOpening, InductiveMerkleTree.BatchOpening.map,
    MerkleTreeBatchExtractability.extractedOpening] at hnot ⊢
  have hvalues := not_ne_iff.mp hnot.1
  have hproof := not_ne_iff.mp hnot.2
  congr
  · exact hvalues.symm
  · exact hproof.symm

/-- Honest batch verification always supplies the selected-path cache evidence required by the
deterministic terminal extraction kernel. -/
private theorem Adversary.terminalOpeningEvidenceProperty
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) :
    adversary.TerminalOpeningEvidenceProperty model := by
  intro privateState state cache z tag attempt hz hattempt _hcheckpoint hdisagreement
  let tree := Checkpoint.extractedTree model.view attempt.checkpoint
  let nodeHash := MerkleTreeBatchExtractability.cacheNodeHash model
    (config.addressKey tag) z.2 attempt.checkpoint.root
  have hrun := adversary.batchProofEvaluatesInCache_of_terminalExecution_support model
    privateState state cache z hz tag attempt hattempt hdisagreement.1
  have hopeningDisagrees :
      MerkleTreeBatchExtractability.OpeningDisagreesWithTree attempt.opening tree :=
    hdisagreement.toOpeningDisagreesWithTree model
  obtain ⟨index, selected, hpath⟩ :=
    hopeningDisagrees.exists_selectedValue_or_path_disagreement
      nodeHash attempt.opening tree
  refine ⟨{
    index := index
    selected := selected
    proof := batchToSingleProofAddressed nodeHash attempt.opening.values
      attempt.opening.proof index selected
    chain := ?_
    disagrees := ?_ }⟩
  · exact
      MerkleTreeBatchExtractability.chainInCache_batchToSingleProofAddressed_cacheNodeHash model
        (config.addressKey tag) z.2 attempt.checkpoint.root attempt.opening.values
        attempt.opening.proof attempt.checkpoint.root hrun index selected
  · exact hpath

/-- Terminal execution always preserves its input extractor state, grows the shared cache, and
leaves every terminal-opening log entry in the final cache. -/
private theorem Adversary.terminalTraceInvariant
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) :
    adversary.TerminalTraceInvariant model := by
  intro privateState state cache _log z _hstateLog hz
  unfold Adversary.terminalExecution at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨claims, terminalSuffix⟩, cacheOpening⟩, hopening, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨attempts, cacheFinal⟩, hverify, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst z
  have hopeningInvariant := OracleComp.log_entry_in_cache_and_mono
    (adversary.opening privateState state) cache
    ((claims, terminalSuffix), cacheOpening) hopening
  have hverifyMono : cacheOpening ≤ cacheFinal :=
    simulateQ_cachingOracle_cache_le (verifyOpeningClaims model claims) cacheOpening
      (attempts, cacheFinal) hverify
  exact ⟨rfl, hopeningInvariant.2.trans hverifyMono,
    fun entry hentry => hverifyMono (hopeningInvariant.1 entry hentry)⟩

/-- Honest-verifier path evidence implies the accepted-opening fresh-target property. -/
private theorem Adversary.terminalAcceptedFreshProperty_of_openingEvidence
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    adversary.TerminalAcceptedFreshProperty model := by
  intro privateState state cache log z hstateLog hno hlogCache hcacheLog hstable hz
    _hstableFinal hopening
  obtain ⟨_hstate, hmono, _hsuffixFinal⟩ :=
    adversary.terminalTraceInvariant model privateState state cache log z hstateLog hz
  obtain ⟨tag, attempt, hattempt, hcheckpoint, hdisagreement⟩ := hopening
  obtain ⟨evidence⟩ :=
    hevidence privateState state cache z tag attempt hz hattempt hcheckpoint hdisagreement
  have hpathDisagreement := evidence.disagrees
  rw [hstable tag attempt.checkpoint hcheckpoint] at hpathDisagreement
  obtain ⟨target, htarget, hfresh⟩ :=
    MerkleTreeExtractability.fresh_extractedTarget_of_extractor_disagreement
      model (config.addressKey tag) evidence.index log cache z.2 attempt.checkpoint.root
      (selectedValueAt attempt.opening.values evidence.index evidence.selected) evidence.proof
      hlogCache hcacheLog hno hmono evidence.chain hpathDisagreement
  refine ⟨target, ?_, hfresh⟩
  simp only [ExtractorState.targetSet, List.mem_toFinset, ExtractorState.targetList,
    targetsOfCheckpoints, List.mem_flatMap]
  refine ⟨⟨tag, attempt.checkpoint⟩, hcheckpoint, ?_⟩
  have htargetsEq := MerkleTreeExtractor.targets_eq_of_tree_eq model.view
    (config.skeleton tag) (config.addressKey tag) attempt.checkpoint.cumulativeLog log
    attempt.checkpoint.root attempt.checkpoint.root (hstable tag attempt.checkpoint hcheckpoint)
  simpa [Checkpoint.targets] using htargetsEq.symm ▸ htarget

/-- Trace preservation, causal suffix stability, and the accepted-opening kernel together imply
the single deterministic terminal fresh-target property used by the ROM theorem. -/
private theorem Adversary.terminalFreshTargetProperty_of_trace_and_accepted
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (htrace : adversary.TerminalTraceInvariant model)
    (haccepted : adversary.TerminalAcceptedFreshProperty model) :
    adversary.TerminalFreshTargetProperty model := by
  intro privateState state cache log z hstateLog hno hlogCache hcacheLog hstable hz hfailure
  obtain ⟨hstate, hmono, hsuffixFinal⟩ :=
    htrace privateState state cache log z hstateLog hz
  have hfailure' :
      AnyCheckpointExtractionDisagreement model.view state z.1.attempts z.1.terminalSuffix := by
    simpa only [Transcript.HasAnyCheckpointExtractionDisagreement, hstate] using hfailure
  have freshOfNotStable
      (hnotStable : ¬ state.StableAt model.view (log ++ z.1.terminalSuffix)) :
      ∃ target ∈ state.liveTargetSet model.view log,
        MerkleTreeExtractability.CacheAddsValue cache z.2 target := by
    obtain ⟨target, htarget, hfresh⟩ :=
      hstable.exists_freshTarget_of_not_stable_append model.view z.1.terminalSuffix
        cache z.2 hcacheLog hmono hsuffixFinal hnotStable
    refine ⟨target, ?_, hfresh⟩
    rwa [hstable.liveTargetSet_eq_targetSet model.view]
  rcases hfailure' with hopening | hequalRoot | hterminal
  · by_cases hstableFinal : state.StableAt model.view (log ++ z.1.terminalSuffix)
    · obtain ⟨target, htarget, hfresh⟩ := haccepted privateState state cache log z
        hstateLog hno hlogCache hcacheLog hstable hz hstableFinal hopening
      refine ⟨target, ?_, hfresh⟩
      rwa [hstable.liveTargetSet_eq_targetSet model.view]
    · exact freshOfNotStable hstableFinal
  · exact (hstable.not_hasEqualRootExtractionDisagreement model.view hequalRoot).elim
  · apply freshOfNotStable
    intro hstableFinal
    have hstableTerminal : state.StableAt model.view
        (state.terminalLog z.1.terminalSuffix) := by
      simpa [ExtractorState.terminalLog, hstateLog] using hstableFinal
    exact hstableTerminal.not_hasCheckpointTerminalExtractionDisagreement
      model.view z.1.terminalSuffix hterminal

/-- The honest-verifier evidence property alone supplies the Merkle-specific part of the complete
terminal fresh-target reduction; generic trace preservation is automatic. -/
private theorem Adversary.terminalFreshTargetProperty_of_openingEvidence
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (hevidence : adversary.TerminalOpeningEvidenceProperty model) :
    adversary.TerminalFreshTargetProperty model :=
  adversary.terminalFreshTargetProperty_of_trace_and_accepted model
    (adversary.terminalTraceInvariant model)
    (adversary.terminalAcceptedFreshProperty_of_openingEvidence model hevidence)

/-- Pointwise terminal ROM estimate at the exact residual adversarial budget.  This is the
terminal interface needed by global sequential accounting: earlier commitment phases may leave a
different residual budget on every supported branch. -/
private theorem Adversary.probEvent_terminalExecution_le_of_freshTarget
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead terminalRemaining terminalCached : ℕ)
    (privateState : adversary.committer.State)
    (state : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
    (hbound : IsTotalQueryBound (adversary.terminalExecution model privateState state)
      (terminalRemaining + verifierOverhead))
    (hfresh : adversary.TerminalFreshTargetProperty model)
    (hstateLog : state.cumulativeLog = log)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ terminalCached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt model.view log)
    (hnodeBudget : state.totalNodeBudget ≤ nodeBudget)
    (hcheckpointCount : state.checkpoints.length ≤ checkpointCount) :
    Pr[ fun z => Transcript.HasAnyCheckpointExtractionDisagreement model z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (adversary.terminalExecution model privateState state)).run cache] ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        terminalRemaining terminalCached : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  let targets := state.liveTargetSet model.view log
  have htargets : targets.card ≤
      sharedExtractedLabelCountBound nodeBudget checkpointCount terminalCached := by
    obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
    apply (state.liveTargetSet_card_le_sharedExtractedLabelCountBound_of_cover model.view log
      cache keys terminalCached hkeysCard {
        log_agrees := fun query response hentry => hlogCache ⟨query, response⟩ hentry
        cache_keys := hkeysMem }).trans
    exact sharedExtractedLabelCountBound_mono_budget hnodeBudget hcheckpointCount
  have hhit :
      Pr[ fun z => Transcript.HasAnyCheckpointExtractionDisagreement model z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          (adversary.terminalExecution model privateState state)).run cache] ≤
        Pr[ fun z => ∃ target ∈ targets, ∃ input : Query, ∃ value : Y,
          z.2 input = some value ∧ cache input = none ∧ value = target |
          (simulateQ (Query →ₒ Y).cachingOracle
            (adversary.terminalExecution model privateState state)).run cache] := by
    apply probEvent_mono
    intro z hz hfailure
    obtain ⟨target, htarget, input, hfinal, hinitial⟩ :=
      hfresh privateState state cache log z hstateLog hno hlogCache hcacheLog hstable hz hfailure
    exact ⟨target, htarget, input, target, hfinal, hinitial, rfl⟩
  have hprob := OracleComp.probEvent_cache_hits_targets_le_of_noCollision_homogeneous
    (adversary.terminalExecution model privateState state)
    (terminalRemaining + verifierOverhead) hbound targets cache hno
  refine hhit.trans (hprob.trans ?_)
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Nat.mul_le_mul_right (terminalRemaining + verifierOverhead) htargets).trans
      (multiCheckpointErrorNumerator_terminal_le nodeBudget checkpointCount verifierOverhead
        terminalRemaining terminalCached)
  · exact zero_le

/-- A public phase schedule plus a uniform terminal-opening bound implies one whole-adversary
query bound. -/
theorem Adversary.isAdversaryPrefixQueryBound_of_schedule
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (rounds : ℕ) (phaseQueryBound : ℕ → ℕ) (terminalQueryBound : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound) :
    adversary.IsAdversaryPrefixQueryBound rounds
      (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) := by
  unfold Adversary.IsAdversaryPrefixQueryBound Adversary.prefixProgram
  apply isTotalQueryBound_bind
  · exact adversary.committer.runCommitments_isTotalQueryBound_schedule phaseQueryBound hcommit
      rounds 0 adversary.committer.initialState
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
  · rintro ⟨privateState, extractorState⟩
    exact isTotalQueryBound_bind (n₁ := terminalQueryBound) (n₂ := 0)
      (hopening privateState extractorState) fun _ => trivial

/-- **Strongest executable multi-extractability theorem (one global adversarial budget).**

The single `queryBound` covers every adaptive commitment phase and terminal opening production
along each complete adversarial execution. Honest batch verification is excluded from that budget
and charged separately through `verifierOverhead`. The conclusion bounds the full three-branch
strong failure event under one shared cached homogeneous random oracle. -/
theorem anyCheckpointDisagreement_rom_bound_of_prefixQueryBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  have hraw := adversary.committer.probEvent_runFromEmptyThen_logged_le model.view config
    (adversary.terminalExecution model) adversary.openingAccountingFinish
    (Transcript.HasAnyCheckpointExtractionDisagreement model) nodeBudget checkpointCount
    verifierOverhead perCheckpoint hconfig
    (by
      intro privateState state terminalRemaining terminalCached cache log hopening hstateLog hno
        hcacheBound hlogCache hcacheLog hstable hnodeBudget hcheckpointCount
      have hopening' : IsTotalQueryBound
          (adversary.opening privateState state) terminalRemaining := by
        have hmapped : IsTotalQueryBound
            ((fun _ => ()) <$> adversary.opening privateState state) terminalRemaining := by
          simpa [Adversary.openingAccountingFinish, map_eq_bind_pure_comp] using hopening
        exact (isQueryBound_map_iff (adversary.opening privateState state) (fun _ => ())
          terminalRemaining _ _).mp hmapped
      exact adversary.probEvent_terminalExecution_le_of_freshTarget model nodeBudget
        checkpointCount verifierOverhead terminalRemaining terminalCached privateState state cache
        log
        (adversary.terminalExecution_isTotalQueryBound_of_opening model privateState state
          terminalRemaining verifierOverhead hopening' hverifier)
        (adversary.terminalFreshTargetProperty_of_openingEvidence model
          (adversary.terminalOpeningEvidenceProperty model))
        hstateLog hno hcacheBound hlogCache hcacheLog hstable hnodeBudget hcheckpointCount)
    rounds queryBound
    (by
      rw [adversary.runCommitmentsThenAccounting_opening_eq_prefixProgram rounds]
      exact hquery)
    hnodes hcheckpoints
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_runFromEmptyThen, probEvent_map]
  simpa [Function.comp_def] using hraw

/-- Finite-opening specialization of the global theorem. At most `openingCount` claims whose
paths cost at most `perClaim` yield the explicit verifier overhead
`openingCount * perClaim`. -/
theorem anyCheckpointDisagreement_rom_bound_of_prefixQueryBound_and_openingCountBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount openingCount perClaim perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hopeningCount : adversary.HasOpeningCountBound openingCount)
    (hperClaim : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount
        (openingCount * perClaim) queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config rounds adversary queryBound
    nodeBudget checkpointCount (openingCount * perClaim) perCheckpoint hquery
    (adversary.hasVerifierQueryBound_of_openingCountBound openingCount perClaim
      hopeningCount hperClaim)
    hconfig hnodes hcheckpoints

/-- Exact structural specialization of the global theorem: one checkpoint per round and at most
`perCheckpoint` nodes contributed by each selected configuration. -/
theorem anyCheckpointDisagreement_rom_bound_uniformShape
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      (multiCheckpointROMErrorNumerator (rounds * perCheckpoint) rounds verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config rounds adversary
    queryBound (rounds * perCheckpoint) rounds verifierOverhead perCheckpoint hquery hverifier
    hconfig le_rfl le_rfl

/-- Per-phase query bounds imply a whole-adversary query bound by summing the commitment schedule
and terminal opening bound. -/
theorem anyCheckpointDisagreement_rom_bound_of_phaseQueryBounds
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  exact anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config rounds
    adversary
    (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound)
    nodeBudget checkpointCount verifierOverhead perCheckpoint
    (adversary.isAdversaryPrefixQueryBound_of_schedule rounds phaseQueryBound terminalQueryBound
      hcommit hopening)
    hverifier hconfig hnodes hcheckpoints

/-- Finite-opening specialization: at most `openingCount` claims, each with path cost at most
`perClaim`, gives verifier overhead `openingCount * perClaim`. -/
theorem anyCheckpointDisagreement_rom_bound_of_phaseQueryBounds_and_openingCountBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (phaseQueryBound : ℕ → ℕ)
    (terminalQueryBound nodeBudget checkpointCount openingCount perClaim perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState)
        (phaseQueryBound round))
    (hopening : ∀ privateState extractorState,
      IsTotalQueryBound (adversary.opening privateState extractorState) terminalQueryBound)
    (hopeningCount : adversary.HasOpeningCountBound openingCount)
    (hperClaim : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount (openingCount * perClaim)
        (commitmentQueryBudget phaseQueryBound rounds 0 + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  anyCheckpointDisagreement_rom_bound_of_phaseQueryBounds model config rounds adversary
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount (openingCount * perClaim)
    perCheckpoint hcommit hopening
    (adversary.hasVerifierQueryBound_of_openingCountBound openingCount perClaim
      hopeningCount hperClaim)
    hconfig hnodes hcheckpoints

/-- The textbook two-branch event as a direct corollary of the global-adversarial-`q` owner
theorem. -/
theorem openingOrEqualRootDisagreement_rom_bound_of_prefixQueryBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasOpeningOrEqualRootDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  openingOrEqualRootDisagreement_bound_of_anyCheckpointExtractionDisagreement_bound model config
    rounds adversary _
    (anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config rounds adversary
      queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hquery hverifier
      hconfig hnodes hcheckpoints)

/-- Coarse binomial relaxation of the global-adversarial-`q` theorem. -/
theorem anyCheckpointDisagreement_binomial_bound_of_prefixQueryBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      ((queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine (anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config
    rounds adversary queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hquery
    hverifier hconfig hnodes hcheckpoints).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiCheckpointROMErrorNumerator_le_coarse nodeBudget checkpointCount
    verifierOverhead queryBound

/-- Quadratic relaxation of the global-adversarial-`q` theorem. -/
theorem anyCheckpointDisagreement_quadratic_bound_of_prefixQueryBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : adversary.IsAdversaryPrefixQueryBound rounds queryBound)
    (hverifier : adversary.HasVerifierQueryBound verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
      extractabilityGame model config rounds adversary] ≤
      ((queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine (anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config
    rounds adversary queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hquery
    hverifier hconfig hnodes hcheckpoints).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiCheckpointROMErrorNumerator_le_quadratic nodeBudget checkpointCount
    verifierOverhead queryBound

end MerkleTreeMultiExtractability
