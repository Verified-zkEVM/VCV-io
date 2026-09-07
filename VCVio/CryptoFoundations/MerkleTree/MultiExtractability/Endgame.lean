/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.ExtractionKernel
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Disagreement
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game

/-!
# Deterministic endgame for stateful Merkle multi-extractability

This module closes the deterministic part of the multi-extractability argument. It retains the
cache evidence that a game transcript's Boolean acceptance bits omit. For every recorded
checkpoint, an invariant supplies the exact cache represented by its cumulative log and its
inclusion in the terminal cache. For every accepted opening disagreement, it supplies the selected
typed leaf and addressed single path generated from the pruned batch proof, together with the
final-cache chain consumed by `fresh_extractedTarget_of_extractor_disagreement`.

Under terminal extraction stability, the equal-root checkpoint branch and checkpoint-to-terminal
branch are impossible. The accepted-opening branch yields either a collision already present in
its checkpoint cache or a concrete checkpoint extractor target added by a fresh terminal-cache
key. Assuming checkpoint collision-freedom removes the first alternative. No probability
statement appears here.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree InductiveMerkleTree OracleComp OracleSpec

variable {Cfg Query Address Y : Type}
variable [DecidableEq Address] [DecidableEq Y]

/-- A cache snapshot for every dependently tagged checkpoint. Only recorded checkpoints are
constrained by `EndgameInvariant`. -/
abbrev CheckpointCacheAssignment (config : Configuration Cfg Address) :=
  (tag : Cfg) → Checkpoint Query Y config tag → (Query →ₒ Y).QueryCache

/-- Single-path evidence erased by storing only an acceptance bit in `EvaluatedOpeningClaim`.
`chain` is
the semantic consequence of shared-cache acceptance; `disagrees` connects that actual accepted
path to checkpoint extraction.  No unused pure hash algebra is retained in this interface. -/
structure OpeningKernelEvidence
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (attempt : EvaluatedOpeningClaim Query Y config tag)
    (terminalCache : (Query →ₒ Y).QueryCache) where
  index : SkeletonLeafIndex (config.skeleton tag)
  selected : attempt.opening.selector.get index = true
  proof : List.Vector Y index.depth
  chain : MerkleTreeExtractability.ChainInCache model (config.addressKey tag) terminalCache
    (selectedValueAt attempt.opening.values index selected) attempt.checkpoint.root index proof
  disagrees :
    some (selectedValueAt attempt.opening.values index selected) ≠
        (Checkpoint.extractedTree model.view attempt.checkpoint).get index.toNodeIndex ∨
      proof.toList.map some ≠
        (generateProof (Checkpoint.extractedTree model.view attempt.checkpoint) index).toList

/-- Deterministic hypotheses needed after the game produces a transcript. Prefix and membership
premises are explicit: no adversary-supplied checkpoint is silently trusted. -/
structure EndgameInvariant
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (terminalCache : (Query →ₒ Y).QueryCache)
    (cacheAt : CheckpointCacheAssignment (Query := Query) (Y := Y) config) : Prop where
  log_agrees : ∀ tag checkpoint,
    (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈ state.checkpoints →
    ∀ entry ∈ checkpoint.cumulativeLog,
      cacheAt tag checkpoint entry.1 = some entry.2
  cache_covered : ∀ tag checkpoint,
    (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈ state.checkpoints →
    ∀ input value, cacheAt tag checkpoint input = some value →
      ∃ entry ∈ checkpoint.cumulativeLog, entry.1 = input ∧ entry.2 = value
  cache_mono : ∀ tag checkpoint,
    (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈ state.checkpoints →
    cacheAt tag checkpoint ≤ terminalCache
  terminal_stable : ∀ tag checkpoint,
    (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈ state.checkpoints →
    Checkpoint.extractedTree model.view checkpoint =
      MerkleTreeExtractor.tree model.view (config.skeleton tag) (config.addressKey tag)
        (state.terminalLog terminalSuffix) checkpoint.root
  opening_kernel : ∀ tag attempt,
    (⟨tag, attempt⟩ : AnyEvaluatedOpeningClaim Cfg Query Address Y config) ∈ attempts →
    (⟨tag, attempt.checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
      state.checkpoints →
    AcceptedOpeningDisagreement model.view attempt →
      Nonempty (OpeningKernelEvidence model attempt terminalCache)

/-- Some recorded checkpoint cache already contains a response collision. -/
def HasCheckpointCacheCollision
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (cacheAt : CheckpointCacheAssignment (Query := Query) (Y := Y) config) : Prop :=
  ∃ tag checkpoint,
    (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈ state.checkpoints ∧
      CacheHasCollision (cacheAt tag checkpoint)

/-- A recorded accepted attempt exposes a checkpoint extractor target added under a fresh key by
the terminal cache. Checkpoint and attempt membership remain part of the witness. -/
def HasFreshCheckpointTarget
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalCache : (Query →ₒ Y).QueryCache)
    (cacheAt : CheckpointCacheAssignment (Query := Query) (Y := Y) config) : Prop :=
  ∃ tag attempt,
    (⟨tag, attempt⟩ : AnyEvaluatedOpeningClaim Cfg Query Address Y config) ∈ attempts ∧
    (⟨tag, attempt.checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
      state.checkpoints ∧
    ∃ target ∈ MerkleTreeExtractability.extractedTargets model
        (config.skeleton tag) (config.addressKey tag)
        attempt.checkpoint.cumulativeLog attempt.checkpoint.root,
      MerkleTreeExtractability.CacheAddsValue
        (cacheAt tag attempt.checkpoint) terminalCache target

variable
  {config : Configuration Cfg Address}
  {model : MerkleTreeExtractability.NodeQueryModel Query Address Y}
  {state : ExtractorState Cfg Query Address Y config}
  {attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)}
  {terminalSuffix : MerkleTreeExtractor.QueryLog Query Y}
  {terminalCache : (Query →ₒ Y).QueryCache}
  {cacheAt : CheckpointCacheAssignment (Query := Query) (Y := Y) config}

/-- Checkpoint collision-freedom gives response injectivity on its cumulative log. -/
theorem EndgameInvariant.responseInjectiveOn
    (invariant : EndgameInvariant model state attempts terminalSuffix terminalCache cacheAt)
    {tag : Cfg} {checkpoint : Checkpoint Query Y config tag}
    (hcheckpoint : (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
      state.checkpoints)
    (hno : ¬ CacheHasCollision (cacheAt tag checkpoint)) :
    MerkleTreeExtractor.ResponseInjectiveOn checkpoint.cumulativeLog :=
  MerkleTreeExtractability.responseInjectiveOn_of_cache_noCollision
    checkpoint.cumulativeLog (cacheAt tag checkpoint)
    (invariant.log_agrees tag checkpoint hcheckpoint) hno

/-- Terminal stability rules out the equal-root checkpoint branch. -/
theorem EndgameInvariant.not_equalRootExtractionDisagreement
    (invariant : EndgameInvariant model state attempts terminalSuffix terminalCache cacheAt) :
    ¬ HasEqualRootExtractionDisagreement model.view state := by
  rintro ⟨tag, left, right, hleft, hright, hroot, hne⟩
  apply hne
  rw [invariant.terminal_stable tag left hleft,
    invariant.terminal_stable tag right hright, hroot]

/-- Terminal stability rules out the checkpoint-to-terminal branch. -/
theorem EndgameInvariant.not_checkpointTerminalExtractionDisagreement
    (invariant : EndgameInvariant model state attempts terminalSuffix terminalCache cacheAt) :
    ¬ HasCheckpointTerminalExtractionDisagreement model.view state terminalSuffix := by
  rintro ⟨tag, checkpoint, hcheckpoint, hne⟩
  exact hne (invariant.terminal_stable tag checkpoint hcheckpoint)

/-- Every strong three-branch failure yields a checkpoint-cache collision or a concrete fresh
extractor target. Equal-root and terminal-evolution branches are discharged by stability. -/
theorem failure_implies_checkpointCollision_or_freshTarget
    (invariant : EndgameInvariant model state attempts terminalSuffix terminalCache cacheAt)
    (hfailure : AnyCheckpointExtractionDisagreement model.view state attempts terminalSuffix) :
    HasCheckpointCacheCollision state cacheAt ∨
      HasFreshCheckpointTarget model state attempts terminalCache cacheAt := by
  classical
  rcases hfailure with hopening | hequalRoot | hterminal
  · obtain ⟨tag, attempt, hattempt, hcheckpoint, hdisagreement⟩ := hopening
    by_cases hcollision : CacheHasCollision (cacheAt tag attempt.checkpoint)
    · exact Or.inl ⟨tag, attempt.checkpoint, hcheckpoint, hcollision⟩
    · obtain ⟨evidence⟩ :=
        invariant.opening_kernel tag attempt hattempt hcheckpoint hdisagreement
      obtain ⟨target, htarget, hfresh⟩ :=
        MerkleTreeExtractability.fresh_extractedTarget_of_extractor_disagreement
          model (config.addressKey tag) evidence.index attempt.checkpoint.cumulativeLog
          (cacheAt tag attempt.checkpoint) terminalCache attempt.checkpoint.root
          (selectedValueAt attempt.opening.values evidence.index evidence.selected) evidence.proof
          (invariant.log_agrees tag attempt.checkpoint hcheckpoint)
          (invariant.cache_covered tag attempt.checkpoint hcheckpoint)
          hcollision (invariant.cache_mono tag attempt.checkpoint hcheckpoint)
          evidence.chain evidence.disagrees
      exact Or.inr ⟨tag, attempt, hattempt, hcheckpoint, target, htarget, hfresh⟩
  · exact (invariant.not_equalRootExtractionDisagreement hequalRoot).elim
  · exact (invariant.not_checkpointTerminalExtractionDisagreement hterminal).elim

/-- With collision-free checkpoint caches, strong failure has only the fresh-target outcome. -/
theorem failure_implies_freshTarget_of_noCheckpointCollision
    (invariant : EndgameInvariant model state attempts terminalSuffix terminalCache cacheAt)
    (hno : ∀ tag checkpoint,
      (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈ state.checkpoints →
      ¬ CacheHasCollision (cacheAt tag checkpoint))
    (hfailure : AnyCheckpointExtractionDisagreement model.view state attempts terminalSuffix) :
    HasFreshCheckpointTarget model state attempts terminalCache cacheAt := by
  rcases failure_implies_checkpointCollision_or_freshTarget invariant hfailure with
    hcollision | hfresh
  · obtain ⟨tag, checkpoint, hcheckpoint, hcollision⟩ := hcollision
    exact (hno tag checkpoint hcheckpoint hcollision).elim
  · exact hfresh

/-- Transcript specialization of the strong deterministic endgame. -/
theorem Transcript.HasAnyCheckpointExtractionDisagreement.implies_freshTarget
    {config : Configuration Cfg Address}
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (transcript : Transcript Cfg Query Address Y config)
    (terminalCache : (Query →ₒ Y).QueryCache)
    (cacheAt : CheckpointCacheAssignment (Query := Query) (Y := Y) config)
    (invariant : EndgameInvariant model transcript.extractorState transcript.attempts
      transcript.terminalSuffix terminalCache cacheAt)
    (hno : ∀ tag checkpoint,
      (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
        transcript.extractorState.checkpoints →
      ¬ CacheHasCollision (cacheAt tag checkpoint))
    (hfailure : Transcript.HasAnyCheckpointExtractionDisagreement model transcript) :
    HasFreshCheckpointTarget model transcript.extractorState transcript.attempts
      terminalCache cacheAt :=
  failure_implies_freshTarget_of_noCheckpointCollision invariant hno hfailure

/-- Public/textbook failure inherits the same deterministic fresh-target conclusion. -/
theorem Transcript.HasOpeningOrEqualRootDisagreement.implies_freshTarget
    {config : Configuration Cfg Address}
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (transcript : Transcript Cfg Query Address Y config)
    (terminalCache : (Query →ₒ Y).QueryCache)
    (cacheAt : CheckpointCacheAssignment (Query := Query) (Y := Y) config)
    (invariant : EndgameInvariant model transcript.extractorState transcript.attempts
      transcript.terminalSuffix terminalCache cacheAt)
    (hno : ∀ tag checkpoint,
      (⟨tag, checkpoint⟩ : AnyCheckpoint Cfg Query Address Y config) ∈
        transcript.extractorState.checkpoints →
      ¬ CacheHasCollision (cacheAt tag checkpoint))
    (hfailure : Transcript.HasOpeningOrEqualRootDisagreement model transcript) :
    HasFreshCheckpointTarget model transcript.extractorState transcript.attempts
      terminalCache cacheAt :=
  Transcript.HasAnyCheckpointExtractionDisagreement.implies_freshTarget model transcript
    terminalCache cacheAt invariant hno
    (Transcript.HasOpeningOrEqualRootDisagreement.toHasAnyCheckpointExtractionDisagreement
      model transcript hfailure)

end MerkleTreeMultiExtractability
