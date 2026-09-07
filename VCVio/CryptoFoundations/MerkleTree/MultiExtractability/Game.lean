/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.BatchExtractability
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Sequential

/-!
# Stateful Merkle Multi-Extractability Game

This module supplies the executable shared-ROM game connecting sequential commitment checkpoints
to dynamically selected pruned batch openings. The terminal adversary returns claims without
acceptance bits; `verifyOpeningClaims` computes every bit through the query-parametric addressed
batch verifier. The terminal adversary log is snapshotted before honest verification, keeping
terminal checkpoint evolution and fresh verifier queries as separate proof obligations.

The executable game currently lives in `Type 0`, matching the probability and total-query-bound
infrastructure it uses. The structural `Configuration`, checkpoint, and extractor-state APIs remain
universe-polymorphic; lifting this game layer is an explicit interface generalization, not an
implicit security assumption.

As in `SequentialCommitter.runCommitments`, `rounds` is a fixed public horizon. Quantifying the
resulting bound over `rounds` supports an adaptive stopping policy through a uniform maximum, but
the executable game does not itself let the adversary choose when to stop.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleSpec OracleComp BinaryTree InductiveMerkleTree

variable {Cfg Query Address Y : Type}

/-- One dynamically typed opening claim against a purported commitment checkpoint. Membership of
the checkpoint in the recorded state is checked by the failure predicate, rather than trusted as
part of this adversary-controlled package. -/
structure OpeningClaim (Query : Type) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- Configuration tag determining the claim's skeleton and address map. -/
  tag : Cfg
  /-- Claimed commitment checkpoint. -/
  checkpoint : Checkpoint Query Y config tag
  /-- Nonempty intrinsic pruned opening. -/
  opening : BatchOpening Y (config.skeleton tag)

/-- Honest verifier cost for one claim, measured by visited internal nodes. -/
def OpeningClaim.queryCount {config : Configuration Cfg Address}
    (claim : OpeningClaim Query Y config) : ℕ :=
  claim.opening.proof.queryCount

/-- Total honest verifier cost for a list of claims. -/
def claimsQueryCount {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config)) : ℕ :=
  (claims.map OpeningClaim.queryCount).sum

/-- Verify every claim sequentially through the complete query model and preserve its dependent
configuration tag in the resulting attempts. -/
def verifyOpeningClaims [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address} :
    List (OpeningClaim Query Y config) →
      OracleComp (Query →ₒ Y)
        (List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
  | [] => pure []
  | claim :: claims => do
      let accepted ← MerkleTreeBatchExtractability.verifyOpening model
        (config.addressKey claim.tag) claim.checkpoint.root claim.opening
      let attempts ← verifyOpeningClaims model claims
      return ⟨claim.tag, {
        checkpoint := claim.checkpoint
        opening := claim.opening
        accepted }⟩ :: attempts

/-- The honest verifier list is bounded by the sum of the proof-dependent structural counts.
This is the safe full-batch overhead; a later disagreement witness may specialize each
accepted failure to one selected path. -/
theorem verifyOpeningClaims_isTotalQueryBound [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config)) :
    IsTotalQueryBound (verifyOpeningClaims model claims) (claimsQueryCount claims) := by
  induction claims with
  | nil => trivial
  | cons claim claims ih =>
      simp only [verifyOpeningClaims, claimsQueryCount, List.map_cons, List.sum_cons]
      exact isTotalQueryBound_bind
        (n₁ := claim.queryCount) (n₂ := claimsQueryCount claims)
        (MerkleTreeBatchExtractability.verifyOpening_isTotalQueryBound model
          (config.addressKey claim.tag) claim.checkpoint.root claim.opening)
        fun _ => isTotalQueryBound_bind (n₁ := claimsQueryCount claims) (n₂ := 0)
          ih fun _ => trivial

/-- Every accepted attempt retained by a supported list-verifier run carries the exact
cache-level execution tree of its originating batch opening in the final shared cache. -/
theorem batchProofEvaluatesInCache_of_mem_support_verifyOpeningClaims
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config))
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (hrun : (attempts, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle (verifyOpeningClaims model claims)).run cache₀))
    (tag : Cfg) (attempt : EvaluatedOpeningClaim Query Y config tag)
    (hmem : (⟨tag, attempt⟩ : AnyEvaluatedOpeningClaim Cfg Query Address Y config) ∈ attempts)
    (haccepted : attempt.accepted = true) :
    MerkleTreeBatchExtractability.BatchProofEvaluatesInCache model (config.addressKey tag) cache₁
      attempt.opening.values attempt.opening.proof attempt.checkpoint.root := by
  induction claims generalizing cache₀ cache₁ attempts with
  | nil =>
      simp only [verifyOpeningClaims, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hrun
      injection hrun with hattempts _
      subst attempts
      simp at hmem
  | cons claim claims ih =>
      simp only [verifyOpeningClaims, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hrun
      obtain ⟨⟨accepted, cacheVerify⟩, hverify, hrun⟩ := hrun
      obtain ⟨⟨rest, cacheRest⟩, hrest, hfinal⟩ := hrun
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hfinal
      injection hfinal with hattempts hcache
      subst attempts
      subst cache₁
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        have haccepted' : accepted = true := by simpa using haccepted
        subst accepted
        have hbatch :=
          MerkleTreeBatchExtractability.batchProofEvaluatesInCache_of_mem_support_verifyOpening
            model (config.addressKey claim.tag) claim.checkpoint.root claim.opening
              cache₀ cacheVerify hverify
        exact MerkleTreeBatchExtractability.batchProofEvaluatesInCache_mono model
          (config.addressKey claim.tag)
          (simulateQ_cachingOracle_cache_le (verifyOpeningClaims model claims)
            cacheVerify (rest, cacheRest) hrest)
          claim.opening.values claim.opening.proof claim.checkpoint.root hbatch
      · exact ih cacheVerify cacheRest rest hrest htail

/-- Sequential multi-commitment adversary with a terminal, adaptively chosen list of batch
opening claims. The private commitment state remains abstract. -/
structure Adversary (Cfg : Type) (Query : Type) (Address : Type) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- Adaptive sequential commitment strategy. -/
  committer : SequentialCommitter Cfg Query Y
  /-- Produce terminal claims after observing the final private and extractor states. -/
  opening : committer.State → ExtractorState Cfg Query Address Y config →
    OracleComp (Query →ₒ Y) (List (OpeningClaim Query Y config))

/-- Observable result of the stateful game. `terminalSuffix` excludes honest verifier queries. -/
structure Transcript (Cfg : Type) (Query : Type) (Address : Type) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- All immutable commitment checkpoints. -/
  extractorState : ExtractorState Cfg Query Address Y config
  /-- Claims paired with honestly computed acceptance bits. -/
  attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)
  /-- Query-log segment produced by the terminal opening adversary. -/
  terminalSuffix : MerkleTreeExtractor.QueryLog Query Y

/-- Oracle syntax of the multi-extractability game before installing random-function semantics. -/
def extractabilityInner [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) := do
  let (privateState, extractorState) ← adversary.committer.runFromEmpty config rounds
  let (claims, terminalSuffix) ← (adversary.opening privateState extractorState).withQueryLog
  let attempts ← verifyOpeningClaims model claims
  return { extractorState, attempts, terminalSuffix }

/-- Shared-cache random-oracle interpretation of the stateful game. All commitments, terminal
opening work, and honest verification use one lazy random function. -/
def extractabilityGame [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) :=
  (Query →ₒ Y).withCacheOverlay ∅
    (extractabilityInner model config rounds adversary)

/-- A transcript contains an opening, equal-root, or terminal-evolution disagreement. -/
def Transcript.HasAnyCheckpointExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (transcript : Transcript Cfg Query Address Y config) : Prop :=
  AnyCheckpointExtractionDisagreement model.view transcript.extractorState transcript.attempts
    transcript.terminalSuffix

/-- A transcript contains an opening or equal-root extraction disagreement. -/
def Transcript.HasOpeningOrEqualRootDisagreement [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (transcript : Transcript Cfg Query Address Y config) : Prop :=
  OpeningOrEqualRootDisagreement model.view transcript.extractorState transcript.attempts

/-- Opening or equal-root disagreement is a checkpoint extraction disagreement. -/
theorem Transcript.HasOpeningOrEqualRootDisagreement.toHasAnyCheckpointExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (transcript : Transcript Cfg Query Address Y config)
    (h : Transcript.HasOpeningOrEqualRootDisagreement model transcript) :
    Transcript.HasAnyCheckpointExtractionDisagreement model transcript :=
  OpeningOrEqualRootDisagreement.toAnyCheckpointExtractionDisagreement model.view
    transcript.extractorState transcript.attempts transcript.terminalSuffix h

/-- Probability of the public textbook event is at most probability of the strongest proof event. -/
theorem prob_hasOpeningOrEqualRootDisagreement_le_hasAnyCheckpointExtractionDisagreement
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    Pr[ Transcript.HasOpeningOrEqualRootDisagreement model |
      extractabilityGame model config rounds adversary] ≤
        Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
          extractabilityGame model config rounds adversary] :=
  _root_.probEvent_mono
    (mx := extractabilityGame model config rounds adversary)
    (fun transcript _ h =>
      Transcript.HasOpeningOrEqualRootDisagreement.toHasAnyCheckpointExtractionDisagreement
        model transcript h)

/-- Any quantitative theorem for the strongest event immediately yields the same bound for the
weaker textbook event. Downstream corollaries should use this theorem rather than repeat the event
decomposition. -/
theorem openingOrEqualRootDisagreement_bound_of_anyCheckpointExtractionDisagreement_bound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) (bound : ENNReal)
    (hstrong :
      Pr[ Transcript.HasAnyCheckpointExtractionDisagreement model |
        extractabilityGame model config rounds adversary] ≤ bound) :
    Pr[ Transcript.HasOpeningOrEqualRootDisagreement model |
      extractabilityGame model config rounds adversary] ≤ bound :=
  (prob_hasOpeningOrEqualRootDisagreement_le_hasAnyCheckpointExtractionDisagreement
    model config rounds adversary).trans hstrong

end MerkleTreeMultiExtractability
