/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Targets

/-!
# Resource Bounds for Merkle Multi-Extractability

The strongest game keeps dependent per-checkpoint shapes and proof-dependent verifier counts.
This module derives fixed scalar bounds needed by probability theorems and then exposes common
uniform-shape/finite-opening relaxations as corollaries.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree InductiveMerkleTree OracleComp

variable {Cfg Query Address Y : Type}

/-- Full node budget of one configuration-tagged binary skeleton in the raw-leaf model. -/
def Configuration.nodeBudget (config : Configuration Cfg Address) (tag : Cfg) : ℕ :=
  2 * (config.skeleton tag).leafCount - 1

/-- Recording one checkpoint adds exactly that configuration's full-tree node budget. -/
@[simp]
theorem ExtractorState.totalNodeBudget_record
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).totalNodeBudget =
      state.totalNodeBudget + config.nodeBudget tag := by
  simp [ExtractorState.totalNodeBudget, nodeBudgetOfCheckpoints,
    Configuration.nodeBudget]

/-- Cumulative-log recording has the same exact resource increment. -/
@[simp]
theorem ExtractorState.totalNodeBudget_recordCumulative
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (tag : Cfg) (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.recordCumulative tag cumulativeLog root).totalNodeBudget =
      state.totalNodeBudget + config.nodeBudget tag := by
  simp [ExtractorState.totalNodeBudget, nodeBudgetOfCheckpoints,
    Configuration.nodeBudget]

/-- If every configuration has node budget at most `perCheckpoint`, a checkpoint list has total
budget at most its length times `perCheckpoint`. -/
theorem nodeBudgetOfCheckpoints_le_length_mul
    {config : Configuration Cfg Address}
    (checkpoints : List (AnyCheckpoint Cfg Query Address Y config))
    (perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint) :
    nodeBudgetOfCheckpoints checkpoints ≤ checkpoints.length * perCheckpoint := by
  induction checkpoints with
  | nil => simp [nodeBudgetOfCheckpoints]
  | cons checkpoint checkpoints ih =>
      obtain ⟨tag, checkpoint⟩ := checkpoint
      simp only [nodeBudgetOfCheckpoints, List.map_cons, List.sum_cons, List.length_cons]
      have htag := hconfig tag
      unfold Configuration.nodeBudget at htag
      calc
        2 * (config.skeleton tag).leafCount - 1 + nodeBudgetOfCheckpoints checkpoints ≤
            perCheckpoint + checkpoints.length * perCheckpoint :=
          Nat.add_le_add htag ih
        _ = (checkpoints.length + 1) * perCheckpoint := by
          rw [Nat.add_mul]
          omega

/-- State-level uniform per-checkpoint node bound. -/
theorem ExtractorState.totalNodeBudget_le_checkpointCount_mul
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint) :
    state.totalNodeBudget ≤ state.checkpoints.length * perCheckpoint :=
  nodeBudgetOfCheckpoints_le_length_mul state.checkpoints perCheckpoint hconfig

/-- Supported sequential executions inherit the deterministic `rounds * perCheckpoint` node
budget. This supplies a transcript-independent numerator input. -/
theorem SequentialCommitter.runFromEmpty_totalNodeBudget_le
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support (committer.runFromEmpty config rounds)) :
    result.2.totalNodeBudget ≤ rounds * perCheckpoint := by
  calc
    result.2.totalNodeBudget ≤ result.2.checkpoints.length * perCheckpoint :=
      result.2.totalNodeBudget_le_checkpointCount_mul perCheckpoint hconfig
    _ = rounds * perCheckpoint := by
      rw [committer.runFromEmpty_checkpoint_count config rounds result hresult]

/-- An arbitrary supported sequential suffix adds at most `rounds * perCheckpoint` nodes to its
initial extractor state. This additive form is the resource invariant used by phase induction. -/
theorem SequentialCommitter.runCommitments_totalNodeBudget_le_add
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (rounds firstRound : ℕ)
    (state : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (result : committer.State × ExtractorState Cfg Query Address Y config)
    (hresult : result ∈ support
      (committer.runCommitments rounds firstRound state extractorState)) :
    result.2.totalNodeBudget ≤
      extractorState.totalNodeBudget + rounds * perCheckpoint := by
  induction rounds generalizing firstRound state extractorState result with
  | zero =>
      simp only [SequentialCommitter.runCommitments, mem_support_pure_iff] at hresult
      subst result
      simp
  | succ rounds ih =>
      simp only [SequentialCommitter.runCommitments, mem_support_bind_iff] at hresult
      obtain ⟨phaseResult, _hphase, hrest⟩ := hresult
      obtain ⟨⟨tag, root, nextState⟩, phaseLog⟩ := phaseResult
      have htail := ih (firstRound + 1) nextState
        (extractorState.record tag phaseLog root) result hrest
      calc
        result.2.totalNodeBudget ≤
            (extractorState.record tag phaseLog root).totalNodeBudget +
              rounds * perCheckpoint := htail
        _ = extractorState.totalNodeBudget + config.nodeBudget tag +
              rounds * perCheckpoint := by rw [ExtractorState.totalNodeBudget_record]
        _ ≤ extractorState.totalNodeBudget + perCheckpoint +
              rounds * perCheckpoint := by gcongr; exact hconfig tag
        _ = extractorState.totalNodeBudget + (rounds + 1) * perCheckpoint := by
          rw [Nat.add_mul]
          omega

/-- A pruned proof never makes more verifier queries than the internal-node count of its
skeleton. -/
theorem OpeningClaim.queryCount_le_leafCount_sub_one
    {config : Configuration Cfg Address}
    (claim : OpeningClaim Query Y config) :
    claim.queryCount ≤ (config.skeleton claim.tag).leafCount - 1 :=
  claim.opening.proof.queryCount_le_leafCount_sub_one

/-- Uniform per-configuration verifier bound for a list of claims. -/
theorem claimsQueryCount_le_length_mul
    {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config)) (perClaim : ℕ)
    (hconfig : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim) :
    claimsQueryCount claims ≤ claims.length * perClaim := by
  induction claims with
  | nil => simp [claimsQueryCount]
  | cons claim claims ih =>
      simp only [claimsQueryCount, List.map_cons, List.sum_cons, List.length_cons]
      have hclaim := (claim.queryCount_le_leafCount_sub_one).trans (hconfig claim.tag)
      calc
        claim.queryCount + claimsQueryCount claims ≤
            perClaim + claims.length * perClaim := Nat.add_le_add hclaim ih
        _ = (claims.length + 1) * perClaim := by
          rw [Nat.add_mul]
          omega

/-- If the terminal adversary returns at most `openingCount` claims, their full-batch verifier
overhead is at most `openingCount * perClaim`. -/
theorem claimsQueryCount_le_openingCount_mul
    {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config)) (openingCount perClaim : ℕ)
    (hcount : claims.length ≤ openingCount)
    (hconfig : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim) :
    claimsQueryCount claims ≤ openingCount * perClaim :=
  (claimsQueryCount_le_length_mul claims perClaim hconfig).trans
    (Nat.mul_le_mul_right perClaim hcount)

/-- Exact syntactic resource predicate for the entire executable inner game. A security theorem
may use this conservative single budget (including honest verification), or refine it into an
adversarial budget plus a separately justified `claimsQueryCount` overhead. -/
def Adversary.IsFullGameQueryBound [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds queryBound : ℕ)
    (adversary : Adversary Cfg Query Address Y config) : Prop :=
  IsTotalQueryBound (extractabilityInner model config rounds adversary) queryBound

/-- All adversarial oracle work—sequential commitments plus terminal opening production—while
excluding honest `verifyOpeningClaims` queries. -/
def Adversary.prefixProgram
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) (rounds : ℕ) :
    OracleComp (Query →ₒ Y) Unit := do
  let (privateState, extractorState) ← adversary.committer.runFromEmpty config rounds
  let _claims ← adversary.opening privateState extractorState
  pure ()

/-- Primary adversarial query-budget predicate for the refined `q` plus
verifier-overhead theorem. -/
def Adversary.IsAdversaryPrefixQueryBound
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) (rounds queryBound : ℕ) : Prop :=
  IsTotalQueryBound (adversary.prefixProgram rounds) queryBound

/-- Uniform support-wise verifier overhead. This hypothesis is necessary because a terminal
adversary can output an arbitrarily long pure claim list without making any oracle query.

The bound quantifies over every well-typed private and extractor state, including states
unreachable from `SequentialCommitter.runFromEmpty`, so it is stronger than the executable theorem
needs. A reachability-restricted predicate is the natural weakening if this uniform form is too
restrictive. -/
def Adversary.HasVerifierQueryBound
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) (verifierBound : ℕ) : Prop :=
  ∀ privateState extractorState claims,
    claims ∈ support (adversary.opening privateState extractorState) →
    claimsQueryCount claims ≤ verifierBound

/-- Support-wise cap on the number of terminal opening claims emitted by the adversary.

The cap quantifies over every well-typed private and extractor state, including states unreachable
from `SequentialCommitter.runFromEmpty`, so it is stronger than the executable theorem needs. A
reachability-restricted predicate is the natural weakening if this uniform form is too
restrictive. -/
def Adversary.HasOpeningCountBound
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config) (openingCount : ℕ) : Prop :=
  ∀ privateState extractorState claims,
    claims ∈ support (adversary.opening privateState extractorState) →
    claims.length ≤ openingCount

/-- A support-wise opening-count cap and a uniform per-configuration path bound produce the
verifier-overhead predicate consumed by the executable security theorem. -/
theorem Adversary.hasVerifierQueryBound_of_openingCountBound
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (openingCount perClaim : ℕ)
    (hcount : adversary.HasOpeningCountBound openingCount)
    (hconfig : ∀ tag, (config.skeleton tag).leafCount - 1 ≤ perClaim) :
    adversary.HasVerifierQueryBound (openingCount * perClaim) := by
  intro privateState extractorState claims hclaims
  exact claimsQueryCount_le_openingCount_mul claims openingCount perClaim
    (hcount privateState extractorState claims hclaims) hconfig

end MerkleTreeMultiExtractability
