/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Stateful
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Potential
import Mathlib.Data.Finset.Card

/-!
# Shared Target Sets for Stateful Merkle Extraction

This module gives semantic content to the shared target count used by multi-extractability
potentials. It flattens the labels reached by every heterogeneous commitment checkpoint into one
finite set. Two independent bounds are proved:

* the set contains no more labels than the sum of the checkpoint tree-node budgets;
* when all checkpoint logs are prefixes of one cache-backed cumulative log, the set contains at
  most two children per populated query key plus one root per checkpoint.

The combined result is the minimum of those two bounds. Duplicated labels across checkpoints are
deduplicated by `Finset`, so the result accounts for a genuine shared target union rather than a
sum of per-checkpoint target counts.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree

universe u v w

variable {Cfg : Type u} {Query : Type v} {Address : Type w} {Y : Type}

/-- Labels reached by extraction at one typed configuration checkpoint. -/
def Checkpoint.targets [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) : List Y :=
  MerkleTreeExtractor.targets view (config.skeleton tag) (config.addressKey tag)
    checkpoint.cumulativeLog checkpoint.root

/-- Flatten the target lists of heterogeneous checkpoints in commitment order. -/
def targetsOfCheckpoints [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (checkpoints : List (AnyCheckpoint Cfg Query Address Y config)) : List Y :=
  checkpoints.flatMap fun checkpoint => checkpoint.2.targets view

/-- Sum of the full-tree node budgets for a heterogeneous checkpoint list. -/
def nodeBudgetOfCheckpoints {config : Configuration Cfg Address}
    (checkpoints : List (AnyCheckpoint Cfg Query Address Y config)) : ℕ :=
  (checkpoints.map fun checkpoint =>
    2 * (config.skeleton checkpoint.1).leafCount - 1).sum

/-- Flatten every target reached at a checkpoint recorded by an extractor state. -/
def ExtractorState.targetList [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : List Y :=
  targetsOfCheckpoints view state.checkpoints

/-- Deduplicated union of all labels reached by recorded checkpoint extractions. -/
def ExtractorState.targetSet [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Finset Y :=
  (state.targetList view).toFinset

/-- Sum of the full-tree node budgets of all recorded checkpoints. -/
def ExtractorState.totalNodeBudget {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : ℕ :=
  nodeBudgetOfCheckpoints state.checkpoints

/-- Flattening target lists preserves the sum of the individual full-tree node bounds. -/
theorem targetsOfCheckpoints_length_le_nodeBudget [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (checkpoints : List (AnyCheckpoint Cfg Query Address Y config)) :
    (targetsOfCheckpoints view checkpoints).length ≤ nodeBudgetOfCheckpoints checkpoints := by
  induction checkpoints with
  | nil => simp [targetsOfCheckpoints, nodeBudgetOfCheckpoints]
  | cons checkpoint checkpoints ih =>
      obtain ⟨tag, checkpoint⟩ := checkpoint
      simp only [targetsOfCheckpoints, List.flatMap_cons, List.length_append,
        nodeBudgetOfCheckpoints, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (MerkleTreeExtractor.targets_length_le view (config.skeleton tag)
          (config.addressKey tag) checkpoint.cumulativeLog checkpoint.root)
        ih

/-- The shared target union contains no more labels than the sum of checkpoint tree nodes. -/
theorem ExtractorState.targetSet_card_le_totalNodeBudget
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) :
    (state.targetSet view).card ≤ state.totalNodeBudget :=
  (List.toFinset_card_le (state.targetList view)).trans
    (targetsOfCheckpoints_length_le_nodeBudget view state.checkpoints)

/-! ## Shared cache and query-key support -/

/-- Roots contributed independently by the recorded commitment checkpoints. -/
def ExtractorState.checkpointRoots [DecidableEq Y]
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Finset Y :=
  (state.checkpoints.map fun checkpoint => checkpoint.2.root).toFinset

/-- The two ordered child labels exposed by a finite set of complete query keys. -/
def queryChildren [DecidableEq Query] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y) (keys : Finset Query) : Finset Y :=
  keys.image (fun query => (view.input query).1) ∪
    keys.image (fun query => (view.input query).2)

/-- Finite semantic support supplied by checkpoint roots and the children of populated keys. -/
def ExtractorState.targetSupport [DecidableEq Query] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y) (keys : Finset Query)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Finset Y :=
  state.checkpointRoots ∪ queryChildren view keys

/-- Invariants connecting the checkpoint history to one shared cumulative log, cache, and finite
set of populated keys. `log_agrees` rules out counting a syntactic log entry whose key is absent
from the cache; `mem_keys_iff` makes `keys.card` the semantic populated-key count. -/
structure ExtractorState.CacheKeysInvariant [DecidableEq Query]
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (cache : Query → Option Y) (keys : Finset Query) : Prop where
  /-- Every checkpoint log is a prefix of the shared cumulative log. -/
  checkpointLogsPrefixCumulativeLog : state.CheckpointLogsPrefixCumulativeLog
  /-- Every cumulative log entry agrees with the shared cache. -/
  log_agrees : ∀ query response,
    (⟨query, response⟩ : (_query : Query) × Y) ∈ state.cumulativeLog →
    cache query = some response
  /-- `keys` contains exactly the populated cache domain. -/
  mem_keys_iff : ∀ query, query ∈ keys ↔ ∃ response, cache query = some response

/-- Checkpoint roots contribute at most one support element per checkpoint. -/
theorem ExtractorState.checkpointRoots_card_le [DecidableEq Y]
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) :
    state.checkpointRoots.card ≤ state.checkpoints.length := by
  calc
    state.checkpointRoots.card ≤
        (state.checkpoints.map fun checkpoint => checkpoint.2.root).length := by
      exact List.toFinset_card_le _
    _ = state.checkpoints.length := by simp

/-- Complete query keys contribute at most two child labels each. -/
theorem queryChildren_card_le [DecidableEq Query] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y) (keys : Finset Query) :
    (queryChildren view keys).card ≤ 2 * keys.card := by
  calc
    (queryChildren view keys).card ≤
        (keys.image fun query => (view.input query).1).card +
          (keys.image fun query => (view.input query).2).card := by
      rw [queryChildren]
      exact Finset.card_union_le _ _
    _ ≤ keys.card + keys.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * keys.card := by omega

/-- The cache-backed finite support has size at most two children per populated query key plus
one root per checkpoint. -/
theorem ExtractorState.targetSupport_card_le [DecidableEq Query] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y) (keys : Finset Query)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) :
    (state.targetSupport view keys).card ≤ 2 * keys.card + state.checkpoints.length := by
  calc
    (state.targetSupport view keys).card ≤
        state.checkpointRoots.card + (queryChildren view keys).card := by
      rw [ExtractorState.targetSupport]
      exact Finset.card_union_le _ _
    _ ≤ state.checkpoints.length + 2 * keys.card :=
      Nat.add_le_add state.checkpointRoots_card_le (queryChildren_card_le view keys)
    _ = 2 * keys.card + state.checkpoints.length := by omega

/-- Under the shared cache/key/log invariants, every reached target is either its checkpoint root
or one of the two children of a populated complete-query key. -/
theorem ExtractorState.targetSet_subset_targetSupport
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (cache : Query → Option Y) (keys : Finset Query)
    (hsupport : state.CacheKeysInvariant cache keys) :
    state.targetSet view ⊆ state.targetSupport view keys := by
  intro target htarget
  simp only [ExtractorState.targetSet, List.mem_toFinset, ExtractorState.targetList,
    targetsOfCheckpoints, List.mem_flatMap] at htarget
  obtain ⟨checkpoint, hcheckpoint, htarget⟩ := htarget
  obtain ⟨tag, checkpoint⟩ := checkpoint
  rcases MerkleTreeExtractor.mem_targets_root_or_log_input view
      (config.skeleton tag) (config.addressKey tag) checkpoint.cumulativeLog
      checkpoint.root htarget with hroot | ⟨entry, hentry, hleft | hright⟩
  · subst target
    apply Finset.mem_union_left
    simp only [ExtractorState.checkpointRoots, List.mem_toFinset, List.mem_map]
    exact ⟨⟨tag, checkpoint⟩, hcheckpoint, rfl⟩
  · have hprefix := hsupport.checkpointLogsPrefixCumulativeLog tag checkpoint hcheckpoint
    rcases hprefix with ⟨suffix, hsuffix⟩
    have hentryState : entry ∈ state.cumulativeLog := by
      rw [← hsuffix]
      exact List.mem_append_left suffix hentry
    have hcache := hsupport.log_agrees entry.1 entry.2 hentryState
    have hkey : entry.1 ∈ keys := (hsupport.mem_keys_iff entry.1).2 ⟨entry.2, hcache⟩
    rw [hleft]
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨entry.1, hkey, rfl⟩
  · have hprefix := hsupport.checkpointLogsPrefixCumulativeLog tag checkpoint hcheckpoint
    rcases hprefix with ⟨suffix, hsuffix⟩
    have hentryState : entry ∈ state.cumulativeLog := by
      rw [← hsuffix]
      exact List.mem_append_left suffix hentry
    have hcache := hsupport.log_agrees entry.1 entry.2 hentryState
    have hkey : entry.1 ∈ keys := (hsupport.mem_keys_iff entry.1).2 ⟨entry.2, hcache⟩
    rw [hright]
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨entry.1, hkey, rfl⟩

/-- Shared query support bounds the semantic target union by two children per populated key plus
one root per checkpoint. -/
theorem ExtractorState.targetSet_card_le_querySupport
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (cache : Query → Option Y) (keys : Finset Query)
    (hsupport : state.CacheKeysInvariant cache keys) :
    (state.targetSet view).card ≤ 2 * keys.card + state.checkpoints.length :=
  (Finset.card_mono (state.targetSet_subset_targetSupport view cache keys hsupport)).trans
    (state.targetSupport_card_le view keys)

/-- The semantic shared target union satisfies the minimum of the structural node budget and
shared query-support budget. -/
theorem ExtractorState.targetSet_card_le_min
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (cache : Query → Option Y) (keys : Finset Query)
    (hsupport : state.CacheKeysInvariant cache keys) :
    (state.targetSet view).card ≤
      min state.totalNodeBudget (2 * keys.card + state.checkpoints.length) :=
  (Nat.le_min).2 ⟨ExtractorState.targetSet_card_le_totalNodeBudget view state,
    ExtractorState.targetSet_card_le_querySupport view state cache keys hsupport⟩

/-- Semantic form of the shared target-count function used by the safe online potential. -/
theorem ExtractorState.targetSet_card_le_sharedExtractedLabelCountBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (cache : Query → Option Y) (keys : Finset Query)
    (hsupport : state.CacheKeysInvariant cache keys) :
    (state.targetSet view).card ≤
      sharedExtractedLabelCountBound state.totalNodeBudget state.checkpoints.length keys.card := by
  simpa only [sharedExtractedLabelCountBound] using
    state.targetSet_card_le_min view cache keys hsupport

/-! ## Live targets under a transient log -/

/-- Targets of all already-recorded roots, re-extracted against an explicit current log. Unlike
`ExtractorState.targetSet`, this set may grow during a later commitment phase and is the online
monitor state used before sampling the next fresh response. -/
def ExtractorState.liveTargetList [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y) : List Y :=
  state.checkpoints.flatMap fun checkpoint =>
    MerkleTreeExtractor.targets view (config.skeleton checkpoint.1)
      (config.addressKey checkpoint.1) log checkpoint.2.root

/-- Deduplicated live target union at an explicit current log. -/
def ExtractorState.liveTargetSet [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y) : Finset Y :=
  (state.liveTargetList view log).toFinset

/-- Live targets remain bounded by the sum of the full node budgets of recorded checkpoints. -/
theorem ExtractorState.liveTargetSet_card_le_totalNodeBudget
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y) :
    (state.liveTargetSet view log).card ≤ state.totalNodeBudget := by
  calc
    (state.liveTargetSet view log).card ≤ (state.liveTargetList view log).length :=
      List.toFinset_card_le _
    _ ≤ state.totalNodeBudget := by
      unfold ExtractorState.liveTargetList ExtractorState.totalNodeBudget
        nodeBudgetOfCheckpoints
      induction state.checkpoints with
      | nil => simp
      | cons checkpoint checkpoints ih =>
          obtain ⟨tag, checkpoint⟩ := checkpoint
          simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
          exact Nat.add_le_add
            (MerkleTreeExtractor.targets_length_le view (config.skeleton tag)
              (config.addressKey tag) log checkpoint.root) ih

/-- Cache/key facts for one transient online log. -/
structure LogCacheKeysInvariant [DecidableEq Query]
    (log : MerkleTreeExtractor.QueryLog Query Y)
    (cache : Query → Option Y) (keys : Finset Query) : Prop where
  /-- Every observed entry agrees with the current cache. -/
  log_agrees : ∀ query response,
    (⟨query, response⟩ : (_query : Query) × Y) ∈ log →
    cache query = some response
  /-- Every populated cache entry has already appeared in the online log. -/
  cache_covered : ∀ query response, cache query = some response →
    (⟨query, response⟩ : (_query : Query) × Y) ∈ log
  /-- The finite key set is exactly the populated cache domain. -/
  mem_keys_iff : ∀ query, query ∈ keys ↔ ∃ response, cache query = some response

/-- Minimal online support needed to bound targets. The key set may overapproximate the populated
cache domain; this is the form preserved by a syntactic `cached` upper bound. -/
structure LogCacheKeysCover [DecidableEq Query]
    (log : MerkleTreeExtractor.QueryLog Query Y)
    (cache : Query → Option Y) (keys : Finset Query) : Prop where
  /-- Every observed entry agrees with the current cache. -/
  log_agrees : ∀ query response,
    (⟨query, response⟩ : (_query : Query) × Y) ∈ log →
    cache query = some response
  /-- Every populated cache key belongs to the finite support. -/
  cache_keys : ∀ query, cache query ≠ none → query ∈ keys

/-- Exact online cache/log/key invariants imply the weaker finite-support cover. -/
theorem LogCacheKeysInvariant.toCover [DecidableEq Query]
    {log : MerkleTreeExtractor.QueryLog Query Y}
    {cache : Query → Option Y} {keys : Finset Query}
    (hsupport : LogCacheKeysInvariant log cache keys) :
    LogCacheKeysCover log cache keys where
  log_agrees := hsupport.log_agrees
  cache_keys query hquery := by
    apply (hsupport.mem_keys_iff query).2
    exact Option.ne_none_iff_exists'.mp hquery

/-- Every live target is a recorded root or a child of a currently populated query key. -/
theorem ExtractorState.liveTargetSet_subset_targetSupport
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y)
    (cache : Query → Option Y) (keys : Finset Query)
    (hsupport : LogCacheKeysCover log cache keys) :
    state.liveTargetSet view log ⊆ state.targetSupport view keys := by
  intro target htarget
  simp only [ExtractorState.liveTargetSet, List.mem_toFinset,
    ExtractorState.liveTargetList, List.mem_flatMap] at htarget
  obtain ⟨checkpoint, hcheckpoint, htarget⟩ := htarget
  obtain ⟨tag, checkpoint⟩ := checkpoint
  rcases MerkleTreeExtractor.mem_targets_root_or_log_input view
      (config.skeleton tag) (config.addressKey tag) log checkpoint.root htarget with
    hroot | ⟨entry, hentry, hleft | hright⟩
  · subst target
    apply Finset.mem_union_left
    simp only [ExtractorState.checkpointRoots, List.mem_toFinset, List.mem_map]
    exact ⟨⟨tag, checkpoint⟩, hcheckpoint, rfl⟩
  · have hcache := hsupport.log_agrees entry.1 entry.2 hentry
    have hkey : entry.1 ∈ keys := hsupport.cache_keys entry.1 (by simp [hcache])
    rw [hleft]
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨entry.1, hkey, rfl⟩
  · have hcache := hsupport.log_agrees entry.1 entry.2 hentry
    have hkey : entry.1 ∈ keys := hsupport.cache_keys entry.1 (by simp [hcache])
    rw [hright]
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨entry.1, hkey, rfl⟩

/-- Online semantic target bound used by the checkpoint-aware stopping recurrence. -/
theorem ExtractorState.liveTargetSet_card_le_sharedExtractedLabelCountBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y)
    (cache : Query → Option Y) (keys : Finset Query)
    (hsupport : LogCacheKeysInvariant log cache keys) :
    (state.liveTargetSet view log).card ≤
      sharedExtractedLabelCountBound state.totalNodeBudget state.checkpoints.length keys.card := by
  apply (Nat.le_min).2
  refine ⟨state.liveTargetSet_card_le_totalNodeBudget view log, ?_⟩
  exact (Finset.card_mono
    (state.liveTargetSet_subset_targetSupport view log cache keys hsupport.toCover)).trans
      (state.targetSupport_card_le view keys)

/-- Online target bound from a finite cache-key cover of cardinality at most `cached`. This is the
form consumed by adaptive-prefix induction, where the exact cache domain need not itself be
enumerable. -/
theorem ExtractorState.liveTargetSet_card_le_sharedExtractedLabelCountBound_of_cover
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y)
    (cache : Query → Option Y) (keys : Finset Query) (cached : ℕ)
    (hkeys : keys.card ≤ cached)
    (hsupport : LogCacheKeysCover log cache keys) :
    (state.liveTargetSet view log).card ≤
      sharedExtractedLabelCountBound state.totalNodeBudget state.checkpoints.length cached := by
  apply (Nat.le_min).2
  refine ⟨state.liveTargetSet_card_le_totalNodeBudget view log, ?_⟩
  exact (Finset.card_mono
    (state.liveTargetSet_subset_targetSupport view log cache keys hsupport)).trans
      ((state.targetSupport_card_le view keys).trans (by gcongr))

end MerkleTreeMultiExtractability
