/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractability
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Addressed
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Disagreement
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Opening
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.QueryBound
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.ToSingle

/-!
# Query-parametric batch openings for Merkle extractability

This module defines the batch-opening surface used by Merkle multi-extractability.  The
authentication data is the intrinsic path-pruned `InductiveMerkleTree.BatchProof`; no tuple of
single authentication paths is introduced.  Verification uses the same
`MerkleTreeExtractability.NodeQueryModel` as the single-opening game, so ordinary and addressed
Merkle trees are specializations of one computation.

The probability theorem is deliberately downstream of this module.  Here the dependent opening
package, query-parametric verifier, and two-phase adversary are executable definitions.  Keeping
this layer deterministic makes the later event decomposition state its security boundary
explicitly.
-/

@[expose] public section

namespace MerkleTreeBatchExtractability

open OracleSpec OracleComp BinaryTree InductiveMerkleTree

universe u

variable {Query Y : Type} {Address : Type u}

/-- Recompute the putative root of a path-pruned batch opening through the complete queries
specified by `model`.  Internal positions are mapped to their actual oracle addresses by
`addressKey`. -/
def getPutativeBatchRootM (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) :
    {s : Skeleton} → (addressKey : SkeletonInternalIndex s → Address) →
      {selector : LeafData Bool s} → SelectedValues Y selector → BatchProof Y selector →
        OracleComp (Query →ₒ Y) Y
  | _, addressKey, _, values, proof =>
      AddressedMerkleTree.getPutativeBatchRootAddressedM
        (fun position left right => liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey position) (left, right))))
        values proof

/-- Verify one packaged path-pruned batch opening against a claimed root. -/
def verifyOpening [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (root : Y)
    (opening : InductiveMerkleTree.BatchOpening Y s) :
    OracleComp (Query →ₒ Y) Bool :=
  AddressedMerkleTree.verifyBatchProofAddressedM
    (fun position left right => liftM ((Query →ₒ Y).query
      (model.mkQuery (addressKey position) (left, right))))
    opening.values root opening.proof

/-- Honest batch verification is bounded by the exact number of internal nodes visited by the
pruned proof. This is the safe verifier overhead used until a disagreement-witness theorem permits
specialization to one selected path. -/
theorem verifyOpening_isTotalQueryBound [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (root : Y)
    (opening : InductiveMerkleTree.BatchOpening Y s) :
    IsTotalQueryBound (verifyOpening model addressKey root opening) opening.proof.queryCount := by
  apply AddressedMerkleTree.isTotalQueryBound_verifyBatchProofAddressedM
  intro position left right
  exact (isQueryBound_query_iff
    (model.mkQuery (addressKey position) (left, right)) 1 _ _).mpr Nat.one_pos

/-- The cache-level execution tree of one addressed pruned batch proof.  It records exactly the
intermediate roots returned by the verifier and the final-cache entry for every internal node.
Unlike a pure hash function, this relation does not need a default response for queries that the
verifier never makes. -/
def BatchProofEvaluatesInCache
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) :
    {s : Skeleton} → (addressKey : SkeletonInternalIndex s → Address) →
      (cache : (Query →ₒ Y).QueryCache) → {selector : LeafData Bool s} →
      SelectedValues Y selector → BatchProof Y selector → Y → Prop
  | _, _, _, _, values, .leaf, root => root = values
  | _, addressKey, cache, _, values, .internalBoth leftProof rightProof, root =>
      ∃ leftRoot rightRoot,
        BatchProofEvaluatesInCache model (fun position => addressKey (.ofLeft position)) cache
          values.1 leftProof leftRoot ∧
        BatchProofEvaluatesInCache model (fun position => addressKey (.ofRight position)) cache
          values.2 rightProof rightRoot ∧
        cache (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root
  | _, addressKey, cache, _, values, .pruneRight _ rightRoot leftProof, root =>
      ∃ leftRoot,
        BatchProofEvaluatesInCache model (fun position => addressKey (.ofLeft position)) cache
          values.1 leftProof leftRoot ∧
        cache (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root
  | _, addressKey, cache, _, values, .pruneLeft _ leftRoot rightProof, root =>
      ∃ rightRoot,
        BatchProofEvaluatesInCache model (fun position => addressKey (.ofRight position)) cache
          values.2 rightProof rightRoot ∧
        cache (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root

/-- Total addressed hash function obtained by completing a partial cache with an arbitrary
default. Results below only evaluate it at queries certified by `BatchProofEvaluatesInCache`, so
the choice of default is semantically irrelevant. -/
def cacheNodeHash
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (cache : (Query →ₒ Y).QueryCache) (default : Y) :
    SkeletonInternalIndex s → Y → Y → Y :=
  fun position left right =>
    (cache (model.mkQuery (addressKey position) (left, right))).getD default

/-- Replaying a certified cache-level batch run through the cache-completed pure hash recovers
the recorded root. -/
theorem getPutativeBatchRootAddressedWithHash_cacheNodeHash_eq_of_batchProofEvaluatesInCache
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (cache : (Query →ₒ Y).QueryCache) (default : Y)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (root : Y)
    (hrun : BatchProofEvaluatesInCache model addressKey cache values proof root) :
    AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
      (cacheNodeHash model addressKey cache default) values proof = root := by
  induction proof generalizing root with
  | leaf => exact hrun.symm
  | internalBoth leftProof rightProof ihLeft ihRight =>
      obtain ⟨leftRoot, rightRoot, hleft, hright, hroot⟩ := hrun
      have hleftRoot := ihLeft
        (fun position => addressKey (.ofLeft position)) values.1 leftRoot hleft
      have hrightRoot := ihRight
        (fun position => addressKey (.ofRight position)) values.2 rightRoot hright
      simp only [AddressedMerkleTree.getPutativeBatchRootAddressedWithHash]
      change cacheNodeHash model addressKey cache default .ofInternal
        (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
          (cacheNodeHash model (fun position => addressKey (.ofLeft position)) cache default)
          values.1 leftProof)
        (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
          (cacheNodeHash model (fun position => addressKey (.ofRight position)) cache default)
          values.2 rightProof) = root
      rw [hleftRoot, hrightRoot]
      simp [cacheNodeHash, hroot]
  | pruneRight hright rightRoot leftProof ih =>
      obtain ⟨leftRoot, hleft, hroot⟩ := hrun
      have hleftRoot := ih
        (fun position => addressKey (.ofLeft position)) values.1 leftRoot hleft
      simp only [AddressedMerkleTree.getPutativeBatchRootAddressedWithHash]
      change cacheNodeHash model addressKey cache default .ofInternal
        (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
          (cacheNodeHash model (fun position => addressKey (.ofLeft position)) cache default)
          values.1 leftProof) rightRoot = root
      rw [hleftRoot]
      simp [cacheNodeHash, hroot]
  | pruneLeft hleft leftRoot rightProof ih =>
      obtain ⟨rightRoot, hright, hroot⟩ := hrun
      have hrightRoot := ih
        (fun position => addressKey (.ofRight position)) values.2 rightRoot hright
      simp only [AddressedMerkleTree.getPutativeBatchRootAddressedWithHash]
      change cacheNodeHash model addressKey cache default .ofInternal leftRoot
        (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
          (cacheNodeHash model (fun position => addressKey (.ofRight position)) cache default)
          values.2 rightProof) = root
      rw [hrightRoot]
      simp [cacheNodeHash, hroot]
/-- A batch execution tree remains valid when the cache grows. -/
theorem batchProofEvaluatesInCache_mono
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    {cache₁ cache₂ : (Query →ₒ Y).QueryCache} (hle : cache₁ ≤ cache₂)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (root : Y)
    (hrun : BatchProofEvaluatesInCache model addressKey cache₁ values proof root) :
    BatchProofEvaluatesInCache model addressKey cache₂ values proof root := by
  induction proof generalizing root with
  | leaf => exact hrun
  | internalBoth leftProof rightProof ihLeft ihRight =>
      obtain ⟨leftRoot, rightRoot, hleft, hright, hroot⟩ := hrun
      exact ⟨leftRoot, rightRoot,
        ihLeft (fun position => addressKey (.ofLeft position)) values.1 leftRoot hleft,
        ihRight (fun position => addressKey (.ofRight position)) values.2 rightRoot hright,
        hle hroot⟩
  | pruneRight hright rightRoot leftProof ih =>
      obtain ⟨leftRoot, hleft, hroot⟩ := hrun
      exact ⟨leftRoot,
        ih (fun position => addressKey (.ofLeft position)) values.1 leftRoot hleft,
        hle hroot⟩
  | pruneLeft hleft leftRoot rightProof ih =>
      obtain ⟨rightRoot, hright, hroot⟩ := hrun
      exact ⟨rightRoot,
        ih (fun position => addressKey (.ofRight position)) values.2 rightRoot hright,
        hle hroot⟩

/-- Every supported addressed batch-root computation is represented by
`BatchProofEvaluatesInCache` in its final cache. -/
theorem batchProofEvaluatesInCache_of_mem_support_getPutativeBatchRootM
    [DecidableEq Query]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (root : Y)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (getPutativeBatchRootM model addressKey values proof)).run cache₀)) :
    BatchProofEvaluatesInCache model addressKey cache₁ values proof root := by
  induction proof generalizing root cache₀ cache₁ with
  | leaf =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM, simulateQ_pure,
        StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      exact congrArg Prod.fst hmem
  | internalBoth leftProof rightProof ihLeft ihRight =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM,
        simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨leftRoot, cacheLeft⟩, hleft, hmem⟩ := hmem
      obtain ⟨⟨rightRoot, cacheRight⟩, hright, hhash⟩ := hmem
      have hentry : cache₁
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root :=
        OracleComp.cachingOracle_query_caches
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))
          cacheRight root cache₁ (by
            simpa only [HasQuery.instOfMonadLift_query,
              cachingOracle.simulateQ_query] using hhash)
      have hleftMono : cacheLeft ≤ cache₁ :=
        (simulateQ_cachingOracle_cache_le
          (getPutativeBatchRootM model
            (fun position => addressKey (.ofRight position)) values.2 rightProof)
          cacheLeft (rightRoot, cacheRight) hright).trans
          (simulateQ_cachingOracle_cache_le
            (liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
            cacheRight (root, cache₁) hhash)
      have hrightMono : cacheRight ≤ cache₁ :=
        simulateQ_cachingOracle_cache_le
          (liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
          cacheRight (root, cache₁) hhash
      exact ⟨leftRoot, rightRoot,
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofLeft position)) hleftMono values.1 leftProof leftRoot
          (ihLeft (fun position => addressKey (.ofLeft position)) values.1 leftRoot
            cache₀ cacheLeft hleft),
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofRight position)) hrightMono values.2 rightProof rightRoot
          (ihRight (fun position => addressKey (.ofRight position)) values.2 rightRoot
            cacheLeft cacheRight hright),
        hentry⟩
  | pruneRight hright rightRoot leftProof ih =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM,
        simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨leftRoot, cacheLeft⟩, hleft, hhash⟩ := hmem
      have hentry : cache₁
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root :=
        OracleComp.cachingOracle_query_caches
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))
          cacheLeft root cache₁ (by
            simpa only [HasQuery.instOfMonadLift_query,
              cachingOracle.simulateQ_query] using hhash)
      have hmono : cacheLeft ≤ cache₁ :=
        simulateQ_cachingOracle_cache_le
          (liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
          cacheLeft (root, cache₁) hhash
      exact ⟨leftRoot,
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofLeft position)) hmono values.1 leftProof leftRoot
          (ih (fun position => addressKey (.ofLeft position)) values.1 leftRoot
            cache₀ cacheLeft hleft),
        hentry⟩
  | pruneLeft hleft leftRoot rightProof ih =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM,
        simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨rightRoot, cacheRight⟩, hright, hhash⟩ := hmem
      have hentry : cache₁
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root :=
        OracleComp.cachingOracle_query_caches
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))
          cacheRight root cache₁ (by
            simpa only [HasQuery.instOfMonadLift_query,
              cachingOracle.simulateQ_query] using hhash)
      have hmono : cacheRight ≤ cache₁ :=
        simulateQ_cachingOracle_cache_le
          (liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
          cacheRight (root, cache₁) hhash
      exact ⟨rightRoot,
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofRight position)) hmono values.2 rightProof rightRoot
          (ih (fun position => addressKey (.ofRight position)) values.2 rightRoot
            cache₀ cacheRight hright),
        hentry⟩

/-- Every supported successful batch-verifier run has a cache-level execution tree rooted at the
claimed commitment. -/
theorem batchProofEvaluatesInCache_of_mem_support_verifyOpening
    [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (root : Y)
    (opening : InductiveMerkleTree.BatchOpening Y s)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (verifyOpening model addressKey root opening)).run cache₀)) :
    BatchProofEvaluatesInCache model addressKey cache₁ opening.values opening.proof root := by
  unfold verifyOpening AddressedMerkleTree.verifyBatchProofAddressedM at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨putativeRoot, cacheMid⟩, hroot, hfinal⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at hfinal
  obtain ⟨haccepted, rfl⟩ := hfinal
  have hputative : putativeRoot = root := by
    simpa only [beq_iff_eq] using haccepted.symm
  subst root
  exact batchProofEvaluatesInCache_of_mem_support_getPutativeBatchRootM model addressKey
    opening.values opening.proof putativeRoot cache₀ cache₁ hroot

/-- The canonical addressed batch-to-single path, instantiated with the final cache's completed
hash function, is a chain in that cache. -/
theorem chainInCache_batchToSingleProofAddressed_cacheNodeHash
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (cache : (Query →ₒ Y).QueryCache) (default : Y)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (batchProof : BatchProof Y selector) (root : Y)
    (hrun : BatchProofEvaluatesInCache model addressKey cache values batchProof root)
    (index : SkeletonLeafIndex s) (selected : selector.get index = true) :
    MerkleTreeExtractability.ChainInCache model addressKey cache
      (selectedValueAt values index selected) root index
      (batchToSingleProofAddressed (cacheNodeHash model addressKey cache default)
        values batchProof index selected) := by
  induction batchProof generalizing root with
  | leaf =>
      cases index with
      | ofLeaf =>
          simpa only [BatchProofEvaluatesInCache, selectedValueAt,
            MerkleTreeExtractability.ChainInCache] using hrun.symm
  | internalBoth leftProof rightProof ihLeft ihRight =>
      obtain ⟨leftRoot, rightRoot, hleft, hright, hroot⟩ := hrun
      cases index with
      | ofLeft index =>
          simp only [batchToSingleProofAddressed]
          have hsibling :=
            getPutativeBatchRootAddressedWithHash_cacheNodeHash_eq_of_batchProofEvaluatesInCache
              model (fun position => addressKey (.ofRight position)) cache default
              values.2 rightProof rightRoot hright
          have hsibling' :
              AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
                (fun address => cacheNodeHash model addressKey cache default (.ofRight address))
                values.2 rightProof = rightRoot := by
            change AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
              (cacheNodeHash model (fun position => addressKey (.ofRight position)) cache default)
              values.2 rightProof = rightRoot
            exact hsibling
          rw [hsibling']
          have hfn :
              (fun address => cacheNodeHash model addressKey cache default (.ofLeft address)) =
                cacheNodeHash model (fun position => addressKey (.ofLeft position))
                  cache default := by rfl
          rw [hfn]
          refine ⟨leftRoot, hroot, ?_⟩
          convert
            (ihLeft (fun position => addressKey (.ofLeft position)) values.1 leftRoot hleft index
              (by simpa using selected)) using 1 <;>
            simp only [selectedValueAt, List.Vector.tail_cons]
      | ofRight index =>
          simp only [batchToSingleProofAddressed]
          have hsibling :=
            getPutativeBatchRootAddressedWithHash_cacheNodeHash_eq_of_batchProofEvaluatesInCache
              model (fun position => addressKey (.ofLeft position)) cache default
              values.1 leftProof leftRoot hleft
          have hsibling' :
              AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
                (fun address => cacheNodeHash model addressKey cache default (.ofLeft address))
                values.1 leftProof = leftRoot := by
            change AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
              (cacheNodeHash model (fun position => addressKey (.ofLeft position)) cache default)
              values.1 leftProof = leftRoot
            exact hsibling
          rw [hsibling']
          have hfn :
              (fun address => cacheNodeHash model addressKey cache default (.ofRight address)) =
                cacheNodeHash model (fun position => addressKey (.ofRight position))
                  cache default := by rfl
          rw [hfn]
          refine ⟨rightRoot, hroot, ?_⟩
          convert
            (ihRight (fun position => addressKey (.ofRight position)) values.2
              rightRoot hright index
              (by simpa using selected)) using 1 <;>
            simp only [selectedValueAt, List.Vector.tail_cons]
  | pruneRight hright rightRoot leftProof ih =>
      obtain ⟨leftRoot, hleft, hroot⟩ := hrun
      cases index with
      | ofLeft index =>
          simp only [batchToSingleProofAddressed]
          have hfn :
              (fun address => cacheNodeHash model addressKey cache default (.ofLeft address)) =
                cacheNodeHash model (fun position => addressKey (.ofLeft position))
                  cache default := by rfl
          rw [hfn]
          refine ⟨leftRoot, hroot, ?_⟩
          convert
            (ih (fun position => addressKey (.ofLeft position)) values.1 leftRoot hleft index
              (by simpa using selected)) using 1 <;>
            simp only [selectedValueAt, List.Vector.tail_cons]
      | ofRight index =>
          exact absurd (LeafData.anySelected_of_get index (by simpa using selected))
            (by simp [hright])
  | pruneLeft hleft leftRoot rightProof ih =>
      obtain ⟨rightRoot, hright, hroot⟩ := hrun
      cases index with
      | ofRight index =>
          simp only [batchToSingleProofAddressed]
          have hfn :
              (fun address => cacheNodeHash model addressKey cache default (.ofRight address)) =
                cacheNodeHash model (fun position => addressKey (.ofRight position))
                  cache default := by rfl
          rw [hfn]
          refine ⟨rightRoot, hroot, ?_⟩
          convert
            (ih (fun position => addressKey (.ofRight position)) values.2 rightRoot hright index
              (by simpa using selected)) using 1 <;>
            simp only [selectedValueAt, List.Vector.tail_cons]
      | ofLeft index =>
          exact absurd (LeafData.anySelected_of_get index (by simpa using selected))
            (by simp [hleft])

/-- A certified successful batch run is accepted by the pure hash obtained from its final cache. -/
theorem acceptedAddressedWithHash_cacheNodeHash_of_batchProofEvaluatesInCache
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (cache : (Query →ₒ Y).QueryCache) (default root : Y)
    (opening : InductiveMerkleTree.BatchOpening Y s)
    (hrun : BatchProofEvaluatesInCache model addressKey cache opening.values opening.proof root) :
    opening.AcceptedAddressedWithHash (cacheNodeHash model addressKey cache default) root :=
  getPutativeBatchRootAddressedWithHash_cacheNodeHash_eq_of_batchProofEvaluatesInCache
    model addressKey cache default opening.values opening.proof root hrun

/-- A two-phase adversary that commits to a root and later returns a dynamically selected,
path-pruned batch opening. -/
structure Adversary (Query Y : Type) (s : Skeleton) where
  /-- State transferred from the commitment phase to the opening phase. -/
  AuxState : Type
  /-- Produce a claimed Merkle root and continuation state. -/
  commit : OracleComp (Query →ₒ Y) (Y × AuxState)
  /-- Choose the selector, claimed values, and pruned proof after the commitment checkpoint. -/
  opening : AuxState → OracleComp (Query →ₒ Y) (InductiveMerkleTree.BatchOpening Y s)

/-- The adversary's two phases, excluding honest verification, have total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton}
    (adversary : Adversary Query Y s) (qb : ℕ) : Prop :=
  IsTotalQueryBound
    (do
      let (_root, aux) ← adversary.commit
      let _opening ← adversary.opening aux
      pure ())
    qb

/-- The batch-opening syntax and its commitment-phase query log.  This is the deterministic
program underlying the shared-cache ROM game; extraction and the winning event are layered on
top so that neither can be hidden in the adversary interface. -/
def openingInner {s : Skeleton} (adversary : Adversary Query Y s) :
    OracleComp (Query →ₒ Y)
      (Y × adversary.AuxState × (Query →ₒ Y).QueryLog ×
        InductiveMerkleTree.BatchOpening Y s) := do
  let ((root, aux), queryLog) ← adversary.commit.withQueryLog
  let opening ← adversary.opening aux
  return (root, aux, queryLog, opening)

/-! ## Single-commitment batch extraction game -/

/-- The canonical batch opening read from a partial extracted tree, using exactly the selector
chosen by the adversary. Missing nodes remain explicit as `none`; this definition does not fill
or otherwise complete the extractor's output. -/
def extractedOpening {s : Skeleton} (tree : FullData (Option Y) s)
    (opening : InductiveMerkleTree.BatchOpening Y s) :
    InductiveMerkleTree.BatchOpening (Option Y) s where
  selector := opening.selector
  values := selectedValues tree.toLeafData opening.selector
  proof := generateBatchProof tree opening.selector opening.anySelected

/-- The adversary's concrete opening is not the `Option.some` image of the canonical opening
read from the commitment-checkpoint extraction. This is deliberately full-opening disagreement:
both selected leaf values and the entire pruned authentication frontier are covered. -/
def OpeningDisagreesWithTree {s : Skeleton} (opening : InductiveMerkleTree.BatchOpening Y s)
    (tree : FullData (Option Y) s) : Prop :=
  opening.values.map some ≠ (extractedOpening tree opening).values ∨
    opening.proof.map some ≠ (extractedOpening tree opening).proof

/-- Full batch-opening disagreement is witnessed at one selected leaf, either by its claimed
value or by the canonical addressed single path expanded from the pruned proof. The path branch
is independent of consistency between `tree` and `nodeHash`: it follows a stored frontier value
at the first structural proof disagreement. -/
theorem OpeningDisagreesWithTree.exists_selectedValue_or_path_disagreement {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y)
    (opening : InductiveMerkleTree.BatchOpening Y s) (tree : FullData (Option Y) s)
    (hne : OpeningDisagreesWithTree opening tree) :
    ∃ index : SkeletonLeafIndex s, ∃ selected : opening.selector.get index = true,
      some (selectedValueAt opening.values index selected) ≠ tree.get index.toNodeIndex ∨
        (batchToSingleProofAddressed nodeHash opening.values opening.proof
          index selected).toList.map some ≠
          (generateProof tree index).toList := by
  rcases hne with hvalues | hproof
  · obtain ⟨index, selected, hvalue⟩ := exists_selectedValueAt_ne_of_ne
      (opening.values.map some) (extractedOpening tree opening).values hvalues
    refine ⟨index, selected, Or.inl ?_⟩
    simpa only [selectedValueAt_map, extractedOpening,
      selectedValueAt_selectedValues_toLeafData] using hvalue
  · obtain ⟨index, selected, hpath⟩ :=
      exists_batchToSingleProofAddressed_map_some_ne_generateProof
        nodeHash opening.values opening.proof tree (by
          simpa only [extractedOpening] using hproof)
    exact ⟨index, selected, Or.inr hpath⟩

/-- Oracle syntax for the batch extractability experiment. The extractor sees only the query
log at the commitment checkpoint. The opening phase and honest batch verification execute after
that snapshot and therefore cannot retroactively populate the extracted tree. -/
def extractabilityInner [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (adversary : Adversary Query Y s) :
    OracleComp (Query →ₒ Y)
      (Y × adversary.AuxState × InductiveMerkleTree.BatchOpening Y s ×
        FullData (Option Y) s × Bool) := do
  let ((root, aux), queryLog) ← adversary.commit.withQueryLog
  let tree := MerkleTreeExtractor.tree model.view s addressKey queryLog root
  let opening ← adversary.opening aux
  let verified ← verifyOpening model addressKey root opening
  return (root, aux, opening, tree, verified)

/-- The exact public failure event for one commitment and one dynamically selected batch
opening: the opening is accepted but differs from checkpoint extraction. Internal proof events
used to establish a ROM bound are intentionally not conflated with this public definition. -/
def BatchOpeningExtractionFailure {s : Skeleton} {AuxState : Type} :
    Y × AuxState × InductiveMerkleTree.BatchOpening Y s × FullData (Option Y) s × Bool → Prop
  | (_, _, opening, tree, verified) =>
      verified = true ∧ OpeningDisagreesWithTree opening tree

/-- Shared-cache random-oracle batch extractability game. Commitment, opening, and honest
verification use one lazy random function, while extraction remains pinned to the commitment
checkpoint log. -/
def extractabilityGame [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (adversary : Adversary Query Y s) :
    OracleComp (Query →ₒ Y)
      (Y × adversary.AuxState × InductiveMerkleTree.BatchOpening Y s ×
        FullData (Option Y) s × Bool) :=
  (Query →ₒ Y).withCacheOverlay ∅
    (extractabilityInner model addressKey adversary)

end MerkleTreeBatchExtractability
