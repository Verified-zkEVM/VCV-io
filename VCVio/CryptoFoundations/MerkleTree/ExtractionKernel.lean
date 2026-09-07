/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic
public import VCVio.OracleComp.QueryTracking.Collision
public import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Deterministic Merkle extraction kernel

This module owns the query model, cached authentication-chain semantics, and deterministic
disagreement reduction shared by Merkle extractability arguments. Given a collision-free commit
cache, an accepted authentication chain that disagrees with the tree reconstructed from the
commit log must contain a later cache query whose response is one of the reconstructed tree's
labels.

The result is independent of probability bounds and adversary games. It applies to arbitrary full
binary skeletons and arbitrary maps from typed internal positions to oracle addresses; the address
map need not be injective.
-/

@[expose] public section

namespace MerkleTreeExtractability

open List OracleSpec OracleComp BinaryTree InductiveMerkleTree

universe u

variable {Query Y : Type} {Address : Type u}

/-- Complete interface between typed Merkle positions and the homogeneous random-oracle query
type. The extractor consumes `view`; verification issues `mkQuery`. Only the two projection laws
are required, so callers may also issue arbitrary queries outside the constructor's image. -/
structure NodeQueryModel (Query : Type) (Address : Type u) (Y : Type) where
  /-- Project complete oracle queries to the address and ordered children used by extraction. -/
  view : MerkleTreeExtractor.QueryView Query Address Y
  /-- Construct the complete oracle query for one addressed pair of children. -/
  mkQuery : Address → Y × Y → Query
  /-- Constructed queries retain their address exactly. -/
  address_mkQuery : ∀ address input, view.address (mkQuery address input) = address
  /-- Constructed queries retain their ordered child pair exactly. -/
  input_mkQuery : ∀ address input, view.input (mkQuery address input) = input

variable [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]

/-- The labels of the non-dummy nodes that the extractor actually reconstructs. Unlike the full
query log, this list follows only response links reachable from the claimed root. -/
abbrev extractedTargets (model : NodeQueryModel Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (Query →ₒ Y).QueryLog) (root : Y) : List Y :=
  MerkleTreeExtractor.targets model.view s addressKey log root

/-- Verify an opening by issuing the model's complete node query at each typed position. -/
def verifyOpening (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (idx : SkeletonLeafIndex s) (leaf root : Y) (proof : List.Vector Y idx.depth) :
    OracleComp (Query →ₒ Y) Bool := do
  let putativeRoot ← AddressedMerkleTree.getPutativeRootAddressedM
    (fun position left right =>
      liftM ((Query →ₒ Y).query (model.mkQuery (addressKey position) (left, right))))
    idx leaf proof
  return putativeRoot == root

/-- A hash chain interpreted in a shared random-oracle cache. Unlike `ChainInLog`, this predicate
records only the final function graph and therefore identifies cache hits and cache misses with
the same response. -/
def ChainInCache (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (cache : (Query →ₒ Y).QueryCache) (leaf root : Y) :
    (idx : SkeletonLeafIndex s) → List.Vector Y idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : Y,
        cache (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head)) = some root ∧
        ChainInCache model (fun position => addressKey (.ofLeft position))
          cache leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : Y,
        cache (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor)) = some root ∧
        ChainInCache model (fun position => addressKey (.ofRight position))
          cache leaf ancestor idxRight proof.tail

/-- The later phase added a previously uncached query whose answer is `target`. -/
def CacheAddsValue (cache₀ cache₁ : (Query →ₒ Y).QueryCache) (target : Y) : Prop :=
  ∃ input : Query, cache₁ input = some target ∧ cache₀ input = none

omit [DecidableEq Query] [DecidableEq Address] [DecidableEq Y] in
/-- A cache chain remains valid when its cache is extended pointwise. -/
lemma chainInCache_mono (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    {cache₁ cache₂ : (Query →ₒ Y).QueryCache} {root leaf : Y}
    {proof : List.Vector Y idx.depth}
    (hle : cache₁ ≤ cache₂)
    (hchain : ChainInCache model addressKey cache₁ leaf root idx proof) :
    ChainInCache model addressKey cache₂ leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact hchain
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨ancestor, hentry, hrec⟩ := hchain
    exact ⟨ancestor, hle hentry,
      ih (fun position => addressKey (.ofLeft position)) hrec⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, hentry, hrec⟩ := hchain
    exact ⟨ancestor, hle hentry,
      ih (fun position => addressKey (.ofRight position)) hrec⟩

omit [DecidableEq Address] [DecidableEq Y] in
/-- Every supported result of the cached putative-root computation induces a chain in the final
cache from the supplied leaf to that result. -/
lemma chainInCache_of_mem_support_getPutativeRoot
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    (leaf : Y) (proof : List.Vector Y idx.depth) (root : Y)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey position) (left, right))))
          idx leaf proof)).run cache₀)) :
    ChainInCache model addressKey cache₁ leaf root idx proof := by
  induction idx generalizing root cache₀ cache₁ with
  | ofLeaf =>
    simp only [AddressedMerkleTree.getPutativeRootAddressedM,
      simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq] at hmem
    exact hmem.1.symm
  | @ofLeft sl sr idxLeft ih =>
    rw [show AddressedMerkleTree.getPutativeRootAddressedM
        (fun position left right =>
          liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey position) (left, right))))
        (.ofLeft idxLeft) leaf proof =
      AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey (.ofLeft position)) (left, right))))
          idxLeft leaf proof.tail >>= fun ancestor =>
        liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head))) from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁
        (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head)) = some root := by
      exact cachingOracle_query_caches
        (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head))
        cacheMid root cache₁ (by
          simpa only [HasQuery.instOfMonadLift_query, cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le
        (liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head))))
        cacheMid _ hhash
    exact ⟨ancestor, hentry,
      chainInCache_mono model (fun position => addressKey (.ofLeft position)) idxLeft hmono
        (ih (fun position => addressKey (.ofLeft position)) proof.tail ancestor
          cache₀ cacheMid hrec)⟩
  | @ofRight sl sr idxRight ih =>
    rw [show AddressedMerkleTree.getPutativeRootAddressedM
        (fun position left right =>
          liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey position) (left, right))))
        (.ofRight idxRight) leaf proof =
      AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey (.ofRight position)) (left, right))))
          idxRight leaf proof.tail >>= fun ancestor =>
        liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor))) from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁
        (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor)) = some root := by
      exact cachingOracle_query_caches
        (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor))
        cacheMid root cache₁ (by
          simpa only [HasQuery.instOfMonadLift_query, cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le
        (liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor))))
        cacheMid _ hhash
    exact ⟨ancestor, hentry,
      chainInCache_mono model (fun position => addressKey (.ofRight position)) idxRight hmono
        (ih (fun position => addressKey (.ofRight position)) proof.tail ancestor
          cache₀ cacheMid hrec)⟩

omit [DecidableEq Address] in
/-- Every successful supported verifier run induces a chain in its final cache from the claimed
leaf to the accepted root. -/
lemma chainInCache_of_mem_support_verifyOpening
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    (leaf root : Y) (proof : List.Vector Y idx.depth)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (verifyOpening model addressKey idx leaf root proof)).run cache₀)) :
    ChainInCache model addressKey cache₁ leaf root idx proof := by
  unfold verifyOpening at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨putativeRoot, cacheMid⟩, hroot, hfinal⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at hfinal
  obtain ⟨hroot_eq, rfl⟩ := hfinal
  have hputative : putativeRoot = root := by
    simpa only [beq_iff_eq] using hroot_eq.symm
  subst root
  exact chainInCache_of_mem_support_getPutativeRoot model addressKey
    idx leaf proof putativeRoot cache₀ cache₁ hroot

omit [DecidableEq Query] [DecidableEq Y] in
/-- A collision-free cache makes the response projection injective on every log represented by
that cache. -/
lemma responseInjectiveOn_of_cache_noCollision
    (log : (Query →ₒ Y).QueryLog) (cache : (Query →ₒ Y).QueryCache)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hno : ¬ CacheHasCollision cache) :
    MerkleTreeExtractor.ResponseInjectiveOn log := by
  intro entry₁ hentry₁ entry₂ hentry₂ hresponse
  exact cache_lookup_eq_of_noCollision hno (hlogCache entry₁ hentry₁)
    ⟨entry₂.2, hlogCache entry₂ hentry₂, heq_of_eq hresponse.symm⟩

omit [DecidableEq Query] in
/-- If the extractor resolves an internal node's children, its reconstructed tree unfolds to the
two recursively reconstructed child trees. -/
lemma extractor_tree_internal_of_children_eq_some
    (model : NodeQueryModel Query Address Y)
    (left right : Skeleton)
    (addressKey : SkeletonInternalIndex (.internal left right) → Address)
    (log : (Query →ₒ Y).QueryLog) (root leftRoot rightRoot : Y)
    (hchildren : MerkleTreeExtractor.children model.view log (addressKey .ofInternal) root =
      some (leftRoot, rightRoot)) :
    MerkleTreeExtractor.tree model.view (.internal left right) addressKey log root =
      FullData.internal (some root)
        (MerkleTreeExtractor.tree model.view left
          (fun position => addressKey (.ofLeft position)) log leftRoot)
        (MerkleTreeExtractor.tree model.view right
          (fun position => addressKey (.ofRight position)) log rightRoot) := by
  simp [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hchildren]

omit [DecidableEq Query] in
/-- If a collision-free commit transcript's extracted opening disagrees with a later accepted
cache chain, then the later phase added a previously uncached query whose response is one of the
labels reached by extraction from the claimed root. -/
lemma fresh_extractedTarget_of_extractor_disagreement
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (idx : SkeletonLeafIndex s)
    (log : (Query →ₒ Y).QueryLog) (cacheCommit cacheFinal : (Query →ₒ Y).QueryCache)
    (root leaf : Y) (proof : List.Vector Y idx.depth)
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hno : ¬ CacheHasCollision cacheCommit)
    (hmono : cacheCommit ≤ cacheFinal)
    (hchain : ChainInCache model addressKey cacheFinal leaf root idx proof)
    (hdisagree :
      some leaf ≠ (MerkleTreeExtractor.tree model.view s addressKey log root).get
        idx.toNodeIndex ∨
      proof.toList.map some ≠
        (generateProof (MerkleTreeExtractor.tree model.view s addressKey log root) idx).toList) :
    ∃ target ∈ extractedTargets model s addressKey log root,
      CacheAddsValue cacheCommit cacheFinal target := by
  induction idx generalizing root with
  | ofLeaf =>
      simp only [ChainInCache] at hchain
      subst root
      have hleaf :
          some leaf ≠
            (MerkleTreeExtractor.tree model.view .leaf addressKey log leaf).get
              SkeletonLeafIndex.ofLeaf.toNodeIndex :=
        hdisagree.resolve_right (by simp [generateProof])
      exact (hleaf rfl).elim
  | @ofLeft sl sr idxLeft ih =>
      obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
      let query := model.mkQuery (addressKey .ofInternal) (ancestor, proof.head)
      cases hqueryCommit : cacheCommit query with
      | none =>
          exact ⟨root,
            MerkleTreeExtractor.root_mem_targets model.view (.internal sl sr)
              addressKey log root,
            query, hquery, hqueryCommit⟩
      | some value =>
          have hvalueFinal := hmono hqueryCommit
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, hinput, houtput⟩ :=
            hcacheLog query root hqueryCommit
          have hentry' : (⟨entry.1, root⟩ : (_query : Query) × Y) ∈ log := by
            convert hentry using 1
            exact Sigma.ext rfl (heq_of_eq houtput.symm)
          have haddress : model.view.address entry.1 = addressKey .ofInternal := by
            rw [hinput, model.address_mkQuery]
          have hviewInput : model.view.input entry.1 = (ancestor, proof.head) := by
            rw [hinput, model.input_mkQuery]
          have hchildren :
              MerkleTreeExtractor.children model.view log (addressKey .ofInternal) root =
                some (ancestor, proof.head) := by
            rw [← hviewInput]
            exact MerkleTreeExtractor.children_eq_some_of_mem_of_responseInjectiveOn
              model.view log (addressKey .ofInternal) root entry.1 haddress hentry'
                (responseInjectiveOn_of_cache_noCollision log cacheCommit hlogCache hno)
          have hchildDisagree :
              some leaf ≠
                  (MerkleTreeExtractor.tree model.view sl
                    (fun position => addressKey (.ofLeft position)) log ancestor).get
                    idxLeft.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sl
                      (fun position => addressKey (.ofLeft position)) log ancestor)
                    idxLeft).toList := by
            rw [extractor_tree_internal_of_children_eq_some model sl sr
              addressKey log root ancestor proof.head hchildren] at hdisagree
            rcases hdisagree with hleaf | hproof
            · exact Or.inl (by
                simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
            · refine Or.inr fun htail => hproof ?_
              have hsibling :
                  (MerkleTreeExtractor.tree model.view sr
                    (fun position => addressKey (.ofRight position)) log proof.head).getRootValue =
                    some proof.head :=
                MerkleTreeExtractor.treeAt_getRootValue model.view sr
                  (fun position => addressKey (.ofRight position)) log proof.head
              have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                rw [← proof.cons_head_tail]
                rfl
              rw [hproofList, List.map_cons]
              change some proof.head :: proof.tail.toList.map some =
                (MerkleTreeExtractor.tree model.view sr
                  (fun position => addressKey (.ofRight position)) log proof.head).getRootValue ::
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sl
                      (fun position => addressKey (.ofLeft position)) log ancestor)
                    idxLeft).toList
              rw [hsibling, htail]
          obtain ⟨target, htarget, hfresh⟩ :=
            ih (fun position => addressKey (.ofLeft position)) ancestor proof.tail
              hchainTail hchildDisagree
          refine ⟨target, ?_, hfresh⟩
          change target ∈ MerkleTreeExtractor.targets model.view (.internal sl sr)
            addressKey log root
          rw [MerkleTreeExtractor.targets_internal_of_children_eq_some model.view sl sr
            addressKey log root ancestor proof.head hchildren]
          simp [htarget]
  | @ofRight sl sr idxRight ih =>
      obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
      let query := model.mkQuery (addressKey .ofInternal) (proof.head, ancestor)
      cases hqueryCommit : cacheCommit query with
      | none =>
          exact ⟨root,
            MerkleTreeExtractor.root_mem_targets model.view (.internal sl sr)
              addressKey log root,
            query, hquery, hqueryCommit⟩
      | some value =>
          have hvalueFinal := hmono hqueryCommit
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, hinput, houtput⟩ :=
            hcacheLog query root hqueryCommit
          have hentry' : (⟨entry.1, root⟩ : (_query : Query) × Y) ∈ log := by
            convert hentry using 1
            exact Sigma.ext rfl (heq_of_eq houtput.symm)
          have haddress : model.view.address entry.1 = addressKey .ofInternal := by
            rw [hinput, model.address_mkQuery]
          have hviewInput : model.view.input entry.1 = (proof.head, ancestor) := by
            rw [hinput, model.input_mkQuery]
          have hchildren :
              MerkleTreeExtractor.children model.view log (addressKey .ofInternal) root =
                some (proof.head, ancestor) := by
            rw [← hviewInput]
            exact MerkleTreeExtractor.children_eq_some_of_mem_of_responseInjectiveOn
              model.view log (addressKey .ofInternal) root entry.1 haddress hentry'
                (responseInjectiveOn_of_cache_noCollision log cacheCommit hlogCache hno)
          have hchildDisagree :
              some leaf ≠
                  (MerkleTreeExtractor.tree model.view sr
                    (fun position => addressKey (.ofRight position)) log ancestor).get
                    idxRight.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sr
                      (fun position => addressKey (.ofRight position)) log ancestor)
                    idxRight).toList := by
            rw [extractor_tree_internal_of_children_eq_some model sl sr
              addressKey log root proof.head ancestor hchildren] at hdisagree
            rcases hdisagree with hleaf | hproof
            · exact Or.inl (by
                simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
            · refine Or.inr fun htail => hproof ?_
              have hsibling :
                  (MerkleTreeExtractor.tree model.view sl
                    (fun position => addressKey (.ofLeft position)) log proof.head).getRootValue =
                    some proof.head :=
                MerkleTreeExtractor.treeAt_getRootValue model.view sl
                  (fun position => addressKey (.ofLeft position)) log proof.head
              have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                rw [← proof.cons_head_tail]
                rfl
              rw [hproofList, List.map_cons]
              change some proof.head :: proof.tail.toList.map some =
                (MerkleTreeExtractor.tree model.view sl
                  (fun position => addressKey (.ofLeft position)) log proof.head).getRootValue ::
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sr
                      (fun position => addressKey (.ofRight position)) log ancestor)
                    idxRight).toList
              rw [hsibling, htail]
          obtain ⟨target, htarget, hfresh⟩ :=
            ih (fun position => addressKey (.ofRight position)) ancestor proof.tail
              hchainTail hchildDisagree
          refine ⟨target, ?_, hfresh⟩
          change target ∈ MerkleTreeExtractor.targets model.view (.internal sl sr)
            addressKey log root
          rw [MerkleTreeExtractor.targets_internal_of_children_eq_some model.view sl sr
            addressKey log root proof.head ancestor hchildren]
          simp [htarget]

end MerkleTreeExtractability
