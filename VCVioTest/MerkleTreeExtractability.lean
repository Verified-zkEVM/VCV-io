/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Evolution

/-!
# Inductive Merkle Extractability Canaries

These examples pin the semantic boundary between raw `OracleComp` syntax, where repeated
queries sample independently, and `extractabilityGame`, where the full experiment is run
through one shared cache.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.MerkleTreeExtractability

noncomputable local instance : IsUniformSpec (InductiveMerkleTree.spec Bool) :=
  IsUniformSpec.ofFintypeInhabited (InductiveMerkleTree.spec Bool)

def repeatedQuery : OracleComp (InductiveMerkleTree.spec Bool) (Bool × Bool) := do
  let first ← ((InductiveMerkleTree.spec Bool).query (false, false) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  let second ← ((InductiveMerkleTree.spec Bool).query (false, false) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  return (first, second)

/-- Raw `OracleComp` semantics permit two different answers to the same input. -/
example : (false, true) ∈ support repeatedQuery := by
  simp [repeatedQuery]

/-- The shared cache makes the same repeated input return the same answer. -/
example : ∀ result ∈ support
    (Prod.fst <$> (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle repeatedQuery).run ∅),
    result.1 = result.2 := by
  intro result hresult
  have hcases : (false, false) = result ∨ (true, true) = result := by
    simpa [repeatedQuery] using hresult
  rcases hcases with rfl | rfl <;> rfl

/-- `extractabilityGame` is exactly the cached interpretation of its oracle syntax, with
the final implementation cache hidden from consumers. -/
example {s : BinaryTree.Skeleton} (adversary : InductiveMerkleTree.Adversary Bool s) :
    InductiveMerkleTree.extractabilityGame adversary =
      (InductiveMerkleTree.spec Bool).withCacheOverlay ∅
        (InductiveMerkleTree.extractabilityInner adversary) := rfl

def depthOneSkeleton : BinaryTree.Skeleton :=
  .internal .leaf .leaf

def leftIndex : BinaryTree.SkeletonLeafIndex depthOneSkeleton :=
  .ofLeft .ofLeaf

def leftProof : List.Vector Bool leftIndex.depth :=
  ⟨[true], rfl⟩

@[simp] private lemma leftProof_head : leftProof.head = true := rfl

def rightIndex : BinaryTree.SkeletonLeafIndex depthOneSkeleton :=
  .ofRight .ofLeaf

def rightProof : List.Vector Bool rightIndex.depth :=
  ⟨[false], rfl⟩

@[simp] private lemma rightProof_head : rightProof.head = false := rfl

abbrev depthOneAdversary : InductiveMerkleTree.Adversary Bool depthOneSkeleton where
  AuxState := Unit
  commit := do
    let root ← ((InductiveMerkleTree.spec Bool).query (false, true) :
      OracleComp (InductiveMerkleTree.spec Bool) Bool)
    return (root, ())
  opening _ := do
    let answer ← ((InductiveMerkleTree.spec Bool).query (false, true) :
      OracleComp (InductiveMerkleTree.spec Bool) Bool)
    if answer then
      return ⟨rightIndex, true, rightProof⟩
    else
      return ⟨leftIndex, false, leftProof⟩

private lemma depthOneCommit_withQueryLog_eq :
    depthOneAdversary.commit.withQueryLog =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure ((root, ()), [⟨(false, true), root⟩])) := by
  change OracleComp.withQueryLog (((fun root => (root, ())) <$>
      ((InductiveMerkleTree.spec Bool).query (false, true) :
        OracleComp (InductiveMerkleTree.spec Bool) Bool))) = _
  rw [map_eq_bind_pure_comp, OracleComp.withQueryLog_bind,
    OracleComp.withQueryLog_query]
  simp

private lemma depthOneCommit_cached_eq :
    (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
      depthOneAdversary.commit.withQueryLog).run ∅ =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure (((root, ()), [⟨(false, true), root⟩]),
          (∅ : (InductiveMerkleTree.spec Bool).QueryCache).cacheQuery
            (false, true) root)) := by
  rw [depthOneCommit_withQueryLog_eq]
  change (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure ((root, ()),
          ([⟨(false, true), root⟩] : (InductiveMerkleTree.spec Bool).QueryLog)))).run ∅ = _
  rw [simulateQ_bind, StateT.run_bind, cachingOracle.simulateQ_query,
    cachingOracle.run_none (by rfl)]
  simp

/-- The commit prefix records the hash input once for the extractor, with the answer installed
in the shared cache before the same input is repeated during opening and verification. -/
example (z : ((Bool × Unit) × (InductiveMerkleTree.spec Bool).QueryLog) ×
    (InductiveMerkleTree.spec Bool).QueryCache)
    (hz : z ∈ support ((simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
      depthOneAdversary.commit.withQueryLog).run ∅)) :
    z.1.2 = [⟨(false, true), z.1.1.1⟩] ∧
      z.2 (false, true) = some z.1.1.1 := by
  rw [depthOneCommit_cached_eq] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨root, _, hz⟩ := hz
  rw [mem_support_pure_iff] at hz
  subst z
  constructor
  · rfl
  · change ((∅ : (InductiveMerkleTree.spec Bool).QueryCache).cacheQuery
      (false, true) root) (false, true) = some root
    exact QueryCache.cacheQuery_self _ _ _

def expectedTree (root : Bool) :
    BinaryTree.FullData (Option Bool) depthOneSkeleton :=
  .internal (some root) (.leaf (some false)) (.leaf (some true))

def expectedLeftProof : List.Vector (Option Bool) leftIndex.depth :=
  some true ::ᵥ List.Vector.nil

def expectedRightProof : List.Vector (Option Bool) rightIndex.depth :=
  some false ::ᵥ List.Vector.nil

private lemma depthOneGame_eq :
    InductiveMerkleTree.extractabilityGame depthOneAdversary =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        if root then
          pure (root, (), ⟨rightIndex, true, rightProof,
            expectedTree root, expectedRightProof, true⟩)
        else
          pure (root, (), ⟨leftIndex, false, leftProof,
            expectedTree root, expectedLeftProof, true⟩)) := by
  rw [show InductiveMerkleTree.extractabilityGame depthOneAdversary =
      (InductiveMerkleTree.spec Bool).withCacheOverlay ∅
        (InductiveMerkleTree.extractabilityInner depthOneAdversary) from rfl]
  rw [show InductiveMerkleTree.extractabilityInner depthOneAdversary =
      depthOneAdversary.commit.withQueryLog >>= fun ((root, aux), queryLog) => do
        let extractedTree := InductiveMerkleTree.extractor depthOneSkeleton queryLog root
        let ⟨idx, leaf, proof⟩ ← depthOneAdversary.opening aux
        let extractedProof := InductiveMerkleTree.generateProof extractedTree idx
        let verified ← InductiveMerkleTree.verifyProof idx leaf root proof
        return (root, aux,
          ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) from
      InductiveMerkleTree.extractabilityInner_eq_unaddressed depthOneAdversary]
  rw [withCacheOverlay_bind, depthOneCommit_cached_eq]
  simp only [bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp (InductiveMerkleTree.spec Bool)) fun root => ?_
  cases root <;>
    simp [OracleSpec.withCacheOverlay,
      InductiveMerkleTree.Extractor.tree, MerkleTreeExtractor.tree,
      MerkleTreeExtractor.treeAt, MerkleTreeExtractor.children,
      InductiveMerkleTree.Extractor.queryView,
      depthOneSkeleton, leftIndex, rightIndex, expectedTree,
      expectedLeftProof, expectedRightProof]

/-- If the shared answer is `false`, the adversary opens the left branch. -/
example : (false, (), ⟨leftIndex, false, leftProof,
    expectedTree false, expectedLeftProof, true⟩) ∈
    support (InductiveMerkleTree.extractabilityGame depthOneAdversary) := by
  rw [depthOneGame_eq]
  simp

/-- If the shared answer is `true`, the adversary opens the right branch. -/
example : (true, (), ⟨rightIndex, true, rightProof,
    expectedTree true, expectedRightProof, true⟩) ∈
    support (InductiveMerkleTree.extractabilityGame depthOneAdversary) := by
  rw [depthOneGame_eq]
  simp

/-- Commit, opening, and verification all query `(false, true)`. The shared oracle returns
one answer throughout, so the commit-prefix extractor recovers the opened leaf and full path. -/
example (transcript : Bool × Unit ×
    ((idx : BinaryTree.SkeletonLeafIndex depthOneSkeleton) × Bool ×
      List.Vector Bool idx.depth × BinaryTree.FullData (Option Bool) depthOneSkeleton ×
      List.Vector (Option Bool) idx.depth × Bool))
    (htranscript : transcript ∈ support
      (InductiveMerkleTree.extractabilityGame depthOneAdversary)) :
    ¬ InductiveMerkleTree.OpeningExtractionFailure transcript := by
  rw [depthOneGame_eq] at htranscript
  rw [mem_support_bind_iff] at htranscript
  obtain ⟨root, _, htranscript⟩ := htranscript
  cases root <;> simp at htranscript
  all_goals subst transcript
  all_goals simp [InductiveMerkleTree.OpeningExtractionFailure,
    InductiveMerkleTree.OpeningExtractionFailure,
    expectedTree, expectedLeftProof, expectedRightProof, depthOneSkeleton,
    leftIndex, rightIndex, leftProof, rightProof]
  all_goals rfl

/-! ## ROM-bound producer canaries -/

abbrev depthZeroAdversary :
    InductiveMerkleTree.Adversary Bool BinaryTree.Skeleton.leaf where
  AuxState := Unit
  commit := pure (false, ())
  opening _ := pure ⟨.ofLeaf, false, List.Vector.nil⟩

private lemma depthZeroAdversary_totalBound :
    depthZeroAdversary.IsTwoPhaseTotalQueryBound 0 := by
  trivial

/-- At depth zero, a query-free two-phase adversary has zero extraction-failure probability.
This pins the fact that the verifier hashes internal nodes only; it does not hash a raw leaf. -/
example :
    Pr[InductiveMerkleTree.OpeningExtractionFailure |
      InductiveMerkleTree.extractabilityGame depthZeroAdversary] = 0 := by
  apply le_antisymm
  · simpa [InductiveMerkleTree.extractabilityROMErrorNumerator,
      MerkleTreeExtractability.extractabilityROMErrorNumerator] using
      InductiveMerkleTree.extractability_rom_bound
      depthZeroAdversary 0 depthZeroAdversary_totalBound
  · exact zero_le

/-- A commit with no hash queries followed by a depth-one opening. Verification's one fresh
hash can hit the commit-time root target, so the fresh-hit term in the ROM theorem is necessary. -/
abbrev freshHitAdversary : InductiveMerkleTree.Adversary Bool depthOneSkeleton where
  AuxState := Unit
  commit := pure (false, ())
  opening _ := pure ⟨leftIndex, false, leftProof⟩

private lemma freshHitAdversary_totalBound :
    freshHitAdversary.IsTwoPhaseTotalQueryBound 0 := by
  trivial

/-- The public finite-maximum theorem sees the `c = 0` stopping branch and its one reachable
target, recovering the exact `1 / |Bool| = 1/2` bound for this game. -/
example :
    Pr[InductiveMerkleTree.OpeningExtractionFailure |
      InductiveMerkleTree.extractabilityGame freshHitAdversary] ≤ (2 : ENNReal)⁻¹ := by
  simpa [InductiveMerkleTree.extractabilityROMErrorNumerator,
    MerkleTreeExtractability.extractabilityROMErrorNumerator, depthOneSkeleton] using
    InductiveMerkleTree.extractability_rom_bound
    freshHitAdversary 0 freshHitAdversary_totalBound

def freshHitExtractedTree : BinaryTree.FullData (Option Bool) depthOneSkeleton :=
  .internal (some false) (.leaf none) (.leaf none)

def freshHitExtractedProof : List.Vector (Option Bool) leftIndex.depth :=
  none ::ᵥ List.Vector.nil

private lemma freshHitGame_eq :
    InductiveMerkleTree.extractabilityGame freshHitAdversary =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun answer =>
        pure (false, (), ⟨leftIndex, false, leftProof,
          freshHitExtractedTree, freshHitExtractedProof, answer == false⟩)) := by
  simp [InductiveMerkleTree.extractabilityGame,
    InductiveMerkleTree.extractabilityInner_eq_unaddressed, OracleSpec.withCacheOverlay,
    freshHitAdversary, freshHitExtractedTree, freshHitExtractedProof,
    InductiveMerkleTree.Extractor.tree, MerkleTreeExtractor.tree,
    MerkleTreeExtractor.treeAt, MerkleTreeExtractor.children,
    InductiveMerkleTree.Extractor.queryView,
    InductiveMerkleTree.verifyProof, InductiveMerkleTree.getPutativeRoot,
    InductiveMerkleTree.singleHash, depthOneSkeleton, leftIndex, leftProof_head]

def freshHitTranscript : Bool × Unit ×
    ((idx : BinaryTree.SkeletonLeafIndex depthOneSkeleton) × Bool ×
      List.Vector Bool idx.depth × BinaryTree.FullData (Option Bool) depthOneSkeleton ×
      List.Vector (Option Bool) idx.depth × Bool) :=
  (false, (), ⟨leftIndex, false, leftProof,
    freshHitExtractedTree, freshHitExtractedProof, true⟩)

/-- The fresh verifier answer `false` produces a supported extraction failure. -/
example : freshHitTranscript ∈
    support (InductiveMerkleTree.extractabilityGame freshHitAdversary) := by
  rw [freshHitGame_eq]
  simp [freshHitTranscript]

example : InductiveMerkleTree.OpeningExtractionFailure freshHitTranscript := by
  simp [freshHitTranscript, InductiveMerkleTree.OpeningExtractionFailure,
    InductiveMerkleTree.OpeningExtractionFailure, freshHitExtractedTree,
    freshHitExtractedProof, depthOneSkeleton, leftIndex]

def wrongRightProof : List.Vector Bool rightIndex.depth :=
  ⟨[true], rfl⟩

@[simp] private lemma wrongRightProof_head : wrongRightProof.head = true := rfl

/-- The extracted right leaf agrees with the opening, but the adversary supplies the wrong left
sibling. A fresh verifier query can still accept, exercising proof-only disagreement on the
orientation opposite to `freshHitAdversary`. -/
abbrev proofOnlyAdversary : InductiveMerkleTree.Adversary Bool depthOneSkeleton where
  AuxState := Unit
  commit := depthOneAdversary.commit
  opening _ := pure ⟨rightIndex, true, wrongRightProof⟩

private lemma proofOnlyGame_eq :
    InductiveMerkleTree.extractabilityGame proofOnlyAdversary =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        ((InductiveMerkleTree.spec Bool).query (true, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun answer =>
        pure (root, (), ⟨rightIndex, true, wrongRightProof,
          expectedTree root, expectedRightProof, answer == root⟩)) := by
  rw [show InductiveMerkleTree.extractabilityGame proofOnlyAdversary =
      (InductiveMerkleTree.spec Bool).withCacheOverlay ∅
        (InductiveMerkleTree.extractabilityInner proofOnlyAdversary) from rfl]
  rw [show InductiveMerkleTree.extractabilityInner proofOnlyAdversary =
      proofOnlyAdversary.commit.withQueryLog >>= fun ((root, aux), queryLog) => do
        let extractedTree := InductiveMerkleTree.extractor depthOneSkeleton queryLog root
        let ⟨idx, leaf, proof⟩ ← proofOnlyAdversary.opening aux
        let extractedProof := InductiveMerkleTree.generateProof extractedTree idx
        let verified ← InductiveMerkleTree.verifyProof idx leaf root proof
        return (root, aux,
          ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) from rfl]
  rw [withCacheOverlay_bind, depthOneCommit_cached_eq]
  simp only [bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp (InductiveMerkleTree.spec Bool)) fun root => ?_
  cases root <;>
    simp [OracleSpec.withCacheOverlay,
      InductiveMerkleTree.Extractor.tree, MerkleTreeExtractor.tree,
      MerkleTreeExtractor.treeAt, MerkleTreeExtractor.children,
      InductiveMerkleTree.Extractor.queryView,
      depthOneSkeleton, rightIndex, expectedTree, expectedRightProof,
      wrongRightProof_head, QueryCache.cacheQuery_of_ne]

def proofOnlyTranscript : Bool × Unit ×
    ((idx : BinaryTree.SkeletonLeafIndex depthOneSkeleton) × Bool ×
      List.Vector Bool idx.depth × BinaryTree.FullData (Option Bool) depthOneSkeleton ×
      List.Vector (Option Bool) idx.depth × Bool) :=
  (false, (), ⟨rightIndex, true, wrongRightProof,
    expectedTree false, expectedRightProof, true⟩)

example : proofOnlyTranscript ∈
    support (InductiveMerkleTree.extractabilityGame proofOnlyAdversary) := by
  rw [proofOnlyGame_eq]
  simp [proofOnlyTranscript]

/-- This winner is proof-only: its extracted leaf is `some true`, while only the path differs. -/
example : InductiveMerkleTree.OpeningExtractionFailure proofOnlyTranscript := by
  simp [proofOnlyTranscript, InductiveMerkleTree.OpeningExtractionFailure,
    InductiveMerkleTree.OpeningExtractionFailure, expectedTree,
    expectedRightProof, wrongRightProof, depthOneSkeleton, rightIndex]

def twoDistinctQueries : OracleComp (InductiveMerkleTree.spec Bool) Unit := do
  let _ ← ((InductiveMerkleTree.spec Bool).query (false, false) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  let _ ← ((InductiveMerkleTree.spec Bool).query (false, true) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  return ()

def collidingCache : (InductiveMerkleTree.spec Bool).QueryCache :=
  ((∅ : (InductiveMerkleTree.spec Bool).QueryCache).cacheQuery (false, false) false).cacheQuery
    (false, true) false

/-- Two distinct fresh inputs can receive the same answer and produce a cache collision. This
pins the birthday branch of the ROM proof separately from the fresh-target branch. -/
example : CacheHasCollision collidingCache := by
  refine ⟨(false, false), (false, true), false, false, by decide, ?_, ?_, HEq.rfl⟩
  · simp [collidingCache, QueryCache.cacheQuery_of_ne]
  · simp [collidingCache]

example : ((), collidingCache) ∈ support
    ((simulateQ (InductiveMerkleTree.spec Bool).cachingOracle twoDistinctQueries).run ∅) := by
  simp [twoDistinctQueries, collidingCache, QueryCache.cacheQuery_of_ne]

/-! ## Complete-query response injectivity -/

namespace FullQueryInjectivityCanary

/-- A complete hash query carries metadata in addition to its ordered child pair. -/
structure TaggedQuery where
  tag : Bool
  childPair : Nat × Nat
  deriving DecidableEq

def queryView : MerkleTreeExtractor.QueryView TaggedQuery Unit Nat where
  address := fun _ => ()
  input := TaggedQuery.childPair

def untagged : TaggedQuery := ⟨false, (2, 3)⟩

def tagged : TaggedQuery := ⟨true, (2, 3)⟩

/-- Both complete queries expose the same ordered children, so a collision check that only
compares child projections cannot distinguish them. -/
example : queryView.input untagged = queryView.input tagged := rfl

/-- The tag remains part of the complete oracle query. -/
example : untagged ≠ tagged := by decide

def sameResponseLog : MerkleTreeExtractor.QueryLog TaggedQuery Nat :=
  [⟨untagged, 7⟩, ⟨tagged, 7⟩]

/-- Child-pair equality is too weak as the transcript collision predicate: it accepts this log. -/
example : ∀ entry₁ ∈ sameResponseLog, ∀ entry₂ ∈ sameResponseLog,
    entry₁.2 = entry₂.2 → queryView.input entry₁.1 = queryView.input entry₂.1 := by
  intro entry₁ h₁ entry₂ h₂ _
  simp only [sameResponseLog, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> rfl

/-- `ResponseInjectiveOn` compares complete queries, and therefore rejects the tag-only
collision even though the ordered child pairs coincide. -/
example : ¬ MerkleTreeExtractor.ResponseInjectiveOn sameResponseLog := by
  intro hinjective
  have hquery : untagged = tagged :=
    hinjective ⟨untagged, 7⟩ (by simp [sameResponseLog])
      ⟨tagged, 7⟩ (by simp [sameResponseLog]) rfl
  exact (by decide : untagged ≠ tagged) hquery

def distinctResponseLog : MerkleTreeExtractor.QueryLog TaggedQuery Nat :=
  [⟨untagged, 7⟩, ⟨tagged, 8⟩]

private lemma distinctResponseLog_injective :
    MerkleTreeExtractor.ResponseInjectiveOn distinctResponseLog := by
  intro entry₁ h₁ entry₂ h₂ hresponse
  simp only [distinctResponseLog, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · rfl
  · simp at hresponse
  · simp at hresponse
  · rfl

def skeleton : BinaryTree.Skeleton := .internal .leaf .leaf

def leftIndex : BinaryTree.SkeletonLeafIndex skeleton := .ofLeft .ofLeaf

def leftProof : List.Vector Nat leftIndex.depth := ⟨[3], rfl⟩

/-- With distinct responses, the generic recovery theorem consumes complete-query injectivity
and recovers the tagged query's left opening. -/
example :
    (MerkleTreeExtractor.treeAt queryView skeleton (fun _ => ()) distinctResponseLog 8).get
        leftIndex.toNodeIndex = some 2 ∧
      (InductiveMerkleTree.generateProof
        (MerkleTreeExtractor.treeAt queryView skeleton (fun _ => ()) distinctResponseLog 8)
        leftIndex).toList = leftProof.toList.map some := by
  apply MerkleTreeExtractor.opening_eq_of_chainInLogAt queryView distinctResponseLog
    distinctResponseLog_injective (fun _ => ()) 8 2 leftIndex leftProof
  exact ⟨tagged, 2, rfl, rfl, by simp [distinctResponseLog], rfl⟩

end FullQueryInjectivityCanary

/-! ## Online extractor evolution -/

namespace EvolutionCanary

open BinaryTree MerkleTreeMultiExtractability

abbrev Query := Nat × (Nat × Nat)

def queryView : MerkleTreeExtractor.QueryView Query Nat Nat where
  address := Prod.fst
  input := Prod.snd

def skeleton : Skeleton :=
  .internal (.internal .leaf .leaf) (.internal .leaf .leaf)

/-- Distinct addresses for the root, left child, and right child internal nodes. -/
def addressKey : SkeletonInternalIndex skeleton → Nat
  | .ofInternal => 0
  | .ofLeft .ofInternal => 1
  | .ofRight .ofInternal => 2

def root : Nat := 50

/-- The root query is known, making `20` and `30` live non-root extractor targets. -/
def preLog : MerkleTreeExtractor.QueryLog Query Nat :=
  [⟨(0, (20, 30)), root⟩]

/-- This entry expands the previously live left-child root. -/
def growingEntry : (_ : Query) × Nat :=
  ⟨(1, (2, 3)), 20⟩

/-- Its response is unrelated to every live target in `preLog`. -/
def decoyEntry : (_ : Query) × Nat :=
  ⟨(1, (7, 8)), 999⟩

def treeBefore : FullData (Option Nat) skeleton :=
  .internal (some root)
    (.internal (some 20) (.leaf none) (.leaf none))
    (.internal (some 30) (.leaf none) (.leaf none))

def treeAfterGrowth : FullData (Option Nat) skeleton :=
  .internal (some root)
    (.internal (some 20) (.leaf (some 2)) (.leaf (some 3)))
    (.internal (some 30) (.leaf none) (.leaf none))

example : MerkleTreeExtractor.tree queryView skeleton addressKey preLog root = treeBefore := by
  rfl

/-- Appending a response equal to the live left-child root expands precisely that subtree. -/
example :
    MerkleTreeExtractor.tree queryView skeleton addressKey (preLog ++ [growingEntry]) root =
      treeAfterGrowth := by
  rfl

private theorem growingEntry_changes_tree :
    MerkleTreeExtractor.tree queryView skeleton addressKey preLog root ≠
      MerkleTreeExtractor.tree queryView skeleton addressKey (preLog ++ [growingEntry]) root := by
  change treeBefore ≠ treeAfterGrowth
  intro heq
  have hleaf := congrArg
    (fun tree : FullData (Option Nat) skeleton =>
      tree.leftSubtree.leftSubtree.getRootValue) heq
  simp [treeBefore, treeAfterGrowth] at hleaf

/-- A response outside the pre-log target set cannot change extraction. -/
example : decoyEntry.2 ∉
      MerkleTreeExtractor.targets queryView skeleton addressKey preLog root ∧
    MerkleTreeExtractor.tree queryView skeleton addressKey preLog root =
      MerkleTreeExtractor.tree queryView skeleton addressKey (preLog ++ [decoyEntry]) root := by
  constructor
  · decide
  · rfl

/-- A decoy entry leaves the live label set intact, so the following causal entry still expands
the left subtree. -/
example :
    growingEntry.2 ∈ MerkleTreeExtractor.targets queryView skeleton addressKey
        (preLog ++ [decoyEntry]) root ∧
      MerkleTreeExtractor.tree queryView skeleton addressKey
          (preLog ++ [decoyEntry, growingEntry]) root = treeAfterGrowth := by
  constructor
  · decide
  · rfl

end EvolutionCanary

end VCVioTest.MerkleTreeExtractability
