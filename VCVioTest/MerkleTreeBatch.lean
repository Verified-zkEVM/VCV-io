/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Completeness
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Addressed
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Disagreement
public meta import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.MapToSingle
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Uniqueness
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game

/-!
# Inductive Merkle Batch-Opening Canaries

Concrete examples that pin the public behavior of path-pruned batch openings: hash argument
order, pruning shape, the singleton reduction to an ordinary authentication path, the
all-selected and empty-selector boundaries, cross-selector collision extraction, and the
multi-opening verifier's accepting and rejecting branches.
-/

@[expose] public section

namespace VCVioTest.MerkleTreeBatch

open BinaryTree InductiveMerkleTree

def fourLeafSkeleton : Skeleton :=
  .internal (.internal .leaf .leaf) (.internal .leaf .leaf)

def leaves : LeafData Nat fourLeafSkeleton :=
  .internal (.internal (.leaf 1) (.leaf 2)) (.internal (.leaf 3) (.leaf 4))

/-- Deliberately noncommutative so the examples detect swapped left/right hash inputs. -/
def orderedHash (left right : Nat) : Nat :=
  2 * left + 3 * right + 1

def cache : FullData Nat fourLeafSkeleton :=
  buildMerkleTreeWithHash leaves orderedHash

def selectFirst : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf true) (.leaf false)) (.internal (.leaf false) (.leaf false))

def selectOuter : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf true) (.leaf false)) (.internal (.leaf false) (.leaf true))

def selectAll : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf true) (.leaf true)) (.internal (.leaf true) (.leaf true))

def selectNone : LeafData Bool fourLeafSkeleton :=
  .internal (.internal (.leaf false) (.leaf false)) (.internal (.leaf false) (.leaf false))

def firstIndex : SkeletonLeafIndex fourLeafSkeleton :=
  .ofLeft (.ofLeft .ofLeaf)

theorem firstSelected : selectFirst.get firstIndex = true := by decide

theorem firstNonempty : selectFirst.anySelected = true := by decide

def firstProof : BatchProof Nat selectFirst :=
  generateBatchProof cache selectFirst firstNonempty

theorem outerNonempty : selectOuter.anySelected = true := by decide

def outerProof : BatchProof Nat selectOuter :=
  generateBatchProof cache selectOuter outerNonempty

theorem allNonempty : selectAll.anySelected = true := by decide

def allProof : BatchProof Nat selectAll :=
  generateBatchProof cache selectAll allNonempty

example : orderedHash 9 19 = 76 := rfl

example : orderedHash 9 19 ≠ orderedHash 19 9 := by decide

example : cache.getRootValue = 76 := rfl

/-- A singleton batch proof is exactly the ordinary authentication path at that index. -/
example :
    batchToSingleProof orderedHash (selectedValues leaves selectFirst) firstProof
      firstIndex firstSelected = generateProof cache firstIndex := by
  rfl

example : selectedValueAt (selectedValues leaves selectFirst) firstIndex firstSelected = 1 := rfl

/-- Both pruning directions occur, with the roots of precisely the unselected siblings. -/
example :
    outerProof =
      .internalBoth (.pruneRight (by decide) 2 .leaf) (.pruneLeft (by decide) 3 .leaf) := by
  rfl

example :
    getPutativeBatchRootWithHash orderedHash (selectedValues leaves selectOuter) outerProof =
      cache.getRootValue := by
  exact functional_batch_completeness leaves selectOuter outerNonempty orderedHash

example :
    getPutativeBatchRootWithHash orderedHash (selectedValues leaves selectOuter) outerProof = 76 :=
  rfl

/-- Opening every leaf carries no stored authentication hash. -/
example :
    allProof =
      .internalBoth (.internalBoth .leaf .leaf) (.internalBoth .leaf .leaf) := by
  rfl

/-- Mapping into a partial-tree value type preserves both pruning directions and maps only
the stored authentication frontier. -/
example :
    outerProof.map some =
      .internalBoth (.pruneRight (by decide) (some 2) .leaf)
        (.pruneLeft (by decide) (some 3) .leaf) := by
  rfl

/-- The all-selected proof contains no stored value for mapping to change. -/
example :
    allProof.map some =
      .internalBoth (.internalBoth .leaf .leaf) (.internalBoth .leaf .leaf) := by
  rfl

/-- Structural query counting is exact on singleton, outer-pair, and all-selected traversals. -/
example : firstProof.queryCount = 2 ∧ outerProof.queryCount = 3 ∧ allProof.queryCount = 3 := by
  decide

/-! ## Addressed traversal order -/

/-- Observable tags for the three typed internal positions of `fourLeafSkeleton`. -/
inductive DepthTwoAddress where
  | rootNode
  | leftNode
  | rightNode
deriving DecidableEq, Repr

/-- Collapse the dependent internal-node index to a traceable address tag. -/
def depthTwoAddress : SkeletonInternalIndex fourLeafSkeleton → DepthTwoAddress
  | .ofInternal => .rootNode
  | .ofLeft .ofInternal => .leftNode
  | .ofRight .ofInternal => .rightNode

/-- One effectful addressed-hash call, retaining its ordered children. -/
structure AddressedHashEvent where
  address : DepthTwoAddress
  left : Nat
  right : Nat
deriving DecidableEq, Repr

abbrev AddressedTraceM := StateM (List AddressedHashEvent)

def addressWeight : DepthTwoAddress → Nat
  | .rootNode => 0
  | .leftNode => 100
  | .rightNode => 200

/-- Address-sensitive, noncommutative node hash with an observable append-only trace. -/
def tracedAddressedHash (address : SkeletonInternalIndex fourLeafSkeleton)
    (left right : Nat) : AddressedTraceM Nat := fun trace =>
  let tag := depthTwoAddress address
  (addressWeight tag + 2 * left + 3 * right + 1,
    trace ++ [{ address := tag, left, right }])

/-- The addressed batch fold visits left child, right child, then root; each recursive call
receives the correct reindexed typed address and preserves ordered hash inputs.  The numeric result
is also noncommutative, so neither swapping children nor merely repairing the trace can satisfy the
canary. -/
example : Id.run
    ((AddressedMerkleTree.getPutativeBatchRootAddressedM tracedAddressedHash
      (selectedValues leaves selectAll) allProof).run []) =
    (876,
      [{ address := .leftNode, left := 1, right := 2 },
       { address := .rightNode, left := 3, right := 4 },
       { address := .rootNode, left := 109, right := 219 }]) := by
  decide

/-- Pure counterpart of `tracedAddressedHash`, retaining address sensitivity and child order. -/
def pureAddressedHash (address : SkeletonInternalIndex fourLeafSkeleton)
    (left right : Nat) : Nat :=
  addressWeight (depthTwoAddress address) + 2 * left + 3 * right + 1

/-- Addressed batch-to-single expansion recomputes the right sibling subtree under the right-child
address and then retains the lower left-child sibling.  Reindexing either subtree incorrectly
changes `219`, while reversing proof order changes the vector. -/
example :
    (batchToSingleProofAddressed pureAddressedHash
      (selectedValues leaves selectOuter) outerProof firstIndex firstSelected).toList =
      [219, 2] := by
  rfl

/-- The generated addressed path recomputes the same noncommutative, address-sensitive root as
the pruned batch opening. -/
example :
    AddressedMerkleTree.getPutativeRootAddressedWithHash pureAddressedHash firstIndex 1
      (batchToSingleProofAddressed pureAddressedHash
        (selectedValues leaves selectOuter) outerProof firstIndex firstSelected) = 876 := by
  rfl

/-- Opening no leaf is excluded by the dependent proof family. -/
example : IsEmpty (BatchProof Nat selectNone) :=
  ⟨fun proof => by
    have h := BatchProof.anySelected_of_batchProof proof
    simp [selectNone] at h⟩

example :
    getPutativeRootWithHash firstIndex
        (selectedValueAt (selectedValues leaves selectFirst) firstIndex firstSelected)
        (batchToSingleProof orderedHash (selectedValues leaves selectFirst) firstProof
          firstIndex firstSelected)
        orderedHash =
      getPutativeBatchRootWithHash orderedHash (selectedValues leaves selectFirst) firstProof := by
  exact getPutativeRootWithHash_batchToSingleProof orderedHash
    (selectedValues leaves selectFirst) firstProof firstIndex firstSelected

/-! ## Cross-selector collision extraction -/

def pairSkeleton : Skeleton :=
  .internal .leaf .leaf

def selectLeft : LeafData Bool pairSkeleton :=
  .internal (.leaf true) (.leaf false)

def selectBoth : LeafData Bool pairSkeleton :=
  .internal (.leaf true) (.leaf true)

def leftValues : SelectedValues Nat selectLeft := by
  change Nat × PUnit
  exact (1, ⟨⟩)

def bothValues : SelectedValues Nat selectBoth := by
  change Nat × Nat
  exact (2, 7)

def leftProof : BatchProof Nat selectLeft :=
  .pruneRight rfl 99 .leaf

def bothProof : BatchProof Nat selectBoth :=
  .internalBoth .leaf .leaf

def pairLeftIndex : SkeletonLeafIndex pairSkeleton :=
  .ofLeft .ofLeaf

theorem leftSelected : selectLeft.get pairLeftIndex = true := rfl

theorem bothLeftSelected : selectBoth.get pairLeftIndex = true := rfl

def constantHash (_left _right : Nat) : Nat :=
  0

theorem selectedValuesDiffer :
    selectedValueAt leftValues pairLeftIndex leftSelected ≠
      selectedValueAt bothValues pairLeftIndex bothLeftSelected := by
  decide

theorem putativeRootsAgree :
    getPutativeBatchRootWithHash constantHash leftValues leftProof =
      getPutativeBatchRootWithHash constantHash bothValues bothProof :=
  rfl

def bothValuesRightChanged : SelectedValues Nat selectBoth := by
  change Nat × Nat
  exact (2, 9)

def bothOpening₁ : BatchOpening Nat pairSkeleton where
  selector := selectBoth
  values := bothValues
  proof := bothProof

def bothOpening₂ : BatchOpening Nat pairSkeleton where
  selector := selectBoth
  values := bothValuesRightChanged
  proof := bothProof

def pairNodeHash (_ : SkeletonInternalIndex pairSkeleton) : Nat → Nat → Nat :=
  constantHash

def pairRightIndex : SkeletonLeafIndex pairSkeleton :=
  .ofRight .ofLeaf

theorem bothOpeningsValuesNotHEq : ¬ HEq bothOpening₁.values bothOpening₂.values := by
  intro heq
  have hvalues : bothValues = bothValuesRightChanged := eq_of_heq heq
  have hright := congrArg
    (fun values : SelectedValues Nat selectBoth =>
      selectedValueAt values pairRightIndex rfl) hvalues
  change 7 = 9 at hright
  omega

theorem bothOpening₁Accepted :
    BatchOpening.AcceptedAddressedWithHash pairNodeHash 0 bothOpening₁ := rfl

theorem bothOpening₂Accepted :
    BatchOpening.AcceptedAddressedWithHash pairNodeHash 0 bothOpening₂ := rfl

/-- The structural decomposition must take the right branch: the left values agree, while the
right values are `7` and `9`. -/
example : ∃ index : SkeletonLeafIndex pairSkeleton,
    ∃ selected : selectBoth.get index = true,
      selectedValueAt bothValues index selected ≠
          selectedValueAt bothValuesRightChanged index selected ∧
        index = pairRightIndex := by
  obtain ⟨index, selected, hvalue⟩ :=
    exists_selectedValueAt_ne_of_ne bothValues bothValuesRightChanged (by
      intro heq
      have hright := congrArg
        (fun values : SelectedValues Nat selectBoth =>
          selectedValueAt values pairRightIndex rfl) heq
      change 7 = 9 at hright
      omega)
  refine ⟨index, selected, hvalue, ?_⟩
  cases index with
  | ofLeft index =>
      cases index
      exact (hvalue rfl).elim
  | ofRight index =>
      cases index
      rfl

/-- The full-opening bridge takes the same right branch.  Its witness type additionally carries
both canonical generated paths and their equations to the shared accepted root. -/
example : ∃ witness : BatchOpening.SelectedPathDisagreement
    pairNodeHash 0 bothOpening₁ bothOpening₂,
    witness.index = pairRightIndex := by
  obtain ⟨witness⟩ := BatchOpening.selectedPathDisagreement_of_accepted
    pairNodeHash 0 bothOpening₁ bothOpening₂ rfl bothOpeningsValuesNotHEq
      bothOpening₁Accepted bothOpening₂Accepted
  have hindex : witness.index = pairRightIndex := by
    rcases witness with
      ⟨index, selected₁, selected₂, hleaf, proof₁, proof₂, hproof₁, hproof₂,
        hverifies₁, hverifies₂⟩
    cases index with
    | ofLeft index =>
        cases index
        exact (hleaf rfl).elim
    | ofRight index =>
        cases index
        rfl
  exact ⟨witness, hindex⟩

example :
    ∃ l₁ r₁ l₂ r₂,
      findCollision constantHash pairLeftIndex
          (batchToSingleProof constantHash leftValues leftProof pairLeftIndex leftSelected)
          (batchToSingleProof constantHash bothValues bothProof pairLeftIndex bothLeftSelected)
          (selectedValueAt leftValues pairLeftIndex leftSelected)
          (selectedValueAt bothValues pairLeftIndex bothLeftSelected) =
            some (l₁, r₁, l₂, r₂)
        ∧ Collision constantHash l₁ r₁ l₂ r₂ := by
  exact getPutativeBatchRootWithHash_binding constantHash
    leftValues leftProof bothValues bothProof pairLeftIndex leftSelected bothLeftSelected
    selectedValuesDiffer putativeRootsAgree

/-! ## Multi-opening verification -/

open _root_.MerkleTreeMultiExtractability

abbrev VerifierQuery := Nat × Nat

/-- Complete-query model for the deterministic multi-opening verifier canary. -/
def verifierModel : MerkleTreeExtractability.NodeQueryModel VerifierQuery Unit Nat where
  view := {
    address := fun _ => ()
    input := id }
  mkQuery _ input := input
  address_mkQuery := by intros; rfl
  input_mkQuery := by intros; rfl

def verifierConfig : Configuration Unit Unit where
  skeleton _ := pairSkeleton
  addressKey _ _ := ()

def acceptingClaim : OpeningClaim VerifierQuery Nat verifierConfig where
  tag := ()
  checkpoint := {
    root := 26
    cumulativeLog := [] }
  opening := {
    selector := selectBoth
    values := bothValues
    proof := bothProof }

def rejectingClaim : OpeningClaim VerifierQuery Nat verifierConfig where
  tag := ()
  checkpoint := {
    root := 27
    cumulativeLog := [] }
  opening := {
    selector := selectBoth
    values := bothValues
    proof := bothProof }

def verifierImpl : QueryImpl (VerifierQuery →ₒ Nat) Id :=
  fun query => orderedHash query.1 query.2

def attemptBits
    (attempts : List (AnyEvaluatedOpeningClaim Unit VerifierQuery Unit Nat verifierConfig)) :
    List Bool :=
  attempts.map fun ⟨_, attempt⟩ => attempt.accepted

/-- `verifyOpeningClaims` preserves duplicates and records every verifier outcome in order. -/
example :
    let attempts := simulateQ verifierImpl
      (verifyOpeningClaims verifierModel [acceptingClaim, rejectingClaim, acceptingClaim])
    attempts.length = 3 ∧ attemptBits attempts = [true, false, true] := by
  decide

end VCVioTest.MerkleTreeBatch
