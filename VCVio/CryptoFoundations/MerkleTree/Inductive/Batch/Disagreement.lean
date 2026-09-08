/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Addressed
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Opening
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.MapToSingle

/-!
# Deterministic batch-opening disagreement witnesses

This module bridges a disagreement between two accepted batch openings to the existing
single-path Merkle kernel.  The bridge is purely structural: unequal selected-value tuples for
one selector expose a concrete selected leaf with unequal values.  Each pruned batch proof is
then expanded at that leaf into an ordinary authentication path.

The addressed path expander threads the typed internal-node hash by `.ofLeft` and `.ofRight`.
This matters when equal child pairs at different tree positions are distinct complete hash
queries.  No collision assumption or probability claim is used here.

## Main results

* `exists_selectedValueAt_ne_of_ne` finds a selected typed leaf index witnessing tuple
  disagreement.
* `batchToSingleProofAddressed` expands an addressed pruned proof at a selected leaf.
* `getPutativeRootAddressedWithHash_batchToSingleProofAddressed` proves root preservation.
* `BatchOpening.selectedPathDisagreement_of_accepted` packages the leaf, both generated paths,
  and both single-path root equations for two accepted full openings.
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree

universe u

variable {Y : Type u}

/-- Every well-typed batch proof exposes at least one selected leaf. This is the indexed
witness form of `BatchProof.anySelected_of_batchProof`. -/
theorem BatchProof.exists_selected {s : Skeleton} {selector : LeafData Bool s}
    (proof : BatchProof Y selector) :
    ∃ index : SkeletonLeafIndex s, selector.get index = true := by
  induction proof with
  | leaf => exact ⟨.ofLeaf, rfl⟩
  | internalBoth leftProof rightProof ihLeft ihRight =>
      obtain ⟨index, selected⟩ := ihLeft
      exact ⟨.ofLeft index, by simpa using selected⟩
  | pruneRight hright rightRoot leftProof ih =>
      obtain ⟨index, selected⟩ := ih
      exact ⟨.ofLeft index, by simpa using selected⟩
  | pruneLeft hleft leftRoot rightProof ih =>
      obtain ⟨index, selected⟩ := ih
      exact ⟨.ofRight index, by simpa using selected⟩

/-- Unequal selected-value tuples for one selector disagree at a concrete selected leaf. -/
theorem exists_selectedValueAt_ne_of_ne {s : Skeleton} {selector : LeafData Bool s}
    (values₁ values₂ : SelectedValues Y selector) (hne : values₁ ≠ values₂) :
    ∃ index : SkeletonLeafIndex s, ∃ selected : selector.get index = true,
      selectedValueAt values₁ index selected ≠ selectedValueAt values₂ index selected := by
  induction selector with
  | leaf selected =>
      cases selected with
      | false =>
          have heq : values₁ = values₂ := by
            cases values₁
            cases values₂
            rfl
          exact (hne heq).elim
      | true => exact ⟨.ofLeaf, rfl, hne⟩
  | @internal left right leftSelector rightSelector ihLeft ihRight =>
      by_cases hleft : values₁.1 = values₂.1
      · have hright : values₁.2 ≠ values₂.2 := by
          intro heq
          exact hne (Prod.ext hleft heq)
        obtain ⟨index, selected, hvalue⟩ := ihRight values₁.2 values₂.2 hright
        refine ⟨.ofRight index, by simpa using selected, ?_⟩
        simpa only [selectedValueAt] using hvalue
      · obtain ⟨index, selected, hvalue⟩ := ihLeft values₁.1 values₂.1 hleft
        refine ⟨.ofLeft index, by simpa using selected, ?_⟩
        simpa only [selectedValueAt] using hvalue

/-- Expand an addressed pruned batch proof into the ordinary authentication path at a selected
leaf.  Recomputed sibling subroots use the typed hash reindexed to that sibling subtree. -/
def batchToSingleProofAddressed : {s : Skeleton} →
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y) →
    {selector : LeafData Bool s} → SelectedValues Y selector → BatchProof Y selector →
    (index : SkeletonLeafIndex s) → selector.get index = true →
      List.Vector Y index.depth
  | _, _, _, _, .leaf, .ofLeaf, _ => List.Vector.nil
  | _, nodeHash, _, values, .internalBoth leftProof rightProof, .ofLeft index, selected =>
      List.Vector.cons
        (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
          (fun address => nodeHash (.ofRight address)) values.2 rightProof)
        (batchToSingleProofAddressed (fun address => nodeHash (.ofLeft address))
          values.1 leftProof index (by simpa using selected))
  | _, nodeHash, _, values, .internalBoth leftProof rightProof, .ofRight index, selected =>
      List.Vector.cons
        (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
          (fun address => nodeHash (.ofLeft address)) values.1 leftProof)
        (batchToSingleProofAddressed (fun address => nodeHash (.ofRight address))
          values.2 rightProof index (by simpa using selected))
  | _, nodeHash, _, values, .pruneRight _ rightRoot leftProof, .ofLeft index, selected =>
      List.Vector.cons rightRoot
        (batchToSingleProofAddressed (fun address => nodeHash (.ofLeft address))
          values.1 leftProof index (by simpa using selected))
  | _, _, .internal _ rightSelector, _, .pruneRight hright _ _, .ofRight index, selected =>
      False.elim (by
        have hany := LeafData.anySelected_of_get index (by simpa using selected)
        simp [hright] at hany)
  | _, nodeHash, _, values, .pruneLeft _ leftRoot rightProof, .ofRight index, selected =>
      List.Vector.cons leftRoot
        (batchToSingleProofAddressed (fun address => nodeHash (.ofRight address))
          values.2 rightProof index (by simpa using selected))
  | _, _, .internal leftSelector _, _, .pruneLeft hleft _ _, .ofLeft index, selected =>
      False.elim (by
        have hany := LeafData.anySelected_of_get index (by simpa using selected)
        simp [hleft] at hany)

/-- Expanding an addressed batch proof at any selected leaf preserves its putative root. -/
theorem getPutativeRootAddressedWithHash_batchToSingleProofAddressed
    {s : Skeleton} (nodeHash : SkeletonInternalIndex s → Y → Y → Y)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (index : SkeletonLeafIndex s)
    (selected : selector.get index = true) :
    AddressedMerkleTree.getPutativeRootAddressedWithHash nodeHash index
        (selectedValueAt values index selected)
        (batchToSingleProofAddressed nodeHash values proof index selected) =
      AddressedMerkleTree.getPutativeBatchRootAddressedWithHash nodeHash values proof := by
  induction proof with
  | leaf => cases index; rfl
  | internalBoth leftProof rightProof ihLeft ihRight =>
      cases index with
      | ofLeft index =>
          exact congrArg₂ (nodeHash .ofInternal)
            (ihLeft (fun address => nodeHash (.ofLeft address)) values.1 index
              (by simpa using selected)) rfl
      | ofRight index =>
          exact congrArg₂ (nodeHash .ofInternal) rfl
            (ihRight (fun address => nodeHash (.ofRight address)) values.2 index
              (by simpa using selected))
  | pruneRight hright rightRoot leftProof ih =>
      cases index with
      | ofLeft index =>
          exact congrArg₂ (nodeHash .ofInternal)
            (ih (fun address => nodeHash (.ofLeft address)) values.1 index
              (by simpa using selected)) rfl
      | ofRight index =>
          exact absurd (LeafData.anySelected_of_get index (by simpa using selected))
            (by simp [hright])
  | pruneLeft hleft leftRoot rightProof ih =>
      cases index with
      | ofRight index =>
          exact congrArg₂ (nodeHash .ofInternal) rfl
            (ih (fun address => nodeHash (.ofRight address)) values.2 index
              (by simpa using selected))
      | ofLeft index =>
          exact absurd (LeafData.anySelected_of_get index (by simpa using selected))
            (by simp [hleft])

/-- The ordinary batch-to-single path is the constant-address specialization of the addressed
expander.  This exposes the existing unaddressed single-path kernel as a direct corollary. -/
theorem batchToSingleProofAddressed_const (hashFn : Y → Y → Y)
    {s : Skeleton} {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (index : SkeletonLeafIndex s)
    (selected : selector.get index = true) :
    batchToSingleProofAddressed (fun _ => hashFn) values proof index selected =
      batchToSingleProof hashFn values proof index selected := by
  induction proof with
  | leaf => cases index; rfl
  | internalBoth leftProof rightProof ihLeft ihRight =>
      cases index with
      | ofLeft index =>
          simp only [batchToSingleProofAddressed, batchToSingleProof]
          apply congrArg₂ List.Vector.cons
          · exact AddressedMerkleTree.getPutativeBatchRootAddressedWithHash_const
              hashFn values.2 rightProof
          · convert ihLeft values.1 index (by simpa using selected) using 1
      | ofRight index =>
          simp only [batchToSingleProofAddressed, batchToSingleProof]
          apply congrArg₂ List.Vector.cons
          · exact AddressedMerkleTree.getPutativeBatchRootAddressedWithHash_const
              hashFn values.1 leftProof
          · convert ihRight values.2 index (by simpa using selected) using 1
  | pruneRight hright rightRoot leftProof ih =>
      cases index with
      | ofLeft index =>
          simp only [batchToSingleProofAddressed, batchToSingleProof]
          apply congrArg (List.Vector.cons rightRoot)
          convert ih values.1 index (by simpa using selected) using 1
      | ofRight index =>
          exact absurd (LeafData.anySelected_of_get index (by simpa using selected))
            (by simp [hright])
  | pruneLeft hleft leftRoot rightProof ih =>
      cases index with
      | ofRight index =>
          simp only [batchToSingleProofAddressed, batchToSingleProof]
          apply congrArg (List.Vector.cons leftRoot)
          convert ih values.2 index (by simpa using selected) using 1
      | ofLeft index =>
          exact absurd (LeafData.anySelected_of_get index (by simpa using selected))
            (by simp [hleft])

/-- Unequal pruned proofs for one selector disagree on the expanded authentication path of
some selected leaf. The selected values may differ as well: proof-data disagreement remains
observable inside the subtree where the proof first differs. -/
theorem exists_batchToSingleProofAddressed_ne_of_ne {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y)
    {selector : LeafData Bool s} (values₁ values₂ : SelectedValues Y selector)
    (proof₁ proof₂ : BatchProof Y selector) (hne : proof₁ ≠ proof₂) :
    ∃ index : SkeletonLeafIndex s, ∃ selected : selector.get index = true,
      batchToSingleProofAddressed nodeHash values₁ proof₁ index selected ≠
        batchToSingleProofAddressed nodeHash values₂ proof₂ index selected := by
  induction proof₁ with
  | leaf =>
      cases proof₂
      exact (hne rfl).elim
  | internalBoth leftProof₁ rightProof₁ ihLeft ihRight =>
      cases proof₂ with
      | internalBoth leftProof₂ rightProof₂ =>
          rcases Classical.em (leftProof₁ = leftProof₂) with hleft | hleft
          · have hright : rightProof₁ ≠ rightProof₂ := by
              intro hright
              subst leftProof₂
              subst rightProof₂
              exact hne rfl
            obtain ⟨index, selected, hpath⟩ :=
              ihRight (fun address => nodeHash (.ofRight address))
                values₁.2 values₂.2 rightProof₂ hright
            refine ⟨.ofRight index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            apply List.Vector.toList_injective
            have hlist := congrArg List.Vector.toList heq
            exact (List.cons.inj (by
              simpa only [batchToSingleProofAddressed, List.Vector.toList_cons] using hlist)).2
          · obtain ⟨index, selected, hpath⟩ :=
              ihLeft (fun address => nodeHash (.ofLeft address))
                values₁.1 values₂.1 leftProof₂ hleft
            refine ⟨.ofLeft index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            apply List.Vector.toList_injective
            have hlist := congrArg List.Vector.toList heq
            exact (List.cons.inj (by
              simpa only [batchToSingleProofAddressed, List.Vector.toList_cons] using hlist)).2
      | pruneRight hright rightRoot leftProof =>
          have hselected := rightProof₁.anySelected_of_batchProof
          exact False.elim (by simp [hright] at hselected)
      | pruneLeft hleft leftRoot rightProof =>
          have hselected := leftProof₁.anySelected_of_batchProof
          exact False.elim (by simp [hleft] at hselected)
  | pruneRight hright₁ rightRoot₁ leftProof₁ ih =>
      cases proof₂ with
      | internalBoth leftProof₂ rightProof₂ =>
          have hselected := rightProof₂.anySelected_of_batchProof
          exact False.elim (by simp [hright₁] at hselected)
      | pruneRight hright₂ rightRoot₂ leftProof₂ =>
          rcases Classical.em (rightRoot₁ = rightRoot₂) with hroot | hroot
          · have hproof : leftProof₁ ≠ leftProof₂ := by
              intro hproof
              subst rightRoot₂
              subst leftProof₂
              exact hne rfl
            obtain ⟨index, selected, hpath⟩ :=
              ih (fun address => nodeHash (.ofLeft address))
                values₁.1 values₂.1 leftProof₂ hproof
            refine ⟨.ofLeft index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            apply List.Vector.toList_injective
            have hlist := congrArg List.Vector.toList heq
            exact (List.cons.inj (by
              simpa only [batchToSingleProofAddressed, List.Vector.toList_cons] using hlist)).2
          · obtain ⟨index, selected⟩ := leftProof₁.exists_selected
            refine ⟨.ofLeft index, by simpa using selected, ?_⟩
            intro heq
            apply hroot
            have hlist := congrArg List.Vector.toList heq
            exact (List.cons.inj (by
              simpa only [batchToSingleProofAddressed, List.Vector.toList_cons] using hlist)).1
      | pruneLeft hleft₂ leftRoot₂ rightProof₂ =>
          have hselected := leftProof₁.anySelected_of_batchProof
          exact False.elim (by simp [hleft₂] at hselected)
  | pruneLeft hleft₁ leftRoot₁ rightProof₁ ih =>
      cases proof₂ with
      | internalBoth leftProof₂ rightProof₂ =>
          have hselected := leftProof₂.anySelected_of_batchProof
          exact False.elim (by simp [hleft₁] at hselected)
      | pruneRight hright₂ rightRoot₂ leftProof₂ =>
          have hselected := rightProof₁.anySelected_of_batchProof
          exact False.elim (by simp [hright₂] at hselected)
      | pruneLeft hleft₂ leftRoot₂ rightProof₂ =>
          rcases Classical.em (leftRoot₁ = leftRoot₂) with hroot | hroot
          · have hproof : rightProof₁ ≠ rightProof₂ := by
              intro hproof
              subst leftRoot₂
              subst rightProof₂
              exact hne rfl
            obtain ⟨index, selected, hpath⟩ :=
              ih (fun address => nodeHash (.ofRight address))
                values₁.2 values₂.2 rightProof₂ hproof
            refine ⟨.ofRight index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            apply List.Vector.toList_injective
            have hlist := congrArg List.Vector.toList heq
            exact (List.cons.inj (by
              simpa only [batchToSingleProofAddressed, List.Vector.toList_cons] using hlist)).2
          · obtain ⟨index, selected⟩ := rightProof₁.exists_selected
            refine ⟨.ofRight index, by simpa using selected, ?_⟩
            intro heq
            apply hroot
            have hlist := congrArg List.Vector.toList heq
            exact (List.cons.inj (by
              simpa only [batchToSingleProofAddressed, List.Vector.toList_cons] using hlist)).1

/-- If a concrete pruned proof, mapped through `some`, differs from the canonical proof read
from a partial tree, then some selected concrete authentication path differs from the tree's
ordinary generated path. No consistency assumption on the partial tree or node hash is needed:
the witness follows the first differing stored frontier value. -/
theorem exists_batchToSingleProofAddressed_map_some_ne_generateProof {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (tree : FullData (Option Y) s)
    (hne : proof.map some ≠
      generateBatchProof tree selector proof.anySelected_of_batchProof) :
    ∃ index : SkeletonLeafIndex s, ∃ selected : selector.get index = true,
      (batchToSingleProofAddressed nodeHash values proof index selected).toList.map some ≠
        (generateProof tree index).toList := by
  induction proof with
  | leaf =>
      cases tree
      exact (hne rfl).elim
  | internalBoth leftProof rightProof ihLeft ihRight =>
      cases tree with
      | internal root leftTree rightTree =>
          have hleftSelected := leftProof.anySelected_of_batchProof
          have hrightSelected := rightProof.anySelected_of_batchProof
          by_cases hleft : leftProof.map some ≠
              generateBatchProof leftTree _ hleftSelected
          · obtain ⟨index, selected, hpath⟩ :=
              ihLeft (fun address => nodeHash (.ofLeft address))
                values.1 leftTree hleft
            refine ⟨.ofLeft index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            change _ ::
                (batchToSingleProofAddressed (fun address => nodeHash (.ofLeft address))
                  values.1 leftProof index selected).toList.map some =
              _ :: (generateProof leftTree index).toList at heq
            exact (List.cons.inj heq).2
          · have hright : rightProof.map some ≠
                generateBatchProof rightTree _ hrightSelected := by
              intro hright
              apply hne
              simp only [BatchProof.map]
              rw [not_not.mp hleft, hright]
              simp only [generateBatchProof]
              split
              · rfl
              · rename_i _ hr
                exact Bool.noConfusion (hrightSelected.symm.trans hr)
              · rename_i hl _
                exact Bool.noConfusion (hleftSelected.symm.trans hl)
              · rename_i hl _
                exact Bool.noConfusion (hleftSelected.symm.trans hl)
            obtain ⟨index, selected, hpath⟩ :=
              ihRight (fun address => nodeHash (.ofRight address))
                values.2 rightTree hright
            refine ⟨.ofRight index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            change _ ::
                (batchToSingleProofAddressed (fun address => nodeHash (.ofRight address))
                  values.2 rightProof index selected).toList.map some =
              _ :: (generateProof rightTree index).toList at heq
            exact (List.cons.inj heq).2
  | pruneRight hright rightRoot leftProof ih =>
      cases tree with
      | internal root leftTree rightTree =>
          have hleftSelected := leftProof.anySelected_of_batchProof
          by_cases hroot : some rightRoot ≠ rightTree.getRootValue
          · obtain ⟨index, selected⟩ := leftProof.exists_selected
            refine ⟨.ofLeft index, by simpa using selected, ?_⟩
            intro heq
            apply hroot
            change some rightRoot :: _ = rightTree.getRootValue :: _ at heq
            exact (List.cons.inj heq).1
          · have hproof : leftProof.map some ≠
                generateBatchProof leftTree _ hleftSelected := by
              intro hproof
              apply hne
              simp only [BatchProof.map]
              rw [not_not.mp hroot, hproof]
              simp only [generateBatchProof]
              split
              · rename_i _ hr
                exact Bool.noConfusion (hright.symm.trans hr)
              · rfl
              · rename_i hl _
                exact Bool.noConfusion (hleftSelected.symm.trans hl)
              · rename_i hl _
                exact Bool.noConfusion (hleftSelected.symm.trans hl)
            obtain ⟨index, selected, hpath⟩ :=
              ih (fun address => nodeHash (.ofLeft address)) values.1 leftTree hproof
            refine ⟨.ofLeft index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            change some rightRoot ::
                (batchToSingleProofAddressed (fun address => nodeHash (.ofLeft address))
                  values.1 leftProof index selected).toList.map some =
              rightTree.getRootValue :: (generateProof leftTree index).toList at heq
            exact (List.cons.inj heq).2
  | pruneLeft hleft leftRoot rightProof ih =>
      cases tree with
      | internal root leftTree rightTree =>
          have hrightSelected := rightProof.anySelected_of_batchProof
          by_cases hroot : some leftRoot ≠ leftTree.getRootValue
          · obtain ⟨index, selected⟩ := rightProof.exists_selected
            refine ⟨.ofRight index, by simpa using selected, ?_⟩
            intro heq
            apply hroot
            change some leftRoot :: _ = leftTree.getRootValue :: _ at heq
            exact (List.cons.inj heq).1
          · have hproof : rightProof.map some ≠
                generateBatchProof rightTree _ hrightSelected := by
              intro hproof
              apply hne
              simp only [BatchProof.map]
              rw [not_not.mp hroot, hproof]
              simp only [generateBatchProof]
              split
              · rename_i hl _
                exact Bool.noConfusion (hleft.symm.trans hl)
              · rename_i hl _
                exact Bool.noConfusion (hleft.symm.trans hl)
              · rfl
              · rename_i _ hr
                exact Bool.noConfusion (hrightSelected.symm.trans hr)
            obtain ⟨index, selected, hpath⟩ :=
              ih (fun address => nodeHash (.ofRight address)) values.2 rightTree hproof
            refine ⟨.ofRight index, by simpa using selected, ?_⟩
            intro heq
            apply hpath
            change some leftRoot ::
                (batchToSingleProofAddressed (fun address => nodeHash (.ofRight address))
                  values.2 rightProof index selected).toList.map some =
              leftTree.getRootValue :: (generateProof rightTree index).toList at heq
            exact (List.cons.inj heq).2

namespace BatchOpening

/-- Pure acceptance of a packaged batch opening under a typed-node hash. -/
def AcceptedAddressedWithHash {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y) (root : Y)
    (opening : BatchOpening Y s) : Prop :=
  AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
    nodeHash opening.values opening.proof = root

/-- At the universe supported by the existing monadic verifier, pure acceptance is exactly a
successful deterministic verifier run. -/
theorem acceptedAddressedWithHash_iff_verify_id {Y₀ : Type} [DecidableEq Y₀]
    {s : Skeleton} (nodeHash : SkeletonInternalIndex s → Y₀ → Y₀ → Y₀)
    (root : Y₀) (opening : BatchOpening Y₀ s) :
    AcceptedAddressedWithHash nodeHash root opening ↔
      Id.run (AddressedMerkleTree.verifyBatchProofAddressedM
        (fun address left right => pure (nodeHash address left right))
        opening.values root opening.proof) = true := by
  simp [AcceptedAddressedWithHash, AddressedMerkleTree.verifyBatchProofAddressedM]

/-- The complete single-path witness extracted from two batch openings.  Separate selection
proofs make the package usable even before a same-selector equality is eliminated. -/
structure SelectedPathDisagreement {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y) (root : Y)
    (opening₁ opening₂ : BatchOpening Y s) where
  /-- Selected leaf where the two claimed tuples differ. -/
  index : SkeletonLeafIndex s
  /-- The first opening selects `index`. -/
  selected₁ : opening₁.selector.get index = true
  /-- The second opening selects `index`. -/
  selected₂ : opening₂.selector.get index = true
  /-- The selected leaf values differ. -/
  leaf_ne : selectedValueAt opening₁.values index selected₁ ≠
    selectedValueAt opening₂.values index selected₂
  /-- Generated single path for the first batch opening. -/
  proof₁ : List.Vector Y index.depth
  /-- Generated single path for the second batch opening. -/
  proof₂ : List.Vector Y index.depth
  /-- `proof₁` is the canonical addressed expansion of the first pruned proof. -/
  proof₁_generated : proof₁ =
    batchToSingleProofAddressed nodeHash opening₁.values opening₁.proof index selected₁
  /-- `proof₂` is the canonical addressed expansion of the second pruned proof. -/
  proof₂_generated : proof₂ =
    batchToSingleProofAddressed nodeHash opening₂.values opening₂.proof index selected₂
  /-- The first generated single opening recomputes the accepted root. -/
  verifies₁ : AddressedMerkleTree.getPutativeRootAddressedWithHash nodeHash index
    (selectedValueAt opening₁.values index selected₁) proof₁ = root
  /-- The second generated single opening recomputes the accepted root. -/
  verifies₂ : AddressedMerkleTree.getPutativeRootAddressedWithHash nodeHash index
    (selectedValueAt opening₂.values index selected₂) proof₂ = root

/-- The packaged paths feed directly into the addressed single-path collision kernel.  The
returned collision includes the typed internal-node address at which the paths merge. -/
theorem SelectedPathDisagreement.exists_addressedCollision [DecidableEq Y]
    {s : Skeleton} {nodeHash : SkeletonInternalIndex s → Y → Y → Y} {root : Y}
    {opening₁ opening₂ : BatchOpening Y s}
    (witness : SelectedPathDisagreement nodeHash root opening₁ opening₂) :
    ∃ collision,
      AddressedMerkleTree.findCollisionAddressed nodeHash witness.index
        witness.proof₁ witness.proof₂
        (selectedValueAt opening₁.values witness.index witness.selected₁)
        (selectedValueAt opening₂.values witness.index witness.selected₂) = some collision ∧
      AddressedMerkleTree.AddressedCollision nodeHash collision :=
  AddressedMerkleTree.getPutativeRootAddressedWithHash_binding_collision
    nodeHash witness.index witness.proof₁ witness.proof₂
    (selectedValueAt opening₁.values witness.index witness.selected₁)
    (selectedValueAt opening₂.values witness.index witness.selected₂)
    (witness.verifies₁.trans witness.verifies₂.symm) witness.leaf_ne

/-- Two accepted full batch openings with the same selector and unequal selected-value payloads
yield a concrete selected leaf disagreement and both canonical addressed single paths verifying
against the same root. -/
theorem selectedPathDisagreement_of_accepted {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → Y → Y → Y) (root : Y)
    (opening₁ opening₂ : BatchOpening Y s)
    (hselector : opening₁.selector = opening₂.selector)
    (hvalues : ¬ HEq opening₁.values opening₂.values)
    (haccepted₁ : AcceptedAddressedWithHash nodeHash root opening₁)
    (haccepted₂ : AcceptedAddressedWithHash nodeHash root opening₂) :
    Nonempty (SelectedPathDisagreement nodeHash root opening₁ opening₂) := by
  rcases opening₁ with ⟨selector₁, values₁, batchProof₁⟩
  rcases opening₂ with ⟨selector₂, values₂, batchProof₂⟩
  dsimp only at hselector hvalues haccepted₁ haccepted₂ ⊢
  subst selector₂
  have hne : values₁ ≠ values₂ := by
    intro heq
    exact hvalues (heq ▸ HEq.rfl)
  obtain ⟨index, selected, hleaf⟩ :=
    exists_selectedValueAt_ne_of_ne values₁ values₂ hne
  let proof₁ := batchToSingleProofAddressed
    nodeHash values₁ batchProof₁ index selected
  let proof₂ := batchToSingleProofAddressed
    nodeHash values₂ batchProof₂ index selected
  refine ⟨⟨index, selected, selected, hleaf, proof₁, proof₂, rfl, rfl, ?_, ?_⟩⟩
  · exact (getPutativeRootAddressedWithHash_batchToSingleProofAddressed
      nodeHash values₁ batchProof₁ index selected).trans haccepted₁
  · exact (getPutativeRootAddressedWithHash_batchToSingleProofAddressed
      nodeHash values₂ batchProof₂ index selected).trans haccepted₂

end BatchOpening

end InductiveMerkleTree
