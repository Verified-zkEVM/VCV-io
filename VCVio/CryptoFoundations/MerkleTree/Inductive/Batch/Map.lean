/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs

/-!
# Functoriality of Batch Merkle Openings

This file defines the pointwise action of a function on the selected values and pruned
authentication hashes of a batch opening. The operations preserve the selector and hence
the intrinsic pruning shape. Identity, composition, honest generation, and putative-root
compatibility laws make the API suitable for comparing concrete openings with openings in
a partial tree such as `FullData (Option α) s`.
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Apply a function to each claimed selected value, preserving the selector. -/
@[simp, grind]
def SelectedValues.map (f : α → β) : {s : Skeleton} → {sel : LeafData Bool s} →
    SelectedValues α sel → SelectedValues β sel
  | _, .leaf true, value => f value
  | _, .leaf false, _ => PUnit.unit
  | _, .internal _ _, values => (SelectedValues.map f values.1, SelectedValues.map f values.2)

/-- Apply a function to every stored frontier hash in a pruned batch proof. -/
@[simp, grind]
def BatchProof.map (f : α → β) : {s : Skeleton} → {sel : LeafData Bool s} →
    BatchProof α sel → BatchProof β sel
  | _, _, .leaf => .leaf
  | _, _, .internalBoth pl pr => .internalBoth (pl.map f) (pr.map f)
  | _, _, .pruneRight hr rightRoot pl => .pruneRight hr (f rightRoot) (pl.map f)
  | _, _, .pruneLeft hl leftRoot pr => .pruneLeft hl (f leftRoot) (pr.map f)

/-- Mapping the identity function over selected values is the identity. -/
@[simp]
theorem SelectedValues.map_id {s : Skeleton} {sel : LeafData Bool s}
    (values : SelectedValues α sel) : values.map id = values := by
  induction sel with
  | leaf b =>
      cases b with
      | true => rfl
      | false => cases values; rfl
  | internal l r ihl ihr =>
      exact Prod.ext (ihl values.1) (ihr values.2)

/-- Mapping a composite function over selected values is successive mapping. -/
@[simp]
theorem SelectedValues.map_comp (f : α → β) (g : β → γ)
    {s : Skeleton} {sel : LeafData Bool s} (values : SelectedValues α sel) :
    (values.map f).map g = values.map (g ∘ f) := by
  induction sel with
  | leaf b => cases b <;> rfl
  | internal l r ihl ihr =>
      exact Prod.ext (ihl values.1) (ihr values.2)

/-- An injective function induces an injective map on selected-value tuples. -/
theorem SelectedValues.map_injective (f : α → β) (hf : Function.Injective f)
    {s : Skeleton} {sel : LeafData Bool s} (values₁ values₂ : SelectedValues α sel)
    (h : values₁.map f = values₂.map f) : values₁ = values₂ := by
  induction sel with
  | leaf b =>
      cases b with
      | true => exact hf h
      | false => cases values₁; cases values₂; rfl
  | internal l r ihl ihr =>
      apply Prod.ext
      · exact ihl values₁.1 values₂.1 (congrArg Prod.fst h)
      · exact ihr values₁.2 values₂.2 (congrArg Prod.snd h)

/-- Mapping the identity function over a batch proof is the identity. -/
@[simp]
theorem BatchProof.map_id {s : Skeleton} {sel : LeafData Bool s}
    (proof : BatchProof α sel) : proof.map id = proof := by
  induction proof <;> simp_all only [BatchProof.map, id_eq]

/-- Mapping a composite function over a batch proof is successive mapping. -/
@[simp]
theorem BatchProof.map_comp (f : α → β) (g : β → γ)
    {s : Skeleton} {sel : LeafData Bool s} (proof : BatchProof α sel) :
    (proof.map f).map g = proof.map (g ∘ f) := by
  induction proof <;> simp_all only [BatchProof.map, Function.comp_apply]

/-- A function with a left inverse induces an injective map on pruned batch proofs. -/
theorem BatchProof.map_injective_of_leftInverse (f : α → β) (g : β → α)
    (hleft : Function.LeftInverse g f)
    {s : Skeleton} {sel : LeafData Bool s} (proof₁ proof₂ : BatchProof α sel)
    (h : proof₁.map f = proof₂.map f) : proof₁ = proof₂ := by
  have hm := congrArg (BatchProof.map g) h
  have hgf : g ∘ f = id := funext hleft
  simpa only [BatchProof.map_comp, hgf, BatchProof.map_id] using hm

/-- An injective function induces an injective map on pruned batch proofs. -/
theorem BatchProof.map_injective (f : α → β) (hf : Function.Injective f)
    {s : Skeleton} {sel : LeafData Bool s} (proof₁ proof₂ : BatchProof α sel)
    (h : proof₁.map f = proof₂.map f) : proof₁ = proof₂ := by
  induction proof₁ with
  | leaf =>
      cases proof₂ with
      | leaf => rfl
  | internalBoth pl₁ pr₁ ihl ihr =>
      cases proof₂ with
      | internalBoth pl₂ pr₂ =>
          simp only [BatchProof.map] at h
          injection h with _ _ _ _ hpl hpr
          rw [ihl pl₂ hpl, ihr pr₂ hpr]
      | pruneRight hr₂ rightRoot₂ pl₂ => cases h
      | pruneLeft hl₂ leftRoot₂ pr₂ => cases h
  | pruneRight hr₁ rightRoot₁ pl₁ ih =>
      cases proof₂ with
      | internalBoth pl₂ pr₂ => cases h
      | pruneRight hr₂ rightRoot₂ pl₂ =>
          simp only [BatchProof.map] at h
          injection h with _ _ _ _ hroot hp
          rw [hf hroot, ih pl₂ hp]
      | pruneLeft hl₂ leftRoot₂ pr₂ => cases h
  | pruneLeft hl₁ leftRoot₁ pr₁ ih =>
      cases proof₂ with
      | internalBoth pl₂ pr₂ => cases h
      | pruneRight hr₂ rightRoot₂ pl₂ => cases h
      | pruneLeft hl₂ leftRoot₂ pr₂ =>
          simp only [BatchProof.map] at h
          injection h with _ _ _ _ hroot hp
          rw [hf hroot, ih pr₂ hp]

/-- Selecting leaves commutes with pointwise mapping of leaf data. -/
@[simp]
theorem SelectedValues.map_selectedValues (f : α → β) {s : Skeleton}
    (leaves : LeafData α s) (sel : LeafData Bool s) :
    (selectedValues leaves sel).map f = selectedValues (leaves.map f) sel := by
  induction sel with
  | leaf b =>
      cases leaves with
      | leaf value => cases b <;> rfl
  | internal l r ihl ihr =>
      cases leaves with
      | internal left right =>
          exact Prod.ext (ihl left) (ihr right)

/-- Honest proof generation commutes with pointwise mapping of a cached full tree. -/
theorem BatchProof.map_generateBatchProof (f : α → β) {s : Skeleton}
    (cache : FullData α s) (sel : LeafData Bool s) (h : sel.anySelected = true) :
    (generateBatchProof cache sel h).map f = generateBatchProof (cache.map f) sel h := by
  induction sel with
  | leaf b =>
      cases cache with
      | leaf value =>
          cases b with
          | false => simp [LeafData.anySelected] at h
          | true => rfl
  | internal l r ihl ihr =>
      cases cache with
      | internal root left right =>
          simp only [LeafData.anySelected, Bool.or_eq_true] at h
          simp only [FullData.map_internal, generateBatchProof]
          split <;> simp_all [BatchProof.map, FullData.map_getRootValue]

/-- Mapping an opening through a homomorphism of binary hash algebras commutes with
putative-root computation. -/
theorem getPutativeBatchRootWithHash_map
    (f : α → β) (hashα : α → α → α) (hashβ : β → β → β)
    (hhash : ∀ left right, f (hashα left right) = hashβ (f left) (f right))
    {s : Skeleton} {sel : LeafData Bool s} (values : SelectedValues α sel)
    (proof : BatchProof α sel) :
    getPutativeBatchRootWithHash hashβ (values.map f) (proof.map f) =
      f (getPutativeBatchRootWithHash hashα values proof) := by
  induction proof with
  | leaf => rfl
  | internalBoth pl pr ihl ihr =>
      simp only [SelectedValues.map, BatchProof.map, getPutativeBatchRootWithHash,
        ihl values.1, ihr values.2, hhash]
  | pruneRight hr rightRoot pl ih =>
      simp only [SelectedValues.map, BatchProof.map, getPutativeBatchRootWithHash,
        ih values.1, hhash]
  | pruneLeft hl leftRoot pr ih =>
      simp only [SelectedValues.map, BatchProof.map, getPutativeBatchRootWithHash,
        ih values.2, hhash]

end InductiveMerkleTree
