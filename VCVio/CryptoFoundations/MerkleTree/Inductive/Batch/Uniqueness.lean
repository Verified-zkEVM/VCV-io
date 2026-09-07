/-
Copyright (c) 2026 IAOM / Equation Capital dba Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abraxas1010 (IAOM / Apoth3osis)
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs

/-!
# Batch Opening Uniqueness

The batch analogue of `VCVio.CryptoFoundations.MerkleTree.Inductive.Uniqueness`: when the
hash function is injective (`Function.Injective2`), any two batch openings for the *same*
selector that produce the same putative root must agree on the claimed values of every
selected leaf and on the entire (pruned) authentication data. The Merkle root uniquely
determines the committed values at all opened positions simultaneously.

`Function.Injective2` is **not** a realistic assumption on a compressing hash — no
`α × α → α` compression is injective on a nontrivial type. These theorems are structural
sanity results (the pruned representation carries no slack). The cryptographically
meaningful binding statement is the *constructive collision* result: see `Binding.lean`
and the cross-selector `getPutativeBatchRootWithHash_binding` in `ToSingle.lean`, which
assume nothing about the hash and return a collision as data.

Two points specific to the batch setting:

* Cross-shape disagreements are impossible by typing plus inhabitation: a `pruneRight`
  opening cannot be confused with an `internalBoth` opening of the same selector, because
  the latter carries a `BatchProof` for a subtree that the former's hypothesis says has no
  selected leaves, and `BatchProof` is uninhabited on such selectors
  (`BatchProof.anySelected_of_batchProof`).
* The claimed-value tuples also agree on their (vacuous) components at pruned subtrees,
  since `SelectedValues` degenerates to a subsingleton there
  (`selectedValues_eq_of_not_anySelected`).

## Main results

- `getPutativeBatchRootWithHash_unique` — batch opening uniqueness under an injective hash
- `getPutativeBatchRootWithHash_batch_roots_ne_of_ne` — contrapositive: distinct claimed
  values at the same selector produce distinct roots
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree

variable {α : Type _}

/-- Over a selector with no selected leaves, the type of claimed values is degenerate: any
two values tuples are equal (every component is a `PUnit`). -/
theorem selectedValues_eq_of_not_anySelected {s : Skeleton} {sel : LeafData Bool s}
    (h : sel.anySelected = false) (v₁ v₂ : SelectedValues α sel) : v₁ = v₂ := by
  induction sel with
  | leaf b =>
    cases b with
    | false => rfl
    | true => simp [LeafData.anySelected] at h
  | internal l r ihl ihr =>
    simp only [LeafData.anySelected, Bool.or_eq_false_iff] at h
    exact Prod.ext (ihl h.1 v₁.1 v₂.1) (ihr h.2 v₁.2 v₂.2)

/-- **Batch opening uniqueness.** When `hashFn` is injective, two batch openings for the
same selector that produce the same putative root must agree on both the claimed selected
values and the entire pruned authentication data. -/
theorem getPutativeBatchRootWithHash_unique
    (hashFn : α → α → α) (hinj : Function.Injective2 hashFn)
    {s : Skeleton} {sel : LeafData Bool s}
    (v₁ v₂ : SelectedValues α sel) (p₁ p₂ : BatchProof α sel)
    (heq : getPutativeBatchRootWithHash hashFn v₁ p₁
         = getPutativeBatchRootWithHash hashFn v₂ p₂) :
    v₁ = v₂ ∧ p₁ = p₂ := by
  induction p₁ with
  | leaf =>
    cases p₂ with
    | leaf => exact ⟨heq, rfl⟩
  | internalBoth pl₁ pr₁ ihl ihr =>
    cases p₂ with
    | internalBoth pl₂ pr₂ =>
      simp only [getPutativeBatchRootWithHash] at heq
      obtain ⟨hL, hR⟩ := hinj heq
      obtain ⟨hvl, hpl⟩ := ihl v₁.1 v₂.1 pl₂ hL
      obtain ⟨hvr, hpr⟩ := ihr v₁.2 v₂.2 pr₂ hR
      exact ⟨Prod.ext hvl hvr, by rw [hpl, hpr]⟩
    | pruneRight hr₂ rightRoot₂ pl₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pr₁) (by simp [hr₂])
    | pruneLeft hl₂ leftRoot₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pl₁) (by simp [hl₂])
  | pruneRight hr₁ rightRoot₁ pl₁ ih =>
    cases p₂ with
    | internalBoth pl₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pr₂) (by simp [hr₁])
    | pruneRight hr₂ rightRoot₂ pl₂ =>
      simp only [getPutativeBatchRootWithHash] at heq
      obtain ⟨hL, hRoot⟩ := hinj heq
      obtain ⟨hvl, hpl⟩ := ih v₁.1 v₂.1 pl₂ hL
      refine ⟨Prod.ext hvl (selectedValues_eq_of_not_anySelected hr₁ v₁.2 v₂.2), ?_⟩
      rw [hpl, hRoot]
    | pruneLeft hl₂ leftRoot₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pr₂) (by simp [hr₁])
  | pruneLeft hl₁ leftRoot₁ pr₁ ih =>
    cases p₂ with
    | internalBoth pl₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pl₂) (by simp [hl₁])
    | pruneRight hr₂ rightRoot₂ pl₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pl₂) (by simp [hl₁])
    | pruneLeft hl₂ leftRoot₂ pr₂ =>
      simp only [getPutativeBatchRootWithHash] at heq
      obtain ⟨hRoot, hR⟩ := hinj heq
      obtain ⟨hvr, hpr⟩ := ih v₁.2 v₂.2 pr₂ hR
      refine ⟨Prod.ext (selectedValues_eq_of_not_anySelected hl₁ v₁.1 v₂.1) hvr, ?_⟩
      rw [hpr, hRoot]

/-- Contrapositive of batch uniqueness: with an injective hash, distinct claimed value
tuples for the same selector always produce distinct putative roots, regardless of the
authentication data used. -/
theorem getPutativeBatchRootWithHash_batch_roots_ne_of_ne
    (hashFn : α → α → α) (hinj : Function.Injective2 hashFn)
    {s : Skeleton} {sel : LeafData Bool s}
    (v₁ v₂ : SelectedValues α sel) (p₁ p₂ : BatchProof α sel) (hne : v₁ ≠ v₂) :
    getPutativeBatchRootWithHash hashFn v₁ p₁
      ≠ getPutativeBatchRootWithHash hashFn v₂ p₂ :=
  fun heq => hne (getPutativeBatchRootWithHash_unique hashFn hinj v₁ v₂ p₁ p₂ heq).1

end InductiveMerkleTree
