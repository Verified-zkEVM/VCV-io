/-
Copyright (c) 2026 Vitalik Buterin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin
-/
import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

/-!
# Merkle Binding (Collision Lemma)

The structural collision lemma for inductive Merkle trees, often called the
"Collision Lemma" (see SNARGs book §18.3): two distinct verifying openings of
the same Merkle root, taken at the same leaf index with the same sibling
proof, entail a collision in the underlying hash function.

Stated against `InductiveMerkleTree.getPutativeRootWithHash` from
[`VCVio/CryptoFoundations/MerkleTree/Inductive/Defs.lean`](Defs.lean): if
recomputed roots agree on inputs `x ≠ y` along an identical path, the proof
extracts an explicit pair witnessing a hash collision.

This is the pure / structural layer of binding; a probabilistic-level
binding-from-collision-resistance reduction is intended to be layered on top
following the `bindingAdvantage_toCommitment_le_keyedCRAdvantage` pattern in
[`VCVio/CryptoFoundations/HashCommitment.lean`](../HashCommitment.lean).

## Main Definitions

- `InductiveMerkleTree.Collision` — predicate stating that two pairs of
  inputs collide under a hash function `H : α × α → α`.

## Main Results

- `InductiveMerkleTree.getPutativeRootWithHash_binding` — from two distinct
  leaf values producing the same putative root, extract a hash collision.

## References

- Justin Thaler. *Proofs, Arguments, and Zero-Knowledge.* §18.3 (Collision
  Lemma for Merkle trees).

-/


namespace InductiveMerkleTree

open BinaryTree

variable {α : Type _}

/-- Two distinct inputs producing the same hash output: a collision for `H`. -/
def Collision (H : α × α → α) (L₁ R₁ L₂ R₂ : α) : Prop :=
  (L₁, R₁) ≠ (L₂, R₂) ∧ H (L₁, R₁) = H (L₂, R₂)

/-- The Merkle binding theorem.

    If two distinct leaf values `x ≠ y` produce the same putative root under
    *the same path `idx` and the same sibling proof*, then we can extract a
    collision in the hash function.

    Proof strategy: induction on `idx`. At each non-leaf step, the recursion
    of `getPutativeRootWithHash` exposes the topmost hash. Either its two
    arguments already coincide (recurse on the subtree) or they differ
    (collision at this level). -/
theorem getPutativeRootWithHash_binding
    (H : α × α → α)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof : List.Vector α idx.depth)
    (x y : α)
    (hne : x ≠ y)
    (heq : getPutativeRootWithHash idx x proof (fun a b => H (a, b))
         = getPutativeRootWithHash idx y proof (fun a b => H (a, b))) :
    ∃ L₁ R₁ L₂ R₂, Collision H L₁ R₁ L₂ R₂ := by
  induction idx generalizing x y with
  | ofLeaf =>
      simp only [getPutativeRootWithHash] at heq
      exact absurd heq hne
  | ofLeft idxLeft ih =>
      simp only [getPutativeRootWithHash] at heq
      set subL := getPutativeRootWithHash idxLeft x proof.tail (fun a b => H (a, b))
      set subR := getPutativeRootWithHash idxLeft y proof.tail (fun a b => H (a, b))
      rcases eq_or_ne subL subR with hsub | hsub
      · exact ih proof.tail x y hne hsub
      · refine ⟨subL, proof.head, subR, proof.head, ?_, heq⟩
        intro hpair
        exact hsub ((Prod.mk.injEq subL proof.head subR proof.head).mp hpair).1
  | ofRight idxRight ih =>
      simp only [getPutativeRootWithHash] at heq
      set subL := getPutativeRootWithHash idxRight x proof.tail (fun a b => H (a, b))
      set subR := getPutativeRootWithHash idxRight y proof.tail (fun a b => H (a, b))
      rcases eq_or_ne subL subR with hsub | hsub
      · exact ih proof.tail x y hne hsub
      · refine ⟨proof.head, subL, proof.head, subR, ?_, heq⟩
        intro hpair
        exact hsub ((Prod.mk.injEq proof.head subL proof.head subR).mp hpair).2

end InductiveMerkleTree
