/-
Copyright (c) 2026 Vitalik Buterin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin
-/
import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

/-!
# Merkle Binding (Collision Lemma)

The structural collision lemma for inductive Merkle trees, often called the
"Collision Lemma" (see SNARGs book §18.3): two distinct leaf values that
verify against the same Merkle root — under possibly different sibling
proofs — entail a collision in the underlying hash function.

The hypothesis `x ≠ y` captures that the adversary equivocates on the
*committed value*, which is what binding requires; the case `x = y` with
different sibling proofs is not a binding break, since the committer is
allowed to know multiple valid proofs of the same value.

The hash function is taken in curried form `α → α → α`, matching the
convention used by `getPutativeRootWithHash` and the rest of the Merkle tree
API.

## Main Definitions

- `InductiveMerkleTree.Collision` — a hash collision under `h : α → α → α`.

## Main Results

- `InductiveMerkleTree.getPutativeRootWithHash_binding` — from any two
  distinct leaf values producing the same root at the same leaf index under
  (possibly different) sibling proofs, extract a hash collision.

## References

- Alessandro Chiesa, Eylon Yogev.
  *Building Cryptographic Proofs from Hash Functions* §18.3 (Collision Lemma).
-/


namespace InductiveMerkleTree

open BinaryTree

variable {α : Type _}

/-- Two distinct input pairs producing the same hash output: a collision for
    the curried hash `h : α → α → α`. -/
def Collision (h : α → α → α) (l₁ r₁ l₂ r₂ : α) : Prop :=
  (l₁, r₁) ≠ (l₂, r₂) ∧ h l₁ r₁ = h l₂ r₂

/-- Merkle binding: from two distinct leaf values `x ≠ y` that produce the
    same putative root at the same leaf index under (possibly different)
    sibling proofs, extract a hash collision.

    Note that `idx` is shared — this is binding *at a fixed position*. The
    distinct-position case requires walking down both paths to the lowest
    common ancestor and is handled separately.

    Proof strategy: induction on `idx`. At each non-leaf step, the recursion
    of `getPutativeRootWithHash` exposes a top-level hash. Either the two
    pairs `(subL, proof₁.head)` and `(subR, proof₂.head)` it consumes already
    differ (top-level collision) or they agree component-wise — in which case
    the inputs to the inner recursive calls disagree, justifying the
    inductive call with `subL = subR`. -/
theorem getPutativeRootWithHash_binding
    (h : α → α → α)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α)
    (hne : x ≠ y)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    ∃ l₁ r₁ l₂ r₂, Collision h l₁ r₁ l₂ r₂ := by
  unfold Collision
  induction idx generalizing x y with
  | _ => grind [getPutativeRootWithHash]

end InductiveMerkleTree
