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

We provide both an explicit *constructive* extractor `findCollision`, which
walks down both proofs and returns the quadruplet `(l₁, r₁, l₂, r₂)` at the
first level where the hash inputs disagree, and the corresponding
*existential* corollary `getPutativeRootWithHash_binding`. The constructive
form is needed downstream — e.g. to argue that the colliding pair must
appear in the adversary's query trace, which is how binding gets translated
into a bound on the adversary's success probability in the random oracle
model.

## Main Definitions

- `InductiveMerkleTree.Collision` — a hash collision under `h : α → α → α`.
- `InductiveMerkleTree.findCollision` — explicit collision extractor:
  walks both sibling proofs in lockstep and returns the first quadruplet
  where the top hash inputs disagree.

## Main Results

- `InductiveMerkleTree.findCollision_isCollision` — under `x ≠ y` and
  equal putative roots, `findCollision` returns `some` quadruplet which is
  a `Collision` for `h`.
- `InductiveMerkleTree.getPutativeRootWithHash_binding` — existential
  corollary: from any two distinct leaf values producing the same root at
  the same leaf index under (possibly different) sibling proofs, extract
  a hash collision.

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

/-- Constructive collision extractor for Merkle binding.

    Walks both sibling proofs in lockstep from the root toward the leaf.
    At each non-leaf level, the top hash takes a pair of inputs computed
    from one of the proofs. If those pairs differ between the two proofs
    we return them as a `(l₁, r₁, l₂, r₂)` candidate; otherwise the inputs
    agree component-wise, so the recursive sub-roots must be equal and we
    descend on the smaller index.

    The function never inspects the hash output equality — that obligation
    is discharged externally by `heq` in `findCollision_isCollision`. So
    the returned quadruplet is a *candidate* collision: the pair-inequality
    half of `Collision` always holds by construction, and the
    hash-output-equality half follows from the `heq` hypothesis carried
    through the recursion.

    Returns `none` only at the leaf level (depth zero), where there is no
    hash to collide on. -/
def findCollision [DecidableEq α] (h : α → α → α) {s : Skeleton} :
    (idx : SkeletonLeafIndex s) → (x y : α) →
      List.Vector α idx.depth → List.Vector α idx.depth →
      Option (α × α × α × α)
  | .ofLeaf, _, _, _, _ => none
  | .ofLeft idxLeft, x, y, proof₁, proof₂ =>
      let subL := getPutativeRootWithHash idxLeft x proof₁.tail h
      let subR := getPutativeRootWithHash idxLeft y proof₂.tail h
      if (subL, proof₁.head) = (subR, proof₂.head)
      then findCollision h idxLeft x y proof₁.tail proof₂.tail
      else some (subL, proof₁.head, subR, proof₂.head)
  | .ofRight idxRight, x, y, proof₁, proof₂ =>
      let subL := getPutativeRootWithHash idxRight x proof₁.tail h
      let subR := getPutativeRootWithHash idxRight y proof₂.tail h
      if (proof₁.head, subL) = (proof₂.head, subR)
      then findCollision h idxRight x y proof₁.tail proof₂.tail
      else some (proof₁.head, subL, proof₂.head, subR)

/-- The extractor is correct: under `x ≠ y` and equal putative roots,
    `findCollision` returns some quadruplet which is a genuine `Collision`
    for `h`. -/
theorem findCollision_isCollision [DecidableEq α]
    (h : α → α → α)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α)
    (hne : x ≠ y)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    ∃ l₁ r₁ l₂ r₂, findCollision h idx x y proof₁ proof₂ = some (l₁, r₁, l₂, r₂)
                 ∧ Collision h l₁ r₁ l₂ r₂ := by
  unfold Collision
  induction idx generalizing x y with
  | ofLeaf => grind [getPutativeRootWithHash]
  | ofLeft idxLeft ih =>
      simp only [getPutativeRootWithHash] at heq
      simp only [findCollision]
      split_ifs with hpair <;> grind [Prod.mk.injEq]
  | ofRight idxRight ih =>
      simp only [getPutativeRootWithHash] at heq
      simp only [findCollision]
      split_ifs with hpair <;> grind [Prod.mk.injEq]

/-- Merkle binding (existential form): from two distinct leaf values
    `x ≠ y` that produce the same putative root at the same leaf index under
    (possibly different) sibling proofs, extract a hash collision.

    Note that `idx` is shared — this is binding *at a fixed position*. The
    distinct-position case requires walking down both paths to the lowest
    common ancestor and is handled separately.

    For the constructive form (which is what downstream extractability
    proofs actually need), see `findCollision_isCollision`. -/
theorem getPutativeRootWithHash_binding
    (h : α → α → α)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α)
    (hne : x ≠ y)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    ∃ l₁ r₁ l₂ r₂, Collision h l₁ r₁ l₂ r₂ := by
  letI : DecidableEq α := Classical.decEq α
  obtain ⟨l₁, r₁, l₂, r₂, _, hcoll⟩ :=
    findCollision_isCollision h idx proof₁ proof₂ x y hne heq
  exact ⟨l₁, r₁, l₂, r₂, hcoll⟩

end InductiveMerkleTree
