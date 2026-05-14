/-
Copyright (c) 2026 Vitalik Buterin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin
-/
import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

/-!
# Merkle Binding (Collision Lemma)

The structural collision lemma for inductive Merkle trees, often called the
"Collision Lemma": two distinct leaf values that
verify against the same Merkle root — under possibly different sibling
proofs — entail a collision in the underlying hash function.

The hypothesis `x ≠ y` captures that the adversary equivocates on the
*committed value*, which is what binding requires; the case `x = y` with
different sibling proofs is not a binding break, since the committer is
allowed to know multiple valid proofs of the same value.

The hash function is taken in curried form `α → α → α`, matching the
convention used by `getPutativeRootWithHash` and the rest of the Merkle tree
API.

The proof is constructive: `findCollision` is a computable function that
walks two Merkle branches and returns a hash collision as data, rather than
merely asserting its existence.

## Main Definitions

- `InductiveMerkleTree.Collision` — specification: a hash collision under
  `h : α → α → α`.
- `InductiveMerkleTree.findCollision` — constructive search: given two
  branches with the same leaf index, look for a hash collision along the
  path.

## Main Results

- `InductiveMerkleTree.findCollision_sound` — if `findCollision` returns
  a tuple, that tuple satisfies `Collision`.
- `InductiveMerkleTree.getPutativeRootWithHash_binding` — from any two
  distinct leaf values producing the same root at the same leaf index under
  (possibly different) sibling proofs, `findCollision` returns `some`.

## References

- Dan Boneh and Victor Shoup. *A Graduate Course in Applied Cryptography.*
  §8.9 (Merkle-Damgård and Merkle trees).
-/


namespace InductiveMerkleTree

open BinaryTree

variable {α : Type _} [DecidableEq α]

/-- Two distinct input pairs producing the same hash output: a collision for
    the curried hash `h : α → α → α`. -/
def Collision (h : α → α → α) (l₁ r₁ l₂ r₂ : α) : Prop :=
  (l₁, r₁) ≠ (l₂, r₂) ∧ h l₁ r₁ = h l₂ r₂

/-- Walk two Merkle branches with the same leaf index, looking for a hash
    collision. Returns `some (l₁, r₁, l₂, r₂)` if a collision is found (two
    distinct input pairs that hash to the same value), or `none` if the
    branches agree everywhere they are compared.

    This is the constructive kernel of the Collision Lemma. Instead of
    merely asserting `∃ l₁ r₁ l₂ r₂, Collision h l₁ r₁ l₂ r₂`, we compute the
    collision explicitly. -/
def findCollision (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α) :
    Option (α × α × α × α) :=
  match idx with
  | .ofLeaf => none
  | .ofLeft idxLeft =>
    let subL1 := getPutativeRootWithHash idxLeft x proof₁.tail h
    let subL2 := getPutativeRootWithHash idxLeft y proof₂.tail h
    if _ : (subL1, proof₁.head) = (subL2, proof₂.head) then
      findCollision h idxLeft proof₁.tail proof₂.tail x y
    else if _ : h subL1 proof₁.head = h subL2 proof₂.head then
      some (subL1, proof₁.head, subL2, proof₂.head)
    else
      none
  | .ofRight idxRight =>
    let subL1 := getPutativeRootWithHash idxRight x proof₁.tail h
    let subL2 := getPutativeRootWithHash idxRight y proof₂.tail h
    if _ : (proof₁.head, subL1) = (proof₂.head, subL2) then
      findCollision h idxRight proof₁.tail proof₂.tail x y
    else if _ : h proof₁.head subL1 = h proof₂.head subL2 then
      some (proof₁.head, subL1, proof₂.head, subL2)
    else
      none

/-- Soundness: if `findCollision` returns a tuple, that tuple is a hash
    collision according to `Collision`. -/
theorem findCollision_sound (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y l₁ r₁ l₂ r₂ : α)
    (hfind : findCollision h idx proof₁ proof₂ x y = some (l₁, r₁, l₂, r₂)) :
    Collision h l₁ r₁ l₂ r₂ := by
  induction idx generalizing x y l₁ r₁ l₂ r₂ with
  | ofLeaf =>
      simp [findCollision] at hfind
  | ofLeft idxLeft ih =>
      -- Unfold findCollision and zeta-reduce the `let` bindings so that
      -- the `if` conditions become visible to `simp`.
      unfold findCollision at hfind
      dsimp at hfind
      by_cases hpair : (getPutativeRootWithHash idxLeft x proof₁.tail h, proof₁.head) =
                       (getPutativeRootWithHash idxLeft y proof₂.tail h, proof₂.head)
      · simp only [hpair] at hfind
        exact ih proof₁.tail proof₂.tail x y l₁ r₁ l₂ r₂ hfind
      · simp only [hpair] at hfind
        by_cases heqhash : h (getPutativeRootWithHash idxLeft x proof₁.tail h) proof₁.head =
                          h (getPutativeRootWithHash idxLeft y proof₂.tail h) proof₂.head
        · simp only [heqhash] at hfind
          -- hfind : some (getPutativeRootWithHash ... , proof₁.head, ...) =
          --         some (l₁, r₁, l₂, r₂)
          -- Decompose into component equalities and substitute.
          have hinj : (getPutativeRootWithHash idxLeft x proof₁.tail h, proof₁.head,
                       getPutativeRootWithHash idxLeft y proof₂.tail h, proof₂.head) =
                      (l₁, r₁, l₂, r₂) := by
            simpa using hfind
          rcases Prod.mk.inj hinj with ⟨h₁, hrest⟩
          rcases Prod.mk.inj hrest with ⟨h₂, hrest⟩
          rcases Prod.mk.inj hrest with ⟨h₃, h₄⟩
          subst h₁; subst h₂; subst h₃; subst h₄
          exact ⟨hpair, heqhash⟩
        · simp [heqhash] at hfind
  | ofRight idxRight ih =>
      unfold findCollision at hfind
      dsimp at hfind
      by_cases hpair : (proof₁.head, getPutativeRootWithHash idxRight x proof₁.tail h) =
                       (proof₂.head, getPutativeRootWithHash idxRight y proof₂.tail h)
      · simp only [hpair] at hfind
        exact ih proof₁.tail proof₂.tail x y l₁ r₁ l₂ r₂ hfind
      · simp only [hpair] at hfind
        by_cases heqhash : h proof₁.head (getPutativeRootWithHash idxRight x proof₁.tail h) =
                          h proof₂.head (getPutativeRootWithHash idxRight y proof₂.tail h)
        · simp only [heqhash] at hfind
          have hinj : (proof₁.head, getPutativeRootWithHash idxRight x proof₁.tail h,
                       proof₂.head, getPutativeRootWithHash idxRight y proof₂.tail h) =
                      (l₁, r₁, l₂, r₂) := by
            simpa using hfind
          rcases Prod.mk.inj hinj with ⟨h₁, hrest⟩
          rcases Prod.mk.inj hrest with ⟨h₂, hrest⟩
          rcases Prod.mk.inj hrest with ⟨h₃, h₄⟩
          subst h₁; subst h₂; subst h₃; subst h₄
          exact ⟨hpair, heqhash⟩
        · simp [heqhash] at hfind

/-- Merkle binding: from two distinct leaf values `x ≠ y` that produce the
    same putative root at the same leaf index under (possibly different)
    sibling proofs, the constructive search `findCollision` returns `some`.

    Note that `idx` is shared — this is binding *at a fixed position*. The
    distinct-position case requires walking down both paths to the lowest
    common ancestor and is handled separately.

    Proof strategy: induction on `idx`. At each non-leaf step, the recursion
    of `getPutativeRootWithHash` exposes a top-level hash. Either the two
    pairs `(subL, proof₁.head)` and `(subR, proof₂.head)` it consumes already
    differ (top-level collision, so `findCollision` returns them) or they
    agree component-wise — in which case the inputs to the inner recursive
    calls disagree, so we recurse. -/
theorem getPutativeRootWithHash_binding
    (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hne : x ≠ y)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    ∃ l₁ r₁ l₂ r₂, findCollision h idx proof₁ proof₂ x y = some (l₁, r₁, l₂, r₂) := by
  induction idx generalizing x y with
  | ofLeaf =>
      simp only [getPutativeRootWithHash] at heq
      exact absurd heq hne
  | ofLeft idxLeft ih =>
      simp only [getPutativeRootWithHash] at heq
      have hhash_eq : h (getPutativeRootWithHash idxLeft x proof₁.tail h) proof₁.head =
                     h (getPutativeRootWithHash idxLeft y proof₂.tail h) proof₂.head := heq
      by_cases hpair : (getPutativeRootWithHash idxLeft x proof₁.tail h, proof₁.head) =
                       (getPutativeRootWithHash idxLeft y proof₂.tail h, proof₂.head)
      · -- Pairs agree: recurse on the smaller index.
        obtain ⟨hsub, _⟩ := Prod.mk.inj hpair
        obtain ⟨l₁, r₁, l₂, r₂, hfind⟩ := ih proof₁.tail proof₂.tail x y hne hsub
        refine ⟨l₁, r₁, l₂, r₂, ?_⟩
        unfold findCollision
        dsimp
        simp [hpair, hfind]
      · -- Pairs differ but hash to the same value: top-level collision.
        refine ⟨getPutativeRootWithHash idxLeft x proof₁.tail h, proof₁.head,
                getPutativeRootWithHash idxLeft y proof₂.tail h, proof₂.head, ?_⟩
        unfold findCollision
        dsimp
        simp [hpair, hhash_eq]
  | ofRight idxRight ih =>
      simp only [getPutativeRootWithHash] at heq
      have hhash_eq : h proof₁.head (getPutativeRootWithHash idxRight x proof₁.tail h) =
                     h proof₂.head (getPutativeRootWithHash idxRight y proof₂.tail h) := heq
      by_cases hpair : (proof₁.head, getPutativeRootWithHash idxRight x proof₁.tail h) =
                       (proof₂.head, getPutativeRootWithHash idxRight y proof₂.tail h)
      · -- Pairs agree: recurse on the smaller index.
        obtain ⟨_, hsub⟩ := Prod.mk.inj hpair
        obtain ⟨l₁, r₁, l₂, r₂, hfind⟩ := ih proof₁.tail proof₂.tail x y hne hsub
        refine ⟨l₁, r₁, l₂, r₂, ?_⟩
        unfold findCollision
        dsimp
        simp [hpair, hfind]
      · -- Pairs differ but hash to the same value: top-level collision.
        refine ⟨proof₁.head, getPutativeRootWithHash idxRight x proof₁.tail h,
                proof₂.head, getPutativeRootWithHash idxRight y proof₂.tail h, ?_⟩
        unfold findCollision
        dsimp
        simp [hpair, hhash_eq]

end InductiveMerkleTree
