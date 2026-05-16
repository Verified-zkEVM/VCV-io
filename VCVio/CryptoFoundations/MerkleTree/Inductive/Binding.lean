/-
Copyright (c) 2026 Vitalik Buterin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin
-/
import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

/-!
# Merkle Binding (Collision Lemma)

The structural collision lemma for inductive Merkle trees, often called the
"Collision Lemma": two distinct openings of the same Merkle root —
distinct in the committed leaf value, the sibling proof, or both — entail a
collision in the underlying hash function.

The hypothesis `(x, proof₁) ≠ (y, proof₂)` captures any equivocation by the
committer at the same leaf index, which is what binding forbids: at a fixed
position there should be a single opening to a given root. (The
distinct-position case is not a binding break and is handled separately.)

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
  distinct openings `(x, proof₁) ≠ (y, proof₂)` producing the same root at
  the same leaf index, `findCollision` returns `some`.
- `InductiveMerkleTree.getPutativeRootWithHash_binding_collision` — the
  user-facing Collision Lemma: the tuple returned by `findCollision` is a
  genuine hash collision.

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

/-- Merkle binding: from two distinct openings `(x, proof₁) ≠ (y, proof₂)`
    that produce the same putative root at the same leaf index, the
    constructive search `findCollision` returns `some`.

    Note that `idx` is shared — this is binding *at a fixed position*. The
    distinct-position case requires walking down both paths to the lowest
    common ancestor and is handled separately.

    The hypothesis is on the *pair* `(value, proof)` rather than just on the
    leaf value, so this also covers the case where two distinct sibling
    proofs of the same leaf produce the same root: that, too, is a binding
    break and the constructive search still produces a collision.

    Proof strategy: induction on `idx`. At each non-leaf step, the recursion
    of `getPutativeRootWithHash` exposes a top-level hash. Either the two
    pairs `(subL, proof₁.head)` and `(subR, proof₂.head)` it consumes already
    differ (top-level collision, so `findCollision` returns them) or they
    agree component-wise — in which case the inputs to the inner recursive
    calls disagree (the original inequality on `(x, proof)` propagates down
    to `(x, proof.tail)`), so we recurse. -/
theorem getPutativeRootWithHash_binding
    (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hne : (x, proof₁) ≠ (y, proof₂))
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    ∃ l₁ r₁ l₂ r₂, findCollision h idx proof₁ proof₂ x y = some (l₁, r₁, l₂, r₂) := by
  induction idx generalizing x y with
  | ofLeaf =>
      -- At depth 0, both proofs are empty vectors hence equal; the inequality
      -- forces `x ≠ y`, contradicting `heq : x = y`.
      simp only [getPutativeRootWithHash] at heq
      refine absurd ?_ hne
      have hp : proof₁ = proof₂ := List.Vector.ext (fun i => i.elim0)
      exact Prod.ext heq hp
  | ofLeft idxLeft ih =>
      simp only [getPutativeRootWithHash] at heq
      have hhash_eq : h (getPutativeRootWithHash idxLeft x proof₁.tail h) proof₁.head =
                     h (getPutativeRootWithHash idxLeft y proof₂.tail h) proof₂.head := heq
      by_cases hpair : (getPutativeRootWithHash idxLeft x proof₁.tail h, proof₁.head) =
                       (getPutativeRootWithHash idxLeft y proof₂.tail h, proof₂.head)
      · -- Pairs agree: propagate `(x, proof₁) ≠ (y, proof₂)` to the tail and recurse.
        obtain ⟨hsub, hhead⟩ := Prod.mk.inj hpair
        have hne_tail : (x, proof₁.tail) ≠ (y, proof₂.tail) := by
          intro h_eq_tail
          obtain ⟨hxy, htail⟩ := Prod.mk.inj h_eq_tail
          apply hne
          refine Prod.ext hxy ?_
          conv_lhs => rw [show proof₁ = proof₁.head ::ᵥ proof₁.tail
            from (List.Vector.cons_head_tail proof₁).symm]
          conv_rhs => rw [show proof₂ = proof₂.head ::ᵥ proof₂.tail
            from (List.Vector.cons_head_tail proof₂).symm]
          rw [hhead, htail]
        obtain ⟨l₁, r₁, l₂, r₂, hfind⟩ := ih proof₁.tail proof₂.tail x y hne_tail hsub
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
      · -- Pairs agree: propagate `(x, proof₁) ≠ (y, proof₂)` to the tail and recurse.
        obtain ⟨hhead, hsub⟩ := Prod.mk.inj hpair
        have hne_tail : (x, proof₁.tail) ≠ (y, proof₂.tail) := by
          intro h_eq_tail
          obtain ⟨hxy, htail⟩ := Prod.mk.inj h_eq_tail
          apply hne
          refine Prod.ext hxy ?_
          conv_lhs => rw [show proof₁ = proof₁.head ::ᵥ proof₁.tail
            from (List.Vector.cons_head_tail proof₁).symm]
          conv_rhs => rw [show proof₂ = proof₂.head ::ᵥ proof₂.tail
            from (List.Vector.cons_head_tail proof₂).symm]
          rw [hhead, htail]
        obtain ⟨l₁, r₁, l₂, r₂, hfind⟩ := ih proof₁.tail proof₂.tail x y hne_tail hsub
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

/-- Collision Lemma for Merkle trees: from two distinct openings
    `(x, proof₁) ≠ (y, proof₂)` that produce the same putative root at the
    same leaf index, `findCollision` returns a tuple that is a genuine hash
    collision.

    Combines `getPutativeRootWithHash_binding` (the search succeeds) with
    `findCollision_sound` (its output satisfies `Collision`) into a single
    witness suitable for collision-resistance reductions. -/
theorem getPutativeRootWithHash_binding_collision
    (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hne : (x, proof₁) ≠ (y, proof₂))
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    ∃ l₁ r₁ l₂ r₂,
      findCollision h idx proof₁ proof₂ x y = some (l₁, r₁, l₂, r₂)
        ∧ Collision h l₁ r₁ l₂ r₂ := by
  obtain ⟨l₁, r₁, l₂, r₂, hfind⟩ :=
    getPutativeRootWithHash_binding h idx proof₁ proof₂ x y hne heq
  exact ⟨l₁, r₁, l₂, r₂, hfind,
    findCollision_sound h idx proof₁ proof₂ x y l₁ r₁ l₂ r₂ hfind⟩

end InductiveMerkleTree
