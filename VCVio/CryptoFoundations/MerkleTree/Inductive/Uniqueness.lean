/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import VCVio.CryptoFoundations.MerkleTree.Inductive.Binding

/-!
# Merkle Opening Uniqueness

When the hash function is injective (`Function.Injective2 h`), any two
openings at the same leaf index that produce the same putative root must
agree on both the leaf value and the authentication path. This is the
deterministic analog of extractability: the Merkle root uniquely determines
the committed value at each position.

Combined with `getPutativeRootWithHash_binding` from `Binding.lean`, this
gives a complete picture of Merkle commitment security:
- **Binding** (no CR needed): same index, distinct values → hash collision.
- **Uniqueness** (injective hash): same index, same root → identical opening.

The distinct-index case is not a binding violation — two different leaf
positions producing the same root is normal Merkle tree operation.

## Main Results

- `getPutativeRootWithHash_unique` — opening uniqueness under injective hash
- `getPutativeRootWithHash_roots_ne_of_ne` — contrapositive: distinct values
  at the same index produce distinct roots

## References

- Justin Thaler. *Proofs, Arguments, and Zero-Knowledge.* §7.3.2.2
  (Merkle-tree string commitment binding property)
- Vitalik Buterin. `Binding.lean` (PR #384) — same-index collision extraction
-/

namespace InductiveMerkleTree

open BinaryTree

variable {α : Type _}

/-- **Merkle opening uniqueness.** When `h` is injective, two openings at the
    same leaf index that produce the same root must agree on both the leaf
    value and the entire authentication path.

    Proof: induction on the index. At each internal node, injectivity of `h`
    forces both hash arguments to agree — the sibling (proof head) and the
    recursive subtree root. The inductive hypothesis then gives agreement on
    the leaf value and the remaining proof elements. -/
theorem getPutativeRootWithHash_unique
    (h : α → α → α) (hinj : Function.Injective2 h)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    x = y ∧ proof₁ = proof₂ := by
  induction idx generalizing x y with
  | ofLeaf =>
    simp only [getPutativeRootWithHash] at heq
    exact ⟨heq, List.Vector.ext (fun i => i.elim0)⟩
  | ofLeft idxLeft ih =>
    simp only [getPutativeRootWithHash] at heq
    have ⟨hsub, hsib⟩ := hinj heq
    obtain ⟨hval, htail⟩ := ih proof₁.tail proof₂.tail x y hsub
    exact ⟨hval, by
      conv_lhs => rw [show proof₁ = proof₁.head ::ᵥ proof₁.tail
        from (List.Vector.cons_head_tail proof₁).symm]
      conv_rhs => rw [show proof₂ = proof₂.head ::ᵥ proof₂.tail
        from (List.Vector.cons_head_tail proof₂).symm]
      rw [hsib, htail]⟩
  | ofRight idxRight ih =>
    simp only [getPutativeRootWithHash] at heq
    have ⟨hsib, hsub⟩ := hinj heq
    obtain ⟨hval, htail⟩ := ih proof₁.tail proof₂.tail x y hsub
    exact ⟨hval, by
      conv_lhs => rw [show proof₁ = proof₁.head ::ᵥ proof₁.tail
        from (List.Vector.cons_head_tail proof₁).symm]
      conv_rhs => rw [show proof₂ = proof₂.head ::ᵥ proof₂.tail
        from (List.Vector.cons_head_tail proof₂).symm]
      rw [hsib, htail]⟩

/-- Contrapositive of uniqueness: with an injective hash, distinct leaf values
    at the same index always produce distinct roots, regardless of the
    authentication paths used. -/
theorem getPutativeRootWithHash_roots_ne_of_ne
    (h : α → α → α) (hinj : Function.Injective2 h)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α) (hne : x ≠ y) :
    getPutativeRootWithHash idx x proof₁ h
      ≠ getPutativeRootWithHash idx y proof₂ h :=
  fun heq => hne (getPutativeRootWithHash_unique h hinj idx proof₁ proof₂ x y heq).1

end InductiveMerkleTree
