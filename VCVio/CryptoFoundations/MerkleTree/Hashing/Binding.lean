/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Hashing.Defs

/-!
# Binding failures for hashed Merkle leaves

When two distinct payloads open to the same root at the same index, the failure can be attributed
to at least one of three abstraction boundaries:

1. the payload encoding is not injective on those payloads;
2. two distinct encoded leaves collide under the leaf-domain query at that address; or
3. two distinct ordered child pairs collide under a node-domain query.

The theorem below exposes this trichotomy constructively.  It reuses the addressed collision walk
for the third case and does not package the result as a probabilistic hash assumption.
-/

@[expose] public section

namespace MerkleTreeHashing

open BinaryTree

universe u v w x y

variable {LeafAddress : Type u} {NodeAddress : Type v}
  {Payload : Type w} {EncodedLeaf : Type x} {Digest : Type y}

/-- Two distinct payloads have the same committed leaf encoding. -/
def EncodingCollision (encode : Payload → EncodedLeaf) (left right : Payload) : Prop :=
  left ≠ right ∧ encode left = encode right

/-- Two distinct payloads receive the same caller-provided digest. -/
def DigestMapCollision (digest : Payload → Digest) (left right : Payload) : Prop :=
  left ≠ right ∧ digest left = digest right

/-- Two distinct encoded leaves have the same leaf-domain digest at one concrete address. -/
def LeafHashCollision
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (address : LeafAddress) (left right : EncodedLeaf) : Prop :=
  left ≠ right ∧ answer (.leaf address left) = answer (.leaf address right)

/-- An internal position at which two distinct ordered child pairs have the same node-domain
digest.  The intrinsic position is retained as part of the witness and mapped to the concrete
hash address by `addressing.node`. -/
def NodeHashCollision {s : Skeleton} (addressing : Addressing s LeafAddress NodeAddress)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (witness : SkeletonInternalIndex s × Digest × Digest × Digest × Digest) : Prop :=
  (witness.2.1, witness.2.2.1) ≠ (witness.2.2.2.1, witness.2.2.2.2) ∧
    answer (.node (addressing.node witness.1) witness.2.1 witness.2.2.1) =
      answer (.node (addressing.node witness.1) witness.2.2.2.1 witness.2.2.2.2)

/-- Binding failures for encoded-and-hashed leaves split into encoding, leaf-hash, and
internal-node collisions. -/
theorem hashed_binding {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (encode : Payload → EncodedLeaf)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector Digest idx.depth)
    (left right : Payload)
    (hroot : getPutativeRootWithHash addressing (.hash encode) idx left proof₁ answer =
      getPutativeRootWithHash addressing (.hash encode) idx right proof₂ answer)
    (hne : left ≠ right) :
    EncodingCollision encode left right ∨
      LeafHashCollision answer (addressing.leaf idx) (encode left) (encode right) ∨
      ∃ witness, NodeHashCollision addressing answer witness := by
  let _ : DecidableEq EncodedLeaf := Classical.decEq _
  let _ : DecidableEq Digest := Classical.decEq _
  by_cases hencode : encode left = encode right
  · exact Or.inl ⟨hne, hencode⟩
  · right
    by_cases hleaf :
        answer (.leaf (addressing.leaf idx) (encode left)) =
          answer (.leaf (addressing.leaf idx) (encode right))
    · exact Or.inl ⟨hencode, hleaf⟩
    · right
      obtain ⟨witness, _, hcollision⟩ :=
        AddressedMerkleTree.getPutativeRootAddressedWithHash_binding_collision
          (fun i l r => answer (.node (addressing.node i) l r)) idx proof₁ proof₂
          (answer (.leaf (addressing.leaf idx) (encode left)))
          (answer (.leaf (addressing.leaf idx) (encode right))) (by simpa [
            getPutativeRootWithHash, leafDigestWith, nodeDigestWith] using hroot) hleaf
      exact ⟨witness, hcollision⟩

/-- With an injective payload encoding, distinct openings yield either a leaf-domain collision or
an internal-node collision. -/
theorem hashed_binding_of_injective {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (encode : Payload → EncodedLeaf) (hencode : Function.Injective encode)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector Digest idx.depth)
    (left right : Payload)
    (hroot : getPutativeRootWithHash addressing (.hash encode) idx left proof₁ answer =
      getPutativeRootWithHash addressing (.hash encode) idx right proof₂ answer)
    (hne : left ≠ right) :
    LeafHashCollision answer (addressing.leaf idx) (encode left) (encode right) ∨
      ∃ witness, NodeHashCollision addressing answer witness := by
  obtain hcollision | hcollision | hcollision :=
    hashed_binding addressing encode answer idx proof₁ proof₂ left right hroot hne
  · exact (hne (hencode hcollision.2)).elim
  · exact Or.inl hcollision
  · exact Or.inr hcollision

/-- Equal roots for distinct payloads using a caller-provided digest map expose either a collision
in that map or an internal-node collision. -/
theorem providedDigest_binding {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (digest : Payload → Digest)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector Digest idx.depth)
    (left right : Payload)
    (hroot : getPutativeRootWithHash addressing (.providedDigest digest) idx left proof₁ answer =
      getPutativeRootWithHash addressing (.providedDigest digest) idx right proof₂ answer)
    (hne : left ≠ right) :
    DigestMapCollision digest left right ∨
      ∃ witness, NodeHashCollision addressing answer witness := by
  let _ : DecidableEq Digest := Classical.decEq _
  by_cases hdigest : digest left = digest right
  · exact Or.inl ⟨hne, hdigest⟩
  · right
    obtain ⟨witness, _, hcollision⟩ :=
      AddressedMerkleTree.getPutativeRootAddressedWithHash_binding_collision
        (fun i l r => answer (.node (addressing.node i) l r)) idx proof₁ proof₂
        (digest left) (digest right) (by simpa [getPutativeRootWithHash, leafDigestWith,
          nodeDigestWith] using hroot) hdigest
    exact ⟨witness, hcollision⟩

/-- Distinct raw digest leaves opening to the same root expose an internal-node collision. -/
theorem prehashed_binding {s : Skeleton}
    (addressing : Addressing s LeafAddress NodeAddress)
    (answer : HashQuery LeafAddress NodeAddress EncodedLeaf Digest → Digest)
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector Digest idx.depth)
    (left right : Digest)
    (hroot : getPutativeRootWithHash addressing .prehashed idx left proof₁ answer =
      getPutativeRootWithHash addressing .prehashed idx right proof₂ answer)
    (hne : left ≠ right) :
    ∃ witness, NodeHashCollision addressing answer witness := by
  obtain hcollision | hcollision :=
    providedDigest_binding addressing id answer idx proof₁ proof₂ left right hroot hne
  · exact (hne hcollision.2).elim
  · exact hcollision

end MerkleTreeHashing
