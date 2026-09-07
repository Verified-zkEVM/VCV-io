/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Query

/-!
# Queried-domain uniqueness for addressed Merkle openings

This module adds a finite-transcript alternative to global injectivity of a compressing hash:
injectivity on the finite query
transcript that covers the two openings being compared.  Query identity includes the full typed
oracle address/key and the ordered child pair. Thus the result has the shape consumed by an
address-aware random-oracle or collision-resistance argument.

`openingQueries` enumerates exactly the node-hash inputs induced by one leaf opening.
`NodeHashInjectiveOnQueries` asks for injectivity only among entries of a supplied list. If two
complete
openings are covered by that list and recompute the same root, `opening_unique_of_queryInjectiveOn`
proves equality of both the leaf value and authentication path.

The theorem applies to single addressed openings; batch-opening uniqueness is developed in the
batch modules.
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree InductiveMerkleTree

universe u v

variable {Address : Type u} {Y : Type v}

/-- The addressed node hash is injective on the supplied finite query transcript.  Unlike
`Function.Injective2`, this permits collisions outside the observed domain. -/
def NodeHashInjectiveOnQueries
    (nodeHash : Address → Y → Y → Y)
    (log : List (NodeQuery Address Y)) : Prop :=
  ∀ q₁ ∈ log, ∀ q₂ ∈ log,
    q₁.eval nodeHash = q₂.eval nodeHash → q₁ = q₂

/-- A collision returned by `findCollisionAddressed` consists of one query from each compared
opening.  This is the transcript-locality bridge needed by queried-domain uniqueness. -/
theorem findCollisionAddressed_mem_openingQueries {s : Skeleton}
    [DecidableEq Y]
    (addressKey : SkeletonInternalIndex s → Address)
    (nodeHash : Address → Y → Y → Y)
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector Y idx.depth) (x y : Y)
    (w : SkeletonInternalIndex s × Y × Y × Y × Y)
    (hw : findCollisionAddressed (fun a => nodeHash (addressKey a))
      idx proof₁ proof₂ x y = some w) :
    ⟨addressKey w.1, (w.2.1, w.2.2.1)⟩ ∈
        openingQueries addressKey nodeHash idx x proof₁ ∧
      ⟨addressKey w.1, (w.2.2.2.1, w.2.2.2.2)⟩ ∈
        openingQueries addressKey nodeHash idx y proof₂ := by
  induction idx with
  | ofLeaf => simp [findCollisionAddressed] at hw
  | ofLeft idx ih =>
      rw [findCollisionAddressed] at hw
      split at hw
      · simp only [Option.map_eq_some_iff] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        obtain ⟨h₁, h₂⟩ := ih (fun a => addressKey (.ofLeft a))
          proof₁.tail proof₂.tail w' hw'
        constructor
        · simp only [openingQueries, List.mem_cons]
          exact Or.inr h₁
        · simp only [openingQueries, List.mem_cons]
          exact Or.inr h₂
      · split at hw
        · simp only [Option.some.injEq] at hw
          subst w
          simp [openingQueries]
        · simp at hw
  | ofRight idx ih =>
      rw [findCollisionAddressed] at hw
      split at hw
      · simp only [Option.map_eq_some_iff] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        obtain ⟨h₁, h₂⟩ := ih (fun a => addressKey (.ofRight a))
          proof₁.tail proof₂.tail w' hw'
        constructor
        · simp only [openingQueries, List.mem_cons]
          exact Or.inr h₁
        · simp only [openingQueries, List.mem_cons]
          exact Or.inr h₂
      · split at hw
        · simp only [Option.some.injEq] at hw
          subst w
          simp [openingQueries]
        · simp at hw

/-- **Queried-domain addressed opening uniqueness.** If the two complete openings are covered by
one transcript on which the addressed hash is injective, equality of their putative roots forces
equality of both the leaf and the authentication path. -/
theorem opening_unique_of_queryInjectiveOn {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (nodeHash : Address → Y → Y → Y)
    (log : List (NodeQuery Address Y)) (hinj : NodeHashInjectiveOnQueries nodeHash log)
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector Y idx.depth) (x y : Y)
    (hcovered₁ : OpeningCovered addressKey nodeHash log idx x proof₁)
    (hcovered₂ : OpeningCovered addressKey nodeHash log idx y proof₂)
    (hroot : getPutativeRootAddressedWithHash (fun a => nodeHash (addressKey a)) idx x proof₁ =
      getPutativeRootAddressedWithHash (fun a => nodeHash (addressKey a)) idx y proof₂) :
    x = y ∧ proof₁ = proof₂ := by
  classical
  let _ : DecidableEq Y := Classical.decEq Y
  by_contra hne
  have hopening : (x, proof₁) ≠ (y, proof₂) := by
    intro hpair
    apply hne
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
    (findCollisionAddressed_isSome_of_opening_ne (fun a => nodeHash (addressKey a))
      idx proof₁ proof₂ x y
      hroot hopening)
  have hcollision := findCollisionAddressed_sound (fun a => nodeHash (addressKey a))
    idx proof₁ proof₂ x y w hw
  obtain ⟨hmem₁, hmem₂⟩ :=
    findCollisionAddressed_mem_openingQueries addressKey nodeHash
      idx proof₁ proof₂ x y w hw
  let q₁ : NodeQuery Address Y := ⟨addressKey w.1, (w.2.1, w.2.2.1)⟩
  let q₂ : NodeQuery Address Y := ⟨addressKey w.1, (w.2.2.2.1, w.2.2.2.2)⟩
  have hq : q₁ = q₂ := hinj q₁ (hcovered₁ q₁ hmem₁) q₂
    (hcovered₂ q₂ hmem₂) hcollision.2
  exact hcollision.1 (congrArg NodeQuery.input hq)

end AddressedMerkleTree
