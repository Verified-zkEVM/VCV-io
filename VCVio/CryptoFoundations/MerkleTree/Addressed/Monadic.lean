/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import PolyFun.Control.Monad.Hom
public import ToMathlib.Data.IndexedBinaryTree.Equiv

/-!
# Effectful node-addressed Merkle trees

Monad-parametric companions to the canonical `AddressedMerkleTree` engine.  Leaves and internal
nodes may perform effects, so a random-oracle instantiation can issue explicit hash queries while
retaining the existing typed-address discipline.  The traversal order is fixed: build the left
subtree, build the right subtree, then hash their roots.

The deterministic-handler and `Id` theorems below show that these programs are interpretations
of the existing pure engine, not a second Merkle-tree semantics.

This module is deliberately a companion to the pre-existing unaddressed
`InductiveMerkleTree.buildMerkleTree` / `getPutativeRoot` API, not its replacement.  The
addressed engine is required by XMSS and FORS because the hash query includes the node address.
Single-opening homogeneous extractability and its query bounds now use a generic complete-query
owner, with the unaddressed theorem recovered by unit-address specialization. Batch opening,
uniqueness, and wholesale replacement of the older construction API remain outside this layer;
`Addressed.Basic` records the existing propositional constant-address bridges.
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree InductiveMerkleTree OracleComp OracleSpec

universe u v

variable {Y : Type v}

/-- Build a fully populated addressed tree with effectful leaf production and node hashing.
The left subtree is evaluated before the right subtree, and both are evaluated before the parent
hash. -/
def buildMerkleTreeAddressedM {m : Type v → Type*} [Monad m] :
    {s : Skeleton} →
      (leaf : SkeletonLeafIndex s → m Y) →
      (nodeHash : SkeletonInternalIndex s → Y → Y → m Y) →
      m (FullData Y s)
  | .leaf, leaf, _ => .leaf <$> leaf .ofLeaf
  | .internal _ _, leaf, nodeHash => do
      let left ← buildMerkleTreeAddressedM
        (fun i => leaf (.ofLeft i)) (fun a => nodeHash (.ofLeft a))
      let right ← buildMerkleTreeAddressedM
        (fun i => leaf (.ofRight i)) (fun a => nodeHash (.ofRight a))
      let root ← nodeHash .ofInternal left.getRootValue right.getRootValue
      return .internal root left right

/-- Recompute a putative root with an effectful address-dependent node hash.  Hashes are issued
from the leaf level upward, matching `getPutativeRootAddressedWithHash`. -/
def getPutativeRootAddressedM {m : Type v → Type*} [Monad m] :
    {s : Skeleton} →
      (nodeHash : SkeletonInternalIndex s → Y → Y → m Y) →
      (idx : SkeletonLeafIndex s) → Y → List.Vector Y idx.depth → m Y
  | _, _, .ofLeaf, leafValue, _ => pure leafValue
  | _, nodeHash, .ofLeft idx, leafValue, proof => do
      let child ← getPutativeRootAddressedM
        (fun a => nodeHash (.ofLeft a)) idx leafValue proof.tail
      nodeHash .ofInternal child proof.head
  | _, nodeHash, .ofRight idx, leafValue, proof => do
      let child ← getPutativeRootAddressedM
        (fun a => nodeHash (.ofRight a)) idx leafValue proof.tail
      nodeHash .ofInternal proof.head child

section Naturality

universe w x

variable {m : Type v → Type w} {n : Type v → Type x}
  [Monad m] [Monad n]

/-- Addressed-tree construction is natural in any monad morphism that maps the leaf and node
callbacks pointwise.  This preserves the entire effect trace, not only the final root value. -/
theorem buildMerkleTreeAddressedM_natural (F : m →ᵐ n) {s : Skeleton}
    [LawfulMonad m] [LawfulMonad n]
    (leafₘ : SkeletonLeafIndex s → m Y)
    (hashₘ : SkeletonInternalIndex s → Y → Y → m Y)
    (leafₙ : SkeletonLeafIndex s → n Y)
    (hashₙ : SkeletonInternalIndex s → Y → Y → n Y)
    (hleaf : ∀ i, F (leafₘ i) = leafₙ i)
    (hhash : ∀ a l r, F (hashₘ a l r) = hashₙ a l r) :
    F (buildMerkleTreeAddressedM leafₘ hashₘ) =
      buildMerkleTreeAddressedM leafₙ hashₙ := by
  induction s with
  | leaf => simp [buildMerkleTreeAddressedM, hleaf]
  | internal sl sr ihl ihr =>
      simp [buildMerkleTreeAddressedM, F.mmap_bind, ihl, ihr, hleaf, hhash]

/-- Putative-root reconstruction is natural in any monad morphism that maps node hashing
pointwise. -/
theorem getPutativeRootAddressedM_natural (F : m →ᵐ n) {s : Skeleton}
    (hashₘ : SkeletonInternalIndex s → Y → Y → m Y)
    (hashₙ : SkeletonInternalIndex s → Y → Y → n Y)
    (hhash : ∀ a l r, F (hashₘ a l r) = hashₙ a l r)
    (idx : SkeletonLeafIndex s) (leafValue : Y) (proof : List.Vector Y idx.depth) :
    F (getPutativeRootAddressedM hashₘ idx leafValue proof) =
      getPutativeRootAddressedM hashₙ idx leafValue proof := by
  induction idx with
  | ofLeaf => simp [getPutativeRootAddressedM]
  | ofLeft idx ih =>
      simp [getPutativeRootAddressedM, F.mmap_bind, ih, hhash]
  | ofRight idx ih =>
      simp [getPutativeRootAddressedM, F.mmap_bind, ih, hhash]

end Naturality

section PureInterpretation

/-- Running effectful addressed root reconstruction in `Id` recovers the canonical pure
addressed reconstruction with the callbacks interpreted pointwise. -/
@[simp]
theorem idRun_getPutativeRootAddressedM :
    {s : Skeleton} →
      (nodeHash : SkeletonInternalIndex s → Y → Y → Id Y) →
      (idx : SkeletonLeafIndex s) → (leafValue : Y) →
      (proof : List.Vector Y idx.depth) →
      Id.run (getPutativeRootAddressedM nodeHash idx leafValue proof) =
        getPutativeRootAddressedWithHash
          (fun a l r => Id.run (nodeHash a l r)) idx leafValue proof
  | _, _, .ofLeaf, _, _ => rfl
  | _, nodeHash, .ofLeft idx, leafValue, proof => by
      simp [getPutativeRootAddressedM, getPutativeRootAddressedWithHash,
        idRun_getPutativeRootAddressedM]
  | _, nodeHash, .ofRight idx, leafValue, proof => by
      simp [getPutativeRootAddressedM, getPutativeRootAddressedWithHash,
        idRun_getPutativeRootAddressedM]

end PureInterpretation

section DeterministicInterpretation

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Interpreting effectful addressed-tree construction through a deterministic handler recovers
the canonical pure addressed tree with pointwise interpreted leaves and node hashes. -/
@[simp]
theorem simulateQ_buildMerkleTreeAddressedM (impl : QueryImpl spec Id) :
    {s : Skeleton} →
      (leaf : SkeletonLeafIndex s → OracleComp spec Y) →
      (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y) →
      simulateQ impl (buildMerkleTreeAddressedM leaf nodeHash) =
        buildMerkleTreeAddressedWithHash
          (LeafData.ofFun s fun i => simulateQ impl (leaf i))
          (fun a l r => simulateQ impl (nodeHash a l r))
  | .leaf, leaf, _ => by
      simp only [buildMerkleTreeAddressedM, simulateQ_map, LeafData.ofFun,
        buildMerkleTreeAddressedWithHash, populateUpAddressed]
      rfl
  | .internal _ _, leaf, nodeHash => by
      simp only [buildMerkleTreeAddressedM, simulateQ_bind]
      rw [simulateQ_buildMerkleTreeAddressedM impl
        (fun i => leaf (.ofLeft i)) (fun a => nodeHash (.ofLeft a))]
      rw [simulateQ_buildMerkleTreeAddressedM impl
        (fun i => leaf (.ofRight i)) (fun a => nodeHash (.ofRight a))]
      rfl

/-- A deterministic handler commutes with effectful addressed root reconstruction. -/
@[simp]
theorem simulateQ_getPutativeRootAddressedM (impl : QueryImpl spec Id) :
    {s : Skeleton} →
      (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y) →
      (idx : SkeletonLeafIndex s) → (leafValue : Y) → (proof : List.Vector Y idx.depth) →
      simulateQ impl (getPutativeRootAddressedM nodeHash idx leafValue proof) =
        getPutativeRootAddressedWithHash
          (fun a l r => simulateQ impl (nodeHash a l r)) idx leafValue proof
  | _, _, .ofLeaf, _, _ => rfl
  | _, nodeHash, .ofLeft idx, leafValue, proof => by
      simp only [getPutativeRootAddressedM, simulateQ_bind,
        getPutativeRootAddressedWithHash]
      rw [simulateQ_getPutativeRootAddressedM impl
        (fun a => nodeHash (.ofLeft a)) idx leafValue proof.tail]
      rfl
  | _, nodeHash, .ofRight idx, leafValue, proof => by
      simp only [getPutativeRootAddressedM, simulateQ_bind,
        getPutativeRootAddressedWithHash]
      rw [simulateQ_getPutativeRootAddressedM impl
        (fun a => nodeHash (.ofRight a)) idx leafValue proof.tail]
      rfl

end DeterministicInterpretation

end AddressedMerkleTree
