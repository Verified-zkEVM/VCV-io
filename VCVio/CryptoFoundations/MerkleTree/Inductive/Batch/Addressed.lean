/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.QueryBound

/-!
# Node-Addressed Batch Merkle Openings

This file extends the canonical typed-address Merkle engine to path-pruned batch openings.
The existing `InductiveMerkleTree.BatchProof` remains the sole proof representation: addresses
are properties of the verifier traversal, not authentication data supplied by the prover.

Both the pure and monadic folds reindex the node hash through `.ofLeft` and `.ofRight` while
descending and invoke it at `.ofInternal` after recovering the children. The monadic fold visits
the left selected subtree before the right selected subtree, then hashes the parent. Its exact
structural query budget is `BatchProof.queryCount` when every node-hash callback costs one query.
-/

@[expose] public section

namespace AddressedMerkleTree

open BinaryTree InductiveMerkleTree OracleComp OracleSpec

universe u v

variable {Y : Type v}

/-- Recompute a putative batch root with a pure hash indexed by typed internal-node address. -/
@[simp, grind]
def getPutativeBatchRootAddressedWithHash :
    {s : Skeleton} → (nodeHash : SkeletonInternalIndex s → Y → Y → Y) →
      {sel : LeafData Bool s} → SelectedValues Y sel → BatchProof Y sel → Y
  | _, _, _, values, .leaf => values
  | _, nodeHash, _, values, .internalBoth pl pr =>
      nodeHash .ofInternal
        (getPutativeBatchRootAddressedWithHash (fun a => nodeHash (.ofLeft a)) values.1 pl)
        (getPutativeBatchRootAddressedWithHash (fun a => nodeHash (.ofRight a)) values.2 pr)
  | _, nodeHash, _, values, .pruneRight _ rightRoot pl =>
      nodeHash .ofInternal
        (getPutativeBatchRootAddressedWithHash (fun a => nodeHash (.ofLeft a)) values.1 pl)
        rightRoot
  | _, nodeHash, _, values, .pruneLeft _ leftRoot pr =>
      nodeHash .ofInternal leftRoot
        (getPutativeBatchRootAddressedWithHash (fun a => nodeHash (.ofRight a)) values.2 pr)

/-- Recompute a putative batch root with an effectful hash indexed by typed internal-node
address. The traversal order is left subtree, right subtree, then parent. -/
@[simp, grind]
def getPutativeBatchRootAddressedM {m : Type v → Type*} [Monad m] :
    {s : Skeleton} → (nodeHash : SkeletonInternalIndex s → Y → Y → m Y) →
      {sel : LeafData Bool s} → SelectedValues Y sel → BatchProof Y sel → m Y
  | _, _, _, values, .leaf => pure values
  | _, nodeHash, _, values, .internalBoth pl pr => do
      let leftRoot ← getPutativeBatchRootAddressedM
        (fun a => nodeHash (.ofLeft a)) values.1 pl
      let rightRoot ← getPutativeBatchRootAddressedM
        (fun a => nodeHash (.ofRight a)) values.2 pr
      nodeHash .ofInternal leftRoot rightRoot
  | _, nodeHash, _, values, .pruneRight _ rightRoot pl => do
      let leftRoot ← getPutativeBatchRootAddressedM
        (fun a => nodeHash (.ofLeft a)) values.1 pl
      nodeHash .ofInternal leftRoot rightRoot
  | _, nodeHash, _, values, .pruneLeft _ leftRoot pr => do
      let rightRoot ← getPutativeBatchRootAddressedM
        (fun a => nodeHash (.ofRight a)) values.2 pr
      nodeHash .ofInternal leftRoot rightRoot

section Verification

variable {Y : Type}

/-- Verify a batch opening with an effectful typed-address node hash. -/
@[simp, grind]
def verifyBatchProofAddressedM {m : Type → Type*} [Monad m] [DecidableEq Y]
    {s : Skeleton} (nodeHash : SkeletonInternalIndex s → Y → Y → m Y)
    {sel : LeafData Bool s} (values : SelectedValues Y sel) (rootValue : Y)
    (proof : BatchProof Y sel) : m Bool := do
  let putativeRoot ← getPutativeBatchRootAddressedM nodeHash values proof
  return putativeRoot == rootValue

end Verification

/-- Running the effectful batch fold in `Id` recovers the pure addressed fold. -/
@[simp]
theorem idRun_getPutativeBatchRootAddressedM :
    {s : Skeleton} →
      (nodeHash : SkeletonInternalIndex s → Y → Y → Id Y) →
      {sel : LeafData Bool s} → (values : SelectedValues Y sel) →
      (proof : BatchProof Y sel) →
      Id.run (getPutativeBatchRootAddressedM nodeHash values proof) =
        getPutativeBatchRootAddressedWithHash
          (fun a l r => Id.run (nodeHash a l r)) values proof
  | _, _, _, _, .leaf => rfl
  | _, nodeHash, _, values, .internalBoth pl pr => by
      simp [getPutativeBatchRootAddressedM, getPutativeBatchRootAddressedWithHash,
        idRun_getPutativeBatchRootAddressedM]
  | _, nodeHash, _, values, .pruneRight _ rightRoot pl => by
      simp [getPutativeBatchRootAddressedM, getPutativeBatchRootAddressedWithHash,
        idRun_getPutativeBatchRootAddressedM]
  | _, nodeHash, _, values, .pruneLeft _ leftRoot pr => by
      simp [getPutativeBatchRootAddressedM, getPutativeBatchRootAddressedWithHash,
        idRun_getPutativeBatchRootAddressedM]

/-- A deterministic oracle handler commutes with effectful addressed batch reconstruction. -/
@[simp]
theorem simulateQ_getPutativeBatchRootAddressedM
    {i : Type u} {spec : OracleSpec.{u, v} i} (impl : QueryImpl spec Id) :
    {s : Skeleton} →
      (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y) →
      {sel : LeafData Bool s} → (values : SelectedValues Y sel) →
      (proof : BatchProof Y sel) →
      simulateQ impl (getPutativeBatchRootAddressedM nodeHash values proof) =
        getPutativeBatchRootAddressedWithHash
          (fun a l r => simulateQ impl (nodeHash a l r)) values proof
  | _, _, _, _, .leaf => rfl
  | _, nodeHash, _, values, .internalBoth pl pr => by
      simp only [getPutativeBatchRootAddressedM, simulateQ_bind,
        getPutativeBatchRootAddressedWithHash]
      rw [simulateQ_getPutativeBatchRootAddressedM impl
        (fun a => nodeHash (.ofLeft a)) values.1 pl]
      rw [simulateQ_getPutativeBatchRootAddressedM impl
        (fun a => nodeHash (.ofRight a)) values.2 pr]
      rfl
  | _, nodeHash, _, values, .pruneRight _ rightRoot pl => by
      simp only [getPutativeBatchRootAddressedM, simulateQ_bind,
        getPutativeBatchRootAddressedWithHash]
      rw [simulateQ_getPutativeBatchRootAddressedM impl
        (fun a => nodeHash (.ofLeft a)) values.1 pl]
      rfl
  | _, nodeHash, _, values, .pruneLeft _ leftRoot pr => by
      simp only [getPutativeBatchRootAddressedM, simulateQ_bind,
        getPutativeBatchRootAddressedWithHash]
      rw [simulateQ_getPutativeBatchRootAddressedM impl
        (fun a => nodeHash (.ofRight a)) values.2 pr]
      rfl

/-- A constant typed-address hash recovers the unaddressed functional batch fold. -/
theorem getPutativeBatchRootAddressedWithHash_const (hash : Y → Y → Y)
    {s : Skeleton} {sel : LeafData Bool s} (values : SelectedValues Y sel)
    (proof : BatchProof Y sel) :
    getPutativeBatchRootAddressedWithHash (fun _ => hash) values proof =
      getPutativeBatchRootWithHash hash values proof := by
  induction proof with
  | leaf => rfl
  | internalBoth pl pr ihl ihr =>
      simp [getPutativeBatchRootAddressedWithHash, getPutativeBatchRootWithHash,
        ihl values.1, ihr values.2]
  | pruneRight hr rightRoot pl ih =>
      simp [getPutativeBatchRootAddressedWithHash, getPutativeBatchRootWithHash, ih values.1]
  | pruneLeft hl leftRoot pr ih =>
      simp [getPutativeBatchRootAddressedWithHash, getPutativeBatchRootWithHash, ih values.2]

section QueryBound

variable {i : Type u} {spec : OracleSpec.{u, u} i} {Y : Type u}

/-- If every node callback costs `nodeBudget`, the addressed batch fold costs the number of
visited internal nodes times `nodeBudget`. -/
theorem isTotalQueryBound_getPutativeBatchRootAddressedM
    {s : Skeleton} (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y)
    (nodeBudget : ℕ) {sel : LeafData Bool s} (values : SelectedValues Y sel)
    (proof : BatchProof Y sel)
    (hnode : ∀ a l r, IsTotalQueryBound (nodeHash a l r) nodeBudget) :
    IsTotalQueryBound (getPutativeBatchRootAddressedM nodeHash values proof)
      (proof.queryCount * nodeBudget) := by
  induction proof with
  | leaf => exact trivial
  | internalBoth pl pr ihl ihr =>
      simp only [getPutativeBatchRootAddressedM, BatchProof.queryCount]
      have hleft := ihl (fun a => nodeHash (.ofLeft a)) values.1
        (fun a => hnode (.ofLeft a))
      have hright := ihr (fun a => nodeHash (.ofRight a)) values.2
        (fun a => hnode (.ofRight a))
      simpa [Nat.add_mul, Nat.add_assoc] using
        isTotalQueryBound_bind hleft fun leftRoot =>
          isTotalQueryBound_bind hright fun rightRoot =>
            hnode .ofInternal leftRoot rightRoot
  | pruneRight hr rightRoot pl ih =>
      simp only [getPutativeBatchRootAddressedM, BatchProof.queryCount]
      have hleft := ih (fun a => nodeHash (.ofLeft a)) values.1
        (fun a => hnode (.ofLeft a))
      simpa [Nat.add_mul] using isTotalQueryBound_bind hleft fun leftRoot =>
        hnode .ofInternal leftRoot rightRoot
  | pruneLeft hl leftRoot pr ih =>
      simp only [getPutativeBatchRootAddressedM, BatchProof.queryCount]
      have hright := ih (fun a => nodeHash (.ofRight a)) values.2
        (fun a => hnode (.ofRight a))
      simpa [Nat.add_mul] using isTotalQueryBound_bind hright fun rightRoot =>
        hnode .ofInternal leftRoot rightRoot

/-- Unit-cost addressed batch reconstruction has structural upper bound
`proof.queryCount`. -/
theorem isTotalQueryBound_getPutativeBatchRootAddressedM_one
    {s : Skeleton} (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y)
    {sel : LeafData Bool s} (values : SelectedValues Y sel) (proof : BatchProof Y sel)
    (hnode : ∀ a l r, IsTotalQueryBound (nodeHash a l r) 1) :
    IsTotalQueryBound (getPutativeBatchRootAddressedM nodeHash values proof)
      proof.queryCount := by
  simpa using isTotalQueryBound_getPutativeBatchRootAddressedM
    nodeHash 1 values proof hnode

end QueryBound

section VerificationQueryBound

variable {i Y : Type} {spec : OracleSpec i}

/-- Unit-cost addressed batch verification has the same structural query budget as root
reconstruction. -/
theorem isTotalQueryBound_verifyBatchProofAddressedM [DecidableEq Y]
    {s : Skeleton} (nodeHash : SkeletonInternalIndex s → Y → Y → OracleComp spec Y)
    {sel : LeafData Bool s} (values : SelectedValues Y sel) (rootValue : Y)
    (proof : BatchProof Y sel)
    (hnode : ∀ a l r, IsTotalQueryBound (nodeHash a l r) 1) :
    IsTotalQueryBound (verifyBatchProofAddressedM nodeHash values rootValue proof)
      proof.queryCount := by
  unfold verifyBatchProofAddressedM
  exact isTotalQueryBound_bind (n₂ := 0)
    (isTotalQueryBound_getPutativeBatchRootAddressedM_one nodeHash values proof hnode)
    fun _ => trivial

end VerificationQueryBound

end AddressedMerkleTree
