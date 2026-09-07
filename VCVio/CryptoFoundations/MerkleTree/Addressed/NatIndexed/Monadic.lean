/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed

/-!
# Effectful natural-number-indexed perfect Merkle trees

Effectful companions to `PerfectMerkleTree.tree`, `merkleRoot`, `authPath`, and `climb`, built on
the canonical typed-address engine.  Both leaves and node hashes are monadic, which is the API
needed by SLH-DSA to represent public hashing as explicit oracle calls.

No oracle handler or cache is selected here.  The caller must interpret the whole surrounding
program with one handler.  In particular, random-oracle consumers must install one shared lazy
oracle across construction, signing, the adversary, and verification. The `Id` interpretation
laws connect these effectful traversals to the established pure API.

The natural-number adapter specializes the addressed engine used by XMSS/FORS. Single-opening
homogeneous extractability is available through `AddressedMerkleTree.Extractability`; batch
opening, full heterogeneous SLH-DSA public-hash accounting, and replacement of the older
unaddressed/vector construction APIs remain separate work.
-/

@[expose] public section

namespace PerfectMerkleTree

open AddressedMerkleTree BinaryTree InductiveMerkleTree OracleComp OracleSpec

universe u v

variable {Y : Type v}

/-- Effectfully build the fully populated perfect subtree at `(height z, index t)`. -/
def treeM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (z t : ℕ) : m (FullData Y (Skeleton.perfect z)) :=
  buildMerkleTreeAddressedM
    (fun i => leaf (i.natIndex t))
    (fun a => nodeHash (a.natAddr t).height (a.natAddr t).index)

@[simp]
theorem treeM_zero {m : Type v → Type*} [Monad m]
    (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y) (t : ℕ) :
    treeM leaf nodeHash 0 t = FullData.leaf <$> leaf t := rfl

/-- Effectful full-tree construction follows the same left/right/parent schedule as the direct
root recursion. -/
theorem treeM_succ {m : Type v → Type*} [Monad m]
    (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y) (z t : ℕ) :
    treeM leaf nodeHash (z + 1) t = do
      let left ← treeM leaf nodeHash z (2 * t)
      let right ← treeM leaf nodeHash z (2 * t + 1)
      let root ← nodeHash (z + 1) t left.getRootValue right.getRootValue
      return .internal root left right := rfl

/-- Effectfully compute the root of the perfect subtree at `(height z, index t)` without
materializing it.  Evaluation is depth-first and left-to-right. -/
def merkleRootM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) : ℕ → ℕ → m Y
  | 0, t => leaf t
  | z + 1, t => do
      let left ← merkleRootM leaf nodeHash z (2 * t)
      let right ← merkleRootM leaf nodeHash z (2 * t + 1)
      nodeHash (z + 1) t left right

/-- Effectfully compute the authentication path of global leaf `idx` over `z` levels.  Only the
sibling subtrees are evaluated: the queried leaf and nodes on its direct path are not recomputed.
Entries and effects are ordered from the leaf level upward, as in FIPS 205. -/
def authPathM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) : ℕ → m (List Y)
  | 0 => pure []
  | z + 1 => do
      let path ← authPathM leaf nodeHash idx z
      let siblingRoot ← merkleRootM leaf nodeHash z (sibling (idx / 2 ^ z))
      return path ++ [siblingRoot]

/-- Effectfully compute an authentication path whose height is retained in the result type.
Only sibling subtrees are evaluated, in leaf-to-root order. -/
def intrinsicAuthPathM {m : Type v → Type*} [Monad m] (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) : (z : ℕ) → m (Vector Y z)
  | 0 => pure #v[]
  | z + 1 => do
      let path ← intrinsicAuthPathM leaf nodeHash idx z
      let siblingRoot ← merkleRootM leaf nodeHash z (sibling (idx / 2 ^ z))
      return path.push siblingRoot

/-- Pure authentication path with its exact height retained in the result type. -/
def intrinsicAuthPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx : ℕ) : (z : ℕ) → Vector Y z
  | 0 => #v[]
  | z + 1 => (intrinsicAuthPath leaf nodeHash idx z).push
      (merkleRoot leaf nodeHash z (sibling (idx / 2 ^ z)))

/-- Erasing the intrinsic length agrees with the list-valued authentication path. -/
@[simp]
theorem intrinsicAuthPath_toList (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx z : ℕ) :
    (intrinsicAuthPath leaf nodeHash idx z).toList = authPath leaf nodeHash idx z := by
  induction z with
  | zero => rfl
  | succ z ih =>
      rw [intrinsicAuthPath, Vector.toList_push, ih, authPath_succ]

/-- Forgetting the intrinsic path width preserves the complete monadic program, including the
order of all leaf and node callbacks. This is the bridge that lets distributional and
query-tracking facts about `authPathM` transfer to `intrinsicAuthPathM` and back inside any
lawful monad, `OracleComp` included. -/
theorem intrinsicAuthPathM_toList {m : Type v → Type*} [Monad m] [LawfulMonad m]
    (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx z : ℕ) :
    (fun path => path.toList) <$> intrinsicAuthPathM leaf nodeHash idx z =
      authPathM leaf nodeHash idx z := by
  induction z with
  | zero => simp [intrinsicAuthPathM, authPathM]
  | succ z ih =>
      rw [intrinsicAuthPathM, authPathM, ← ih]
      simp [Vector.toList_push]

/-- Effectfully recover a root from a leaf value and a leaf-first authentication path. -/
def climbM {m : Type v → Type*} [Monad m] (nodeHash : ℕ → ℕ → Y → Y → m Y)
    (idx : ℕ) (node : Y) (auth : List Y) : m Y :=
  getPutativeRootAddressedM
    (fun a => nodeHash (a.natAddr (idx / 2 ^ auth.length)).height
      (a.natAddr (idx / 2 ^ auth.length)).index)
    (SkeletonLeafIndex.ofNat auth.length idx) node ⟨auth.reverse, by simp⟩

section Naturality

universe w x

variable {m : Type v → Type w} {n : Type v → Type x}
  [Monad m] [Monad n]

/-- Perfect-tree construction commutes with any monad morphism mapping its callbacks
pointwise. -/
theorem treeM_natural (F : m →ᵐ n)
    [LawfulMonad m] [LawfulMonad n]
    (leafₘ : ℕ → m Y) (hashₘ : ℕ → ℕ → Y → Y → m Y)
    (leafₙ : ℕ → n Y) (hashₙ : ℕ → ℕ → Y → Y → n Y)
    (hleaf : ∀ i, F (leafₘ i) = leafₙ i)
    (hhash : ∀ h i l r, F (hashₘ h i l r) = hashₙ h i l r)
    (z t : ℕ) :
    F (treeM leafₘ hashₘ z t) = treeM leafₙ hashₙ z t := by
  unfold treeM
  apply buildMerkleTreeAddressedM_natural
  · intro i
    exact hleaf _
  · intro a l r
    exact hhash _ _ l r

/-- Direct root computation commutes with any monad morphism mapping its callbacks
pointwise. -/
theorem merkleRootM_natural (F : m →ᵐ n)
    (leafₘ : ℕ → m Y) (hashₘ : ℕ → ℕ → Y → Y → m Y)
    (leafₙ : ℕ → n Y) (hashₙ : ℕ → ℕ → Y → Y → n Y)
    (hleaf : ∀ i, F (leafₘ i) = leafₙ i)
    (hhash : ∀ h i l r, F (hashₘ h i l r) = hashₙ h i l r)
    (z t : ℕ) :
    F (merkleRootM leafₘ hashₘ z t) = merkleRootM leafₙ hashₙ z t := by
  induction z generalizing t with
  | zero => simpa [merkleRootM] using hleaf t
  | succ z ih =>
      simp [merkleRootM, F.mmap_bind, ih, hhash]

/-- Streaming authentication-path construction commutes with any monad morphism mapping its
callbacks pointwise. -/
theorem authPathM_natural (F : m →ᵐ n)
    (leafₘ : ℕ → m Y) (hashₘ : ℕ → ℕ → Y → Y → m Y)
    (leafₙ : ℕ → n Y) (hashₙ : ℕ → ℕ → Y → Y → n Y)
    (hleaf : ∀ i, F (leafₘ i) = leafₙ i)
    (hhash : ∀ h i l r, F (hashₘ h i l r) = hashₙ h i l r)
    (idx z : ℕ) :
    F (authPathM leafₘ hashₘ idx z) = authPathM leafₙ hashₙ idx z := by
  induction z with
  | zero => simp [authPathM]
  | succ z ih =>
      simp [authPathM, F.mmap_bind, ih,
        merkleRootM_natural F leafₘ hashₘ leafₙ hashₙ hleaf hhash]

/-- Intrinsic authentication-path construction commutes with a monad morphism mapping its
leaf and node callbacks pointwise. -/
theorem intrinsicAuthPathM_natural (F : m →ᵐ n)
    (leafₘ : ℕ → m Y) (hashₘ : ℕ → ℕ → Y → Y → m Y)
    (leafₙ : ℕ → n Y) (hashₙ : ℕ → ℕ → Y → Y → n Y)
    (hleaf : ∀ i, F (leafₘ i) = leafₙ i)
    (hhash : ∀ h i l r, F (hashₘ h i l r) = hashₙ h i l r)
    (idx z : ℕ) :
    F (intrinsicAuthPathM leafₘ hashₘ idx z) = intrinsicAuthPathM leafₙ hashₙ idx z := by
  induction z with
  | zero => simp [intrinsicAuthPathM, F.mmap_pure]
  | succ z ih =>
      simp [intrinsicAuthPathM, F.mmap_bind, ih,
        merkleRootM_natural F leafₘ hashₘ leafₙ hashₙ hleaf hhash]

/-- Root recovery commutes with any monad morphism mapping node hashing pointwise. -/
theorem climbM_natural (F : m →ᵐ n)
    (hashₘ : ℕ → ℕ → Y → Y → m Y) (hashₙ : ℕ → ℕ → Y → Y → n Y)
    (hhash : ∀ h i l r, F (hashₘ h i l r) = hashₙ h i l r)
    (idx : ℕ) (node : Y) (auth : List Y) :
    F (climbM hashₘ idx node auth) = climbM hashₙ idx node auth := by
  unfold climbM
  apply getPutativeRootAddressedM_natural
  intro a l r
  exact hhash _ _ l r

/-- The direct root program has exactly the effects and order of building the full tree and
projecting its root.  This theorem deliberately orients away from materialising the full tree. -/
theorem merkleRootM_eq_map_treeM {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y) (z t : ℕ) :
    merkleRootM leaf nodeHash z t =
      FullData.getRootValue <$> treeM leaf nodeHash z t := by
  induction z generalizing t with
  | zero => simp [merkleRootM]
  | succ z ih =>
      simp [merkleRootM, treeM_succ, ih]

end Naturality

section PureInterpretation

/-- Running direct perfect-subtree root computation in `Id` recovers the canonical pure root. -/
@[simp]
theorem idRun_merkleRootM (leaf : ℕ → Id Y)
    (nodeHash : ℕ → ℕ → Y → Y → Id Y) (z t : ℕ) :
    Id.run (merkleRootM leaf nodeHash z t) =
      merkleRoot (fun i => Id.run (leaf i))
        (fun h i l r => Id.run (nodeHash h i l r)) z t := by
  induction z generalizing t with
  | zero => rfl
  | succ z ih => simp [merkleRootM, merkleRoot_succ, ih]

/-- Running sibling-only authentication-path construction in `Id` recovers the canonical pure
authentication path. -/
@[simp]
theorem idRun_authPathM (leaf : ℕ → Id Y)
    (nodeHash : ℕ → ℕ → Y → Y → Id Y) (idx z : ℕ) :
    Id.run (authPathM leaf nodeHash idx z) =
      authPath (fun i => Id.run (leaf i))
        (fun h i l r => Id.run (nodeHash h i l r)) idx z := by
  induction z with
  | zero => rfl
  | succ z ih =>
      simp [authPathM, authPath_succ, ih, idRun_merkleRootM]

/-- Running root recovery in `Id` recovers the canonical pure climb. -/
@[simp]
theorem idRun_climbM (nodeHash : ℕ → ℕ → Y → Y → Id Y)
    (idx : ℕ) (node : Y) (auth : List Y) :
    Id.run (climbM nodeHash idx node auth) =
      climb (fun h i l r => Id.run (nodeHash h i l r)) idx node auth := by
  unfold climbM climb nodeHashAt
  simpa only using
    (AddressedMerkleTree.idRun_getPutativeRootAddressedM
      (fun a => nodeHash (a.natAddr (idx / 2 ^ auth.length)).height
        (a.natAddr (idx / 2 ^ auth.length)).index)
      (SkeletonLeafIndex.ofNat auth.length idx) node
      (⟨auth.reverse, by simp⟩ :
        List.Vector Y (SkeletonLeafIndex.ofNat auth.length idx).depth))

end PureInterpretation

section DeterministicInterpretation

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- A deterministic handler commutes with effectful perfect-tree construction. -/
@[simp]
theorem simulateQ_treeM (impl : QueryImpl spec Id) (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ) :
    simulateQ impl (treeM leaf nodeHash z t) =
      tree (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) z t := by
  unfold treeM tree
  rw [simulateQ_buildMerkleTreeAddressedM]
  rfl

/-- A deterministic handler commutes with effectful root production. -/
@[simp]
theorem simulateQ_merkleRootM (impl : QueryImpl spec Id) (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ) :
    simulateQ impl (merkleRootM leaf nodeHash z t) =
      merkleRoot (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) z t := by
  induction z generalizing t with
  | zero => rfl
  | succ z ih =>
      simp only [merkleRootM, simulateQ_bind, merkleRoot_succ, ih]
      rfl

/-- Simulating an intrinsic authentication-path program with a deterministic oracle handler
maps its leaves and node hashes pointwise. -/
@[simp]
theorem simulateQ_intrinsicAuthPathM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx z : ℕ) :
    simulateQ impl (intrinsicAuthPathM leaf nodeHash idx z) =
      intrinsicAuthPath (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) idx z := by
  induction z with
  | zero => rfl
  | succ z ih =>
      simp only [intrinsicAuthPathM, simulateQ_bind, simulateQ_pure, intrinsicAuthPath, ih,
        simulateQ_merkleRootM]
      rfl

/-- A deterministic handler commutes with effectful authentication-path production. -/
@[simp]
theorem simulateQ_authPathM (impl : QueryImpl spec Id) (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx z : ℕ) :
    simulateQ impl (authPathM leaf nodeHash idx z) =
      authPath (fun i => simulateQ impl (leaf i))
        (fun h i l r => simulateQ impl (nodeHash h i l r)) idx z := by
  induction z with
  | zero => rfl
  | succ z ih =>
      simp only [authPathM, simulateQ_bind, simulateQ_pure, ih, simulateQ_merkleRootM]
      rw [authPath_succ]
      rfl

/-- A deterministic handler commutes with effectful root recovery. -/
@[simp]
theorem simulateQ_climbM (impl : QueryImpl spec Id)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx : ℕ) (node : Y)
    (auth : List Y) :
    simulateQ impl (climbM nodeHash idx node auth) =
      climb (fun h i l r => simulateQ impl (nodeHash h i l r)) idx node auth := by
  unfold climbM climb
  unfold nodeHashAt
  simpa only using
    (simulateQ_getPutativeRootAddressedM impl
      (fun a => nodeHash (a.natAddr (idx / 2 ^ auth.length)).height
        (a.natAddr (idx / 2 ^ auth.length)).index)
      (SkeletonLeafIndex.ofNat auth.length idx) node
      (⟨auth.reverse, by simp⟩ :
        List.Vector Y (SkeletonLeafIndex.ofNat auth.length idx).depth))

/-- Functional Merkle completeness after fixing one deterministic answer function for the whole
honest opening computation.  This does not claim completeness under raw free-oracle evaluation,
where repeated syntactic queries would be sampled independently. -/
theorem simulateQ_climbM_authPathM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx z : ℕ) :
    simulateQ impl (do
      let leafValue ← leaf idx
      let path ← authPathM leaf nodeHash idx z
      climbM nodeHash idx leafValue path) =
      simulateQ impl (merkleRootM leaf nodeHash z (idx / 2 ^ z)) := by
  simp only [simulateQ_bind, simulateQ_authPathM, simulateQ_climbM, simulateQ_merkleRootM]
  exact climb_authPath
    (fun i => simulateQ impl (leaf i))
    (fun h i l r => simulateQ impl (nodeHash h i l r)) idx z

end DeterministicInterpretation

end PerfectMerkleTree
