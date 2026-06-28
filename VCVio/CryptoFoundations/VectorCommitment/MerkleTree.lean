/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import VCVio.CryptoFoundations.VectorCommitment.Basic
import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import VCVio.CryptoFoundations.MerkleTree.Inductive.Completeness

/-!
# Inductive Merkle trees as (batch-opening) vector commitments

This file realizes the inductive Merkle tree of
`VCVio.CryptoFoundations.MerkleTree.Inductive.Defs` against the abstract positional commitment
interfaces of `VCVio.CryptoFoundations.VectorCommitment.Basic`:

- `InductiveMerkleTree.vectorCommitment` — the Merkle `VectorCommitment` (single-position opening);
- `InductiveMerkleTree.naiveBatchOpenMerkleTree` — a `BatchOpeningVectorCommitment` obtained from
  the above via `VectorCommitment.toBatchOpening`. It is *naive* in that a batch opening is just the
  list of individual leaf authentication paths, with no sharing of common interior hashes; a
  purpose-built batch proof could be more succinct.

These instances are what a consumer such as the Kilian transformation
(`VCVio.CryptoFoundations.Kilian`) is meant to be supplied with; that file depends on the abstract
commitment interface only, not on this concrete Merkle realization.

The construction is in the standard-model / collision-resistant-hash formulation: hashing is a pure
two-to-one function `hashFn`, so all commitment operations are pure and the instances live in any
monad. Positions are laid out on a caller-supplied skeleton `s` via a position-to-leaf equivalence
`e : ι ≃ SkeletonLeafIndex s`; an opening is the authentication path (the sibling hashes along the
leaf's branch), carried as a plain `List` of hashes.
-/

open OracleComp OracleSpec BinaryTree

namespace InductiveMerkleTree

variable {α : Type}

/-- Build the leaf data of a Merkle tree of skeleton `s` from a function assigning a value to each
leaf position. -/
def leafDataOfFn : (s : Skeleton) → (SkeletonLeafIndex s → α) → LeafData α s
  | Skeleton.leaf, f => LeafData.leaf (f SkeletonLeafIndex.ofLeaf)
  | Skeleton.internal _ _, f =>
      LeafData.internal
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofLeft i))
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofRight i))

/-- The inductive Merkle tree as a `VectorCommitment`.

Positions `ι` are mapped to the leaves of skeleton `s` by the equivalence `e`, and `hashFn` is the
two-to-one compression function. Committing builds the full tree and exposes its root; an opening
for a position is its authentication path (`generateProof`), carried as a `List`; verification
recomputes the putative root from the leaf value and path (`getPutativeRootWithHash`) and compares
it to the commitment. The operations are pure, so the instance is available in any monad `m`. -/
def vectorCommitment {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    VectorCommitment m ι α α (FullData α s) (List α) where
  commit data :=
    let tree := buildMerkleTreeWithHash (leafDataOfFn s fun i => data (e.symm i)) hashFn
    pure (tree.getRootValue, tree)
  decode tree i := tree.toLeafData.get (e i)
  openAt tree i := pure (generateProof tree (e i)).toList
  verifyOpen root i v op :=
    if h : op.length = (e i).depth then
      decide (getPutativeRootWithHash (e i) v ⟨op, h⟩ hashFn = root)
    else false

/-- The inductive Merkle tree as a `BatchOpeningVectorCommitment`, obtained from
`InductiveMerkleTree.vectorCommitment` via `VectorCommitment.toBatchOpening`.

A batch opening for a list of positions is simply the list of their individual authentication paths
(each as `(position, value, path)`); verification checks each claimed position against its path
independently. This shares no interior hashes between paths, hence *naive* — a dedicated multi-leaf
Merkle proof could compress the common prefixes — but it is correct and requires nothing beyond the
single-position instance. -/
def naiveBatchOpenMerkleTree {ι : Type} {m : Type → Type} [Monad m]
    [DecidableEq ι] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    BatchOpeningVectorCommitment m ι α α (FullData α s) (List (ι × α × List α)) :=
  (vectorCommitment s e hashFn).toBatchOpening

/-! ### Correctness -/

/-- Mapping a pure-valued effect over a list collapses to a pure mapped list. -/
theorem mapM_pure_map {m : Type → Type} [Monad m] [LawfulMonad m] {β γ : Type} (g : β → γ) :
    ∀ is : List β, (is.mapM fun i => (pure (g i) : m γ)) = pure (is.map g)
  | [] => by simp
  | a :: as => by simp [List.mapM_cons, mapM_pure_map g as]

/-- Eta for `List.Vector`: rebuilding the subtype from `v.toList` returns `v`. -/
@[simp]
theorem vector_mk_toList {n : ℕ} (v : List.Vector α n) (h : v.toList.length = n) :
    (⟨v.toList, h⟩ : List.Vector α n) = v :=
  List.Vector.toList_injective (List.Vector.toList_mk _ _)

/-- Rebuilding a tree from leaf data `ld` and reading its leaves back recovers `ld`. -/
@[simp]
theorem toLeafData_buildMerkleTreeWithHash {s : Skeleton}
    (ld : LeafData α s) (hashFn : α → α → α) :
    (buildMerkleTreeWithHash ld hashFn).toLeafData = ld := by
  induction ld with
  | leaf a => rfl
  | internal left right ihl ihr =>
      simp only [buildMerkleTreeWithHash, populateUp_internal, FullData.toLeafData_internal] at *
      rw [ihl, ihr]

/-- **Perfect correctness of the Merkle vector commitment.** Every position opened honestly against
an honestly built tree verifies against the committed root. The opening's authentication path is
`generateProof`, and the check reduces to `InductiveMerkleTree.functional_completeness`. -/
theorem vectorCommitment_perfectlyCorrect {ι : Type} {m : Type → Type} [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    (vectorCommitment (m := m) s e hashFn).PerfectlyCorrect := by
  intro data i c st hcst op hop
  simp only [vectorCommitment, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcst
  obtain ⟨rfl, rfl⟩ := hcst
  simp only [vectorCommitment, support_pure, Set.mem_singleton_iff] at hop
  subst hop
  simp only [vectorCommitment, List.Vector.toList_length, dite_true,
    toLeafData_buildMerkleTreeWithHash, decide_eq_true_eq, vector_mk_toList]
  exact functional_completeness (e i) _ hashFn

/-! Per-field reductions for the Merkle vector commitment, letting proofs unfold `commit` / `decode`
/ `openAt` without also unfolding `verifyOpen` into its `dite`. -/

@[simp]
theorem vectorCommitment_decode {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α)
    (st : FullData α s) (i : ι) :
    (vectorCommitment (m := m) s e hashFn).decode st i = st.toLeafData.get (e i) := rfl

@[simp]
theorem vectorCommitment_openAt {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α)
    (st : FullData α s) (i : ι) :
    (vectorCommitment (m := m) s e hashFn).openAt st i =
      pure (generateProof st (e i)).toList := rfl

theorem vectorCommitment_commit {ι : Type} {m : Type → Type} [Monad m] [DecidableEq α]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) (data : ι → α) :
    (vectorCommitment (m := m) s e hashFn).commit data =
      pure (let t := buildMerkleTreeWithHash (leafDataOfFn s fun i => data (e.symm i)) hashFn;
        (t.getRootValue, t)) := rfl

/-- **Perfect correctness of the naive batch-opening Merkle commitment.** A batch opening of any
list of positions verifies the decoded claims. Since the batch opening is just the list of the
individual authentication paths, this reduces to `vectorCommitment_perfectlyCorrect`. -/
theorem naiveBatchOpenMerkleTree_perfectlyCorrect {ι : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [DecidableEq α] [DecidableEq ι]
    (s : Skeleton) (e : ι ≃ SkeletonLeafIndex s) (hashFn : α → α → α) :
    (naiveBatchOpenMerkleTree (m := m) s e hashFn).PerfectlyCorrect := by
  have hvc := vectorCommitment_perfectlyCorrect (m := m) s e hashFn
  intro data is c st hcst op hop
  simp only [naiveBatchOpenMerkleTree, VectorCommitment.toBatchOpening, vectorCommitment_commit,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcst
  obtain ⟨rfl, rfl⟩ := hcst
  set tree := buildMerkleTreeWithHash (leafDataOfFn s fun i => data (e.symm i)) hashFn with htree
  simp only [naiveBatchOpenMerkleTree, VectorCommitment.toBatchOpening, vectorCommitment_openAt,
    vectorCommitment_decode, bind_pure_comp, map_pure, mapM_pure_map, support_pure,
    Set.mem_singleton_iff] at hop
  subst hop
  -- The batch opening is `is.map g`, with `g i` the leaf value and authentication path at `i`.
  set g : ι → ι × α × List α :=
    fun i => (i, tree.toLeafData.get (e i), (generateProof tree (e i)).toList) with hg
  -- The honestly built commitment/state, used to invoke single-position correctness.
  have hc : (tree.getRootValue, tree) ∈
      support ((vectorCommitment (m := m) s e hashFn).commit data) := by
    simp only [vectorCommitment_commit, htree, support_pure, Set.mem_singleton_iff]
  -- Each opened position verifies against the root, via the single-position correctness `hvc`.
  have hverify : ∀ i, (vectorCommitment (m := m) s e hashFn).verifyOpen tree.getRootValue i
      (tree.toLeafData.get (e i)) (generateProof tree (e i)).toList = true := by
    intro i
    have ho : (generateProof tree (e i)).toList ∈
        support ((vectorCommitment (m := m) s e hashFn).openAt tree i) := by
      simp only [vectorCommitment_openAt, support_pure, Set.mem_singleton_iff]
    simpa only [vectorCommitment_decode] using hvc data i tree.getRootValue tree hc _ ho
  simp only [naiveBatchOpenMerkleTree, VectorCommitment.toBatchOpening, vectorCommitment_decode,
    List.all_eq_true, List.mem_map, forall_exists_index, and_imp]
  rintro _ i hi rfl
  dsimp only
  -- Look up position `i` in the batch opening; it is present because `i ∈ is`.
  rcases hfind : (List.map g is).find? (fun entry => decide (entry.1 = i)) with _ | entry
  · rw [List.find?_eq_none] at hfind
    exact ((hfind (g i) (List.mem_map_of_mem hi)) (by simp [hg])).elim
  · obtain ⟨j, _, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hfind)
    have hj : j = i := by simpa [hg] using List.find?_some hfind
    rw [hfind]
    simp [hg, hj, hverify]

end InductiveMerkleTree
