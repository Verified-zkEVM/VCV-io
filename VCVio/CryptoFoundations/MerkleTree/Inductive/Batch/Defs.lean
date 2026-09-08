/-
Copyright (c) 2026 IAOM / Equation Capital dba Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abraxas1010 (IAOM / Apoth3osis)
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs

/-!
# Batch Openings for Inductive Merkle Trees

This file defines *batch* openings for the inductive Merkle tree construction of
`VCVio.CryptoFoundations.MerkleTree.Inductive.Defs`: opening several leaves of one tree
against a single root with a single, deduplicated piece of authentication data.

A batch opening is specified by a *selector* `sel : LeafData Bool s` marking which leaves
are opened. The authentication data `BatchProof α sel` mirrors the shape of the tree, but is
*pruned*: a subtree containing no selected leaf contributes exactly one hash (its root) to
the proof, and the proof does not descend into it. In particular:

* opening a single leaf recovers (the information content of) the single-index
  `generateProof` copath;
* opening *all* leaves yields a proof carrying **no** hashes at all (the verifier recomputes
  everything from the claimed leaf values);
* shared copath nodes between the opened leaves are never duplicated.

This is the vector-commitment operation used by the query phase of IOP-based proof systems
(FRI/STIR/WHIR) and by the BCS transform, where a verifier opens many leaves of one
committed vector at once.

## Relation to path pruning in the SNARGs book

This is an intrinsic encoding of the *path-pruning* optimization in
[*Building Cryptographic Proofs from Hash Functions*](https://snargsbook.org/). The book
first presents a multi-opening as one authentication path per opened location, then removes
both duplicate commitments and commitments derivable from the opened leaves. Its optimized
proof contains the minimal authentication frontier: the vertices in the union of the
copaths, minus the vertices in the union of the paths.

`BatchProof` represents that same frontier directly for an arbitrary indexed binary-tree
skeleton. An unselected subtree contributes exactly its root, while a subtree containing
selected leaves is recomputed from its selected values and recursively pruned proof. The
dependent constructors make the pruned shape canonical instead of representing the
frontier as a separate flat vertex set. `batchToSingleProof` in `Batch.ToSingle` is the
corresponding expansion into an authentication path for one selected leaf. A separate
tuple-of-paths compression API and a full compression/expansion equivalence are not
formalized here.

## Main definitions

* `InductiveMerkleTree.BatchProof`: pruned authentication data for a selector. The family is
  indexed by the selector, so structurally malformed proofs (extra hashes, hashes for opened
  subtrees, or descent into pruned subtrees) are unrepresentable. It is inhabited only when
  the selector selects at least one leaf.
* `InductiveMerkleTree.SelectedValues`: the tuple of claimed values for the selected leaves.
* `InductiveMerkleTree.selectedValues`: extract the selected values from leaf data.
* `InductiveMerkleTree.generateBatchProof`: the honest prover, reading pruned subtree roots
  off the cached full tree.
* `InductiveMerkleTree.getPutativeBatchRoot(WithHash)`: recompute the root from claimed
  values plus batch proof (monadic and functional forms), with the `simulateQ` reduction
  lemma connecting them.
* `InductiveMerkleTree.verifyBatchProof`: compare the putative root against a claimed root.

Completeness is proved in `VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Completeness`,
and opening uniqueness under an injective hash in
`VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Uniqueness`.

**Tracked follow-up (sparse selectors).** The dense selector `LeafData Bool s` is the
right internal representation for the recursions here, but downstream consumers
(FRI/STIR/WHIR-style query patterns in ArkLib) naturally hold a sparse `List`/`Finset` of
query indices. A conversion API (sparse index set → dense selector, with `getLeaf`-level
correspondence lemmas) should be added before those consumers land, so they neither pay
for nor expose a full-tree selection mask.
-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

universe u

variable {α : Type _}

/--
Authentication data for a batch opening with selector `sel`.

The proof mirrors the tree's shape but is *pruned at unselected subtrees*: whenever one
child of an internal node contains no selected leaf, the proof stores that child's root
hash and descends only into the other child. When both children contain selected leaves,
the proof stores no hash at that node and descends into both. At a selected leaf the proof
stores nothing (the verifier is given the claimed leaf value separately, via
`SelectedValues`).

The hypotheses on the pruning constructors make the proof shape canonical for its selector:
for every selector that selects at least one leaf exactly one constructor applies at each
node. Conversely the family is *uninhabited* whenever `sel.anySelected = false` (see
`BatchProof.anySelected_of_batchProof` below): there is no such thing as a
batch proof that opens nothing.
-/
inductive BatchProof (α : Type u) : {s : Skeleton} → LeafData Bool s → Type u
  /-- Opening a selected leaf carries no authentication data of its own. -/
  | leaf : BatchProof α (.leaf true)
  /-- Both children contain selected leaves: descend into both, store nothing. -/
  | internalBoth {sₗ sᵣ : Skeleton} {l : LeafData Bool sₗ} {r : LeafData Bool sᵣ}
      (pl : BatchProof α l) (pr : BatchProof α r) : BatchProof α (.internal l r)
  /-- The right child contains no selected leaf: store its root hash, descend left. -/
  | pruneRight {sₗ sᵣ : Skeleton} {l : LeafData Bool sₗ} {r : LeafData Bool sᵣ}
      (hr : r.anySelected = false) (rightRoot : α) (pl : BatchProof α l) :
      BatchProof α (.internal l r)
  /-- The left child contains no selected leaf: store its root hash, descend right. -/
  | pruneLeft {sₗ sᵣ : Skeleton} {l : LeafData Bool sₗ} {r : LeafData Bool sᵣ}
      (hl : l.anySelected = false) (leftRoot : α) (pr : BatchProof α r) :
      BatchProof α (.internal l r)

/-- A batch proof exists only for selectors that select at least one leaf. This structural
inhabitation invariant is part of the proof representation's basic API. -/
theorem BatchProof.anySelected_of_batchProof {s : Skeleton} {sel : LeafData Bool s}
    (proof : BatchProof α sel) : sel.anySelected = true := by
  induction proof with
  | leaf => rfl
  | internalBoth pl pr ihl ihr => simp [LeafData.anySelected, ihl, ihr]
  | pruneRight hr rightRoot pl ih => simp [LeafData.anySelected, ih]
  | pruneLeft hl leftRoot pr ih => simp [LeafData.anySelected, ih]

/-- The tuple of claimed values for the leaves selected by `sel`: one `α` per selected
leaf, `PUnit` at unselected leaves, products at internal nodes.

The reducer is available at implicit transparency because dependent recursion
on a batch proof must identify this type with the product of the recursively
selected child values. -/
@[simp, grind, implicit_reducible]
def SelectedValues (α : Type u) : {s : Skeleton} → LeafData Bool s → Type u
  | _, .leaf true => α
  | _, .leaf false => PUnit
  | _, .internal l r => SelectedValues α l × SelectedValues α r

/-- Extract the claimed values of the selected leaves from the tree's leaf data. This is the
batch analogue of `LeafData.get` at a single index. -/
@[simp, grind]
def selectedValues : {s : Skeleton} → (leaves : LeafData α s) → (sel : LeafData Bool s) →
    SelectedValues α sel
  | _, .leaf a, .leaf true => a
  | _, .leaf _, .leaf false => ⟨⟩
  | _, .internal la ra, .internal l r => (selectedValues la l, selectedValues ra r)

/--
The honest prover for batch openings: walk the cached full tree, storing the root of each
pruned (unselected) subtree, and descending wherever there are selected leaves. Requires the
selector to select at least one leaf.
-/
@[simp, grind]
def generateBatchProof : {s : Skeleton} → (cache : FullData α s) → (sel : LeafData Bool s) →
    sel.anySelected = true → BatchProof α sel
  | _, _, .leaf true, _ => .leaf
  | _, cache, .internal l r, h =>
    match hl : l.anySelected, hr : r.anySelected with
    | true, true =>
      .internalBoth (generateBatchProof cache.leftSubtree l hl)
        (generateBatchProof cache.rightSubtree r hr)
    | true, false =>
      .pruneRight hr cache.rightSubtree.getRootValue (generateBatchProof cache.leftSubtree l hl)
    | false, true =>
      .pruneLeft hl cache.leftSubtree.getRootValue (generateBatchProof cache.rightSubtree r hr)
    | false, false => by
      exfalso
      simp only [LeafData.anySelected, hl, hr, Bool.or_self] at h
      exact Bool.false_ne_true h

/--
A functional form of the putative batch root computation, with an explicit hash function.

Recompute the root of the tree from the claimed values of the selected leaves and the
pruned authentication data: at a selected leaf, use the claimed value; at a pruned subtree,
use the stored root hash; at an internal node, hash the two recomputed children in tree
order.
-/
@[simp, grind]
def getPutativeBatchRootWithHash (hashFn : α → α → α) :
    {s : Skeleton} → {sel : LeafData Bool s} → SelectedValues α sel → BatchProof α sel → α
  | _, _, v, .leaf => v
  | _, _, v, .internalBoth pl pr =>
    hashFn (getPutativeBatchRootWithHash hashFn v.1 pl)
      (getPutativeBatchRootWithHash hashFn v.2 pr)
  | _, _, v, .pruneRight _ rightRoot pl =>
    hashFn (getPutativeBatchRootWithHash hashFn v.1 pl) rightRoot
  | _, _, v, .pruneLeft _ leftRoot pr =>
    hashFn leftRoot (getPutativeBatchRootWithHash hashFn v.2 pr)

/--
Monadic form of the putative batch root computation, hashing through the oracle. This is the
batch analogue of `getPutativeRoot`.
-/
@[simp, grind]
def getPutativeBatchRoot {m : Type _ → Type _} [Monad m] [HasQuery (spec α) m] :
    {s : Skeleton} → {sel : LeafData Bool s} → SelectedValues α sel → BatchProof α sel → m α
  | _, _, v, .leaf => pure v
  | _, _, v, .internalBoth pl pr => do
    let leftRoot ← getPutativeBatchRoot v.1 pl
    let rightRoot ← getPutativeBatchRoot v.2 pr
    singleHash leftRoot rightRoot
  | _, _, v, .pruneRight _ rightRoot pl => do
    let leftRoot ← getPutativeBatchRoot v.1 pl
    singleHash leftRoot rightRoot
  | _, _, v, .pruneLeft _ leftRoot pr => do
    let rightRoot ← getPutativeBatchRoot v.2 pr
    singleHash leftRoot rightRoot

/--
Running the monadic `getPutativeBatchRoot` with an oracle function `f` is the same as
running the functional `getPutativeBatchRootWithHash` with the corresponding hash function.
-/
@[simp, grind =]
lemma simulateQ_getPutativeBatchRoot {s : Skeleton} {sel : LeafData Bool s}
    (v : SelectedValues α sel) (proof : BatchProof α sel) (f : QueryImpl (spec α) Id) :
    simulateQ f (getPutativeBatchRoot v proof) =
      getPutativeBatchRootWithHash (fun left right => f ⟨left, right⟩) v proof := by
  induction proof with
  | leaf => rfl
  | internalBoth pl pr ihl ihr =>
    simp only [getPutativeBatchRoot, getPutativeBatchRootWithHash, singleHash,
      simulateQ_bind, ihl, ihr]
    rfl
  | pruneRight hr rightRoot pl ih =>
    simp only [getPutativeBatchRoot, getPutativeBatchRootWithHash, singleHash,
      simulateQ_bind, ih]
    rfl
  | pruneLeft hl leftRoot pr ih =>
    simp only [getPutativeBatchRoot, getPutativeBatchRootWithHash, singleHash,
      simulateQ_bind, ih]
    rfl

/--
Verify a batch opening: recompute the putative root from the claimed selected values and
the batch proof, and compare with the claimed root. This is the batch analogue of
`verifyProof`.
-/
@[simp, grind]
def verifyBatchProof {m : Type _ → Type _} [Monad m] [HasQuery (spec α) m] [DecidableEq α]
    {s : Skeleton} {sel : LeafData Bool s} (values : SelectedValues α sel)
    (rootValue : α) (proof : BatchProof α sel) : m Bool := do
  let putativeRoot ← (getPutativeBatchRoot values proof : m α)
  return (putativeRoot == rootValue)

end InductiveMerkleTree
