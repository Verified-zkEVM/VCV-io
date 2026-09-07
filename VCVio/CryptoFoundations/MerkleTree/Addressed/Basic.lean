/-
Copyright (c) 2026 Richard Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Binding
public import VCVio.CryptoFoundations.TweakableHash

/-! # Node-Addressed Merkle Trees

Merkle trees whose node hash may depend on the **full address** of the node being
hashed — the typed root-path position `SkeletonInternalIndex s` — via
`nodeHash : SkeletonInternalIndex s → α → α → α`.

Tree building, putative-root recomputation, completeness, and constructive collision
tracing are defined and proven **once here**, for an arbitrary `nodeHash`. Every hash
discipline expressible as a `nodeHash` — the ordinary tree (constant), the
level-separated tree (`nodeHash` through the depth of the addressed subtree), and
XMSS/SLH-DSA-style fully-addressed trees (`nodeHash` through an arbitrary
address-to-tweak map) — inherits all of it by specialization.

The unaddressed API in `MerkleTree.Inductive` is not defined as a wrapper around this engine: its
definitions (`getPutativeRootWithHash`, `populateUp`, `findCollision`) stand
independently. The `Instances` section establishes that the unaddressed API is
**propositionally subsumed** at the constant instance: its build and putative-root computations are
recovered (`populateUpAddressed_const`, `getPutativeRootAddressed_const`), its
completeness theorem is *re-derived* from this engine's rather than reproved
(`functional_completeness_of_addressed`), and its constructive collision walk is
literally this engine's walk with the address tag erased
(`findCollisionAddressed_const`).

Design: at each recursion step into a child, the engine passes the *reindexed* hash
`fun a => nodeHash (.ofLeft a)` (resp. `.ofRight`) — the address is threaded by
precomposition, so no explicit path accumulator or embedding parameter appears.

Contents:

* `SkeletonInternalIndex` — typed addresses of **internal** nodes (only internal nodes hash);
  `SkeletonInternalIndex.subtreeDepth` recovers the height of the addressed subtree (the
  level-separation data), and the full constructor path is the XMSS address.
* `populateUpAddressed` / `buildMerkleTreeAddressedWithHash` — cache construction.
* `getPutativeRootAddressedWithHash` — putative-root recomputation from a leaf, an
  authentication path (`generateProof` is reused unchanged — proofs carry no
  addresses), and a leaf index.
* `addressed_functional_completeness` — honest paths verify, for **every** `nodeHash`.
* `AddressedCollision`, `findCollisionAddressed`, `findCollisionAddressed_sound` —
  the constructive collision kernel, returning the collision **as data, tagged with
  the address** at which it occurs: two distinct pairs with equal hash *under that
  address's hash function*.
* `findCollisionAddressed_oriented` — the same walk oriented from an honest tree and
  opening toward an adversarial opening.
* `getPutativeRootAddressedWithHash_binding_collision` — the user-facing binding
  statement: distinct leaf values verifying to the same root at the same index yield
  an address-tagged collision.
* `addressed_oriented_binding` — the oriented binding statement used by
  target-collision-resistance reductions.

The symmetric collision statement here is deliberately **not** phrased as a
target-collision-resistance win: TCR is directional (one endpoint fixed at
target-registration time). The oriented results retain which collision endpoint came from the
honest tree so downstream reductions can preserve that direction.
-/

@[expose] public section

namespace AddressedMerkleTree

open List OracleSpec OracleComp BinaryTree InductiveMerkleTree

variable {α : Type _} [DecidableEq α]


/-- Build the full cache of a Merkle tree under an address-dependent hash: each
internal node stores `nodeHash addr leftRoot rightRoot` where `addr` is that node's
address. The address is threaded by reindexing `nodeHash` along `.ofLeft` / `.ofRight`. -/
@[simp, grind]
def populateUpAddressed : {s : Skeleton} → (nodeHash : SkeletonInternalIndex s → α → α → α) →
    LeafData α s → FullData α s
  | .leaf, _, .leaf v => .leaf v
  | .internal _ _, nh, .internal dl dr =>
    let L := populateUpAddressed (fun a => nh (.ofLeft a)) dl
    let R := populateUpAddressed (fun a => nh (.ofRight a)) dr
    .internal (nh .ofInternal L.getRootValue R.getRootValue) L R

/-- Alias matching the naming of the unaddressed engine. -/
@[simp, grind]
def buildMerkleTreeAddressedWithHash {s : Skeleton} (leaf_tree : LeafData α s)
    (nodeHash : SkeletonInternalIndex s → α → α → α) : FullData α s :=
  populateUpAddressed nodeHash leaf_tree

/-- Recompute the putative root from a leaf value, its index, and an authentication
path, hashing each step under the address of the node being reconstituted. The
node reconstituted by the *last* step is the root (`.ofInternal`); descending into the
index reindexes the hash along the path. -/
@[simp, grind]
def getPutativeRootAddressedWithHash :
    {s : Skeleton} → (nodeHash : SkeletonInternalIndex s → α → α → α) →
      (idx : SkeletonLeafIndex s) → (leafValue : α) → List.Vector α idx.depth → α
  | _, _, .ofLeaf, leafValue, _ => leafValue
  | _, nh, .ofLeft idxLeft, leafValue, proof =>
    nh .ofInternal (getPutativeRootAddressedWithHash (fun a => nh (.ofLeft a)) idxLeft
      leafValue proof.tail) proof.head
  | _, nh, .ofRight idxRight, leafValue, proof =>
    nh .ofInternal proof.head (getPutativeRootAddressedWithHash (fun a => nh (.ofRight a)) idxRight
      leafValue proof.tail)

omit [DecidableEq α] in
/-- **Completeness of the engine**: an honestly generated authentication path
recomputes the honest root, for every address-dependent hash. -/
theorem addressed_functional_completeness {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leaf_data_tree : LeafData α s)
    (nodeHash : SkeletonInternalIndex s → α → α → α) :
    getPutativeRootAddressedWithHash nodeHash idx (leaf_data_tree.get idx)
      (generateProof (buildMerkleTreeAddressedWithHash leaf_data_tree nodeHash) idx)
    = (buildMerkleTreeAddressedWithHash leaf_data_tree nodeHash).getRootValue := by
  induction idx with
  | ofLeaf => cases leaf_data_tree; rfl
  | ofLeft idxLeft ih =>
    cases leaf_data_tree with
    | internal dl dr =>
      simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
        getPutativeRootAddressedWithHash, InductiveMerkleTree.generateProof,
        List.Vector.head_cons, BinaryTree.LeafData.get, BinaryTree.FullData.getRootValue]
      exact congrArg (fun z => nodeHash .ofInternal z _) (ih dl (fun a => nodeHash (.ofLeft a)))
  | ofRight idxRight ih =>
    cases leaf_data_tree with
    | internal dl dr =>
      simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
        getPutativeRootAddressedWithHash, InductiveMerkleTree.generateProof,
        List.Vector.head_cons, BinaryTree.LeafData.get, BinaryTree.FullData.getRootValue]
      exact congrArg (nodeHash .ofInternal _) (ih dr (fun a => nodeHash (.ofRight a)))

/-- An address-tagged collision: two *distinct* input pairs with equal digest under
the hash **at that address**. -/
def AddressedCollision {s : Skeleton} (nodeHash : SkeletonInternalIndex s → α → α → α)
    (w : SkeletonInternalIndex s × α × α × α × α) : Prop :=
  (w.2.1, w.2.2.1) ≠ (w.2.2.2.1, w.2.2.2.2) ∧
    nodeHash w.1 w.2.1 w.2.2.1 = nodeHash w.1 w.2.2.2.1 w.2.2.2.2

/-- Walk two verifying branches at the same leaf index looking for the level at
which they merge; return the collision **as data, tagged with its address**. -/
def findCollisionAddressed : {s : Skeleton} → (nodeHash : SkeletonInternalIndex s → α → α → α) →
    (idx : SkeletonLeafIndex s) → (proof₁ proof₂ : List.Vector α idx.depth) →
    (x y : α) → Option (SkeletonInternalIndex s × α × α × α × α)
  | _, _, .ofLeaf, _, _, _, _ => none
  | _, nh, .ofLeft idxLeft, proof₁, proof₂, x, y =>
    let subL1 := getPutativeRootAddressedWithHash (fun a => nh (.ofLeft a)) idxLeft x proof₁.tail
    let subL2 := getPutativeRootAddressedWithHash (fun a => nh (.ofLeft a)) idxLeft y proof₂.tail
    if (subL1, proof₁.head) = (subL2, proof₂.head) then
      (findCollisionAddressed (fun a => nh (.ofLeft a)) idxLeft proof₁.tail proof₂.tail x y).map
        (fun w => (.ofLeft w.1, w.2))
    else if nh .ofInternal subL1 proof₁.head = nh .ofInternal subL2 proof₂.head then
      some (.ofInternal, subL1, proof₁.head, subL2, proof₂.head)
    else
      none
  | _, nh, .ofRight idxRight, proof₁, proof₂, x, y =>
    let subR1 := getPutativeRootAddressedWithHash (fun a => nh (.ofRight a)) idxRight x proof₁.tail
    let subR2 := getPutativeRootAddressedWithHash (fun a => nh (.ofRight a)) idxRight y proof₂.tail
    if (proof₁.head, subR1) = (proof₂.head, subR2) then
      (findCollisionAddressed (fun a => nh (.ofRight a)) idxRight proof₁.tail proof₂.tail x y).map
        (fun w => (.ofRight w.1, w.2))
    else if nh .ofInternal proof₁.head subR1 = nh .ofInternal proof₂.head subR2 then
      some (.ofInternal, proof₁.head, subR1, proof₂.head, subR2)
    else
      none

/-- **Soundness of the kernel**: anything returned is an address-tagged collision. -/
theorem findCollisionAddressed_sound {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (w : SkeletonInternalIndex s × α × α × α × α)
    (hw : findCollisionAddressed nodeHash idx proof₁ proof₂ x y = some w) :
    AddressedCollision nodeHash w := by
  induction idx with
  | ofLeaf => simp [findCollisionAddressed] at hw
  | ofLeft idxLeft ih =>
    rw [findCollisionAddressed] at hw
    split at hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact ih (fun a => nodeHash (.ofLeft a)) proof₁.tail proof₂.tail w' hw'
    · rename_i hneq
      split at hw
      · rename_i heq
        simp only [Option.some.injEq] at hw
        subst hw
        exact ⟨hneq, heq⟩
      · simp at hw
  | ofRight idxRight ih =>
    rw [findCollisionAddressed] at hw
    split at hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact ih (fun a => nodeHash (.ofRight a)) proof₁.tail proof₂.tail w' hw'
    · rename_i hneq
      split at hw
      · rename_i heq
        simp only [Option.some.injEq] at hw
        subst hw
        exact ⟨hneq, heq⟩
      · simp at hw

/-- **Locality of the kernel**: the collision address returned by `findCollisionAddressed` is
an ancestor of the opened leaf — the walk only ever descends along `idx`'s own path. -/
theorem findCollisionAddressed_isAncestorOf {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (w : SkeletonInternalIndex s × α × α × α × α)
    (hw : findCollisionAddressed nodeHash idx proof₁ proof₂ x y = some w) :
    w.1.IsAncestorOf idx := by
  induction idx with
  | ofLeaf => simp [findCollisionAddressed] at hw
  | ofLeft idxLeft ih =>
    rw [findCollisionAddressed] at hw
    split at hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact ih (fun a => nodeHash (.ofLeft a)) proof₁.tail proof₂.tail w' hw'
    · split at hw
      · simp only [Option.some.injEq] at hw
        subst hw
        trivial
      · simp at hw
  | ofRight idxRight ih =>
    rw [findCollisionAddressed] at hw
    split at hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact ih (fun a => nodeHash (.ofRight a)) proof₁.tail proof₂.tail w' hw'
    · split at hw
      · simp only [Option.some.injEq] at hw
        subst hw
        trivial
      · simp at hw

/-- If two distinct openings at the same index recompute the same root,
`findCollisionAddressed` finds a collision.  Distinctness covers disagreement in either the leaf
value or the authentication path. -/
theorem findCollisionAddressed_isSome_of_opening_ne {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx x proof₁
      = getPutativeRootAddressedWithHash nodeHash idx y proof₂)
    (hne : (x, proof₁) ≠ (y, proof₂)) :
    (findCollisionAddressed nodeHash idx proof₁ proof₂ x y).isSome := by
  induction idx with
  | ofLeaf =>
    simp only [vector_eq_nil] at hroot
    exact (hne (Prod.ext hroot (List.Vector.ext fun i => i.elim0))).elim
  | ofLeft idxLeft ih =>
    rw [findCollisionAddressed]
    split
    · rename_i hagree
      simp only [Prod.mk.injEq] at hagree
      simp only [Option.isSome_map]
      apply ih (fun a => nodeHash (.ofLeft a)) proof₁.tail proof₂.tail hagree.1
      intro hbranch
      have hvalue : x = y := congrArg Prod.fst hbranch
      have htail : proof₁.tail = proof₂.tail := congrArg Prod.snd hbranch
      apply hne
      apply Prod.ext hvalue
      exact proof₁.cons_head_tail.symm.trans
        (hagree.2 ▸ htail ▸ proof₂.cons_head_tail)
    · split
      · simp
      · rename_i hne'
        exact absurd (by simpa [getPutativeRootAddressedWithHash] using hroot) hne'
  | ofRight idxRight ih =>
    rw [findCollisionAddressed]
    split
    · rename_i hagree
      simp only [Prod.mk.injEq] at hagree
      simp only [Option.isSome_map]
      apply ih (fun a => nodeHash (.ofRight a)) proof₁.tail proof₂.tail hagree.2
      intro hbranch
      have hvalue : x = y := congrArg Prod.fst hbranch
      have htail : proof₁.tail = proof₂.tail := congrArg Prod.snd hbranch
      apply hne
      apply Prod.ext hvalue
      exact proof₁.cons_head_tail.symm.trans
        (hagree.1 ▸ htail ▸ proof₂.cons_head_tail)
    · split
      · simp
      · rename_i hne'
        exact absurd (by simpa [getPutativeRootAddressedWithHash] using hroot) hne'

/-- Leaf-disagreement specialization of `findCollisionAddressed_isSome_of_opening_ne`. -/
theorem findCollisionAddressed_isSome {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx x proof₁
      = getPutativeRootAddressedWithHash nodeHash idx y proof₂)
    (hne : x ≠ y) :
    (findCollisionAddressed nodeHash idx proof₁ proof₂ x y).isSome :=
  findCollisionAddressed_isSome_of_opening_ne nodeHash idx proof₁ proof₂ x y hroot
    (fun h => hne (congrArg Prod.fst h))

/-- **Binding, user-facing**: two openings of the same index recomputing the same
root with distinct leaf values yield an address-tagged collision, as data. -/
theorem getPutativeRootAddressedWithHash_binding_collision {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx x proof₁
      = getPutativeRootAddressedWithHash nodeHash idx y proof₂)
    (hne : x ≠ y) :
    ∃ w, findCollisionAddressed nodeHash idx proof₁ proof₂ x y = some w ∧
      AddressedCollision nodeHash w := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
    (findCollisionAddressed_isSome nodeHash idx proof₁ proof₂ x y hroot hne)
  exact ⟨w, hw, findCollisionAddressed_sound nodeHash idx proof₁ proof₂ x y w hw⟩

/-! ## Target orientation

`findCollisionAddressed` is symmetric in its two openings. The theorems below break
the symmetry for the honest-vs-adversarial configuration: when the first opening is
the **honest** one (leaf and path generated from a built cache), the first endpoint
of the returned collision is exactly the pair of child roots **stored in the cache at
the returned address** — a value fixed by the (commitment-time) build, before any
adversarial opening exists. This is the *directional* content a target-collision
reduction needs, exposed as data; the probabilistic game packaging is deliberately
kept separate. -/

/-- The pair of child root values stored at an internal address of a cache. These
are the honestly-precommitted hash inputs at that node. -/
@[simp]
def childPairAt : {s : Skeleton} → FullData α s → SkeletonInternalIndex s → α × α
  | _, .internal _ L R, .ofInternal => (L.getRootValue, R.getRootValue)
  | _, .internal _ L _, .ofLeft a => childPairAt L a
  | _, .internal _ _ R, .ofRight a => childPairAt R a

/-- **Orientation**: against an honest first opening, the collision's first endpoint
is the precommitted child pair at the returned address. -/
theorem findCollisionAddressed_oriented {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (ld : LeafData α s)
    (idx : SkeletonLeafIndex s) (y : α) (proof₂ : List.Vector α idx.depth)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx y proof₂
      = (buildMerkleTreeAddressedWithHash ld nodeHash).getRootValue)
    (hne : ld.get idx ≠ y) :
    ∃ (a : SkeletonInternalIndex s) (c : α × α),
      findCollisionAddressed nodeHash idx
        (InductiveMerkleTree.generateProof
          (buildMerkleTreeAddressedWithHash ld nodeHash) idx) proof₂
        (ld.get idx) y
      = some (a, (childPairAt (buildMerkleTreeAddressedWithHash ld nodeHash) a).1,
          (childPairAt (buildMerkleTreeAddressedWithHash ld nodeHash) a).2,
          c.1, c.2) := by
  induction idx with
  | ofLeaf =>
    cases ld with
    | leaf v =>
      simp only [getPutativeRootAddressedWithHash, buildMerkleTreeAddressedWithHash,
        populateUpAddressed, FullData.getRootValue_leaf] at hroot
      exact absurd hroot.symm (by simpa using hne)
  | ofLeft idxLeft ih =>
    cases ld with
    | internal dl dr =>
      have hsub : getPutativeRootAddressedWithHash (fun a => nodeHash (.ofLeft a)) idxLeft
          (dl.get idxLeft)
          (InductiveMerkleTree.generateProof
            (populateUpAddressed (fun a => nodeHash (.ofLeft a)) dl) idxLeft)
        = (populateUpAddressed (fun a => nodeHash (.ofLeft a)) dl).getRootValue :=
        addressed_functional_completeness idxLeft dl (fun a => nodeHash (.ofLeft a))
      have hroot' : nodeHash .ofInternal
          (getPutativeRootAddressedWithHash (fun a => nodeHash (.ofLeft a)) idxLeft y
            proof₂.tail) proof₂.head
        = nodeHash .ofInternal
            (populateUpAddressed (fun a => nodeHash (.ofLeft a)) dl).getRootValue
            (populateUpAddressed (fun a => nodeHash (.ofRight a)) dr).getRootValue := by
        simpa only [getPutativeRootAddressedWithHash, buildMerkleTreeAddressedWithHash,
          populateUpAddressed, FullData.internal_getRootValue] using hroot
      rw [findCollisionAddressed]
      split
      · rename_i hagree
        simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
          InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
          SkeletonLeafIndex.depth, List.Vector.tail_cons, List.Vector.head_cons,
          BinaryTree.LeafData.get, hsub, Prod.mk.injEq] at hagree
        obtain ⟨a', c, hwalk⟩ := ih (fun a => nodeHash (.ofLeft a)) dl proof₂.tail
          (show getPutativeRootAddressedWithHash (fun a => nodeHash (.ofLeft a)) idxLeft y
              proof₂.tail
            = (buildMerkleTreeAddressedWithHash dl (fun a => nodeHash (.ofLeft a))).getRootValue
            from hagree.1.symm)
          (by simpa using hne)
        refine ⟨.ofLeft a', c, ?_⟩
        simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
          InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
          SkeletonLeafIndex.depth, List.Vector.tail_cons,
          BinaryTree.LeafData.get] at hwalk ⊢
        rw [hwalk]
        simp [childPairAt]
      · split
        · refine ⟨.ofInternal, (getPutativeRootAddressedWithHash (fun a => nodeHash (.ofLeft a))
            idxLeft y proof₂.tail, proof₂.head), ?_⟩
          simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
            InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
            SkeletonLeafIndex.depth, List.Vector.tail_cons, List.Vector.head_cons,
            BinaryTree.LeafData.get, hsub, childPairAt]
        · rename_i hne2
          refine absurd ?_ hne2
          simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
            InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
            SkeletonLeafIndex.depth, List.Vector.tail_cons, List.Vector.head_cons,
            BinaryTree.LeafData.get, hsub]
          exact hroot'.symm
  | ofRight idxRight ih =>
    cases ld with
    | internal dl dr =>
      have hsub : getPutativeRootAddressedWithHash (fun a => nodeHash (.ofRight a)) idxRight
          (dr.get idxRight)
          (InductiveMerkleTree.generateProof
            (populateUpAddressed (fun a => nodeHash (.ofRight a)) dr) idxRight)
        = (populateUpAddressed (fun a => nodeHash (.ofRight a)) dr).getRootValue :=
        addressed_functional_completeness idxRight dr (fun a => nodeHash (.ofRight a))
      have hroot' : nodeHash .ofInternal proof₂.head
          (getPutativeRootAddressedWithHash (fun a => nodeHash (.ofRight a)) idxRight y
            proof₂.tail)
        = nodeHash .ofInternal
            (populateUpAddressed (fun a => nodeHash (.ofLeft a)) dl).getRootValue
            (populateUpAddressed (fun a => nodeHash (.ofRight a)) dr).getRootValue := by
        simpa only [getPutativeRootAddressedWithHash, buildMerkleTreeAddressedWithHash,
          populateUpAddressed, FullData.internal_getRootValue] using hroot
      rw [findCollisionAddressed]
      split
      · rename_i hagree
        simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
          InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
          SkeletonLeafIndex.depth, List.Vector.tail_cons, List.Vector.head_cons,
          BinaryTree.LeafData.get, hsub, Prod.mk.injEq] at hagree
        obtain ⟨a', c, hwalk⟩ := ih (fun a => nodeHash (.ofRight a)) dr proof₂.tail
          (show getPutativeRootAddressedWithHash (fun a => nodeHash (.ofRight a)) idxRight y
              proof₂.tail
            = (buildMerkleTreeAddressedWithHash dr (fun a => nodeHash (.ofRight a))).getRootValue
            from hagree.2.symm)
          (by simpa using hne)
        refine ⟨.ofRight a', c, ?_⟩
        simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
          InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
          SkeletonLeafIndex.depth, List.Vector.tail_cons,
          BinaryTree.LeafData.get] at hwalk ⊢
        rw [hwalk]
        simp [childPairAt]
      · split
        · refine ⟨.ofInternal, (proof₂.head, getPutativeRootAddressedWithHash
            (fun a => nodeHash (.ofRight a)) idxRight y proof₂.tail), ?_⟩
          simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
            InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
            SkeletonLeafIndex.depth, List.Vector.tail_cons, List.Vector.head_cons,
            BinaryTree.LeafData.get, hsub, childPairAt]
        · rename_i hne2
          refine absurd ?_ hne2
          simp only [buildMerkleTreeAddressedWithHash, populateUpAddressed,
            InductiveMerkleTree.generateProof, FullData.leftSubtree, FullData.rightSubtree,
            SkeletonLeafIndex.depth, List.Vector.tail_cons, List.Vector.head_cons,
            BinaryTree.LeafData.get, hsub]
          exact hroot'.symm

omit [DecidableEq α] in
/-- **Oriented binding, user-facing**: an adversarial opening that verifies against an
honestly built root with a different leaf value yields a collision whose first
endpoint is the honestly-precommitted child pair at the tagged address, which lies on the
opened leaf's own root path — the directional configuration a target-collision reduction
consumes. -/
theorem addressed_oriented_binding {s : Skeleton}
    (nodeHash : SkeletonInternalIndex s → α → α → α) (ld : LeafData α s)
    (idx : SkeletonLeafIndex s) (y : α) (proof₂ : List.Vector α idx.depth)
    (hroot : getPutativeRootAddressedWithHash nodeHash idx y proof₂
      = (buildMerkleTreeAddressedWithHash ld nodeHash).getRootValue)
    (hne : ld.get idx ≠ y) :
    ∃ (a : SkeletonInternalIndex s) (c : α × α), a.IsAncestorOf idx ∧
      (childPairAt (buildMerkleTreeAddressedWithHash ld nodeHash) a) ≠ c ∧
      nodeHash a (childPairAt (buildMerkleTreeAddressedWithHash ld nodeHash) a).1
          (childPairAt (buildMerkleTreeAddressedWithHash ld nodeHash) a).2
        = nodeHash a c.1 c.2 := by
  let : DecidableEq α := Classical.decEq α
  obtain ⟨a, c, hwalk⟩ :=
    findCollisionAddressed_oriented nodeHash ld idx y proof₂ hroot hne
  have hcol := findCollisionAddressed_sound nodeHash idx _ proof₂ (ld.get idx) y _ hwalk
  have hanc := findCollisionAddressed_isAncestorOf nodeHash idx _ proof₂ (ld.get idx) y _ hwalk
  exact ⟨a, c, hanc, by simpa [AddressedCollision, Prod.ext_iff] using hcol.1,
    by simpa [AddressedCollision] using hcol.2⟩

/-! ## Instances: three hash disciplines, one engine

The three hash disciplines are specializations of `nodeHash`; the theorems above
specialize with them. The theorems below are the **subsumption certificates** for the
constant instance: they exhibit the unaddressed `MerkleTree.Inductive` API as this
engine specialized, at the level of its computations
(`populateUpAddressed_const`, `getPutativeRootAddressed_const`,
`buildMerkleTreeAddressed_const`), its completeness theorem
(`functional_completeness_of_addressed`, derived here rather than reproved) and its
constructive collision kernel (`findCollisionAddressed_const`: address erasure sends
one to the other on the nose). The subsumption is propositional, not definitional —
see the scope note in the module header. The level-separated (`Tweaked`) development
factors through `SkeletonInternalIndex.subtreeDepth` and is *definitionally* an instance
(`levelNodeHash_eq_addressed` is `rfl`). -/

section Instances

omit [DecidableEq α] in
/-- **Ordinary instance**: a constant `nodeHash` recovers the unaddressed
putative-root computation. -/
theorem getPutativeRootAddressed_const (h : α → α → α) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (x : α) (proof : List.Vector α idx.depth) :
    getPutativeRootAddressedWithHash (s := s) (fun _ => h) idx x proof
      = InductiveMerkleTree.getPutativeRootWithHash idx x proof h := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idxLeft ih => simp [getPutativeRootAddressedWithHash, ih]
  | ofRight idxRight ih => simp [getPutativeRootAddressedWithHash, ih]

omit [DecidableEq α] in
/-- **Ordinary instance**: a constant `nodeHash` recovers the unaddressed cache
construction. -/
theorem populateUpAddressed_const (h : α → α → α) {s : Skeleton}
    (ld : LeafData α s) :
    populateUpAddressed (fun _ => h) ld = BinaryTree.populateUp ld h := by
  induction ld with
  | leaf v => rfl
  | internal dl dr ihl ihr => simp [populateUpAddressed, BinaryTree.populateUp, ihl, ihr]

omit [DecidableEq α] in
/-- **Ordinary instance**: a constant `nodeHash` recovers the unaddressed build. -/
theorem buildMerkleTreeAddressed_const (h : α → α → α) {s : Skeleton}
    (ld : LeafData α s) :
    buildMerkleTreeAddressedWithHash ld (fun _ => h)
      = InductiveMerkleTree.buildMerkleTreeWithHash ld h :=
  populateUpAddressed_const h ld

omit [DecidableEq α] in
/-- **Subsumption certificate (completeness)**: the unaddressed completeness theorem
is a consequence of the engine's, at the constant instance. This is not a second
proof of completeness — it is the first one, specialized. -/
theorem functional_completeness_of_addressed (h : α → α → α) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (ld : LeafData α s) :
    InductiveMerkleTree.getPutativeRootWithHash idx (ld.get idx)
        (InductiveMerkleTree.generateProof
          (InductiveMerkleTree.buildMerkleTreeWithHash ld h) idx) h
      = (InductiveMerkleTree.buildMerkleTreeWithHash ld h).getRootValue := by
  rw [← buildMerkleTreeAddressed_const h ld, ← getPutativeRootAddressed_const h]
  exact addressed_functional_completeness idx ld (fun _ => h)

/-- **Subsumption certificate (collision kernel)**: erasing the address tag from the
engine's constructive collision walk yields *exactly* the unaddressed `findCollision`.
So the two collision kernels are not parallel implementations that happen to agree on
their statements — they are one function, up to the address decoration. -/
theorem findCollisionAddressed_const (h : α → α → α) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector α idx.depth) (x y : α) :
    (findCollisionAddressed (fun _ => h) idx proof₁ proof₂ x y).map (fun w => w.2)
      = InductiveMerkleTree.findCollision h idx proof₁ proof₂ x y := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idxLeft ih =>
    rw [findCollisionAddressed, InductiveMerkleTree.findCollision]
    simp only [getPutativeRootAddressed_const, dite_eq_ite]
    split
    · rw [Option.map_map]; exact ih proof₁.tail proof₂.tail
    · split <;> rfl
  | ofRight idxRight ih =>
    rw [findCollisionAddressed, InductiveMerkleTree.findCollision]
    simp only [getPutativeRootAddressed_const, dite_eq_ite]
    split
    · rw [Option.map_map]; exact ih proof₁.tail proof₂.tail
    · split <;> rfl

/-- **Level-separated instance**: hash through the depth of the addressed subtree.
This is the discipline of the `Tweaked` development: per-level domain separation. -/
def levelNodeHash {PkSeed Tweak Y : Type} (th : TweakableHash PkSeed Tweak (Y × Y) Y)
    (pk : PkSeed) (tweakAt : ℕ → Tweak) {s : Skeleton} : SkeletonInternalIndex s → Y → Y → Y :=
  fun a l r => th.eval pk (tweakAt a.subtreeDepth) (l, r)

/-- **Fully-addressed (XMSS-style) instance**: hash through an arbitrary map out of
the full typed address — per-node domain separation. Any concrete addressing scheme
(layer, horizontal index, domain tag) factors through `tweakOf`; nothing about the
address is discarded before the user's map is applied. -/
def addressedNodeHash {PkSeed Tweak Y : Type} (th : TweakableHash PkSeed Tweak (Y × Y) Y)
    (pk : PkSeed) {s : Skeleton} (tweakOf : SkeletonInternalIndex s → Tweak) :
    SkeletonInternalIndex s → Y → Y → Y :=
  fun a l r => th.eval pk (tweakOf a) (l, r)

/-- The level instance factors through the fully-addressed one — level separation is
the special case `tweakOf = tweakAt ∘ subtreeDepth`. -/
theorem levelNodeHash_eq_addressed {PkSeed Tweak Y : Type}
    (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed) (tweakAt : ℕ → Tweak)
    {s : Skeleton} :
    levelNodeHash th pk tweakAt (s := s)
      = addressedNodeHash th pk (fun a => tweakAt a.subtreeDepth) := rfl

end Instances

end AddressedMerkleTree
