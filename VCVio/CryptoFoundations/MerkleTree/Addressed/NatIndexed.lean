/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Basic
public import ToMathlib.Data.IndexedBinaryTree.Perfect
public import ToMathlib.Data.IndexedBinaryTree.Equiv

/-!
# Perfect Merkle trees with heap-style natural-number addressing

The node-addressed Merkle engine (`AddressedMerkleTree`) specialised to **perfect** binary
trees whose nodes are addressed by `(height, horizontal index)` pairs of natural numbers, as in
XMSS and the FORS trees of SLH-DSA (FIPS 205 §6, §8). A leaf-value function `leaf : ℕ → Y` and a
position-indexed node hash `nodeHash height index left right` determine, for every height `z` and
horizontal index `t`, the subtree whose leaves are
`leaf (t * 2 ^ z), …, leaf (t * 2 ^ z + 2 ^ z - 1)`
and whose internal node at `(h, i)` is `nodeHash h i (left child) (right child)`.

* `tree leaf nodeHash z t` — the fully populated subtree at `(z, t)`, as
  `AddressedMerkleTree.buildMerkleTreeAddressedWithHash` over `Skeleton.perfect z`.
* `merkleRoot leaf nodeHash z t` — its root, satisfying the FIPS 205 Algorithm 9 / 15 recursion
  (`merkleRoot_zero`, `merkleRoot_succ`).
* `authPath leaf nodeHash idx z` — the authentication path of leaf `idx` over `z` levels, listed
  from the leaf level upwards (the FIPS 205 order); the reversal of the engine's
  `InductiveMerkleTree.generateProof`.
* `climb nodeHash idx node auth` — root recovery from a leaf value and an authentication path
  (Algorithms 11 / 17); the engine's `getPutativeRootAddressedWithHash`.
* `climb_authPath` — completeness, from `addressed_functional_completeness`.
* `findCollision leaf nodeHash idx y auth` — the ℕ-addressed collision extractor: the engine's
  `findCollisionAddressed` run against the honest opening of leaf `idx`, returning the height
  `h` of the collision node together with the honest and adversarial child pairs. The node's
  horizontal index is not returned because it is determined: every address the kernel can
  return is an ancestor of leaf `idx`, hence sits at horizontal index `idx / 2 ^ h`
  (`findCollision_sound`, `findCollision_oriented`).
* `climb_binding` — oriented binding, from `findCollision_oriented`: an adversarial opening
  that verifies against the honest root with a different leaf value yields, at some height
  `0 < h ≤ z`, a collision of `nodeHash h (idx / 2 ^ h)` whose first endpoint is the honestly
  computed child pair at that address. Since the target is determined by `(idx, h)`, a
  multi-target target-collision reduction on the node hash has at most `z` candidate targets
  per opened leaf.
-/

@[expose] public section

namespace PerfectMerkleTree

open BinaryTree AddressedMerkleTree InductiveMerkleTree

variable {Y : Type _}

/-- The leaf data of the perfect height-`z` subtree rooted at horizontal index `t`. -/
def leafData (leaf : ℕ → Y) (z t : ℕ) : LeafData Y (Skeleton.perfect z) :=
  LeafData.ofFun _ fun i => leaf (i.natIndex t)

/-- The address-dependent node hash of the subtree rooted at `(z, t)`, obtained from a
`(height, horizontal index)`-indexed hash by reading each internal node's address. -/
def nodeHashAt (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    SkeletonInternalIndex (Skeleton.perfect z) → Y → Y → Y :=
  fun a => nodeHash (a.natAddr t).height (a.natAddr t).index

/-- The fully populated perfect subtree at `(height z, horizontal index t)`. -/
def tree (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    FullData Y (Skeleton.perfect z) :=
  buildMerkleTreeAddressedWithHash (leafData leaf z t) (nodeHashAt nodeHash z t)

/-- The root of the perfect subtree at `(height z, horizontal index t)`. -/
def merkleRoot (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) : Y :=
  (tree leaf nodeHash z t).getRootValue

@[simp]
theorem tree_zero (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (t : ℕ) :
    tree leaf nodeHash 0 t = .leaf (leaf t) := rfl

/-- The subtree at `(z + 1, t)` hashes the subtrees at `(z, 2t)` and `(z, 2t + 1)`.

This (like `tree_zero`) is `rfl` because `Skeleton.perfect` is `implicit_reducible`,
`LeafData.ofFun` / `populateUpAddressed` unfold structurally on `.internal`, and the `.ofLeft` /
`.ofRight` cases of `SkeletonLeafIndex.natIndex` and `SkeletonInternalIndex.natAddr` recurse with
exactly `2 * t` / `2 * t + 1`. A change to any of those reduction behaviours will surface here. -/
theorem tree_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    tree leaf nodeHash (z + 1) t
      = .internal (nodeHash (z + 1) t (merkleRoot leaf nodeHash z (2 * t))
          (merkleRoot leaf nodeHash z (2 * t + 1)))
        (tree leaf nodeHash z (2 * t)) (tree leaf nodeHash z (2 * t + 1)) := rfl

@[simp]
theorem merkleRoot_zero (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (t : ℕ) :
    merkleRoot leaf nodeHash 0 t = leaf t := rfl

/-- The FIPS 205 Algorithm 9 / 15 recursion for subtree roots. -/
theorem merkleRoot_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    merkleRoot leaf nodeHash (z + 1) t
      = nodeHash (z + 1) t (merkleRoot leaf nodeHash z (2 * t))
          (merkleRoot leaf nodeHash z (2 * t + 1)) := rfl

/-- Flip the least-significant bit of a heap-style node index. -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- A node and its sibling share their parent. -/
theorem sibling_div_two (i : ℕ) : sibling i / 2 = i / 2 := by
  unfold sibling
  split_ifs <;> omega

/-- A node and its sibling share every ancestor at positive height. -/
theorem sibling_div_pow (i k : ℕ) (hk : 0 < k) : sibling i / 2 ^ k = i / 2 ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, sibling_div_two]

/-- The authentication path of leaf `idx` over `z` levels, listed from the leaf level upwards:
entry `j` is the root of the sibling subtree at height `j`. -/
def authPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) : List Y :=
  (generateProof (tree leaf nodeHash z (idx / 2 ^ z))
    (SkeletonLeafIndex.ofNat z idx)).toList.reverse

@[simp]
theorem authPath_length (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    (authPath leaf nodeHash idx z).length = z := by
  simp [authPath]

/-- Extending an authentication path by one level appends the root of the sibling subtree at
that level.  This is the streaming/FIPS view of the canonical full-tree definition. -/
theorem authPath_succ (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    authPath leaf nodeHash idx (z + 1) =
      authPath leaf nodeHash idx z ++
        [merkleRoot leaf nodeHash z (sibling (idx / 2 ^ z))] := by
  unfold authPath sibling
  simp only [SkeletonLeafIndex.ofNat]
  rw [tree_succ]
  by_cases h : idx / 2 ^ z % 2 = 0
  · rw [if_pos h]
    have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have heven : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
    simp only [generateProof, List.Vector.toList_cons, List.reverse_cons,
      FullData.leftSubtree, FullData.rightSubtree, FullData.getRootValue]
    rw [heven]
    rw [if_pos h]
    rfl
  · rw [if_neg h]
    have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
    have hmod : idx / 2 ^ z % 2 = 1 := by omega
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hodd : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by
      rw [hdiv]
      omega
    have hleft : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z - 1 := by omega
    simp only [generateProof, List.Vector.toList_cons, List.reverse_cons,
      FullData.leftSubtree, FullData.rightSubtree, FullData.getRootValue]
    rw [hodd]
    rw [if_neg h]
    unfold merkleRoot
    unfold FullData.getRootValue
    rw [hleft]

/-- Root recovery: starting from `node` at leaf position `idx`, fold in the sibling values of
`auth` (leaf level first), hashing each step under the address of the node being reconstructed.
The tree height is the length of `auth`. -/
def climb (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y) (auth : List Y) : Y :=
  getPutativeRootAddressedWithHash (nodeHashAt nodeHash auth.length (idx / 2 ^ auth.length))
    (SkeletonLeafIndex.ofNat auth.length idx) node ⟨auth.reverse, by simp⟩

/-- `climb` on a path of known length `z`, unfolded to the engine's putative root. -/
theorem climb_eq (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) (node : Y) (auth : List Y)
    {z : ℕ} (hlen : auth.length = z) :
    climb nodeHash idx node auth
      = getPutativeRootAddressedWithHash (nodeHashAt nodeHash z (idx / 2 ^ z))
          (SkeletonLeafIndex.ofNat z idx) node ⟨auth.reverse, by simp [hlen]⟩ := by
  subst hlen; rfl

/-- The honest leaf value is the leaf of `leafData` at `ofNat z idx`. -/
theorem leafData_get_ofNat (leaf : ℕ → Y) (z idx : ℕ) :
    (leafData leaf z (idx / 2 ^ z)).get (SkeletonLeafIndex.ofNat z idx) = leaf idx := by
  simp [leafData]

/-- **Merkle auth-path consistency.** Climbing the honest authentication path of leaf `idx`
from the honest leaf value reconstructs the height-`z` ancestor root. -/
theorem climb_authPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    climb nodeHash idx (leaf idx) (authPath leaf nodeHash idx z)
      = merkleRoot leaf nodeHash z (idx / 2 ^ z) := by
  rw [climb_eq nodeHash idx _ _ (authPath_length leaf nodeHash idx z)]
  have hvec : (⟨(authPath leaf nodeHash idx z).reverse, by simp⟩ :
      List.Vector Y (SkeletonLeafIndex.ofNat z idx).depth)
      = generateProof (tree leaf nodeHash z (idx / 2 ^ z)) (SkeletonLeafIndex.ofNat z idx) := by
    apply Subtype.ext
    simp only [authPath, List.reverse_reverse]
    rfl
  rw [hvec, ← leafData_get_ofNat leaf z idx]
  exact addressed_functional_completeness _ _ _

/-- The child pair stored at an internal address of the honest tree is the pair of honest child
roots at that `(height, index)` address. -/
theorem childPairAt_tree (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) {z : ℕ} (t : ℕ)
    (a : SkeletonInternalIndex (Skeleton.perfect z)) :
    childPairAt (tree leaf nodeHash z t) a
      = (merkleRoot leaf nodeHash ((a.natAddr t).height - 1) (2 * (a.natAddr t).index),
          merkleRoot leaf nodeHash ((a.natAddr t).height - 1) (2 * (a.natAddr t).index + 1)) := by
  induction z generalizing t with
  | zero => nomatch a
  | succ z ih =>
    cases a with
    | ofInternal =>
      rw [tree_succ]
      rfl
    | ofLeft a => rw [tree_succ]; simpa [SkeletonInternalIndex.natAddr] using ih (2 * t) a
    | ofRight a => rw [tree_succ]; simpa [SkeletonInternalIndex.natAddr] using ih (2 * t + 1) a

/-- The horizontal index of an ancestor of the leaf `ofNat z idx`, in the subtree rooted at
`idx / 2 ^ z`, is `idx` shifted down by the ancestor's height. -/
theorem natAddr_index_of_isAncestorOf_ofNat {z idx : ℕ}
    {a : SkeletonInternalIndex (Skeleton.perfect z)}
    (h : a.IsAncestorOf (SkeletonLeafIndex.ofNat z idx)) :
    (a.natAddr (idx / 2 ^ z)).index = idx / 2 ^ (a.natAddr (idx / 2 ^ z)).height := by
  rw [a.natAddr_index_of_isAncestorOf (idx / 2 ^ z) h, SkeletonLeafIndex.natIndex_ofNat]

/-- The honestly computed child pair of the internal node at `(h, i)`. -/
def honestChildren (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (h i : ℕ) : Y × Y :=
  (merkleRoot leaf nodeHash (h - 1) (2 * i), merkleRoot leaf nodeHash (h - 1) (2 * i + 1))

/-- Collision extraction, as data. Run the engine's `findCollisionAddressed` kernel against the
honest opening of leaf `idx` (honest leaf value and honest authentication path over
`auth.length` levels) and the adversarial opening `(y, auth)`. On success returns the height `h`
of the collision node, the honest child pair there, and the adversarial child pair; the node's
horizontal index is `idx / 2 ^ h` (`findCollision_sound`). -/
def findCollision [DecidableEq Y] (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ)
    (y : Y) (auth : List Y) : Option (ℕ × (Y × Y) × (Y × Y)) :=
  (findCollisionAddressed (nodeHashAt nodeHash auth.length (idx / 2 ^ auth.length))
    (SkeletonLeafIndex.ofNat auth.length idx)
    (generateProof (tree leaf nodeHash auth.length (idx / 2 ^ auth.length))
      (SkeletonLeafIndex.ofNat auth.length idx))
    ⟨auth.reverse, by simp⟩ (leaf idx) y).map
    fun w => ((w.1.natAddr (idx / 2 ^ auth.length)).height, (w.2.1, w.2.2.1),
      (w.2.2.2.1, w.2.2.2.2))

/-- `findCollision` on a path of known length `z`, unfolded to the engine kernel. -/
theorem findCollision_eq [DecidableEq Y] (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (idx : ℕ) (y : Y) (auth : List Y) {z : ℕ} (hlen : auth.length = z) :
    findCollision leaf nodeHash idx y auth
      = (findCollisionAddressed (nodeHashAt nodeHash z (idx / 2 ^ z))
          (SkeletonLeafIndex.ofNat z idx)
          (generateProof (tree leaf nodeHash z (idx / 2 ^ z)) (SkeletonLeafIndex.ofNat z idx))
          ⟨auth.reverse, by simp [hlen]⟩ (leaf idx) y).map
          fun w => ((w.1.natAddr (idx / 2 ^ z)).height, (w.2.1, w.2.2.1),
            (w.2.2.2.1, w.2.2.2.2)) := by
  subst hlen; rfl

/-- **Soundness of `findCollision`.** Anything it returns is a collision of `nodeHash` at the
address `(h, idx / 2 ^ h)` of an internal node on the root path of leaf `idx`. -/
theorem findCollision_sound [DecidableEq Y] (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (z idx : ℕ) (y : Y) (auth : List Y) (hlen : auth.length = z)
    (h : ℕ) (c₁ c₂ : Y × Y) (hw : findCollision leaf nodeHash idx y auth = some (h, c₁, c₂)) :
    0 < h ∧ h ≤ z ∧ c₁ ≠ c₂ ∧
      nodeHash h (idx / 2 ^ h) c₁.1 c₁.2 = nodeHash h (idx / 2 ^ h) c₂.1 c₂.2 := by
  rw [findCollision_eq leaf nodeHash idx y auth hlen, Option.map_eq_some_iff] at hw
  obtain ⟨w, hw, hmap⟩ := hw
  simp only [Prod.mk.injEq] at hmap
  obtain ⟨rfl, rfl, rfl⟩ := hmap
  have hcol := findCollisionAddressed_sound _ _ _ _ _ _ w hw
  have hanc := findCollisionAddressed_isAncestorOf _ _ _ _ _ _ w hw
  have hidx := natAddr_index_of_isAncestorOf_ofNat hanc
  obtain ⟨hpos, hle⟩ := w.1.natAddr_height_pos_le (idx / 2 ^ z)
  refine ⟨hpos, hle, ?_, ?_⟩
  · simpa [AddressedCollision, Prod.ext_iff] using hcol.1
  · have := hcol.2
    simp only [nodeHashAt, hidx] at this
    exact this

/-- **Oriented extraction.** Against an adversarial opening that verifies to the honest root
with a leaf value `y ≠ leaf idx`, `findCollision` succeeds and its first pair is the honest
child pair at the returned address `(h, idx / 2 ^ h)`. -/
theorem findCollision_oriented [DecidableEq Y] (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y)
    (z idx : ℕ) (y : Y) (auth : List Y) (hlen : auth.length = z)
    (hroot : climb nodeHash idx y auth = merkleRoot leaf nodeHash z (idx / 2 ^ z))
    (hne : leaf idx ≠ y) :
    ∃ (h : ℕ) (c : Y × Y),
      findCollision leaf nodeHash idx y auth
        = some (h, honestChildren leaf nodeHash h (idx / 2 ^ h), c) := by
  rw [climb_eq nodeHash idx y auth hlen] at hroot
  have hne' : (leafData leaf z (idx / 2 ^ z)).get (SkeletonLeafIndex.ofNat z idx) ≠ y := by
    rwa [leafData_get_ofNat]
  obtain ⟨a, c, hwalk⟩ := findCollisionAddressed_oriented (nodeHashAt nodeHash z (idx / 2 ^ z))
    (leafData leaf z (idx / 2 ^ z)) (SkeletonLeafIndex.ofNat z idx) y _ hroot hne'
  rw [leafData_get_ofNat] at hwalk
  have hanc := findCollisionAddressed_isAncestorOf _ _ _ _ _ _ _ hwalk
  have hidx := natAddr_index_of_isAncestorOf_ofNat hanc
  refine ⟨(a.natAddr (idx / 2 ^ z)).height, c, ?_⟩
  rw [findCollision_eq leaf nodeHash idx y auth hlen]
  rw [show tree leaf nodeHash z (idx / 2 ^ z)
      = buildMerkleTreeAddressedWithHash (leafData leaf z (idx / 2 ^ z))
          (nodeHashAt nodeHash z (idx / 2 ^ z)) from rfl, hwalk, Option.map_some]
  have key := childPairAt_tree leaf nodeHash (idx / 2 ^ z) a
  unfold tree at key
  rw [key, ← hidx]
  rfl

/-- **Oriented Merkle binding.** An authentication path of length `z` that climbs from a leaf
value `y ≠ leaf idx` to the honest height-`z` root exhibits, at the internal node of height
`0 < h ≤ z` on the root path of leaf `idx` — address `(h, idx / 2 ^ h)` — a collision of
`nodeHash h (idx / 2 ^ h)` whose first endpoint is the honestly computed child pair there: a
target fixed by the honest tree, before the adversarial opening, and determined by `(idx, h)`.
Propositional form of `findCollision_oriented`. -/
theorem climb_binding (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (z idx : ℕ) (y : Y)
    (auth : List Y) (hlen : auth.length = z)
    (hroot : climb nodeHash idx y auth = merkleRoot leaf nodeHash z (idx / 2 ^ z))
    (hne : leaf idx ≠ y) :
    ∃ (h : ℕ) (c : Y × Y), 0 < h ∧ h ≤ z ∧
      (merkleRoot leaf nodeHash (h - 1) (2 * (idx / 2 ^ h)),
          merkleRoot leaf nodeHash (h - 1) (2 * (idx / 2 ^ h) + 1))
        ≠ c ∧
      nodeHash h (idx / 2 ^ h) (merkleRoot leaf nodeHash (h - 1) (2 * (idx / 2 ^ h)))
          (merkleRoot leaf nodeHash (h - 1) (2 * (idx / 2 ^ h) + 1))
        = nodeHash h (idx / 2 ^ h) c.1 c.2 := by
  let : DecidableEq Y := Classical.decEq Y
  obtain ⟨h, c, hw⟩ := findCollision_oriented leaf nodeHash z idx y auth hlen hroot hne
  obtain ⟨hpos, hle, hne, hcol⟩ := findCollision_sound leaf nodeHash z idx y auth hlen h _ c hw
  exact ⟨h, c, hpos, hle, hne, hcol⟩

end PerfectMerkleTree
