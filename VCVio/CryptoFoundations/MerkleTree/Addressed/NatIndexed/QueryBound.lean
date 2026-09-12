/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.MerkleTree.Addressed.QueryBound

/-!
# Query bounds for effectful natural-number-indexed Merkle trees

Structural total-query bounds for the effectful addressed-Merkle traversal.  The formulas expose
the exact number of leaf and internal-node callback invocations; the callback hypotheses may in
turn bound each invocation by any fixed number of oracle queries.

The current `OracleComp.IsTotalQueryBound` API is universe-homogeneous, so these corollaries use
one universe for the oracle domain, ranges, and Merkle values.  The underlying traversal remains
fully monad- and universe-parametric.

The final section records, for an arbitrary predicate on programs that holds of every `pure` and
is preserved by `bind`, sufficient conditions for that predicate to hold of a traversal, in terms
of the leaf indices and `(height, index)` node addresses the traversal visits.
-/

@[expose] public section

namespace PerfectMerkleTree

open BinaryTree OracleComp OracleSpec

universe u

variable {ι Y : Type u} {spec : OracleSpec.{u, u} ι}

private theorem tree_query_budget_succ (z leafBudget nodeBudget : ℕ) :
    2 * (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) + nodeBudget =
      2 ^ (z + 1) * leafBudget + (2 ^ (z + 1) - 1) * nodeBudget := by
  have hpow : 0 < 2 ^ z := pow_pos (by decide) _
  rw [pow_succ, Nat.mul_comm (2 ^ z) 2]
  have hcoeff : 2 * (2 ^ z - 1) + 1 = 2 * 2 ^ z - 1 := by omega
  calc
    2 * (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) + nodeBudget =
        (2 * 2 ^ z) * leafBudget + (2 * (2 ^ z - 1) + 1) * nodeBudget := by ring
    _ = (2 * 2 ^ z) * leafBudget + (2 * 2 ^ z - 1) * nodeBudget := by rw [hcoeff]

private theorem auth_query_budget_succ (z leafBudget nodeBudget : ℕ) :
    ((2 ^ z - 1) * leafBudget + (2 ^ z - z - 1) * nodeBudget) +
        (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) =
      (2 ^ (z + 1) - 1) * leafBudget +
        (2 ^ (z + 1) - (z + 1) - 1) * nodeBudget := by
  have hpow : 0 < 2 ^ z := pow_pos (by decide) _
  have hzpow : z + 1 ≤ 2 ^ z := by
    induction z with
    | zero => simp
    | succ z ih =>
        rw [pow_succ]
        omega
  rw [pow_succ, Nat.mul_comm (2 ^ z) 2]
  have hleaf : (2 ^ z - 1) + 2 ^ z = 2 * 2 ^ z - 1 := by omega
  have hnode : (2 ^ z - z - 1) + (2 ^ z - 1) = 2 * 2 ^ z - (z + 1) - 1 := by omega
  calc
    ((2 ^ z - 1) * leafBudget + (2 ^ z - z - 1) * nodeBudget) +
        (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) =
      ((2 ^ z - 1) + 2 ^ z) * leafBudget +
        ((2 ^ z - z - 1) + (2 ^ z - 1)) * nodeBudget := by ring
    _ = (2 * 2 ^ z - 1) * leafBudget +
        (2 * 2 ^ z - (z + 1) - 1) * nodeBudget := by rw [hleaf, hnode]

/-- Building a height-`z` perfect tree invokes the leaf callback `2 ^ z` times and the
internal-node callback `2 ^ z - 1` times. -/
theorem isTotalQueryBound_treeM
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget z t : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (treeM leaf nodeHash z t)
      (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) := by
  induction z generalizing t with
  | zero =>
      rw [show 2 ^ 0 * leafBudget + (2 ^ 0 - 1) * nodeBudget = leafBudget by norm_num]
      rw [treeM_zero]
      exact (isQueryBound_map_iff (leaf t) BinaryTree.FullData.leaf leafBudget _ _).mpr (hleaf t)
  | succ z ih =>
      rw [treeM_succ]
      have hleft := ih (2 * t)
      have hright := ih (2 * t + 1)
      have hboth := isTotalQueryBound_bind hleft fun left =>
        isTotalQueryBound_bind hright fun right =>
          isTotalQueryBound_bind (hnode (z + 1) t left.getRootValue right.getRootValue)
            fun root => show IsTotalQueryBound
              (pure (BinaryTree.FullData.internal root left right) : OracleComp spec _) 0 from
                trivial
      refine hboth.mono ?_
      rw [← tree_query_budget_succ]
      omega

/-- Direct root computation has the same structural query budget as full-tree construction:
`2 ^ z` leaf callbacks and `2 ^ z - 1` internal-node callbacks. -/
theorem isTotalQueryBound_merkleRootM
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget z t : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (merkleRootM leaf nodeHash z t)
      (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) := by
  induction z generalizing t with
  | zero => simpa [merkleRootM] using hleaf t
  | succ z ih =>
      simp only [merkleRootM]
      have hleft := ih (2 * t)
      have hright := ih (2 * t + 1)
      have hboth := isTotalQueryBound_bind hleft fun left =>
        isTotalQueryBound_bind hright fun right => hnode (z + 1) t left right
      refine hboth.mono ?_
      rw [← tree_query_budget_succ]
      omega

/-- A height-`z` authentication path visits every leaf outside the opened path exactly through
its sibling subtrees: `2 ^ z - 1` leaf callbacks and `2 ^ z - z - 1` internal-node callbacks. -/
theorem isTotalQueryBound_authPathM
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget idx z : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (authPathM leaf nodeHash idx z)
      ((2 ^ z - 1) * leafBudget + (2 ^ z - z - 1) * nodeBudget) := by
  induction z with
  | zero => exact trivial
  | succ z ih =>
      simp only [authPathM]
      have hsibling := isTotalQueryBound_merkleRootM leaf nodeHash leafBudget nodeBudget z
        (sibling (idx / 2 ^ z)) hleaf hnode
      have hboth := isTotalQueryBound_bind ih fun path =>
        isTotalQueryBound_bind hsibling fun siblingRoot =>
          show IsTotalQueryBound
            (pure (path ++ [siblingRoot]) : OracleComp spec _) 0 from trivial
      refine hboth.mono ?_
      rw [← auth_query_budget_succ]
      omega

/-- The intrinsically shaped authentication-path program has the same callback budget as the
list-valued traversal. -/
theorem isTotalQueryBound_intrinsicAuthPathM
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget idx z : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (intrinsicAuthPathM leaf nodeHash idx z)
      ((2 ^ z - 1) * leafBudget + (2 ^ z - z - 1) * nodeBudget) := by
  induction z with
  | zero => exact trivial
  | succ z ih =>
      simp only [intrinsicAuthPathM]
      have hsibling := isTotalQueryBound_merkleRootM leaf nodeHash
        leafBudget nodeBudget z (sibling (idx / 2 ^ z)) hleaf hnode
      have hboth := isTotalQueryBound_bind ih fun path =>
        isTotalQueryBound_bind hsibling fun siblingRoot =>
          show IsTotalQueryBound
            (pure (path.push siblingRoot) : OracleComp spec _) 0 from trivial
      refine hboth.mono ?_
      rw [← auth_query_budget_succ]
      omega

/-- Compose an authentication-path traversal with a continuation whose bound applies to every
well-formed result.  The path-length premise retains the structural fact that `authPathM` returns
exactly one sibling per level; ordinary `isTotalQueryBound_bind` cannot express this refinement
because it quantifies over every list supplied to the continuation. -/
theorem isTotalQueryBound_authPathM_bind
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget idx z continuationBudget : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget)
    {beta : Type u} (k : List Y → OracleComp spec beta)
    (hk : ∀ path, path.length = z → IsTotalQueryBound (k path) continuationBudget) :
    IsTotalQueryBound (authPathM leaf nodeHash idx z >>= k)
      (((2 ^ z - 1) * leafBudget + (2 ^ z - z - 1) * nodeBudget) +
        continuationBudget) := by
  induction z generalizing k continuationBudget with
  | zero =>
      simpa [authPathM] using hk [] rfl
  | succ z ih =>
      rw [authPathM]
      simp only [bind_assoc]
      let siblingBudget :=
        2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget
      have hrest : ∀ path, path.length = z →
          IsTotalQueryBound (do
            let siblingRoot ← merkleRootM leaf nodeHash z (sibling (idx / 2 ^ z))
            k (path ++ [siblingRoot])) (siblingBudget + continuationBudget) := by
        intro path hlength
        exact isTotalQueryBound_bind
          (isTotalQueryBound_merkleRootM leaf nodeHash leafBudget nodeBudget z
            (sibling (idx / 2 ^ z)) hleaf hnode)
          fun siblingRoot => hk (path ++ [siblingRoot]) (by simp [hlength])
      have hbound := ih (siblingBudget + continuationBudget)
        (fun path => do
          let siblingRoot ← merkleRootM leaf nodeHash z (sibling (idx / 2 ^ z))
          k (path ++ [siblingRoot])) hrest
      have hbudget :
          (((2 ^ z - 1) * leafBudget + (2 ^ z - z - 1) * nodeBudget) +
              siblingBudget) + continuationBudget =
            ((2 ^ (z + 1) - 1) * leafBudget +
              (2 ^ (z + 1) - (z + 1) - 1) * nodeBudget) +
                continuationBudget := by
        rw [auth_query_budget_succ]
      rw [← hbudget]
      simpa [Nat.add_assoc] using hbound

/-- Root recovery invokes the internal-node callback once per authentication-path entry. -/
theorem isTotalQueryBound_climbM
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (nodeBudget idx : ℕ) (node : Y) (auth : List Y)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (climbM nodeHash idx node auth) (auth.length * nodeBudget) := by
  unfold climbM
  simpa using AddressedMerkleTree.isTotalQueryBound_getPutativeRootAddressedM
    (fun a => nodeHash (a.natAddr (idx / 2 ^ auth.length)).height
      (a.natAddr (idx / 2 ^ auth.length)).index)
    nodeBudget (SkeletonLeafIndex.ofNat auth.length idx) node ⟨auth.reverse, by simp⟩
    (fun a l r => hnode _ _ l r)

/-! ## Pathwise predicates and the visited addresses

The lemmas of this section are stated for an arbitrary predicate `Q` on the programs of a monad
`m` that holds of every `pure` and is preserved by `bind`.  Each records the leaf indices and the
`(height, index)` node addresses at which a traversal invokes its callbacks, so that `Q` holds of
the traversal as soon as it holds of the callbacks at those addresses.  The lemmas state only the
sufficiency direction.  (A traversal does visit exactly the recorded addresses; the
`isTotalQueryBound_*` lemmas above bound the queries those visits cost.)  For an `OracleComp`, one
such predicate is `fun oa => OracleComp.IsQueryBound oa () (fun t _ => P t) (fun _ _ => ())` for
a query predicate `P`, by `OracleComp.isQueryBound_pure` and `OracleComp.isQueryBound_bind`; the
total bounds above are not of this shape because their budget is consumed.

Address sets are stated through quotients: leaf `i` lies in the height-`z` subtree rooted at
horizontal index `t` exactly when `i / 2 ^ z = t`, and the internal node `(h, i)` lies in it
exactly when `0 < h ≤ z` and `i / 2 ^ (z - h) = t`. -/

section PathwisePredicate

universe w

variable {m : Type u → Type w} [Monad m]
  (Q : ∀ {α : Type u}, m α → Prop)
  (hpure : ∀ {α : Type u} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type u} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))

private theorem div_pow_eq_div_pow_div_pow (i s z : ℕ) (hsz : s ≤ z) :
    i / 2 ^ z = i / 2 ^ s / 2 ^ (z - s) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hsz]

include hbind in
/-- `Q` holds of `merkleRootM leaf nodeHash z t` as soon as it holds of `leaf i` at every leaf of
the subtree rooted at `(z, t)`, the indices with `i / 2 ^ z = t`, and of `nodeHash h i l r` at every
internal node of that subtree, the addresses with `0 < h ≤ z` and `i / 2 ^ (z - h) = t`.  The
traversal visits exactly those addresses, but this lemma states only the sufficiency direction;
`isTotalQueryBound_merkleRootM` bounds the queries those visits cost. -/
theorem merkleRootM_pred_of_subtree (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y)
    (z t : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = t → Q (leaf i))
    (hnode : ∀ h i, 0 < h → h ≤ z → i / 2 ^ (z - h) = t → ∀ l r, Q (nodeHash h i l r)) :
    Q (merkleRootM leaf nodeHash z t) := by
  induction z generalizing t with
  | zero => exact hleaf t (by simp)
  | succ z ih =>
      simp only [merkleRootM]
      refine hbind _ _ (ih (2 * t) ?_ ?_) fun left =>
        hbind _ _ (ih (2 * t + 1) ?_ ?_) fun right =>
          hnode (z + 1) t (by omega) le_rfl (by simp) left right
      · intro i hi
        apply hleaf i
        rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]
        omega
      · intro h i hh hhz hi l r
        apply hnode h i hh (by omega) _ l r
        rw [show z + 1 - h = z - h + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, hi]
        omega
      · intro i hi
        apply hleaf i
        rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]
        omega
      · intro h i hh hhz hi l r
        apply hnode h i hh (by omega) _ l r
        rw [show z + 1 - h = z - h + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, hi]
        omega

include hpure hbind in
/-- `intrinsicAuthPathM leaf nodeHash idx z` evaluates, for each level `s < z`, the sibling
subtree of the level-`s` ancestor of leaf `idx`, rooted at `(s, sibling (idx / 2 ^ s))`, and
nothing else.  The hypotheses therefore range over the leaves and internal nodes of exactly those
subtrees; they do not mention the leaf `idx`, its ancestors, or the root at height `z`. -/
theorem intrinsicAuthPathM_pred_of_siblings (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx z : ℕ)
    (hleaf : ∀ s, s < z → ∀ i, i / 2 ^ s = sibling (idx / 2 ^ s) → Q (leaf i))
    (hnode : ∀ s, s < z → ∀ h i, 0 < h → h ≤ s → i / 2 ^ (s - h) = sibling (idx / 2 ^ s) →
      ∀ l r, Q (nodeHash h i l r)) :
    Q (intrinsicAuthPathM leaf nodeHash idx z) := by
  induction z with
  | zero => exact hpure _
  | succ z ih =>
      simp only [intrinsicAuthPathM]
      refine hbind _ _ (ih ?_ ?_) fun path => hbind _ _ ?_ fun siblingRoot => hpure _
      · exact fun s hs => hleaf s (by omega)
      · exact fun s hs => hnode s (by omega)
      · exact merkleRootM_pred_of_subtree Q hbind leaf nodeHash z _
          (hleaf z (by omega)) (hnode z (by omega))

include hpure hbind in
/-- Every sibling subtree that `intrinsicAuthPathM leaf nodeHash idx z` evaluates lies inside the
height-`z` subtree containing leaf `idx`, rooted at `(z, idx / 2 ^ z)`.  This corollary of
`intrinsicAuthPathM_pred_of_siblings` asks for `Q` at every leaf and every internal node of that
containing subtree, so its hypotheses over-approximate the visited addresses by the leaf `idx`,
its ancestors, and the root at height `z`. -/
theorem intrinsicAuthPathM_pred_of_tree (leaf : ℕ → m Y)
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx z : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = idx / 2 ^ z → Q (leaf i))
    (hnode : ∀ h i, 0 < h → h ≤ z → i / 2 ^ (z - h) = idx / 2 ^ z →
      ∀ l r, Q (nodeHash h i l r)) :
    Q (intrinsicAuthPathM leaf nodeHash idx z) := by
  apply intrinsicAuthPathM_pred_of_siblings Q hpure hbind
  · intro s hs i hi
    apply hleaf i
    rw [div_pow_eq_div_pow_div_pow i s z hs.le, div_pow_eq_div_pow_div_pow idx s z hs.le, hi,
      sibling_div_pow _ _ (by omega)]
  · intro s hs h i hh hhs hi l r
    apply hnode h i hh (by omega) _ l r
    rw [div_pow_eq_div_pow_div_pow i (s - h) (z - h) (by omega),
      show z - h - (s - h) = z - s by omega, hi, sibling_div_pow _ _ (by omega),
      div_pow_eq_div_pow_div_pow idx s z hs.le]

include hpure hbind in
/-- `Q` holds of `climbM nodeHash idx node auth` as soon as it holds of
`nodeHash h (idx / 2 ^ h) l r` at every ancestor of leaf `idx` up to height `auth.length`, the
nodes with `0 < h ≤ auth.length`.  The climb visits exactly those ancestors, one per level, but
this lemma states only the sufficiency direction; `isTotalQueryBound_climbM` bounds the queries
those visits cost. -/
theorem climbM_pred_of_ancestors (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y)
    (auth : List Y)
    (hnode : ∀ h, 0 < h → h ≤ auth.length → ∀ l r, Q (nodeHash h (idx / 2 ^ h) l r)) :
    Q (climbM nodeHash idx node auth) := by
  unfold climbM
  apply AddressedMerkleTree.getPutativeRootAddressedM_pred_of_ancestors Q hpure hbind
  intro a ha l r
  obtain ⟨hpos, hle⟩ := SkeletonInternalIndex.natAddr_height_pos_le (idx / 2 ^ auth.length) a
  rw [natAddr_index_of_isAncestorOf_ofNat ha]
  exact hnode _ hpos hle l r

end PathwisePredicate

end PerfectMerkleTree
