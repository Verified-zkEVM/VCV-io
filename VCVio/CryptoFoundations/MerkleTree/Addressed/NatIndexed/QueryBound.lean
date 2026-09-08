/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
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

end PerfectMerkleTree
