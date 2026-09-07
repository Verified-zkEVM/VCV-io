/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.TraceTargets
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# Trace provenance of the FORS programs

This module extends the pathwise predicate `QueriesWithinConstructionTargets` of
`HashSig.SLHDSA.Security.TraceTargets` from the WOTS+ programs to the FORS programs.  Each theorem
says that every public-hash query a program can issue, under any oracle answers, uses an encoded
address from the union ledger `constructionAddresses`; the `*_traceContract` theorems pair that
with the program's total query bound.

The FORS programs are certified at the FORS address of a reachable `BottomPosition`, and through
`BottomPosition.ofDigestParts` at the digest-derived address `DigestParts.forsAdrs` that
`GeneralScheme.signInternalM` and `verifyInternalM` pass to them.  Their Merkle traversals are
handled by the generic address-tracking lemmas `PerfectMerkleTree.merkleRootM_pred_of_subtree`,
`intrinsicAuthPathM_pred_of_tree`, and `climbM_pred_of_ancestors`, instantiated at the
construction predicate; the leaf and node addresses those lemmas surface are placed in the FORS
ledgers by `mem_forsLeafAddresses`, `mem_forsTreeAddresses`, and `mem_forsRootAddresses`.

## References

- NIST FIPS 205, §8 (Algorithms 14--17, the FORS programs)
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The construction predicate through the Merkle traversals -/

/-- The construction predicate holds of a subtree root whenever it holds of the leaf program at
every leaf of the subtree and of the node-hash program at every internal node of the subtree. -/
theorem QueriesWithinConstructionTargets.merkleRootM {Y : Type}
    (leaf : ℕ → OracleComp (publicHashSpec core) Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp (publicHashSpec core) Y) (z t : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = t → QueriesWithinConstructionTargets core (leaf i))
    (hnode : ∀ h i, 0 < h → h ≤ z → i / 2 ^ (z - h) = t → ∀ l r,
      QueriesWithinConstructionTargets core (nodeHash h i l r)) :
    QueriesWithinConstructionTargets core (PerfectMerkleTree.merkleRootM leaf nodeHash z t) :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree (QueriesWithinConstructionTargets core)
    (fun _ _ hprogram hcontinuation =>
      QueriesWithinConstructionTargets.bind hprogram hcontinuation)
    leaf nodeHash z t hleaf hnode

/-- The construction predicate holds of an authentication path whenever it holds of the leaf and
node-hash programs throughout the height-`z` subtree containing the opened leaf. -/
theorem QueriesWithinConstructionTargets.intrinsicAuthPathM {Y : Type}
    (leaf : ℕ → OracleComp (publicHashSpec core) Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp (publicHashSpec core) Y) (idx z : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = idx / 2 ^ z → QueriesWithinConstructionTargets core (leaf i))
    (hnode : ∀ h i, 0 < h → h ≤ z → i / 2 ^ (z - h) = idx / 2 ^ z → ∀ l r,
      QueriesWithinConstructionTargets core (nodeHash h i l r)) :
    QueriesWithinConstructionTargets core
      (PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z) :=
  PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree (QueriesWithinConstructionTargets core)
    (fun x => queriesWithinConstructionTargets_pure core x)
    (fun _ _ hprogram hcontinuation =>
      QueriesWithinConstructionTargets.bind hprogram hcontinuation)
    leaf nodeHash idx z hleaf hnode

/-- The construction predicate holds of a root recovery whenever it holds of the node-hash program
at every ancestor of the opened leaf up to the path length. -/
theorem QueriesWithinConstructionTargets.climbM {Y : Type}
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp (publicHashSpec core) Y) (idx : ℕ) (node : Y)
    (auth : List Y)
    (hnode : ∀ h, 0 < h → h ≤ auth.length → ∀ l r,
      QueriesWithinConstructionTargets core (nodeHash h (idx / 2 ^ h) l r)) :
    QueriesWithinConstructionTargets core (PerfectMerkleTree.climbM nodeHash idx node auth) :=
  PerfectMerkleTree.climbM_pred_of_ancestors (QueriesWithinConstructionTargets core)
    (fun x => queriesWithinConstructionTargets_pure core x)
    (fun _ _ hprogram hcontinuation =>
      QueriesWithinConstructionTargets.bind hprogram hcontinuation)
    nodeHash idx node auth hnode

/-! ## FORS addresses of a reachable bottom position -/

/-- The height-`a` tree containing the leaf `forsSignWith` selects in FORS tree `i` is tree `i`. -/
theorem forsLeafIndex_div (p : Params) (md : List Byte) (i : ℕ) :
    (i * 2 ^ p.a + forsIdx p md i) / 2 ^ p.a = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (forsIdx_lt p md i), Nat.zero_add]

/-- Every leaf of FORS tree `tree` at a reachable bottom position is a union-ledger target. -/
theorem forsLeafAdrs_mem_constructionAddresses (pos : BottomPosition vp)
    (tree : Fin vp.params.k) {i : ℕ} (hi : i / 2 ^ vp.params.a = tree.val) :
    forsNodeAdrs pos.forsAdrs 0 i ∈ constructionAddresses vp := by
  rw [mem_constructionAddresses_iff]
  refine Or.inl ?_
  have hidx : tree.val * vp.params.t + i % 2 ^ vp.params.a = i := by
    rw [← hi]
    exact Nat.div_add_mod' i _
  simpa [hidx] using mem_forsLeafAddresses vp pos tree
    ⟨i % 2 ^ vp.params.a, Nat.mod_lt i (by positivity)⟩

/-- Every internal node of FORS tree `tree` at a reachable bottom position is a union-ledger
target. -/
theorem forsTreeAdrs_mem_constructionAddresses (pos : BottomPosition vp)
    (tree : Fin vp.params.k) {h i : ℕ} (hh : 0 < h) (hha : h ≤ vp.params.a)
    (hi : i / 2 ^ (vp.params.a - h) = tree.val) :
    forsNodeAdrs pos.forsAdrs h i ∈ constructionAddresses vp := by
  rw [mem_constructionAddresses_iff]
  refine Or.inr (Or.inl ?_)
  have hidx : tree.val * 2 ^ (vp.params.a - h) + i % 2 ^ (vp.params.a - h) = i := by
    rw [← hi]
    exact Nat.div_add_mod' i _
  simpa [hidx] using mem_forsTreeAddresses vp pos tree hh hha
    (Nat.mod_lt i (by positivity) : i % 2 ^ (vp.params.a - h) < 2 ^ (vp.params.a - h))

/-- The FORS root compression of a reachable bottom position is a union-ledger target. -/
theorem forsRootAdrs_mem_constructionAddresses (pos : BottomPosition vp) :
    forsPkAdrs pos.forsAdrs ∈ constructionAddresses vp := by
  rw [mem_constructionAddresses_iff]
  exact Or.inr (Or.inr (Or.inl (mem_forsRootAddresses vp pos)))

/-! ## FORS programs -/

/-- One FORS tree root at a reachable bottom position issues `F` only at that tree's leaves and
`H` only at its internal nodes. -/
theorem forsRootM_queriesWithinConstructionTargets (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) (tree : Fin vp.params.k) :
    QueriesWithinConstructionTargets core
      (forsRootM core skSeed pkSeed pos.forsAdrs tree.val :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.merkleRootM core
    (forsLeafWith core (PublicHash.f core pkSeed) skSeed pkSeed pos.forsAdrs)
    (forsNodeHashWith (PublicHash.h core pkSeed) pos.forsAdrs) vp.params.a tree.val
  · intro i hi
    exact publicHash_f_queriesWithinConstructionTargets_of_mem core pkSeed _ _
      (forsLeafAdrs_mem_constructionAddresses pos tree hi)
  · intro h i hh hha hi l r
    exact publicHash_h_queriesWithinConstructionTargets_of_mem core pkSeed _ l r
      (forsTreeAdrs_mem_constructionAddresses pos tree hh hha hi)

/-- FORS public-key generation at a reachable bottom position queries only union-ledger
tweaks. -/
theorem forsPkGenM_queriesWithinConstructionTargets (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : BottomPosition vp) :
    QueriesWithinConstructionTargets core
      (forsPkGenM core skSeed pkSeed pos.forsAdrs : OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
    (QueriesWithinConstructionTargets.ofFnM core _ fun tree =>
      forsRootM_queriesWithinConstructionTargets core skSeed pkSeed pos tree)
  intro roots
  exact publicHash_tl_queriesWithinConstructionTargets_of_mem core pkSeed _ _
    (forsRootAdrs_mem_constructionAddresses pos)

/-- FORS signing at a reachable bottom position queries only union-ledger tweaks: for each tree,
the sibling subtrees of the selected leaf lie inside that tree. -/
theorem forsSignM_queriesWithinConstructionTargets (md : List Byte) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : BottomPosition vp) :
    QueriesWithinConstructionTargets core
      (forsSignM core md skSeed pkSeed pos.forsAdrs :
        OracleComp (publicHashSpec core) (ForsSigCore vp.params core)) := by
  apply QueriesWithinConstructionTargets.ofFnM core
  intro tree
  dsimp only
  apply QueriesWithinConstructionTargets.bind
  · apply QueriesWithinConstructionTargets.intrinsicAuthPathM core
      (forsLeafWith core (PublicHash.f core pkSeed) skSeed pkSeed pos.forsAdrs)
      (forsNodeHashWith (PublicHash.h core pkSeed) pos.forsAdrs)
    · intro i hi
      rw [forsLeafIndex_div] at hi
      exact publicHash_f_queriesWithinConstructionTargets_of_mem core pkSeed _ _
        (forsLeafAdrs_mem_constructionAddresses pos tree hi)
    · intro h i hh hha hi l r
      rw [forsLeafIndex_div] at hi
      exact publicHash_h_queriesWithinConstructionTargets_of_mem core pkSeed _ l r
        (forsTreeAdrs_mem_constructionAddresses pos tree hh hha hi)
  · intro path
    exact queriesWithinConstructionTargets_pure core _

/-- FORS public-key recovery at a reachable bottom position queries only union-ledger tweaks:
for each tree, the revealed leaf and the ancestors climbed lie inside that tree. -/
theorem forsPkFromSigM_queriesWithinConstructionTargets (sig : ForsSigCore vp.params core)
    (md : List Byte) (pkSeed : core.PkSeed) (pos : BottomPosition vp) :
    QueriesWithinConstructionTargets core
      (forsPkFromSigM core sig md pkSeed pos.forsAdrs :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
  · apply QueriesWithinConstructionTargets.ofFnM core
    intro tree
    dsimp only
    apply QueriesWithinConstructionTargets.bind
    · exact publicHash_f_queriesWithinConstructionTargets_of_mem core pkSeed _ _
        (forsLeafAdrs_mem_constructionAddresses pos tree (forsLeafIndex_div _ md _))
    · intro leaf
      apply QueriesWithinConstructionTargets.climbM core
        (forsNodeHashWith (PublicHash.h core pkSeed) pos.forsAdrs)
      intro h hh hha l r
      simp only [Vector.length_toList] at hha
      apply publicHash_h_queriesWithinConstructionTargets_of_mem core pkSeed _ l r
      apply forsTreeAdrs_mem_constructionAddresses pos tree hh hha
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hha, forsLeafIndex_div]
  · intro roots
    exact publicHash_tl_queriesWithinConstructionTargets_of_mem core pkSeed _ _
      (forsRootAdrs_mem_constructionAddresses pos)

/-! ## FORS programs at the digest-derived address -/

/-- FORS public-key generation at the address Algorithm 19 derives from a digest. -/
theorem forsPkGenM_queriesWithinConstructionTargets_digest (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
      (forsPkGenM core skSeed pkSeed parts.forsAdrs : OracleComp (publicHashSpec core) core.Y) := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts]
  exact forsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed _

/-- FORS signing at the address Algorithm 19 derives from a digest. -/
theorem forsSignM_queriesWithinConstructionTargets_digest (md : List Byte) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
      (forsSignM core md skSeed pkSeed parts.forsAdrs :
        OracleComp (publicHashSpec core) (ForsSigCore vp.params core)) := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts]
  exact forsSignM_queriesWithinConstructionTargets core md skSeed pkSeed _

/-- FORS public-key recovery at the address Algorithms 19 and 20 derive from a digest. -/
theorem forsPkFromSigM_queriesWithinConstructionTargets_digest (sig : ForsSigCore vp.params core)
    (md : List Byte) (pkSeed : core.PkSeed) (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
      (forsPkFromSigM core sig md pkSeed parts.forsAdrs :
        OracleComp (publicHashSpec core) core.Y) := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts]
  exact forsPkFromSigM_queriesWithinConstructionTargets core sig md pkSeed _

/-! ## FORS trace contracts -/

/-- FORS public-key generation at a reachable bottom position queries only union-ledger tweaks
and makes at most `k * (2 ^ a + (2 ^ a - 1)) + 1` queries. -/
theorem forsPkGenM_traceContract (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) :
    QueriesWithinConstructionTargets core
        (forsPkGenM core skSeed pkSeed pos.forsAdrs :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (forsPkGenM core skSeed pkSeed pos.forsAdrs : OracleComp (publicHashSpec core) core.Y)
        (vp.params.k * (2 ^ vp.params.a + (2 ^ vp.params.a - 1)) + 1) :=
  ⟨forsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed pos,
    forsPkGenM_isTotalQueryBound core skSeed pkSeed pos.forsAdrs⟩

/-- FORS signing at a reachable bottom position queries only union-ledger tweaks and makes at
most `k * ((2 ^ a - 1) + (2 ^ a - a - 1))` queries. -/
theorem forsSignM_traceContract (md : List Byte) (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) :
    QueriesWithinConstructionTargets core
        (forsSignM core md skSeed pkSeed pos.forsAdrs :
          OracleComp (publicHashSpec core) (ForsSigCore vp.params core)) ∧
      IsTotalQueryBound
        (forsSignM core md skSeed pkSeed pos.forsAdrs :
          OracleComp (publicHashSpec core) (ForsSigCore vp.params core))
        (vp.params.k * ((2 ^ vp.params.a - 1) + (2 ^ vp.params.a - vp.params.a - 1))) :=
  ⟨forsSignM_queriesWithinConstructionTargets core md skSeed pkSeed pos,
    forsSignM_isTotalQueryBound core md skSeed pkSeed pos.forsAdrs⟩

/-- FORS public-key recovery at a reachable bottom position queries only union-ledger tweaks and
makes at most `k * (a + 1) + 1` queries. -/
theorem forsPkFromSigM_traceContract (sig : ForsSigCore vp.params core) (md : List Byte)
    (pkSeed : core.PkSeed) (pos : BottomPosition vp) :
    QueriesWithinConstructionTargets core
        (forsPkFromSigM core sig md pkSeed pos.forsAdrs :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (forsPkFromSigM core sig md pkSeed pos.forsAdrs :
          OracleComp (publicHashSpec core) core.Y)
        (vp.params.k * (vp.params.a + 1) + 1) :=
  ⟨forsPkFromSigM_queriesWithinConstructionTargets core sig md pkSeed pos,
    forsPkFromSigM_isTotalQueryBound core sig md pkSeed pos.forsAdrs⟩

/-! ## XMSS addresses of a reachable tree -/

/-- Every internal node of a reachable XMSS tree is a union-ledger target. -/
theorem xmssNodeAdrs_mem_constructionAddresses (coord : LayerTreeCoord vp) {h i : ℕ}
    (hh : 0 < h) (hhp : h ≤ vp.params.hp) (hi : i < 2 ^ (vp.params.hp - h)) :
    xmssNodeAdrs coord.toAdrs h i ∈ constructionAddresses vp := by
  rw [mem_constructionAddresses_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_xmssNodeAddresses vp coord hh hhp hi)))))

/-- The same for a caller holding a full layer position. -/
theorem xmssNodeAdrs_mem_constructionAddresses_of_position (pos : LayerPosition vp) {h i : ℕ}
    (hh : 0 < h) (hhp : h ≤ vp.params.hp) (hi : i < 2 ^ (vp.params.hp - h)) :
    xmssNodeAdrs pos.toAdrs h i ∈ constructionAddresses vp := by
  rw [mem_constructionAddresses_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (mem_xmssNodeAddresses_of_position vp pos hh hhp hi)))))

/-- A leaf index of a subtree at `(z, t)` inside a height-`hp` tree is below `2 ^ hp`. -/
private theorem lt_pow_of_div_pow_lt {i z t hp : ℕ} (hz : z ≤ hp) (hi : i / 2 ^ z = t)
    (ht : t < 2 ^ (hp - z)) : i < 2 ^ hp := by
  have hlt : i / 2 ^ z < 2 ^ (hp - z) := by
    rw [hi]
    exact ht
  rwa [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hz] at hlt

/-! ## XMSS programs -/

/-- The XMSS leaf program at leaf `i` of a reachable tree is WOTS+ public-key generation at the
reachable instance `(coord.layer, coord.tree, i)`. -/
theorem xmssLeafM_queriesWithinConstructionTargets (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) {i : ℕ} (hi : i < 2 ^ vp.params.hp) :
    QueriesWithinConstructionTargets core
      (xmssLeafM core skSeed pkSeed coord.toAdrs i : OracleComp (publicHashSpec core) core.Y) :=
  wotsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed ⟨coord.layer, coord.tree, ⟨i, hi⟩⟩

/-- The same for a caller holding a full layer position; the leaf `i` need not be the position's
own leaf. -/
theorem xmssLeafM_queriesWithinConstructionTargets_of_position (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) {i : ℕ} (hi : i < 2 ^ vp.params.hp) :
    QueriesWithinConstructionTargets core
      (xmssLeafM core skSeed pkSeed pos.toAdrs i : OracleComp (publicHashSpec core) core.Y) :=
  wotsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed ⟨pos.layer, pos.tree, ⟨i, hi⟩⟩

/-- An XMSS subtree root at `(z, t)` inside a reachable tree, `z ≤ hp` and `t < 2 ^ (hp - z)`,
issues WOTS+ leaf generation only at that tree's leaves and `H` only at its internal nodes. -/
theorem xmssNodeM_queriesWithinConstructionTargets (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) {z t : ℕ} (hz : z ≤ vp.params.hp)
    (ht : t < 2 ^ (vp.params.hp - z)) :
    QueriesWithinConstructionTargets core
      (xmssNodeM core skSeed pkSeed coord.toAdrs z t : OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.merkleRootM core
    (xmssLeafM core skSeed pkSeed coord.toAdrs) (xmssNodeHashM core pkSeed coord.toAdrs) z t
  · intro i hi
    exact xmssLeafM_queriesWithinConstructionTargets core skSeed pkSeed coord
      (lt_pow_of_div_pow_lt hz hi ht)
  · intro h i hh hhz hi l r
    apply publicHash_h_queriesWithinConstructionTargets_of_mem core pkSeed _ l r
    apply xmssNodeAdrs_mem_constructionAddresses coord hh (hhz.trans hz)
    have hlt : i / 2 ^ (z - h) < 2 ^ (vp.params.hp - z) := by
      rw [hi]
      exact ht
    rwa [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show vp.params.hp - z + (z - h) = vp.params.hp - h by omega] at hlt

/-- The root of a reachable XMSS tree queries only union-ledger tweaks. -/
theorem xmssRootM_queriesWithinConstructionTargets (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) :
    QueriesWithinConstructionTargets core
      (xmssRootM core skSeed pkSeed coord.toAdrs : OracleComp (publicHashSpec core) core.Y) :=
  xmssNodeM_queriesWithinConstructionTargets core skSeed pkSeed coord le_rfl (by positivity)

/-- The root of the XMSS tree containing a reachable position queries only union-ledger tweaks. -/
theorem xmssRootM_queriesWithinConstructionTargets_of_position (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (xmssRootM core skSeed pkSeed pos.toAdrs : OracleComp (publicHashSpec core) core.Y) := by
  rw [← LayerTreeCoord.ofPosition_toAdrs pos]
  exact xmssRootM_queriesWithinConstructionTargets core skSeed pkSeed _

/-- XMSS signing at a reachable position queries only union-ledger tweaks: the sibling subtrees
of the authentication path lie inside the position's tree, and the WOTS+ signature is issued at
the position's own instance. -/
theorem xmssSignM_queriesWithinConstructionTargets (msg : core.Y) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (xmssSignM core msg skSeed pkSeed pos.toAdrs pos.leaf.val :
        OracleComp (publicHashSpec core) (XmssSig vp.params core)) := by
  have hleaf : pos.leaf.val / 2 ^ vp.params.hp = 0 := Nat.div_eq_of_lt pos.leaf.isLt
  apply QueriesWithinConstructionTargets.bind
  · apply QueriesWithinConstructionTargets.intrinsicAuthPathM core
      (xmssLeafM core skSeed pkSeed pos.toAdrs) (xmssNodeHashM core pkSeed pos.toAdrs)
      pos.leaf.val vp.params.hp
    · intro i hi
      rw [hleaf] at hi
      exact xmssLeafM_queriesWithinConstructionTargets_of_position core skSeed pkSeed pos
        (lt_pow_of_div_pow_lt le_rfl hi (by positivity))
    · intro h i hh hhp hi l r
      rw [hleaf] at hi
      apply publicHash_h_queriesWithinConstructionTargets_of_mem core pkSeed _ l r
      apply xmssNodeAdrs_mem_constructionAddresses_of_position pos hh hhp
      have hlt : i / 2 ^ (vp.params.hp - h) < 1 := by
        rw [hi]
        exact Nat.one_pos
      rwa [Nat.div_lt_iff_lt_mul (by positivity), Nat.one_mul] at hlt
  · intro path
    apply QueriesWithinConstructionTargets.bind
      (wotsSignM_queriesWithinConstructionTargets core msg skSeed pkSeed pos)
    intro sig
    exact queriesWithinConstructionTargets_pure core _

/-- XMSS root recovery at a reachable position queries only union-ledger tweaks: the WOTS+ key is
recovered at the position's own instance, and the climbed ancestors lie inside its tree. -/
theorem xmssPkFromSigM_queriesWithinConstructionTargets (sig : XmssSig vp.params core)
    (msg : core.Y) (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (xmssPkFromSigM core pos.leaf.val sig msg pkSeed pos.toAdrs :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
    (wotsPkFromSigM_queriesWithinConstructionTargets core sig.wots msg pkSeed pos)
  intro leaf
  apply QueriesWithinConstructionTargets.climbM core (xmssNodeHashM core pkSeed pos.toAdrs)
  intro h hh hhp l r
  simp only [Vector.length_toList] at hhp
  apply publicHash_h_queriesWithinConstructionTargets_of_mem core pkSeed _ l r
  apply xmssNodeAdrs_mem_constructionAddresses_of_position pos hh hhp
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hhp]
  exact pos.leaf.isLt

/-! ## XMSS trace contracts -/

/-- An XMSS subtree root inside a reachable tree queries only union-ledger tweaks and makes at
most `xmssNodeQueryBound p z` queries. -/
theorem xmssNodeM_traceContract (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) {z t : ℕ} (hz : z ≤ vp.params.hp)
    (ht : t < 2 ^ (vp.params.hp - z)) :
    QueriesWithinConstructionTargets core
        (xmssNodeM core skSeed pkSeed coord.toAdrs z t :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (xmssNodeM core skSeed pkSeed coord.toAdrs z t : OracleComp (publicHashSpec core) core.Y)
        (xmssNodeQueryBound vp.params z) :=
  ⟨xmssNodeM_queriesWithinConstructionTargets core skSeed pkSeed coord hz ht,
    xmssNodeM_isTotalQueryBound core skSeed pkSeed coord.toAdrs z t⟩

/-- The root of a reachable XMSS tree queries only union-ledger tweaks and makes at most
`xmssNodeQueryBound p hp` queries. -/
theorem xmssRootM_traceContract (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) :
    QueriesWithinConstructionTargets core
        (xmssRootM core skSeed pkSeed coord.toAdrs : OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (xmssRootM core skSeed pkSeed coord.toAdrs : OracleComp (publicHashSpec core) core.Y)
        (xmssNodeQueryBound vp.params vp.params.hp) :=
  ⟨xmssRootM_queriesWithinConstructionTargets core skSeed pkSeed coord,
    xmssRootM_isTotalQueryBound core skSeed pkSeed coord.toAdrs⟩

/-- XMSS signing at a reachable position queries only union-ledger tweaks and makes at most
`(∑ i, chainStepsCore core msg i) + xmssAuthPathQueryBound p hp` queries. -/
theorem xmssSignM_traceContract (msg : core.Y) (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
        (xmssSignM core msg skSeed pkSeed pos.toAdrs pos.leaf.val :
          OracleComp (publicHashSpec core) (XmssSig vp.params core)) ∧
      IsTotalQueryBound
        (xmssSignM core msg skSeed pkSeed pos.toAdrs pos.leaf.val :
          OracleComp (publicHashSpec core) (XmssSig vp.params core))
        ((∑ i : Fin vp.params.len, chainStepsCore core msg i.val) +
          xmssAuthPathQueryBound vp.params vp.params.hp) :=
  ⟨xmssSignM_queriesWithinConstructionTargets core msg skSeed pkSeed pos,
    xmssSignM_isTotalQueryBound core msg skSeed pkSeed pos.toAdrs pos.leaf.val⟩

/-- XMSS root recovery at a reachable position queries only union-ledger tweaks and makes at most
`(∑ i, (w - 1 - chainStepsCore core msg i)) + 1 + hp` queries. -/
theorem xmssPkFromSigM_traceContract (sig : XmssSig vp.params core) (msg : core.Y)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
        (xmssPkFromSigM core pos.leaf.val sig msg pkSeed pos.toAdrs :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (xmssPkFromSigM core pos.leaf.val sig msg pkSeed pos.toAdrs :
          OracleComp (publicHashSpec core) core.Y)
        ((∑ i : Fin vp.params.len, (vp.params.w - 1 - chainStepsCore core msg i.val)) + 1 +
          vp.params.hp) :=
  ⟨xmssPkFromSigM_queriesWithinConstructionTargets core sig msg pkSeed pos,
    xmssPkFromSigM_isTotalQueryBound core pos.leaf.val sig msg pkSeed pos.toAdrs⟩

end SLHDSA.Security
