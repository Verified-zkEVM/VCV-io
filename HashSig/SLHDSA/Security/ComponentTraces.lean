/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.TraceTargets
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# Trace provenance of the FORS, XMSS, hypertree, and internal scheme programs

This module extends the pathwise predicate `QueriesWithinConstructionTargets` of
`HashSig.SLHDSA.Security.TraceTargets` from the WOTS+ programs to the FORS, XMSS, hypertree, and
internal scheme programs.  Each theorem says that every `thash` query a program can issue, under
any oracle answers, uses an encoded address from the union ledger `constructionAddresses`, while
`H_msg`, which carries no address, is accepted unconditionally; the `*_traceContract` theorems pair
that with the program's total query bound.

The FORS programs are certified at the FORS address of a reachable `BottomPosition`, and through
`BottomPosition.ofDigestParts` at the digest-derived address `DigestParts.forsAdrs` that
`GeneralScheme.signInternalM` and `verifyInternalM` pass to them.  Their Merkle traversals are
handled by the generic address-tracking lemmas `PerfectMerkleTree.merkleRootM_pred_of_subtree`,
`intrinsicAuthPathM_pred_of_tree`, and `climbM_pred_of_ancestors`, instantiated at the
construction predicate; the leaf and node addresses those lemmas surface are placed in the FORS
ledgers by `mem_forsLeafAddresses`, `mem_forsTreeAddresses`, and `mem_forsRootAddresses`.

The XMSS programs are certified inside a reachable tree, given either as a `LayerTreeCoord` or as
the tree containing a `LayerPosition`.  A subtree root `xmssNodeM` at `(z, t)` with `z ≤ hp` and
`t < 2 ^ (hp - z)`, and the tree root `xmssRootM`, compute each WOTS+ leaf `i < 2 ^ hp` through
`wotsPkGenM_queriesWithinConstructionTargets` at the reachable instance `(layer, tree, i)`, and
issue `H` only at internal nodes `(h, i)` with `0 < h ≤ hp` and `i < 2 ^ (hp - h)`, which
`mem_xmssNodeAddresses` places in the ledger.  `xmssSignM` and `xmssPkFromSigM` are certified at a
position's own leaf, where the WOTS+ signing and recovery lemmas of `TraceTargets` apply to the
leaf and the Merkle lemmas above to the sibling subtrees and the climbed ancestors.  The `WOTS_PRF`
addresses are consumed by `core.PRF`, which is not a query of `publicHashSpec`, so no lemma here
mentions them.

The hypertree loops `GeneralHypertree.signFromPositionM` and `recoverFromPositionM` are certified
from any reachable `LayerPosition` by induction on the remaining layers, each layer applying the
XMSS lemmas at the current position before `LayerPosition.next`; `GeneralHypertree.signM`,
`pkFromSigM`, and `verifyM` are their instances at `LayerPosition.initial`, and
`GeneralHypertree.rootM` is `xmssRootM` at the top tree `LayerTreeCoord.top`, whose base address
`LayerTreeCoord.top_toAdrs_layerAdrs` identifies with the one Algorithm 18 uses.  The internal
scheme programs `GeneralScheme.keygenInternalM`, `signInternalM`, and `verifyInternalM` sequence
`H_msg` with the FORS programs at the digest-derived address and the hypertree programs above.  The
contracts at these two levels pair the predicate with the bounds of
`HashSig.SLHDSA.HypertreeGeneral.QueryBound` and `GeneralSchemeQueryBound`, which are upper bounds
rather than exact counts.

Theorem names follow the program names, with one convention: the `GeneralHypertree` programs carry
the `hypertree` prefix (`hypertreeSignM_…` certifies `GeneralHypertree.signM`), which keeps them
apart from the XMSS programs and from any future `signM`, while the `GeneralScheme` programs keep
their FIPS names unqualified (`keygenInternalM_…` certifies `GeneralScheme.keygenInternalM`), the
depth-one programs being the `slh*InternalM` family.

## References

- NIST FIPS 205, §6 (Algorithms 9--11, the XMSS programs), §7 (Algorithms 12--13, the hypertree
  programs), §8 (Algorithms 14--17, the FORS programs), and §9 (Algorithms 18--20, the internal
  scheme programs)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified".  Its EasyCrypt development carries an analogous address-validity
  discipline, the predicates `valid_xadrs`, split by `valid_xadrs_xadrschpkcotrh` into chain,
  public-key-compression, and tree-hash addresses (`proofs/FL_SL_XMSS_MT_ES.ec`), and
  `valid_fadrs` (`proofs/FORS_ES.ec`), under which its address lemmas are stated.
  `mem_constructionAddresses_iff` is the analogue of that split here, six-way because the FORS
  and WOTS+ roles are separate ledgers; no correspondence between the two developments is claimed.
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
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp (publicHashSpec core) Y) (idx : ℕ)
    (node : Y) (auth : List Y)
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

/-- One FORS tree root at a reachable bottom position queries only union-ledger tweaks: its `F`
queries are at that tree's leaves and its `H` queries at its internal nodes. -/
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
  rw [← LayerTreeCoord.ofPosition_toAdrs pos]
  exact xmssNodeAdrs_mem_constructionAddresses _ hh hhp hi

/-- A leaf index of a subtree at `(z, t)` inside a height-`hp` tree is below `2 ^ hp`. -/
private theorem lt_pow_of_div_pow_lt {i z t hp : ℕ} (hz : z ≤ hp) (hi : i / 2 ^ z = t)
    (ht : t < 2 ^ (hp - z)) : i < 2 ^ hp := by
  have hlt : i / 2 ^ z < 2 ^ (hp - z) := by
    rw [hi]
    exact ht
  rwa [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hz] at hlt

/-! ## XMSS programs -/

/-- The XMSS leaf program at leaf `i` of a reachable tree queries only union-ledger tweaks: it is
WOTS+ public-key generation at the reachable instance `(coord.layer, coord.tree, i)`. -/
theorem xmssLeafM_queriesWithinConstructionTargets (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) {i : ℕ} (hi : i < 2 ^ vp.params.hp) :
    QueriesWithinConstructionTargets core
      (xmssLeafM core skSeed pkSeed coord.toAdrs i : OracleComp (publicHashSpec core) core.Y) :=
  wotsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed
    ⟨coord.layer, coord.tree, ⟨i, hi⟩⟩

/-- The same for a caller holding a full layer position; the leaf `i` need not be the position's
own leaf. -/
theorem xmssLeafM_queriesWithinConstructionTargets_of_position (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) {i : ℕ} (hi : i < 2 ^ vp.params.hp) :
    QueriesWithinConstructionTargets core
      (xmssLeafM core skSeed pkSeed pos.toAdrs i : OracleComp (publicHashSpec core) core.Y) :=
  wotsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed
    ⟨pos.layer, pos.tree, ⟨i, hi⟩⟩

/-- An XMSS subtree root at `(z, t)` inside a reachable tree, `z ≤ hp` and `t < 2 ^ (hp - z)`,
queries only union-ledger tweaks: its WOTS+ leaf generation is at that tree's leaves and its `H`
queries at its internal nodes. -/
theorem xmssNodeM_queriesWithinConstructionTargets (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (coord : LayerTreeCoord vp) {z t : ℕ} (hz : z ≤ vp.params.hp)
    (ht : t < 2 ^ (vp.params.hp - z)) :
    QueriesWithinConstructionTargets core
      (xmssNodeM core skSeed pkSeed coord.toAdrs z t :
        OracleComp (publicHashSpec core) core.Y) := by
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

/-! ## The top-layer tree -/

/-- The top tree's base address is the one `GeneralHypertree.rootM` computes its root at. -/
theorem LayerTreeCoord.top_toAdrs_layerAdrs (vp : ValidatedParams) :
    (LayerTreeCoord.top vp).toAdrs = GeneralHypertree.layerAdrs (vp.params.d - 1) 0 :=
  LayerTreeCoord.top_toAdrs vp

/-! ## Hypertree programs -/

/-- The typed layer loop of Algorithm 12 from any reachable position queries only union-ledger
tweaks: each layer signs at the current position, recovers the root at the same position unless it
is the unrecovered final component, and continues at the next position. -/
theorem signFromPositionM_queriesWithinConstructionTargets (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    QueriesWithinConstructionTargets core
      (GeneralHypertree.signFromPositionM vp core skSeed pkSeed recoverFinal pos layers
          hremaining msg :
        OracleComp (publicHashSpec core) (Vector (XmssSig vp.params core) layers)) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => simp [GeneralHypertree.signFromPositionM, GeneralHypertree.signFromPositionWith]
  | one =>
      cases recoverFinal with
      | false =>
          have h := QueriesWithinConstructionTargets.bind
            (xmssSignM_queriesWithinConstructionTargets core msg skSeed pkSeed pos)
            (fun sig => queriesWithinConstructionTargets_pure core
              (#v[sig] : Vector (XmssSig vp.params core) 1))
          simpa [GeneralHypertree.signFromPositionM, GeneralHypertree.signFromPositionWith,
            xmssSignM] using h
      | true =>
          have h := QueriesWithinConstructionTargets.bind
            (xmssSignM_queriesWithinConstructionTargets core msg skSeed pkSeed pos)
            (fun sig => QueriesWithinConstructionTargets.bind
              (xmssPkFromSigM_queriesWithinConstructionTargets core sig msg pkSeed pos)
              (fun _ => queriesWithinConstructionTargets_pure core
                (#v[sig] : Vector (XmssSig vp.params core) 1)))
          simpa [GeneralHypertree.signFromPositionM, GeneralHypertree.signFromPositionWith,
            xmssSignM, xmssPkFromSigM] using h
  | more layers _ ih =>
      let next := pos.next (by omega)
      have h := QueriesWithinConstructionTargets.bind
        (xmssSignM_queriesWithinConstructionTargets core msg skSeed pkSeed pos)
        (fun sig => QueriesWithinConstructionTargets.bind
          (xmssPkFromSigM_queriesWithinConstructionTargets core sig msg pkSeed pos)
          (fun root => QueriesWithinConstructionTargets.bind
            (ih (recoverFinal := false) (pos := next) (hremaining := by simp [next]; omega)
              (msg := root))
            (fun rest => queriesWithinConstructionTargets_pure core (rest.insertIdx 0 sig))))
      simpa [GeneralHypertree.signFromPositionM, GeneralHypertree.signFromPositionWith,
        xmssSignM, xmssPkFromSigM, next, bind_assoc] using h

/-- The typed layer loop of Algorithm 13 from any reachable position queries only union-ledger
tweaks: each layer recovers one XMSS root at the current position and continues at the next. -/
theorem recoverFromPositionM_queriesWithinConstructionTargets (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) (layers : ℕ) (hremaining : pos.layer.val + layers = vp.params.d)
    (msg : core.Y) (sigs : Vector (XmssSig vp.params core) layers) :
    QueriesWithinConstructionTargets core
      (GeneralHypertree.recoverFromPositionM vp core pkSeed pos layers hremaining msg sigs :
        OracleComp (publicHashSpec core) core.Y) := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero =>
      simp [GeneralHypertree.recoverFromPositionM, GeneralHypertree.recoverFromPositionWith]
  | one =>
      simpa [GeneralHypertree.recoverFromPositionM, GeneralHypertree.recoverFromPositionWith,
        xmssPkFromSigM] using
        xmssPkFromSigM_queriesWithinConstructionTargets core sigs.head msg pkSeed pos
  | more layers _ ih =>
      let next := pos.next (by omega)
      have h := QueriesWithinConstructionTargets.bind
        (xmssPkFromSigM_queriesWithinConstructionTargets core sigs.head msg pkSeed pos)
        (fun root => ih (pos := next) (hremaining := by simp [next]; omega) (msg := root)
          (sigs := sigs.tail))
      simpa [GeneralHypertree.recoverFromPositionM, GeneralHypertree.recoverFromPositionWith,
        xmssPkFromSigM, next] using h

/-- Hypertree signing (Algorithm 12) at the digest-derived layer-zero position queries only
union-ledger tweaks. -/
theorem hypertreeSignM_queriesWithinConstructionTargets (msg : core.Y) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
      (GeneralHypertree.signM vp core msg skSeed pkSeed parts :
        OracleComp (publicHashSpec core) (GeneralHypertree.Signature vp core)) :=
  signFromPositionM_queriesWithinConstructionTargets core skSeed pkSeed _ _ _ _ msg

/-- Hypertree root recovery (Algorithm 13) at the digest-derived layer-zero position queries only
union-ledger tweaks. -/
theorem hypertreePkFromSigM_queriesWithinConstructionTargets (msg : core.Y)
    (sig : GeneralHypertree.Signature vp core) (pkSeed : core.PkSeed)
    (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
      (GeneralHypertree.pkFromSigM vp core msg sig pkSeed parts :
        OracleComp (publicHashSpec core) core.Y) :=
  recoverFromPositionM_queriesWithinConstructionTargets core pkSeed _ _ _ msg sig

/-- Hypertree verification queries only union-ledger tweaks: it is its root recovery followed by a
comparison. -/
theorem hypertreeVerifyM_queriesWithinConstructionTargets [DecidableEq core.Y] (msg : core.Y)
    (sig : GeneralHypertree.Signature vp core) (pkSeed : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) :
    QueriesWithinConstructionTargets core
      (GeneralHypertree.verifyM vp core msg sig pkSeed parts pkRoot :
        OracleComp (publicHashSpec core) Bool) :=
  QueriesWithinConstructionTargets.bind
    (hypertreePkFromSigM_queriesWithinConstructionTargets core msg sig pkSeed parts)
    (fun recovered => queriesWithinConstructionTargets_pure core (decide (recovered = pkRoot)))

/-- The top-layer root computation of Algorithm 18 queries only union-ledger tweaks: it is
`xmssRootM` at the reachable tree `LayerTreeCoord.top`. -/
theorem hypertreeRootM_queriesWithinConstructionTargets (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) :
    QueriesWithinConstructionTargets core
      (GeneralHypertree.rootM vp core skSeed pkSeed : OracleComp (publicHashSpec core) core.Y) := by
  have h := xmssRootM_queriesWithinConstructionTargets core skSeed pkSeed (LayerTreeCoord.top vp)
  rw [LayerTreeCoord.top_toAdrs_layerAdrs] at h
  exact h

/-! ## Internal scheme programs -/

/-- Algorithm 18 queries only union-ledger tweaks: it computes the top-layer root. -/
theorem keygenInternalM_queriesWithinConstructionTargets (skSeed : core.SkSeed)
    (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    QueriesWithinConstructionTargets core
      (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) :=
  QueriesWithinConstructionTargets.bind
    (hypertreeRootM_queriesWithinConstructionTargets core skSeed pkSeed)
    (fun pkRoot => queriesWithinConstructionTargets_pure core
      (PublicKeyCore.mk pkSeed pkRoot, SecretKeyCore.mk skSeed skPrf pkSeed pkRoot))

/-- Algorithm 19 queries only union-ledger tweaks: `H_msg` carries no address, and the FORS and
hypertree programs run at the addresses derived from its digest. -/
theorem signInternalM_queriesWithinConstructionTargets (msg : List Byte)
    (sk : SecretKeyCore core) (addrnd : core.Y) :
    QueriesWithinConstructionTargets core
      (GeneralScheme.signInternalM vp core msg sk addrnd :
        OracleComp (publicHashSpec core) (GeneralScheme.SignatureCore vp core)) := by
  apply QueriesWithinConstructionTargets.bind
    (publicHash_hmsg_queriesWithinConstructionTargets core _ sk.pkSeed sk.pkRoot msg)
  intro digest
  apply QueriesWithinConstructionTargets.bind
    (forsSignM_queriesWithinConstructionTargets_digest core _ sk.skSeed sk.pkSeed
      (splitDigest vp.params digest))
  intro forsSig
  apply QueriesWithinConstructionTargets.bind
    (forsPkFromSigM_queriesWithinConstructionTargets_digest core forsSig _ sk.pkSeed
      (splitDigest vp.params digest))
  intro forsPk
  apply QueriesWithinConstructionTargets.bind
    (hypertreeSignM_queriesWithinConstructionTargets core forsPk sk.skSeed sk.pkSeed
      (splitDigest vp.params digest))
  intro htSig
  exact queriesWithinConstructionTargets_pure core _

/-- Algorithm 20 queries only union-ledger tweaks: `H_msg`, then FORS and hypertree recovery at
the addresses derived from its digest. -/
theorem verifyInternalM_queriesWithinConstructionTargets [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    QueriesWithinConstructionTargets core
      (GeneralScheme.verifyInternalM vp core msg sig pk :
        OracleComp (publicHashSpec core) Bool) := by
  apply QueriesWithinConstructionTargets.bind
    (publicHash_hmsg_queriesWithinConstructionTargets core sig.randomness pk.pkSeed pk.pkRoot msg)
  intro digest
  apply QueriesWithinConstructionTargets.bind
    (forsPkFromSigM_queriesWithinConstructionTargets_digest core sig.fors _ pk.pkSeed
      (splitDigest vp.params digest))
  intro forsPk
  exact hypertreeVerifyM_queriesWithinConstructionTargets core forsPk sig.hypertree pk.pkSeed
    (splitDigest vp.params digest) pk.pkRoot

/-! ## Hypertree and scheme trace contracts -/

/-- Hypertree signing at the digest-derived position queries only union-ledger tweaks and makes at
most `GeneralHypertree.signQueryBound p` queries. -/
theorem hypertreeSignM_traceContract (msg : core.Y) (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
        (GeneralHypertree.signM vp core msg skSeed pkSeed parts :
          OracleComp (publicHashSpec core) (GeneralHypertree.Signature vp core)) ∧
      IsTotalQueryBound
        (GeneralHypertree.signM vp core msg skSeed pkSeed parts :
          OracleComp (publicHashSpec core) (GeneralHypertree.Signature vp core))
        (GeneralHypertree.signQueryBound vp.params) :=
  ⟨hypertreeSignM_queriesWithinConstructionTargets core msg skSeed pkSeed parts,
    GeneralHypertree.signM_isTotalQueryBound vp core msg skSeed pkSeed parts⟩

/-- Hypertree root recovery at the digest-derived position queries only union-ledger tweaks and
makes at most `GeneralHypertree.recoverQueryBound p` queries. -/
theorem hypertreePkFromSigM_traceContract (msg : core.Y) (sig : GeneralHypertree.Signature vp core)
    (pkSeed : core.PkSeed) (parts : DigestParts vp.params) :
    QueriesWithinConstructionTargets core
        (GeneralHypertree.pkFromSigM vp core msg sig pkSeed parts :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (GeneralHypertree.pkFromSigM vp core msg sig pkSeed parts :
          OracleComp (publicHashSpec core) core.Y)
        (GeneralHypertree.recoverQueryBound vp.params) :=
  ⟨hypertreePkFromSigM_queriesWithinConstructionTargets core msg sig pkSeed parts,
    GeneralHypertree.pkFromSigM_isTotalQueryBound vp core msg sig pkSeed parts⟩

/-- Internal key generation queries only union-ledger tweaks and makes at most
`GeneralScheme.keygenInternalQueryBound p` queries. -/
theorem keygenInternalM_traceContract (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) :
    QueriesWithinConstructionTargets core
        (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) ∧
      IsTotalQueryBound
        (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core))
        (GeneralScheme.keygenInternalQueryBound vp.params) :=
  ⟨keygenInternalM_queriesWithinConstructionTargets core skSeed skPrf pkSeed,
    GeneralScheme.keygenInternalM_isTotalQueryBound vp core skSeed skPrf pkSeed⟩

/-- Internal signing queries only union-ledger tweaks and makes at most
`GeneralScheme.signInternalQueryBound p` queries. -/
theorem signInternalM_traceContract (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    QueriesWithinConstructionTargets core
        (GeneralScheme.signInternalM vp core msg sk addrnd :
          OracleComp (publicHashSpec core) (GeneralScheme.SignatureCore vp core)) ∧
      IsTotalQueryBound
        (GeneralScheme.signInternalM vp core msg sk addrnd :
          OracleComp (publicHashSpec core) (GeneralScheme.SignatureCore vp core))
        (GeneralScheme.signInternalQueryBound vp.params) :=
  ⟨signInternalM_queriesWithinConstructionTargets core msg sk addrnd,
    GeneralScheme.signInternalM_isTotalQueryBound vp core msg sk addrnd⟩

/-- Internal verification queries only union-ledger tweaks and makes at most
`GeneralScheme.verifyInternalQueryBound p` queries. -/
theorem verifyInternalM_traceContract [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    QueriesWithinConstructionTargets core
        (GeneralScheme.verifyInternalM vp core msg sig pk :
          OracleComp (publicHashSpec core) Bool) ∧
      IsTotalQueryBound
        (GeneralScheme.verifyInternalM vp core msg sig pk :
          OracleComp (publicHashSpec core) Bool)
        (GeneralScheme.verifyInternalQueryBound vp.params) :=
  ⟨verifyInternalM_queriesWithinConstructionTargets core msg sig pk,
    GeneralScheme.verifyInternalM_isTotalQueryBound vp core msg sig pk⟩

end SLHDSA.Security
