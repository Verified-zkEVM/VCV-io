/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Collision
import VCVio.CryptoFoundations.MerkleTree.Inductive.Lemmas
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Inductive Merkle Tree Extractability

-/

open scoped NNReal

section ToVCV

/--
Convenience corrolary to `probEvent_mono` for when the implication holds everywhere,
not just on the support of the distribution.
-/
lemma probEvent_mono''.{u, v} {m : Type u → Type v} [Monad m] {α : Type u} [HasEvalSPMF m]
    {mx : m α} {p q : α → Prop}
    (h : ∀ x, p x → q x) : Pr[p | mx] ≤ Pr[q | mx] := by
  apply probEvent_mono
  tauto


/--
For any computation `oa` and predicate `p`, the probability of `p` holding on the output
equals the probability of `p ∘ Prod.fst` holding on the output of `oa.withQueryLog`.
This follows from the fact that `withQueryLog` only appends a log without changing the
output value.
-/
lemma probEvent_withQueryLog {ι : Type} {oSpec : OracleSpec ι}
    [oSpec.Fintype] [oSpec.Inhabited] {α : Type}
    (oa : OracleComp oSpec α) (p : α → Prop) :
    Pr[p | oa] = Pr[p ∘ Prod.fst | oa.withQueryLog] :=
  (loggingOracle.probEvent_fst_run_simulateQ oa p).symm

end ToVCV



namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

def populate_down_tree {α : Type} (s : Skeleton)
    (children : α → (α × α))
    (root : α) :
    FullData α s :=
  match s with
  | .leaf => FullData.leaf root
  | .internal s_left s_right =>
    let ⟨left_root, right_root⟩ := children root
    FullData.internal
      root
      (populate_down_tree s_left children left_root)
      (populate_down_tree s_right children right_root)

/--
The extraction algorithm for Merkle trees.

This algorithm takes a merkle tree cache, a root, and a skeleton, and
returns (optionally?) a FullData of Option α.

* It starts with the root and constructs a tree down to the leaves.
* If a node is not in the cache, its children are None
* If a node is in the cache twice (a collision), its children are None
* If a node is None, its children are None
* Otherwise, a nodes children are the children in the cache.


TODO, if there is a collision, but it isn't used or is only used in a subtree,
should the rest of the tree work? Or should it all fail?

(I think, after my conversation with Mattias and Felix, this doesn't matter.
If there is a collision, we are already in the bad case.
What is just needed is that the extractor gives some default value in the ablated case.
)
-/
def extractor {α : Type} [DecidableEq α] [SampleableType α]
    [OracleSpec.Fintype (spec α)]
    (s : Skeleton)
    (cache : (spec α).QueryLog)
    (root : α) :
    FullData (Option α) s :=
  let queries := cache;
  let children (node : Option α) : (Option α × Option α) :=
    match node with
    | none => (none, none)
    | some a =>
      -- Find the first query resulting in this value
    match queries.find? (fun ⟨_, r⟩ => r == a) with
      | none => (none, none)
      | some q =>
        let child_hashes := q.1;
        (some child_hashes.1, some child_hashes.2)
  populate_down_tree s children (some root)

/--
The game for extractability.
-/
def extractability_game
    [DecidableEq α] [SampleableType α] [Fintype α] [OracleSpec.Fintype (spec α)]
    {s : Skeleton}
    {AuxState : Type}
    (committingAdv : OracleComp (spec α)
        (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)) :
    OracleComp (spec α)
      (α × AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  do
    let ((root, aux), queryLog) ← committingAdv.withQueryLog
    let extractedTree := extractor s queryLog root
    let ⟨idx, leaf, proof⟩ ← openingAdv aux
    let extractedProof := generateProof extractedTree idx
    let verifiedOpt ← (verifyProof idx leaf root proof).run
    let verified := verifiedOpt.isSome
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩)



/--
The event that the adversary wins the extractability game:
verification passes but the extracted leaf or proof does not match.
-/
def adversary_wins_extractability_game_event {α : Type} [BEq α] {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop
  | (_, _, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) =>
    verified ∧
    (not (leaf == extractedTree.get idx.toNodeIndex)
    ∨ not (proof.toList.map Option.some == extractedProof.toList))

/--
The event that the adversary wins the extractability game with logging:
verification passes but the extracted leaf or proof does not match.
The query log is ignored for the win condition.
-/
def adversary_wins_extractability_game_with_logging_event
    {α : Type} [BEq α] {s : Skeleton} {AuxState : Type} :
    (α × AuxState ×
       ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
        FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
    (spec α).QueryLog → Prop :=
  adversary_wins_extractability_game_event ∘ Prod.fst

/--
`adversary_wins_extractability_game_with_logging_event` is
`adversary_wins_extractability_game_event` composed with `Prod.fst`.
-/
lemma adversary_wins_extractability_game_with_logging_event_eq
    {α : Type} [BEq α] {s : Skeleton} {AuxState : Type} :
    @adversary_wins_extractability_game_with_logging_event α _ s AuxState =
    adversary_wins_extractability_game_event ∘ Prod.fst := rfl

/-! ### Query bound for `extractability_game` -/

/--
If the combined adversary pair `(committingAdv, openingAdv)` has total query bound `qb`,
then the full extractability game has total query bound `qb + s.depth`.

The extra `s.depth` accounts for the `verifyProof` step, which traverses the path from the
queried leaf to the root, making at most `s.depth` oracle queries.
-/
theorem extractability_game_IsTotalQueryBound
    [DecidableEq α] [SampleableType α] [Fintype α] [OracleSpec.Fintype (spec α)]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (h : IsTotalQueryBound
        (do let (_root, aux) ← committingAdv;
            let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux; pure ())
        qb) :
    IsTotalQueryBound
        ((extractability_game committingAdv openingAdv))
        (qb + s.depth) := by
  -- Re-associate `extractability_game` as `prefix >>= suffix`, where the prefix
  -- bundles `committingAdv.withQueryLog ; openingAdv` and the suffix runs
  -- `verifyProof.run` and assembles the final return tuple.
  have heq : extractability_game committingAdv openingAdv =
      (committingAdv.withQueryLog >>= fun p =>
        openingAdv p.1.2 >>= fun q => pure (p, q)) >>=
      fun pq =>
        (verifyProof pq.2.1 pq.2.2.1 pq.1.1.1 pq.2.2.2).run >>= fun verifiedOpt =>
          pure (pq.1.1.1, pq.1.1.2,
                ⟨pq.2.1, pq.2.2.1, pq.2.2.2,
                 extractor s pq.1.2 pq.1.1.1,
                 generateProof (extractor s pq.1.2 pq.1.1.1) pq.2.1,
                 verifiedOpt.isSome⟩) := by
    unfold extractability_game
    simp only [bind_assoc, pure_bind]
  rw [heq]
  clear heq
  refine isTotalQueryBound_bind (n₁ := qb) (n₂ := s.depth) ?_ ?_
  · -- Prefix bound: same queries as `h`'s computation, hence bounded by `qb`.
    have hmap : (fun _ => ()) <$>
        (committingAdv.withQueryLog >>= fun p => openingAdv p.1.2 >>= fun q => pure (p, q)) =
        (do let (_root, aux) ← committingAdv
            let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
            pure ()) := by
      simp only [map_bind, map_pure]
      exact loggingOracle.run_simulateQ_bind_fst committingAdv
        (fun r => openingAdv r.2 >>= fun _ => pure ())
    exact (isQueryBound_iff_of_map_eq hmap (fun _ b => 0 < b) (fun _ b => b - 1)).mpr h
  · -- Suffix bound: verifyProof.run + pure ≤ s.depth.
    rintro ⟨p, q⟩
    refine isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0) ?_ ?_
    · exact verifyProof_run_isTotalQueryBound_skeleton_depth q.1 q.2.1 p.1.1 q.2.2
    · intro _; trivial


theorem evalDist_extractability_game_eq
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited] {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)) :
  evalDist (extractability_game committingAdv openingAdv) =
    evalDist (Prod.fst <$> (extractability_game committingAdv openingAdv).withQueryLog) := by
  congr 1
  exact (loggingOracle.fst_map_run_simulateQ _).symm

/-! ### No-collision lucky-guess bound -/

/-- Every skeleton has at least one leaf. -/
private lemma leafCount_pos_aux : ∀ s : Skeleton, 0 < s.leafCount
  | Skeleton.leaf => Nat.zero_lt_one
  | Skeleton.internal left _ => Nat.add_pos_left (leafCount_pos_aux left) _

/--
Sub-event of `bad event` where the extractor's path from `root` to the opened leaf
index is *intact* in committingAdv's log. Equivalently: the extracted leaf at `idx`
is `some _` rather than `none`.

This is the "Case A" of the no-collision case decomposition: when the chain from
root to leaf is intact in committingLog, no-collision forces the verifier's chain
to coincide with the extractor's, so the win condition fails.
-/
private def noColl_caseA_event {α : Type} [BEq α] [DecidableEq α]
    {s : Skeleton} {AuxState : Type} :
    (α × AuxState ×
       ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
        FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog → Prop
  | (vals, log) =>
    let ⟨_, _, idx, _, _, extractedTree, _, _⟩ := vals
    ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals ∧
      extractedTree.get idx.toNodeIndex ≠ none

/--
Sub-event of `bad event` where the extractor's path from `root` to the opened leaf
index is *broken* in committingAdv's log. Equivalently: the extracted leaf at `idx`
is `none`.

This is the "Case B" of the no-collision case decomposition: when the chain is
broken, the leaf-mismatch disjunct of `adversary_wins_extractability_game_event`
fires automatically, reducing the bad event to `verified = true`. Verification
then requires the random oracle to coincidentally produce a chain reaching `root`,
which is the `1/|α|` lucky-guess event.
-/
private def noColl_caseB_event {α : Type} [BEq α] [DecidableEq α]
    {s : Skeleton} {AuxState : Type} :
    (α × AuxState ×
       ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
        FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog → Prop
  | (vals, log) =>
    let ⟨_, _, idx, _, _, extractedTree, _, _⟩ := vals
    ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals ∧
      extractedTree.get idx.toNodeIndex = none

/--
The bad event `¬ collisionIn log ∧ adversary_wins_extractability_game_event vals`
decomposes as the disjoint union of `noColl_caseA_event` and `noColl_caseB_event`,
according to whether the extracted leaf at the opened index is `some _` or `none`.
-/
private lemma noColl_bad_iff_caseA_or_caseB
    {α : Type} [BEq α] [DecidableEq α] {s : Skeleton} {AuxState : Type}
    (x : (α × AuxState ×
            ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
             FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
         (spec α).QueryLog) :
    (¬ collisionIn x.2 ∧ adversary_wins_extractability_game_event x.1) ↔
      noColl_caseA_event x ∨ noColl_caseB_event x := by
  rcases x with ⟨⟨_, _, ⟨idx, _, _, extractedTree, _, _⟩⟩, log⟩
  simp only [noColl_caseA_event, noColl_caseB_event]
  by_cases h : extractedTree.get idx.toNodeIndex = none
  · simp [h]
  · simp [h]

/--
Auxiliary arithmetic fact: every skeleton has positive leaf count and non-negative
depth, so `1 ≤ 2 * (s.depth + 1) * s.leafCount`. Used to bridge a tight `1/|α|`
probability bound to the looser `2 * (s.depth + 1) * s.leafCount / |α|` form
demanded by `extractability_game_noCollision_wins_le`.
-/
private lemma one_le_two_mul_succ_depth_mul_leafCount_aux (s : Skeleton) :
    1 ≤ 2 * (s.depth + 1) * s.leafCount := by
  have h := leafCount_pos_aux s
  nlinarith

/--
**Case A bound: probability 0.** When the extractor's path from `root` to the opened
leaf index is intact in committingAdv's log (i.e. the extracted leaf at `idx` is
`some _`), no-collision forces the verifier's chain to coincide with the extractor's
path, so opened `(leaf, proof)` matches the extracted pair and the win condition
fails. Hence the joint event "intact extracted path ∧ no collision ∧ adversary wins"
has probability `0`.

The proof requires an induction on the skeleton tracing the chain level-by-level
under no-collision; left as `sorry` for now.
-/
private theorem extractability_game_noColl_caseA_eq_zero
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (h_le_qb : 4 * s.leafCount + 1 ≤ qb) :
    Pr[noColl_caseA_event |
        (extractability_game committingAdv openingAdv).withQueryLog] = 0 := by
  apply probEvent_eq_zero
  rintro ⟨vals, log⟩ _hsupport
  obtain ⟨root, aux, idx, leaf, proof, extractedTree, extractedProof, verified⟩ := vals
  rintro ⟨_h_no_coll, _h_adv_wins, _h_ne_none⟩
  /-
  Substantive obligation: under `_h_no_coll`, `_h_adv_wins`, and `_h_ne_none`, derive
  `False`. By induction on `idx : SkeletonLeafIndex s` (going up from the leaf):
  at each level `k`, the value at the corresponding node in `extractedTree` is
  `some v` (since `_h_ne_none` propagates upward through `extractor`). `v` is the
  unique output of some committingAdv query, so by `_h_no_coll`, the verifier's
  level-`k` query must use the same input pair as committingAdv's. Inductively the
  verifier's chain coincides with `extractor`'s path, so opened `(leaf, proof)`
  equals extracted `(leaf, proof)`, contradicting `_h_adv_wins`.

  Formalization handles needed:
    * `extractor_get_eq_some_iff_chain_intact`: a structural lemma relating
      `extractedTree.get idx ≠ none` to the existence of a committingAdv-supported
      path from `root` to `idx`.
    * `verifyProof_run_eq_some_iff_chain_to_root`: characterization of when the
      verifier's chain reaches `root`, in terms of the queries it makes.
    * No-collision induction step: if a value `v` is produced by some committingAdv
      query and by another query, the inputs must agree.
  -/
  sorry

/--
**Case B bound: probability `≤ 1/|α|`.** When the extractor's path from `root` to
the opened leaf index is broken in committingAdv's log (i.e. the extracted leaf at
`idx` is `none`), verification succeeding requires the random oracle to produce a
chain reaching `root` whose terminal hash query has a fresh input pair (under no
collision). Since the random oracle's output on a fresh input is uniform on `α`,
the probability of hitting any specific target value is `1/|α|`.

The proof reduces to a `probOutput_query`-style bound on the verifier's terminal
hash query; left as `sorry` for now.
-/
private theorem extractability_game_noColl_caseB_le_inv_card
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (h_le_qb : 4 * s.leafCount + 1 ≤ qb) :
    Pr[noColl_caseB_event |
        (extractability_game committingAdv openingAdv).withQueryLog] ≤
      (1 : ENNReal) / (Fintype.card α : ENNReal) := by
  -- Weaken `noColl_caseB_event` to `verified = true ∧ extractedTree.get idx = none`:
  -- the no-collision and proof-mismatch parts of the predicate are dropped, since the
  -- leaf-mismatch disjunct of `adversary_wins_extractability_game_event` already
  -- holds automatically under `extractedTree.get idx = none`.
  refine le_trans (probEvent_mono'' (p := noColl_caseB_event)
      (q := fun (x : (α × AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog) =>
        let ⟨_, _, idx, _, _, extractedTree, _, verified⟩ := x.1
        verified = true ∧ extractedTree.get idx.toNodeIndex = none) ?_) ?_
  · rintro ⟨vals, log⟩
    obtain ⟨root, aux, idx, leaf, proof, extractedTree, extractedProof, verified⟩ := vals
    rintro ⟨_, h_adv_wins, h_extract_none⟩
    -- `adversary_wins_extractability_game_event` always carries `verified` as its
    -- outermost conjunct.
    refine ⟨?_, h_extract_none⟩
    rcases h_adv_wins with ⟨h_v, _⟩
    exact h_v
  /-
  Substantive obligation: bound
    `Pr[fun x => verified x.1 = true ∧ extractedTree x.1 .get idx x.1 = none |
        game.withQueryLog] ≤ 1 / |α|`.

  Strategy: `verified = true` forces the verifier's hash chain to reach `root`.
  Under `extractedTree.get idx = none`, the chain leaves committingAdv's tree at
  some level `k ∈ {1, …, idx.depth}` where the verifier's hash output equals a
  value not produced by any committingAdv query along the path. The "fresh"
  random-oracle output at that level is uniform on `α`, hitting any specific
  target value with probability `1/|α|`.

  Apply `probOutput_query` / `evalDist_query` on the verifier's terminal hash
  query (when the chain "rejoins" `root`). The hypothesis `4 * s.leafCount + 1 ≤ qb`
  bounds the size of the combined log, ruling out the pathological case where
  many opener queries pre-set the random oracle to produce `root` on
  inputs the verifier later queries.
  -/
  sorry

/--
**Tight no-collision bound.** Conditional on the combined query log of
`extractability_game` containing no collision, the adversary wins with probability at
most `1 / |α|`. Combines `extractability_game_noColl_caseA_eq_zero` (probability 0
when the extractor's path is intact) and `extractability_game_noColl_caseB_le_inv_card`
(probability `≤ 1/|α|` when the path is broken) via the case decomposition
`noColl_bad_iff_caseA_or_caseB` and `probEvent_or_le`.
-/
private theorem extractability_game_noCollision_wins_le_inv_card
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (h_le_qb : 4 * s.leafCount + 1 ≤ qb) :
    Pr[fun (vals, log) =>
        ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
      (extractability_game committingAdv openingAdv).withQueryLog] ≤
        (1 : ENNReal) / (Fintype.card α : ENNReal) := by
  -- The combined log of the entire game has at most `qb + s.depth` entries: the
  -- committingAdv/openingAdv pair contribute at most `qb` queries (by
  -- `h_IsQueryBound_qb`), and `verifyProof` adds at most `s.depth` more.
  have game_query_bound :=
    extractability_game_IsTotalQueryBound committingAdv openingAdv qb h_IsQueryBound_qb
  -- Trivially handle the small-cardinality cases where the bound `1/|α|` is
  -- already `≥ 1`, so `Pr[…] ≤ 1` (via `probEvent_le_one`) suffices. This isolates
  -- the substantive work to `Fintype.card α ≥ 2`.
  by_cases h_card : (Fintype.card α : ENNReal) ≤ 1
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top)]
    simpa using h_card
  push Not at h_card
  -- Rewrite the bad event as `caseA ∨ caseB`.
  have hbad_eq : (fun x : (α × AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog =>
        ¬ collisionIn x.2 ∧ adversary_wins_extractability_game_event x.1) =
      (fun x => noColl_caseA_event x ∨ noColl_caseB_event x) :=
    funext fun x => propext (noColl_bad_iff_caseA_or_caseB x)
  -- Apply union bound and dispatch to the case sub-lemmas.
  calc Pr[fun (vals, log) =>
            ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
            (extractability_game committingAdv openingAdv).withQueryLog]
      = Pr[fun x => noColl_caseA_event x ∨ noColl_caseB_event x |
            (extractability_game committingAdv openingAdv).withQueryLog] := by
        rw [hbad_eq]
    _ ≤ Pr[noColl_caseA_event |
            (extractability_game committingAdv openingAdv).withQueryLog] +
        Pr[noColl_caseB_event |
            (extractability_game committingAdv openingAdv).withQueryLog] := by
        apply probEvent_or_le
    _ = 0 + Pr[noColl_caseB_event |
            (extractability_game committingAdv openingAdv).withQueryLog] := by
        rw [extractability_game_noColl_caseA_eq_zero committingAdv openingAdv
              qb h_IsQueryBound_qb h_le_qb]
    _ = Pr[noColl_caseB_event |
            (extractability_game committingAdv openingAdv).withQueryLog] := zero_add _
    _ ≤ (1 : ENNReal) / (Fintype.card α : ENNReal) :=
        extractability_game_noColl_caseB_le_inv_card committingAdv openingAdv
          qb h_IsQueryBound_qb h_le_qb

/--
**No-collision lucky-guess bound.** Conditional on the combined query log of
`extractability_game` containing no collision, the adversary still wins only by a
"lucky guess": the committer publishes a `root` it never computed via the random
oracle, and the verifier's hash chain coincidentally produces that `root` at the top.
The total probability of this joint event is bounded by
`2 * (s.depth + 1) * s.leafCount / |α|`.

Proof. We first establish the tighter `1/|α|` bound in
`extractability_game_noCollision_wins_le_inv_card` (which carries the actual
probabilistic content), then loosen via `1 ≤ 2 * (s.depth + 1) * s.leafCount`.

Outline of the tight bound (formalized in
`extractability_game_noCollision_wins_le_inv_card`):

  Case A — `root ∈ committingLog.outputs`.
    Under no-collision, committingAdv's query producing `root` is the *unique*
    combined-log query producing it, so any chain reaching `root` must use that
    exact input pair. Inducting down the tree from `root`, the verifier's level-`k`
    query input must agree with committingAdv's level-`k` query (for k = s.depth,
    …, 1): if it did not, the verifier's level-`k` output would either equal the
    extracted node value at that position (forcing input agreement by no-collision)
    or differ (breaking the chain to `root`). By induction the verifier's chain
    traces exactly the path `extractor` builds, so opened (leaf, proof) equals
    extracted (leaf, proof) and the win condition fails. Hence
    `Pr[case A ∧ no-collision ∧ win] = 0`.

  Case B — `root ∉ committingLog.outputs`.
    Then `extractor s queryLog root` returns the all-`none` extension below the
    root, so the leaf-mismatch disjunct of `adversary_wins_extractability_game_event`
    is automatic whenever `idx.depth > 0`, reducing the win event to
    `verified = true`. Verification succeeding requires the random oracle to produce
    `root` at the verifier's terminal hash query. Since by case hypothesis no prior
    committingAdv query produced `root`, that terminal output is uniform on `α`
    (conditional on its input pair being fresh, which no-collision guarantees up to
    duplicate-query reuse), so it equals `root` with probability `1/|α|`.

Formalization sketch (for the tight bound).
  1. Decompose the event via `probEvent_or_le` along the `root ∈ committingLog`
     boolean disjunction.
  2. Case A: show the joint event is empty (probability `0`) by constructing, from
     a no-collision committing log and a chain reaching `root`, an explicit
     induction on the skeleton that exhibits the verifier's chain coinciding with
     `extractor`'s path.
  3. Case B: bound by `probOutput_query` / `evalDist_query` on the verifier's
     terminal hash query, whose input is fresh and output is uniform on `α`.
-/
theorem extractability_game_noCollision_wins_le
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (h_le_qb : 4 * s.leafCount + 1 ≤ qb) :
    Pr[fun (vals, log) =>
        ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
      (extractability_game committingAdv openingAdv).withQueryLog] ≤
        2 * (s.depth + 1) * s.leafCount / (Fintype.card α : ENNReal) := by
  refine le_trans
    (extractability_game_noCollision_wins_le_inv_card committingAdv openingAdv
      qb h_IsQueryBound_qb h_le_qb) ?_
  apply ENNReal.div_le_div_right
  exact_mod_cast one_le_two_mul_succ_depth_mul_leafCount_aux s

/--
The extractability theorem for Merkle trees.

Adapting from the SNARGs book Lemma 18.5.1:

For any query bound `qb`,
and for any adversary `committingAdv` that outputs a root and auxiliary data
and any `openingAdv` that takes the auxiliary data and outputs a leaf index, leaf value, and proof,
such that committingAdv and openingAdv together obey the query bound `qb`.

If the `committingAdv` and `openingAdv` are executed, and the `extractor` algorithm is run on the
resulting cache and root from `committingAdv`,
then with probability at most κ
does simultaneously

* the merkle tree verification pass on the proof from `openingAdv`
* with the extracted leaf value not matching the opened leaf value
  or the adversary producing a proof different from the extracted proof.

Where κ is ≤ 1/2 * (qb - 1) * qb / (Fintype.card α)
        + 2 * (s.depth + 1) * s.leafCount / (Fintype.card α)
(For sufficiently large qb)

Here, we loosen this a bit to attempt a proof by considering all collisions
in the combined query logs of the committing and opening adversaries and the verification.
-/
theorem extractability [DecidableEq α] [SampleableType α] [Fintype α] [Inhabited α]
    {s : Skeleton}
    {AuxState : Type}
    (committingAdv : OracleComp (spec α)
        (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (h_le_qb : 4 * s.leafCount + 1 ≤ qb)
          :
    Pr[adversary_wins_extractability_game_event |
        extractability_game committingAdv openingAdv] ≤
        ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α)
        + 2 * (s.depth + 1) * s.leafCount / (Fintype.card α)
    := by
      calc
    -- We first rewrite the game to include the combined query log
    _ = Pr[adversary_wins_extractability_game_with_logging_event |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      simp only [adversary_wins_extractability_game_with_logging_event]
      rw [← probEvent_withQueryLog]
    -- The bad event happens only when there is a collision event
    -- or the bad event happens with no collision
    _ ≤ Pr[fun (vals, log) =>
            collisionIn log ∨
            (¬ collisionIn log ∧ adversary_wins_extractability_game_event vals) |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      apply probEvent_mono''
      intro ⟨vals, log⟩
      simp [adversary_wins_extractability_game_with_logging_event]
      tauto
    -- We apply the union bound
    _ ≤ Pr[fun (vals, log) => collisionIn log |
            (extractability_game committingAdv openingAdv).withQueryLog] +
        Pr[fun (vals, log) =>
            ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      apply probEvent_or_le
    -- We bound the collision event probability with a collision bound
    _ ≤ ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α) +
        Pr[fun (vals, log) =>
            ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      gcongr
      have game_query_bound :=
        extractability_game_IsTotalQueryBound committingAdv openingAdv qb h_IsQueryBound_qb
      have hbound := collision_probability_bound
        (extractability_game committingAdv openingAdv) (qb + s.depth) game_query_bound
      convert hbound using 2
      push_cast
      rfl
    -- We bound the no-collision bad event probability
    _ ≤ ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α) +
        2 * (s.depth + 1) * s.leafCount / (Fintype.card α) := by
      have h := extractability_game_noCollision_wins_le committingAdv openingAdv
        (s := s) (AuxState := AuxState) qb h_IsQueryBound_qb h_le_qb
      have h' : Pr[fun (vals, log) =>
            ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] ≤
            2 * (s.depth + 1) * s.leafCount / (Fintype.card α : ENNReal) := by
        exact_mod_cast h
      gcongr
      norm_cast

  /-
  Now we can break down the bad event into smaller events
  In the SNARGS book, they define
  E_col = the event that there is a collision in committingLog
  E_tree = the event that the tree extraction with committingLog
           is different from the tree extraction
           with the combined committingLog and openingLog
  E_sub = the event that The verificationLog contains a query to a node not in the committingLog
          and verification succeeds

  The SNARGs book makes the observation that

  Pr[Adversary wins] ≤ Pr[E_col]
                       + Pr[E_tree | not E_col]
                       + Pr[E_sub | not E_col and not E_tree]
                       + Pr[Adversary wins | not E_col and not E_tree and not E_sub]

  But I think this really stands in for the tighter version, which might be easier to reason about.

  Pr[Adversary wins] ≤ Pr[E_col]
                       + Pr[E_tree and not E_col]
                       + Pr[E_sub and not E_col and not E_tree]
                       + Pr[Adversary wins and not E_col and not E_tree and not E_sub]

  TODO: does the proof really have to be this complicated?
  Can't we simply look at the event of any collision at all happening?

  * Does a collision happen in the adversary's queries and verification combined?
    * Probability of YES is small by query bound
    * If not, then consider whether the index opened exists in the extracted tree.
      * If yes, then if the proof differs at all, we must leave the extracted tree
        * After which, we can't return without a collision, so we don't verify.
      * If no, then the only way to verify is to have a collision in the verification proof.

  -/


end InductiveMerkleTree
