/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Collision

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
        (do let (root, aux) ← committingAdv;
            let ⟨idx, leaf, proof⟩ ← openingAdv aux; pure ())
        qb) :
    IsTotalQueryBound
        ((extractability_game committingAdv openingAdv))
        (qb + s.depth) := by
  sorry


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
          let (root, aux) ← committingAdv
          let ⟨idx, leaf, proof⟩ ← openingAdv aux
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
      have hno_coll : Pr[fun (vals, log) =>
            ¬ collisionIn log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] ≤
            2 * (s.depth + 1) * s.leafCount / (Fintype.card α : ENNReal) := by
        sorry
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
