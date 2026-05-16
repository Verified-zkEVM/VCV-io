/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Lemmas
import VCVio.OracleComp.QueryTracking.Birthday
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Inductive Merkle Tree Extractability

This file develops extractability for the inductive Merkle tree commitment scheme. The
extractor reconstructs a partial tree from the committing adversary's query log and the
opened root, and the main theorem bounds the probability that an adversary opens a leaf
that disagrees with the extracted tree.

## Main definitions

* `extractor`: builds a `FullData (Option α) s` from a query log, root, and skeleton by
  walking down from the root and pulling each node's children from the unique log entry
  whose response matches.
* `extractability_game`: the bundled game pairing a committing adversary with an opening
  adversary and recording the verifier's outcome along with the extracted tree and proof.
* `chainInLog`: structural predicate witnessing that a query log contains the hash chain
  from `root` down to `leaf` along the path determined by `idx`.

## Main results

* `extractability`: an adversary wins the extractability game with probability at most
  `(qb + s.depth)^2 / (2|α|) + 1 / |α|`, by union-bounding collision probability against
  the no-collision lucky-guess bound.

Note that our bound is looser than the SNARGs book's bound in Lemma 18.5.1 of
`((qb - 1) * qb) / 2 / |α| + (depth + 1) * 2 * size / |α|`.
This is because we have simplified the proof at the expense of tightness
(tighter, that is, in the qb >> size case)
by analyzing collisions for the full game at once.
A future improvement might be to re-structure the proof to recover the tighter bound.

## References

* [Building Cryptographic Proofs from Hash Functions by Chiesa and Yogev](https://snargsbook.org/), Lemma 18.5.1.

-/

open scoped NNReal

section ToVCV

/--
For any computation `oa` and predicate `p`, the probability of `p` holding on the output
equals the probability of `p ∘ Prod.fst` holding on the output of `oa.withQueryLog`.
This follows from the fact that `withQueryLog` only appends a log without changing the
output value. The lemma exists as a phrasing in terms of `oa.withQueryLog` (which is
`@[reducible]`) so that `rw` can match it; the underlying fact is
`loggingOracle.probEvent_fst_run_simulateQ`.
-/
lemma probEvent_withQueryLog {ι : Type} {oSpec : OracleSpec ι}
    [oSpec.Fintype] [oSpec.Inhabited] {α : Type}
    (oa : OracleComp oSpec α) (p : α → Prop) :
    Pr[p ∘ Prod.fst | oa.withQueryLog] = Pr[p | oa] :=
  loggingOracle.probEvent_fst_run_simulateQ oa p

end ToVCV

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/--
The child-decomposition function used by the Merkle-tree `extractor`. Given a `cache`
and a node value `a`, look up the first query in `cache` whose response is `a` and return
its input pair; if no such entry exists, return `none`.
-/
def extractorChildren {α : Type} [DecidableEq α]
    (cache : (spec α).QueryLog) (a : α) : Option (α × α) :=
  match cache.find? (fun ⟨_, r⟩ => r == a) with
  | none => none
  | some q => some (q.1.1, q.1.2)

/--
The extraction algorithm for Merkle trees: from a query log `cache`, a `root`, and a
skeleton `s`, build a partial tree of type `FullData (Option α) s` by walking down from
`root`. A node with value `some a` looks up the unique log entry whose response is `a`
and uses its input pair as the children's values; in every other case (no matching entry,
or the parent is already `none`) both children are `none`. Implemented as
`optionPopulateDown` driven by `extractorChildren`.
-/
def extractor {α : Type} [DecidableEq α] [SampleableType α]
    [OracleSpec.Fintype (spec α)]
    (s : Skeleton) (cache : (spec α).QueryLog) (root : α) :
    FullData (Option α) s :=
  optionPopulateDown s (extractorChildren cache) root

/--
Predicate stating that `log` contains a hash chain from `root` (combined with the
sibling values in `proof`) down to `leaf` along the path determined by `idx`.

This captures what it means for the verifier's `getPutativeRoot` evaluation to
succeed at returning `root`: at each level the verifier queries the hash oracle
with a specific input pair and gets back the parent's value, and that query
becomes a log entry.
-/
def chainInLog : ∀ {s : Skeleton}, (spec α).QueryLog → α →
    (idx : SkeletonLeafIndex s) → α → List.Vector α idx.depth → Prop
  | _, _, root, .ofLeaf, leaf, _ => leaf = root
  | _, log, root, .ofLeft idxLeft, leaf, proof =>
      ∃ ancestor : α,
        (⟨(ancestor, proof.head), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        chainInLog log ancestor idxLeft leaf proof.tail
  | _, log, root, .ofRight idxRight, leaf, proof =>
      ∃ ancestor : α,
        (⟨(proof.head, ancestor), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        chainInLog log ancestor idxRight leaf proof.tail

/-- If the query log's first entry with response `root` is the pair `⟨(x, y), root⟩`,
then the extractor at an internal skeleton unfolds to that node's two children using
`x` and `y` as the new "ancestor" values for the left and right subtrees. -/
private lemma extractor_internal_eq_of_find?_eq
    [DecidableEq α] [SampleableType α] [(spec α).Fintype]
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root x y : α)
    (h_find : log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
                some ⟨(x, y), root⟩) :
    extractor (Skeleton.internal sl sr) log root =
      FullData.internal (some root) (extractor sl log x) (extractor sr log y) := by
  have h_children : extractorChildren log root = some (x, y) := by
    change (match log.find? _ with | none => none | some q => some (q.1.1, q.1.2)) = _
    rw [h_find]
  simp only [extractor]
  rw [optionPopulateDown_internal, h_children]
  rfl

/--
The game for extractability.

This is represented as a single `OracleComp`
that runs the committing adversary, extractor, opening adversary, and verifier in sequence and
returns the transcript of the execution.
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
    let verified ← verifyProof idx leaf root proof
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
  -- bundles `committingAdv.withQueryLog; openingAdv` and the suffix runs
  -- `verifyProof` and assembles the final return tuple.
  rw [show extractability_game committingAdv openingAdv =
      (committingAdv.withQueryLog >>= fun p =>
        openingAdv p.1.2 >>= fun q => pure (p, q)) >>=
      fun pq =>
        verifyProof pq.2.1 pq.2.2.1 pq.1.1.1 pq.2.2.2 >>= fun verified =>
          pure (pq.1.1.1, pq.1.1.2,
                ⟨pq.2.1, pq.2.2.1, pq.2.2.2,
                 extractor s pq.1.2 pq.1.1.1,
                 generateProof (extractor s pq.1.2 pq.1.1.1) pq.2.1,
                 verified⟩) by unfold extractability_game; simp only [bind_assoc, pure_bind]]
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
  · -- Suffix bound: verifyProof + pure ≤ s.depth.
    rintro ⟨p, q⟩
    exact isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
      (verifyProof_isTotalQueryBound_skeleton_depth q.1 q.2.1 p.1.1 q.2.2) (fun _ => trivial)

private lemma chainInLog_mono {α : Type} {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ {log1 log2 : (spec α).QueryLog} {root leaf : α}
      {proof : List.Vector α idx.depth},
    (∀ q, q ∈ log1 → q ∈ log2) →
    chainInLog log1 root idx leaf proof →
    chainInLog log2 root idx leaf proof := by
  induction idx with
  | ofLeaf => intros _ _ _ _ _ _ h; exact h
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    intro _ _ _ _ _ h_sub ⟨ancestor, h_mem, h_rec⟩
    exact ⟨ancestor, h_sub _ h_mem, ih h_sub h_rec⟩

private lemma singleHash_withQueryLog
    [SampleableType α] [(spec α).Fintype] [(spec α).Inhabited]
    (a b : α) :
    (singleHash (m := OracleComp (spec α)) a b).withQueryLog =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>=
        fun u => pure (u, ([⟨(a, b), u⟩] : (spec α).QueryLog)) := by
  -- `singleHash a b = liftM ((spec α).query (a, b))` after `bind_pure` simplifies
  -- the `do let out ← _; return out` shape.
  have h : (singleHash (m := OracleComp (spec α)) a b) =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) := by
    change liftM ((spec α).query (a, b)) >>= pure = _
    rw [bind_pure]
  rw [h, OracleComp.withQueryLog_query]

/-- Decomposition of `getPutativeRoot.withQueryLog` at a `.ofLeft` step: the
output value `r` is the hash response on `(a, proof.head)` for some recursive
ancestor `a`, and the log decomposes as `log_a ++ [⟨(a, proof.head), r⟩]`. -/
private lemma getPutativeRoot_ofLeft_withQueryLog_decompose
    [SampleableType α] [(spec α).Fintype] [(spec α).Inhabited]
    {sl sr : Skeleton} (idxLeft : SkeletonLeafIndex sl)
    (leaf : α)
    (proof : List.Vector α
      (SkeletonLeafIndex.ofLeft idxLeft : SkeletonLeafIndex (Skeleton.internal sl sr)).depth)
    (r : α) (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
      (getPutativeRoot (m := OracleComp (spec α))
        (SkeletonLeafIndex.ofLeft idxLeft) leaf proof).withQueryLog) :
    ∃ a log_a, (a, log_a) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail).withQueryLog
      ∧ log_v = log_a ++ [⟨(a, proof.head), r⟩] := by
  rw [show (getPutativeRoot (m := OracleComp (spec α))
      (SkeletonLeafIndex.ofLeft idxLeft) leaf proof) =
      getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail >>=
        fun a => singleHash a proof.head from rfl,
    OracleComp.withQueryLog_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨a, log_a⟩, h_rec, hmem⟩ := hmem
  rw [singleHash_withQueryLog, support_map, Set.mem_image] at hmem
  obtain ⟨⟨_, _⟩, h_q, h_eq2⟩ := hmem
  rw [mem_support_bind_iff] at h_q
  obtain ⟨_, _, h_pure⟩ := h_q
  rw [mem_support_pure_iff, Prod.mk.injEq] at h_pure
  obtain ⟨rfl, rfl⟩ := h_pure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq2
  exact ⟨a, log_a, h_rec, rfl⟩

/-- Mirror of `getPutativeRoot_ofLeft_withQueryLog_decompose` for the right
subtree: the chain entry is `⟨(proof.head, a), r⟩`. -/
private lemma getPutativeRoot_ofRight_withQueryLog_decompose
    [SampleableType α] [(spec α).Fintype] [(spec α).Inhabited]
    {sl sr : Skeleton} (idxRight : SkeletonLeafIndex sr)
    (leaf : α)
    (proof : List.Vector α
      (SkeletonLeafIndex.ofRight idxRight : SkeletonLeafIndex (Skeleton.internal sl sr)).depth)
    (r : α) (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
      (getPutativeRoot (m := OracleComp (spec α))
        (SkeletonLeafIndex.ofRight idxRight) leaf proof).withQueryLog) :
    ∃ a log_a, (a, log_a) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail).withQueryLog
      ∧ log_v = log_a ++ [⟨(proof.head, a), r⟩] := by
  rw [show (getPutativeRoot (m := OracleComp (spec α))
      (SkeletonLeafIndex.ofRight idxRight) leaf proof) =
      getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail >>=
        fun a => singleHash proof.head a from rfl,
    OracleComp.withQueryLog_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨a, log_a⟩, h_rec, hmem⟩ := hmem
  rw [singleHash_withQueryLog, support_map, Set.mem_image] at hmem
  obtain ⟨⟨_, _⟩, h_q, h_eq2⟩ := hmem
  rw [mem_support_bind_iff] at h_q
  obtain ⟨_, _, h_pure⟩ := h_q
  rw [mem_support_pure_iff, Prod.mk.injEq] at h_pure
  obtain ⟨rfl, rfl⟩ := h_pure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq2
  exact ⟨a, log_a, h_rec, rfl⟩

private lemma getPutativeRoot_support_chain
    [SampleableType α] [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ (leaf : α) (proof : List.Vector α idx.depth) (r : α)
      (log_v : (spec α).QueryLog),
    (r, log_v) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof).withQueryLog →
    chainInLog log_v r idx leaf proof := by
  induction idx with
  | ofLeaf =>
    intros leaf _proof r log_v hmem
    rw [show (getPutativeRoot (m := OracleComp (spec α))
        SkeletonLeafIndex.ofLeaf leaf _proof) = pure leaf from rfl,
      OracleComp.withQueryLog_pure, mem_support_pure_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    simp only [chainInLog]
  | @ofLeft sl sr idxLeft ih =>
    intros leaf proof r log_v hmem
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_ofLeft_withQueryLog_decompose idxLeft leaf proof r log_v hmem
    exact ⟨a, by simp,
      chainInLog_mono _ (fun _ hq => List.mem_append_left _ hq)
        (ih leaf proof.tail a log_a h_rec)⟩
  | @ofRight sl sr idxRight ih =>
    intros leaf proof r log_v hmem
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_ofRight_withQueryLog_decompose idxRight leaf proof r log_v hmem
    exact ⟨a, by simp,
      chainInLog_mono _ (fun _ hq => List.mem_append_left _ hq)
        (ih leaf proof.tail a log_a h_rec)⟩

private lemma verifyProof_support_chain
    {α : Type} [DecidableEq α] [SampleableType α] [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (log_v : (spec α).QueryLog)
    (hmem : (true, log_v) ∈ support
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog) :
    chainInLog log_v root idx leaf proof := by
  -- Reshape `verifyProof` to `getPutativeRoot >>= (· == root)`.
  rw [show verifyProof (m := OracleComp (spec α)) idx leaf root proof =
      (do let r ← getPutativeRoot (m := OracleComp (spec α)) idx leaf proof
          pure (r == root)) from rfl,
    OracleComp.withQueryLog_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨r, log_g⟩, h_g, hmem⟩ := hmem
  rw [support_map, Set.mem_image] at hmem
  obtain ⟨⟨b, log_x⟩, h_x, h_eq⟩ := hmem
  -- `Prod.map id (log_g ++ ·) (b, log_x) = (true, log_v)` gives `b = true`,
  -- `log_g ++ log_x = log_v`.
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
  rw [OracleComp.withQueryLog_pure, mem_support_pure_iff] at h_x
  obtain ⟨h_b_eq, rfl⟩ := Prod.mk.inj h_x
  -- `r == root = true` implies `r = root`.
  obtain rfl : r = root := by simpa using h_b_eq.symm
  simpa using getPutativeRoot_support_chain idx leaf proof r log_g h_g

private lemma extractorChildren_eq_none_of_find?_eq_none [DecidableEq α]
    {log_c : (spec α).QueryLog} {a : α}
    (hf : log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == a) = none) :
    extractorChildren log_c a = none := by
  change (match log_c.find? _ with | none => none | some q => some (q.1.1, q.1.2)) = none
  rw [hf]

/-- **Self-log fixed point.** The two log layers produced by
`oa.withQueryLog.withQueryLog` agree on every support point: simulating the
logging oracle over `oa.withQueryLog` records exactly the queries that the
inner `withQueryLog` already recorded, since `withQueryLog` does not add new
queries to the underlying `OracleComp`. -/
theorem withQueryLog_self_log_eq
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) {v : α} {l₁ l₂ : spec.QueryLog}
    (hmem : ((v, l₁), l₂) ∈ support oa.withQueryLog.withQueryLog) :
    l₁ = l₂ := by
  induction oa using OracleComp.inductionOn generalizing v l₁ l₂ with
  | pure x =>
      change ((v, l₁), l₂) ∈ support
        ((pure x : OracleComp spec α).withQueryLog.withQueryLog) at hmem
      rw [OracleComp.withQueryLog_pure, OracleComp.withQueryLog_pure,
        mem_support_pure_iff] at hmem
      obtain ⟨⟨_, rfl⟩, rfl⟩ := Prod.mk.inj hmem |>.imp_left Prod.mk.inj
      rfl
  | query_bind t mx ih =>
      change ((v, l₁), l₂) ∈ support
        (((liftM (OracleSpec.query t) : OracleComp spec _) >>=
          fun u => mx u).withQueryLog.withQueryLog) at hmem
      rw [OracleComp.withQueryLog_bind, OracleComp.withQueryLog_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨u₁, log_q1⟩, log_q2⟩, h₁, hmem⟩ := hmem
      rw [OracleComp.withQueryLog_query, OracleComp.withQueryLog_bind,
        mem_support_bind_iff] at h₁
      obtain ⟨⟨u₂, log_qa⟩, h₁a, h₁b⟩ := h₁
      simp only [OracleComp.withQueryLog_query, mem_support_bind_iff,
        mem_support_pure_iff, Prod.mk.injEq] at h₁a
      obtain ⟨u, _, rfl, rfl⟩ := h₁a
      rw [support_map, Set.mem_image] at h₁b
      obtain ⟨⟨⟨u', l_inner⟩, l_outer⟩, h_pure, h_eq_b⟩ := h₁b
      simp only [OracleComp.withQueryLog_pure, mem_support_pure_iff,
        Prod.mk.injEq] at h_pure
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h_pure
      simp only [Prod.map_apply, id_eq, Prod.mk.injEq, List.append_nil] at h_eq_b
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h_eq_b
      rw [support_map, Set.mem_image] at hmem
      obtain ⟨⟨⟨v', l₁'⟩, l₂'⟩, h_inner_outer, h_eq⟩ := hmem
      simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h_eq
      simp only at h_inner_outer
      rw [show (Prod.map id (fun x => ([⟨t, u'⟩] ++ x : (spec).QueryLog)) <$>
              (mx u').withQueryLog) =
            ((mx u').withQueryLog >>=
              fun p => pure (Prod.map id (fun x => [⟨t, u'⟩] ++ x) p))
          by rw [map_eq_pure_bind],
        OracleComp.withQueryLog_bind, mem_support_bind_iff] at h_inner_outer
      obtain ⟨⟨⟨v', l₁'⟩, l₂'⟩, h_inner, h_rest⟩ := h_inner_outer
      rw [support_map, Set.mem_image] at h_rest
      obtain ⟨⟨pX, lX⟩, h_pX, h_eq_X⟩ := h_rest
      rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_pX
      obtain ⟨rfl, rfl⟩ := h_pX
      simp only [Prod.map_apply, id_eq, List.append_nil, Prod.mk.injEq] at h_eq_X
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h_eq_X
      rw [ih u' h_inner]

/-- Destructures support membership of the (verified) `extractability_game` into
its two relevant logged components: a committingAdv log `log_c` and a verifyProof
log `log_v`, both ⊆ `log`, together with the equalities pinning `extractedTree`
and `extractedProof` to the extractor's outputs on `log_c` and the opened root. -/
private lemma extractability_game_support_decompose
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    {root : α} {aux : AuxState} {idx : SkeletonLeafIndex s} {leaf : α}
    {proof : List.Vector α idx.depth}
    {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth}
    {log : (spec α).QueryLog}
    (hsup : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractability_game committingAdv openingAdv).withQueryLog) :
    ∃ log_c log_v : (spec α).QueryLog,
      (true, log_v) ∈ support
          (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog ∧
      (∀ q, q ∈ log_v → q ∈ log) ∧
      (∀ q, q ∈ log_c → q ∈ log) ∧
      extractedTree = extractor s log_c root ∧
      extractedProof = generateProof (extractor s log_c root) idx := by
  unfold extractability_game at hsup
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at hsup
  obtain ⟨⟨⟨root_c, aux_c⟩, log_c⟩, h_c, hsup⟩ := hsup
  rw [support_map, Set.mem_image] at hsup
  obtain ⟨⟨_, _⟩, h_co, h_eq_co⟩ := hsup
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at h_co
  obtain ⟨⟨⟨idx_o, leaf_o, proof_o⟩, _⟩, _, h_co⟩ := h_co
  rw [support_map, Set.mem_image] at h_co
  obtain ⟨⟨_, _⟩, h_v, h_eq_v⟩ := h_co
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at h_v
  obtain ⟨⟨_, log_v⟩, h_vp, h_v⟩ := h_v
  rw [support_map, Set.mem_image] at h_v
  obtain ⟨⟨_, _⟩, h_p, h_eq_p⟩ := h_v
  rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_p
  obtain ⟨h_p1, rfl⟩ := h_p
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_co h_eq_v h_eq_p
  obtain ⟨h_eq_co1, h_eq_co2⟩ := h_eq_co
  obtain ⟨h_eq_v1, h_eq_v2⟩ := h_eq_v
  obtain ⟨h_eq_p1, h_eq_p2⟩ := h_eq_p
  rw [← h_eq_p1, h_p1] at h_eq_v1
  rw [← h_eq_v1] at h_eq_co1
  simp only [Prod.mk.injEq] at h_eq_co1
  obtain ⟨rfl, rfl, h_sigma_eq⟩ := h_eq_co1
  obtain ⟨h_idx_eq, h_rest_eq⟩ := Sigma.mk.inj h_sigma_eq
  subst h_idx_eq
  simp only [heq_eq_eq, Prod.mk.injEq] at h_rest_eq
  obtain ⟨rfl, rfl, h_tree_eq, h_proof_ext_eq, rfl⟩ := h_rest_eq
  rw [withQueryLog_self_log_eq committingAdv h_c] at h_tree_eq h_proof_ext_eq
  refine ⟨log_c, log_v, h_vp, ?_, ?_, h_tree_eq.symm, h_proof_ext_eq.symm⟩
  · intro q hq
    rw [← h_eq_co2, ← h_eq_v2, ← h_eq_p2]
    simpa using List.mem_append_right _ (List.mem_append_right _ hq)
  · intro q hq
    rw [← h_eq_co2, ← h_eq_v2, ← h_eq_p2]
    simpa using List.mem_append_left _ (List.mem_append_left _ hq)

/-- **Log-level binding (Collision Lemma at the log level).** Log-formalized
analog of `getPutativeRootWithHash_binding_collision`: two distinct openings
`(x, proof₁) ≠ (y, proof₂)` of the same `root` at the same index, both
witnessed by hash chains `chainInLog` in the same `log`, force `log` to
contain a hash collision (two log entries with equal responses but distinct
inputs).

Proof: induction on `idx`, mirroring the constructive recursion of
`findCollision` (cf. `Binding.lean`). At each non-leaf level both chains
expose a top entry `⟨(_, _), root⟩ ∈ log`; either the two top inputs differ
(immediate `LogHasCollision` since both produce response `root`) or they
coincide and we recurse on the shared ancestor — the original inequality
`(x, proof₁) ≠ (y, proof₂)` propagates to `(x, proof₁.tail) ≠ (y, proof₂.tail)`. -/
theorem chainInLog_logCollision_of_ne
    {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ (log : (spec α).QueryLog) (root x y : α)
      (proof₁ proof₂ : List.Vector α idx.depth),
    (x, proof₁) ≠ (y, proof₂) →
    chainInLog log root idx x proof₁ →
    chainInLog log root idx y proof₂ →
    LogHasCollision log := by
  induction idx with
  | ofLeaf =>
    intros log root x y proof₁ proof₂ hne hc₁ hc₂
    exfalso; apply hne
    simp only [chainInLog] at hc₁ hc₂
    have hp : proof₁ = proof₂ := List.Vector.ext (fun i => i.elim0)
    exact Prod.ext (hc₁.trans hc₂.symm) hp
  | @ofLeft sl sr idxLeft ih =>
    rintro log root x y proof₁ proof₂ hne ⟨a₁, h₁_mem, hc₁⟩ ⟨a₂, h₂_mem, hc₂⟩
    by_cases hpair : (a₁, proof₁.head) = (a₂, proof₂.head)
    · obtain ⟨ha, hhead⟩ := Prod.mk.inj hpair
      subst ha
      refine ih _ _ _ _ _ _ ?_ hc₁ hc₂
      intro heq
      apply hne
      obtain ⟨hxy, htail⟩ := Prod.mk.inj heq
      refine Prod.ext hxy ?_
      conv_lhs => rw [show proof₁ = proof₁.head ::ᵥ proof₁.tail
        from (List.Vector.cons_head_tail proof₁).symm]
      conv_rhs => rw [show proof₂ = proof₂.head ::ᵥ proof₂.tail
        from (List.Vector.cons_head_tail proof₂).symm]
      rw [hhead, htail]
    · -- Different inputs, same response (root): immediate log collision.
      refine LogHasCollision.of_mem ?_ h₁_mem h₂_mem (heq_of_eq rfl)
      intro h_eq_sigma
      exact hpair (congrArg Sigma.fst h_eq_sigma)
  | @ofRight sl sr idxRight ih =>
    rintro log root x y proof₁ proof₂ hne ⟨a₁, h₁_mem, hc₁⟩ ⟨a₂, h₂_mem, hc₂⟩
    by_cases hpair : (proof₁.head, a₁) = (proof₂.head, a₂)
    · obtain ⟨hhead, ha⟩ := Prod.mk.inj hpair
      subst ha
      refine ih _ _ _ _ _ _ ?_ hc₁ hc₂
      intro heq
      apply hne
      obtain ⟨hxy, htail⟩ := Prod.mk.inj heq
      refine Prod.ext hxy ?_
      conv_lhs => rw [show proof₁ = proof₁.head ::ᵥ proof₁.tail
        from (List.Vector.cons_head_tail proof₁).symm]
      conv_rhs => rw [show proof₂ = proof₂.head ::ᵥ proof₂.tail
        from (List.Vector.cons_head_tail proof₂).symm]
      rw [hhead, htail]
    · refine LogHasCollision.of_mem ?_ h₁_mem h₂_mem (heq_of_eq rfl)
      intro h_eq_sigma
      exact hpair (congrArg Sigma.fst h_eq_sigma)

/-- **Extractor recovery to a log chain.** When the extractor's path at `idx`
is intact (the value there is `≠ none`), the extracted leaf value and proof
form a hash chain `chainInLog` in the log. The conclusion bundles three
facts: the extracted leaf (`extLeaf`), the recovered authentication path
(`extProof`), and a chain witness in `log` connecting them to `root`.

Proof: induction on `idx`, mirroring the extractor's `populateDown` descent.
At each non-leaf level the non-none hypothesis forces `log.find? (·.2 == root)`
to return some entry `⟨(l, r), root⟩`, which becomes the chain entry at this
level; the IH recurses into the appropriate subtree. -/
theorem extractor_chainInLog
    [DecidableEq α] [SampleableType α] [(spec α).Fintype]
    {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ (log : (spec α).QueryLog) (root : α),
    (extractor s log root).get idx.toNodeIndex ≠ none →
    ∃ extLeaf : α, ∃ extProof : List.Vector α idx.depth,
      (extractor s log root).get idx.toNodeIndex = some extLeaf ∧
      (generateProof (extractor s log root) idx).toList = extProof.toList.map some ∧
      chainInLog log root idx extLeaf extProof := by
  induction idx with
  | ofLeaf =>
    intros log root _
    exact ⟨root, ⟨[], rfl⟩, rfl, rfl, rfl⟩
  | @ofLeft sl sr idxLeft ih =>
    intros log root h_ne_none
    -- `h_ne_none` forces `log.find? (·.2 == root) = some _`.
    obtain ⟨q, h_find⟩ :
        ∃ q : (_i : (α × α)) × α,
          log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) = some q := by
      rcases hf : log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) with _ | q
      · refine absurd ?_ h_ne_none
        simp only [extractor]
        rw [optionPopulateDown_internal, extractorChildren_eq_none_of_find?_eq_none hf]
        change (populateDown sl (Option.bindPair (extractorChildren log)) none).get
            idxLeft.toNodeIndex = none
        exact populateDown_none_get_eq_none (Option.bindPair (extractorChildren log)) rfl
          idxLeft.toNodeIndex
      · exact ⟨q, rfl⟩
    have hq2 : q.2 = root := by
      simpa using (List.find?_eq_some_iff_getElem.mp h_find).1
    have hq_eq : q = ⟨(q.1.1, q.1.2), root⟩ := by
      rcases q with ⟨⟨_, _⟩, _⟩; subst hq2; rfl
    have h_find' : log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
                   some ⟨(q.1.1, q.1.2), root⟩ := by rw [h_find, hq_eq]
    have h_log_mem : (⟨(q.1.1, q.1.2), root⟩ : (_i : (α × α)) × α) ∈ log := by
      rw [← hq_eq]; exact List.mem_of_find?_eq_some h_find
    have h_decomp := extractor_internal_eq_of_find?_eq sl sr log root q.1.1 q.1.2 h_find'
    rw [h_decomp]
    have h_ne_none_l : (extractor sl log q.1.1).get idxLeft.toNodeIndex ≠ none := fun he =>
      h_ne_none (by rw [h_decomp]; exact he)
    obtain ⟨extLeafL, extProofL, h_extLeaf_eq_L, h_extProof_eq_L, h_chain_L⟩ :=
      ih log q.1.1 h_ne_none_l
    refine ⟨extLeafL, q.1.2 ::ᵥ extProofL, h_extLeaf_eq_L, ?_, q.1.1, h_log_mem, h_chain_L⟩
    change (extractor sr log q.1.2).getRootValue ::
          (generateProof (extractor sl log q.1.1) idxLeft).toList =
        (q.1.2 ::ᵥ extProofL).toList.map some
    have h_root_value : (extractor sr log q.1.2).getRootValue = some q.1.2 :=
      optionPopulateDown_getRootValue _ _
    rw [h_root_value, h_extProof_eq_L]
    rfl
  | @ofRight sl sr idxRight ih =>
    intros log root h_ne_none
    obtain ⟨q, h_find⟩ :
        ∃ q : (_i : (α × α)) × α,
          log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) = some q := by
      rcases hf : log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) with _ | q
      · refine absurd ?_ h_ne_none
        simp only [extractor]
        rw [optionPopulateDown_internal, extractorChildren_eq_none_of_find?_eq_none hf]
        change (populateDown sr (Option.bindPair (extractorChildren log)) none).get
            idxRight.toNodeIndex = none
        exact populateDown_none_get_eq_none (Option.bindPair (extractorChildren log)) rfl
          idxRight.toNodeIndex
      · exact ⟨q, rfl⟩
    have hq2 : q.2 = root := by
      simpa using (List.find?_eq_some_iff_getElem.mp h_find).1
    have hq_eq : q = ⟨(q.1.1, q.1.2), root⟩ := by
      rcases q with ⟨⟨_, _⟩, _⟩; subst hq2; rfl
    have h_find' : log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
                   some ⟨(q.1.1, q.1.2), root⟩ := by rw [h_find, hq_eq]
    have h_log_mem : (⟨(q.1.1, q.1.2), root⟩ : (_i : (α × α)) × α) ∈ log := by
      rw [← hq_eq]; exact List.mem_of_find?_eq_some h_find
    have h_decomp := extractor_internal_eq_of_find?_eq sl sr log root q.1.1 q.1.2 h_find'
    rw [h_decomp]
    have h_ne_none_r : (extractor sr log q.1.2).get idxRight.toNodeIndex ≠ none := fun he =>
      h_ne_none (by rw [h_decomp]; exact he)
    obtain ⟨extLeafR, extProofR, h_extLeaf_eq_R, h_extProof_eq_R, h_chain_R⟩ :=
      ih log q.1.2 h_ne_none_r
    refine ⟨extLeafR, q.1.1 ::ᵥ extProofR, h_extLeaf_eq_R, ?_, q.1.2, h_log_mem, h_chain_R⟩
    change (extractor sl log q.1.1).getRootValue ::
          (generateProof (extractor sr log q.1.2) idxRight).toList =
        (q.1.1 ::ᵥ extProofR).toList.map some
    have h_root_value : (extractor sl log q.1.1).getRootValue = some q.1.1 :=
      optionPopulateDown_getRootValue _ _
    rw [h_root_value, h_extProof_eq_R]
    rfl

/--
**Pure consistency lemma.** Under no-collision, if the extractor's path from
`root` to the node at `idx` is intact (the value there is `≠ none`) and
`chainInLog log root idx leaf proof` holds, then the extracted leaf value
equals `some leaf` and the extracted proof matches `proof.toList.map some`
pointwise.

Proof: `extractor_chainInLog` recovers a chain witness `(extLeaf, extProof)`
from the extractor's reconstruction. If `(extLeaf, extProof) = (leaf, proof)`
we are done; otherwise the two distinct chains force a `LogHasCollision` via
`chainInLog_logCollision_of_ne`, contradicting `¬LogHasCollision log`. -/
theorem extractor_chain_match
    [DecidableEq α] [SampleableType α] [(spec α).Fintype]
    {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ (log : (spec α).QueryLog) (root : α) (leaf : α)
      (proof : List.Vector α idx.depth),
    ¬ LogHasCollision log →
    (extractor s log root).get idx.toNodeIndex ≠ none →
    chainInLog log root idx leaf proof →
    (extractor s log root).get idx.toNodeIndex = some leaf ∧
      (generateProof (extractor s log root) idx).toList = proof.toList.map some := by
  intros log root leaf proof h_no_coll h_ne_none h_chain
  obtain ⟨extLeaf, extProof, h_extLeaf_eq, h_extProof_eq, h_extChain⟩ :=
    extractor_chainInLog idx log root h_ne_none
  by_cases hpair : (extLeaf, extProof) = (leaf, proof)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hpair
    subst h1; subst h2
    exact ⟨h_extLeaf_eq, h_extProof_eq⟩
  · exact absurd (chainInLog_logCollision_of_ne idx log root extLeaf leaf
      extProof proof hpair h_extChain h_chain) h_no_coll

private theorem extractability_game_no_coll_match
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    {root : α} {aux : AuxState} {idx : SkeletonLeafIndex s} {leaf : α}
    {proof : List.Vector α idx.depth}
    {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth}
    {log : (spec α).QueryLog}
    (h_no_coll : ¬ LogHasCollision log)
    (h_ne_none : extractedTree.get idx.toNodeIndex ≠ none)
    (hsupport : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractability_game committingAdv openingAdv).withQueryLog) :
    extractedTree.get idx.toNodeIndex = some leaf ∧
      proof.toList.map some = extractedProof.toList := by
  obtain ⟨log_c, log_v, h_vp, h_sub_v, h_sub_c, h_tree_eq, h_proof_ext_eq⟩ :=
    extractability_game_support_decompose committingAdv openingAdv hsupport
  -- Verifier's chain in `log` (via `log_v ⊆ log`).
  have h_chain_log : chainInLog log root idx leaf proof :=
    chainInLog_mono idx h_sub_v (verifyProof_support_chain idx leaf root proof log_v h_vp)
  -- Extractor's reconstruction non-none on `log_c`.
  have h_ne_none_lc : (extractor s log_c root).get idx.toNodeIndex ≠ none := by
    rw [← h_tree_eq]; exact h_ne_none
  -- Extractor's reconstruction produces a chain in `log_c`, hence in `log`.
  obtain ⟨extLeaf, extProof, h_extLeaf_eq, h_extProof_eq, h_extChain_lc⟩ :=
    extractor_chainInLog idx log_c root h_ne_none_lc
  have h_extChain_log : chainInLog log root idx extLeaf extProof :=
    chainInLog_mono idx h_sub_c h_extChain_lc
  -- Either openings match (we are done) or log has a collision (contradiction).
  by_cases hpair : (extLeaf, extProof) = (leaf, proof)
  · obtain ⟨hl, hp⟩ := Prod.mk.inj hpair
    subst hl; subst hp
    refine ⟨h_tree_eq.symm ▸ h_extLeaf_eq, ?_⟩
    rw [h_proof_ext_eq, h_extProof_eq]
  · exact absurd (chainInLog_logCollision_of_ne idx log root extLeaf leaf
      extProof proof hpair h_extChain_log h_chain_log) h_no_coll

private def noColl_caseA_event {α : Type} [BEq α] [DecidableEq α]
    {s : Skeleton} {AuxState : Type} :
    (α × AuxState ×
       ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
        FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog → Prop
  | (vals, log) =>
    let ⟨_, _, idx, _, _, extractedTree, _, _⟩ := vals
    ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals ∧
      extractedTree.get idx.toNodeIndex ≠ none

private def noColl_caseB_event {α : Type} [BEq α] [DecidableEq α]
    {s : Skeleton} {AuxState : Type} :
    (α × AuxState ×
       ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
        FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog → Prop
  | (vals, log) =>
    let ⟨_, _, idx, _, _, extractedTree, _, _⟩ := vals
    ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals ∧
      extractedTree.get idx.toNodeIndex = none

private lemma noColl_bad_iff_caseA_or_caseB
    {α : Type} [BEq α] [DecidableEq α] {s : Skeleton} {AuxState : Type}
    (x : (α × AuxState ×
            ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
             FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
         (spec α).QueryLog) :
    (¬ LogHasCollision x.2 ∧ adversary_wins_extractability_game_event x.1) ↔
      noColl_caseA_event x ∨ noColl_caseB_event x := by
  rcases x with ⟨⟨_, _, ⟨idx, _, _, extractedTree, _, _⟩⟩, log⟩
  simp only [noColl_caseA_event, noColl_caseB_event]
  by_cases h : extractedTree.get idx.toNodeIndex = none
  · simp [h]
  · simp [h]

private theorem extractability_game_noColl_caseA_eq_zero
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (_h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb) :
    Pr[noColl_caseA_event |
        (extractability_game committingAdv openingAdv).withQueryLog] = 0 := by
  apply probEvent_eq_zero
  rintro ⟨vals, log⟩ hsupport
  obtain ⟨root, aux, idx, leaf, proof, _, _, verified⟩ := vals
  rintro ⟨h_no_coll, ⟨rfl, h_adv_wins⟩, h_ne_none⟩
  obtain ⟨h_eq_leaf, h_map⟩ :=
    extractability_game_no_coll_match committingAdv openingAdv h_no_coll h_ne_none hsupport
  simp [h_map, h_eq_leaf] at h_adv_wins

private lemma probOutput_singleHash_eq_inv_card
    [SampleableType α] [Fintype α] [(spec α).Fintype] [(spec α).Inhabited]
    (a b root : α) :
    Pr[= root | (singleHash (m := OracleComp (spec α)) a b
                  : OracleComp (spec α) α)] =
      (Fintype.card α : ENNReal)⁻¹ := by
  have h : (singleHash (m := OracleComp (spec α)) a b : OracleComp (spec α) α) =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) := by
    change (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>= pure = _
    rw [bind_pure]
  rw [h, probOutput_query (spec := spec α) (a, b) root]
  congr!

private lemma probOutput_getPutativeRoot_eq_inv_card_of_pos_depth
    [SampleableType α] [Fintype α] [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {idx : SkeletonLeafIndex s} (h_pos : 0 < idx.depth)
    (leaf : α) (proof : List.Vector α idx.depth) (root : α) :
    Pr[= root | (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof
                  : OracleComp (spec α) α)] =
      (Fintype.card α : ENNReal)⁻¹ := by
  cases idx with
  | ofLeaf => exact absurd h_pos (Nat.lt_irrefl _)
  | @ofLeft sl sr idxLeft =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
              (SkeletonLeafIndex.ofLeft idxLeft) leaf proof
              : OracleComp (spec α) α) =
        (getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail) >>=
          fun a => (singleHash a proof.head : OracleComp (spec α) α) from rfl,
      probOutput_bind_eq_tsum]
    have key : ∀ a : α,
        Pr[= root | (singleHash (m := OracleComp (spec α)) a proof.head
                      : OracleComp (spec α) α)] = (Fintype.card α : ENNReal)⁻¹ :=
      fun a => probOutput_singleHash_eq_inv_card a proof.head root
    simp_rw [key]
    rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]
  | @ofRight sl sr idxRight =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
              (SkeletonLeafIndex.ofRight idxRight) leaf proof
              : OracleComp (spec α) α) =
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail) >>=
          fun a => (singleHash proof.head a : OracleComp (spec α) α) from rfl,
      probOutput_bind_eq_tsum]
    have key : ∀ a : α,
        Pr[= root | (singleHash (m := OracleComp (spec α)) proof.head a
                      : OracleComp (spec α) α)] = (Fintype.card α : ENNReal)⁻¹ :=
      fun a => probOutput_singleHash_eq_inv_card proof.head a root
    simp_rw [key]
    rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private lemma probEvent_verifyProof_eq_true_eq_inv_card_of_pos_depth
    [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {idx : SkeletonLeafIndex s} (h_pos : 0 < idx.depth)
    (leaf root : α) (proof : List.Vector α idx.depth) :
    Pr[(· = true) | (verifyProof (m := OracleComp (spec α)) idx leaf root proof
                      : OracleComp (spec α) Bool)] =
      (Fintype.card α : ENNReal)⁻¹ := by
  rw [show (verifyProof (m := OracleComp (spec α)) idx leaf root proof
              : OracleComp (spec α) Bool) =
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof) >>=
          fun r => (pure (r == root) : OracleComp (spec α) Bool) from rfl]
  rw [show (fun r : α => (pure (r == root) : OracleComp (spec α) Bool)) =
        pure ∘ (fun r : α => (r == root)) from rfl,
    probEvent_bind_pure_comp]
  have h_eq : ((fun b : Bool => b = true) ∘ (fun r : α => (r == root)) : α → Prop) =
      (fun r : α => r = root) := by
    funext r
    exact propext beq_iff_eq
  rw [h_eq, probEvent_eq_eq_probOutput]
  exact probOutput_getPutativeRoot_eq_inv_card_of_pos_depth h_pos leaf proof root

private lemma probEvent_verifyProof_extractor_none_le_inv_card
    [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} (idx : SkeletonLeafIndex s) (leaf root : α)
    (proof : List.Vector α idx.depth) (log_c : (spec α).QueryLog) :
    Pr[fun verified : Bool => verified = true ∧
         (extractor s log_c root).get idx.toNodeIndex = none |
       (verifyProof (m := OracleComp (spec α)) idx leaf root proof
         : OracleComp (spec α) Bool)] ≤
      (Fintype.card α : ENNReal)⁻¹ := by
  by_cases h_get : (extractor s log_c root).get idx.toNodeIndex = none
  · -- Extractor's path is broken: derive `0 < idx.depth` and apply verifyProof bound.
    have h_pos : 0 < idx.depth := by
      cases idx with
      | ofLeaf =>
        -- `s = Skeleton.leaf`, so `extractor` returns `FullData.leaf (some root)` and
        -- `.get .ofLeaf` is `some root`, contradicting `h_get`.
        exfalso
        change (some root : Option α) = none at h_get
        exact Option.some_ne_none _ h_get
      | ofLeft _ => exact Nat.succ_pos _
      | ofRight _ => exact Nat.succ_pos _
    refine (probEvent_mono'' (q := fun b : Bool => b = true) ?_).trans
      (probEvent_verifyProof_eq_true_eq_inv_card_of_pos_depth h_pos leaf root proof).le
    rintro _ ⟨h_v, _⟩; exact h_v
  · -- Extractor's path is intact: the bad event is impossible.
    refine probEvent_eq_zero ?_ |>.le.trans (zero_le _) |>.trans le_rfl
    rintro _ _ ⟨_, h⟩; exact h_get h

private theorem extractability_game_noColl_caseB_le_inv_card_aux
    {α : Type} [DecidableEq α] [SampleableType α] [Fintype α]
    [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} {AuxState : Type}
    (committingAdv : OracleComp (spec α) (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α)
          ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth))
    (qb : ℕ)
    (_h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (_h_card : 1 < (Fintype.card α : ENNReal)) :
    Pr[(fun x : (α × AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog =>
        let ⟨_, _, idx, _, _, extractedTree, _, verified⟩ := x.1
        verified = true ∧ extractedTree.get idx.toNodeIndex = none) |
      (extractability_game committingAdv openingAdv).withQueryLog] ≤
        (1 : ENNReal) / (Fintype.card α : ENNReal) := by
  rw [one_div]
  -- Step 1: Drop the outer log via `probEvent_withQueryLog`. We first convert
  -- `fun x => ... x.1 ...` to the equivalent `(fun vals => ...) ∘ Prod.fst`
  -- (defeq), then rewrite via the lemma.
  change Pr[((fun vals : α × AuxState ×
            ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
             FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) =>
            let ⟨_, _, idx, _, _, extractedTree, _, verified⟩ := vals
            verified = true ∧ extractedTree.get idx.toNodeIndex = none) ∘ Prod.fst) |
        (extractability_game committingAdv openingAdv).withQueryLog] ≤ _
  rw [probEvent_withQueryLog]
  -- Step 2: Restructure the game as a triple bind so we can decompose it via
  -- `probEvent_bind_le_of_forall_le`.
  rw [show extractability_game committingAdv openingAdv =
        committingAdv.withQueryLog >>= fun rootAuxLog =>
          openingAdv rootAuxLog.1.2 >>= fun ilp =>
            verifyProof ilp.1 ilp.2.1 rootAuxLog.1.1 ilp.2.2 >>= fun verified =>
              pure (rootAuxLog.1.1, rootAuxLog.1.2,
                ⟨ilp.1, ilp.2.1, ilp.2.2,
                 extractor s rootAuxLog.2 rootAuxLog.1.1,
                 generateProof (extractor s rootAuxLog.2 rootAuxLog.1.1) ilp.1,
                 verified⟩) by
        unfold extractability_game; rfl]
  -- Step 3: peel off `committingAdv.withQueryLog`.
  refine probEvent_bind_le_of_forall_le ?_
  rintro ⟨⟨root, aux⟩, log_c⟩ _
  -- Peel off `openingAdv aux`.
  refine probEvent_bind_le_of_forall_le ?_
  rintro ⟨idx, leaf, proof⟩ _
  -- Inner: `verifyProof idx leaf root proof >>= fun verified => pure (...)`.
  -- Reshape the pure as `pure ∘ wrap_verified` and apply `probEvent_bind_pure_comp`.
  rw [show (fun verified : Bool =>
        (pure (root, aux,
          ⟨idx, leaf, proof, extractor s log_c root,
           generateProof (extractor s log_c root) idx, verified⟩) :
          OracleComp (spec α) (α × AuxState ×
            ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
             FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)))) =
        pure ∘ (fun verified : Bool => (root, aux,
          ⟨idx, leaf, proof, extractor s log_c root,
           generateProof (extractor s log_c root) idx, verified⟩)) from rfl]
  rw [probEvent_bind_pure_comp]
  -- The composed event simplifies to `verified = true ∧ extractor.get = none`.
  exact probEvent_verifyProof_extractor_none_le_inv_card idx leaf root proof log_c

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
        qb) :
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
  · rintro ⟨⟨_, _, _, _, _, _, _, _⟩, _⟩ ⟨_, ⟨h_v, _⟩, h_extract_none⟩
    exact ⟨h_v, h_extract_none⟩
  by_cases h_card : (Fintype.card α : ENNReal) ≤ 1
  · refine probEvent_le_one.trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top)]
    simpa using h_card
  · exact extractability_game_noColl_caseB_le_inv_card_aux
      committingAdv openingAdv qb h_IsQueryBound_qb (not_le.mp h_card)

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
        qb) :
    Pr[fun (vals, log) =>
        ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals |
      (extractability_game committingAdv openingAdv).withQueryLog] ≤
        (1 : ENNReal) / (Fintype.card α : ENNReal) := by
  -- Trivially handle the small-cardinality cases where the bound `1/|α|` is
  -- already `≥ 1`, so `Pr[…] ≤ 1` (via `probEvent_le_one`) suffices. This isolates
  -- the substantive work to `Fintype.card α ≥ 2`.
  by_cases h_card : (Fintype.card α : ENNReal) ≤ 1
  · refine probEvent_le_one.trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top)]
    simpa using h_card
  -- Rewrite the bad event as `caseA ∨ caseB`, apply union bound, dispatch to sub-lemmas.
  calc Pr[fun (vals, log) =>
            ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals |
            (extractability_game committingAdv openingAdv).withQueryLog]
      = Pr[fun x => noColl_caseA_event x ∨ noColl_caseB_event x |
            (extractability_game committingAdv openingAdv).withQueryLog] := by
        rw [funext fun x => propext (noColl_bad_iff_caseA_or_caseB x)]
    _ ≤ Pr[noColl_caseA_event |
            (extractability_game committingAdv openingAdv).withQueryLog] +
        Pr[noColl_caseB_event |
            (extractability_game committingAdv openingAdv).withQueryLog] :=
        probEvent_or_le ..
    _ ≤ 0 + (1 : ENNReal) / (Fintype.card α : ENNReal) := by
        gcongr
        · exact (extractability_game_noColl_caseA_eq_zero committingAdv openingAdv
            qb h_IsQueryBound_qb).le
        · exact extractability_game_noColl_caseB_le_inv_card committingAdv openingAdv
            qb h_IsQueryBound_qb
    _ = (1 : ENNReal) / (Fintype.card α : ENNReal) := zero_add _

private theorem extractability_game_noCollision_wins_le
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
        qb) :
    Pr[fun (vals, log) =>
        ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals |
      (extractability_game committingAdv openingAdv).withQueryLog] ≤
        1 / (Fintype.card α : ENNReal) := by
  refine le_trans
    (extractability_game_noCollision_wins_le_inv_card committingAdv openingAdv
      qb h_IsQueryBound_qb) ?_
  apply ENNReal.div_le_div_right
  grind

/--
The extractability theorem for Merkle trees.

Adapting from the SNARGs book Lemma 18.5.1:

For any adversary `committingAdv` that outputs a root and auxiliary data,
and any `openingAdv` that takes the auxiliary data and outputs a leaf index, leaf value, and proof,
such that committingAdv and openingAdv together obey the query bound `qb`.
If the `committingAdv` and `openingAdv` are executed, and the `extractor` algorithm is run on the
resulting cache and root from `committingAdv`,
then with probability at most κ does the adversary "win the extractability game"
i.e. simultaneously

* the merkle tree verification passes on the proof from `openingAdv`
* but the extracted (leaf value, proof) pair
  does not match the adversary's (leaf value, proof pair)

Where κ is 1/|α| * ((qb + s.depth)^2 / 2 + 1).
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
        qb) :
    Pr[adversary_wins_extractability_game_event |
        extractability_game committingAdv openingAdv] ≤
        ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α)
        + 1 / (Fintype.card α)
    := by
  calc
    -- We first rewrite the game to include the combined query log
    _ = Pr[adversary_wins_extractability_game_with_logging_event |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      simp only [adversary_wins_extractability_game_with_logging_event]
      rw [probEvent_withQueryLog]
    -- The bad event happens only when there is a collision event
    -- or the bad event happens with no collision
    _ ≤ Pr[fun (vals, log) =>
            LogHasCollision log ∨
            (¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals) |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      refine probEvent_mono'' fun ⟨vals, log⟩ => ?_
      simp [adversary_wins_extractability_game_with_logging_event]
      tauto
    -- We apply the union bound
    _ ≤ Pr[fun (vals, log) => LogHasCollision log |
            (extractability_game committingAdv openingAdv).withQueryLog] +
        Pr[fun (vals, log) =>
            ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] :=
      probEvent_or_le ..
    -- We bound the collision event probability with a birthday bound
    _ ≤ ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α) +
        Pr[fun (vals, log) =>
            ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] := by
      gcongr
      have hbound := OracleComp.probEvent_logCollision_le_birthday_total (spec := spec α)
        (extractability_game committingAdv openingAdv) (qb + s.depth)
        (extractability_game_IsTotalQueryBound committingAdv openingAdv qb h_IsQueryBound_qb)
        (fun t => by
          have heq : (spec α).Range default = (spec α).Range t := rfl
          exact (Fintype.card_congr (Equiv.cast heq)).le)
      convert hbound using 2
      push_cast
      rfl
    -- We bound the no-collision bad event probability
    _ ≤ ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α) +
        1 / (Fintype.card α) := by
      have h' : Pr[fun (vals, log) =>
            ¬ LogHasCollision log ∧ adversary_wins_extractability_game_event vals |
          (extractability_game committingAdv openingAdv).withQueryLog] ≤
            1 / (Fintype.card α : ENNReal) :=
        mod_cast extractability_game_noCollision_wins_le committingAdv openingAdv
          (s := s) (AuxState := AuxState) qb h_IsQueryBound_qb
      gcongr
      norm_cast

end InductiveMerkleTree
