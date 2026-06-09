/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.QueryBound
import VCVio.OracleComp.QueryTracking.Birthday
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Inductive Merkle Tree Extractability

This file develops extractability for the inductive Merkle tree commitment scheme. The
extractor reconstructs a partial tree from the committing adversary's query log and the
opened root, and the main theorem bounds the probability that an adversary opens a leaf
that disagrees with the extracted tree.

## Main definitions

We make several definitions to set up and analyze the extractability game
under namespace `InductiveMerkleTree`:

* `Adversary`: a two-phase Merkle tree adversary, bundling an auxiliary state type, a
  committing phase producing a claimed root and state, and an opening phase producing a
  (leaf index, leaf value, authentication path) triple from that state.
* `extractor`: builds a `FullData (Option α) s` from a query log, root, and skeleton by
  walking down from the root and pulling each node's children from the unique log entry
  whose response matches.
* `extractabilityGame`: the bundled game running a `Adversary` against the extractor
  and verifier, recording the verifier's outcome along with the extracted tree and proof.
* `ChainInLog`: structural predicate witnessing that a query log contains the hash chain
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

## TODO

- The lemmas here all specialize to `(m := OracleComp (spec α))` because the proofs rely
  on `OracleComp`-specific machinery — `withQueryLog`, `support`, `probEvent`, and the
  `ChainInLog log` predicate over a concrete `QueryLog`. Generalizing them to an arbitrary
  monad `m` (so they apply to e.g. `SimulateQ` without re-proving) would first require a
  generic "computation-with-query-log" interface at the framework level,
  but might be good at some point.

## References

* [Building Cryptographic Proofs from Hash Functions by Chiesa and Yogev](https://snargsbook.org/), Lemma 18.5.1.

-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/-- Local `IsUniformSpec` opt-in for `spec α`: the single Merkle hash oracle samples
uniformly from `α` whenever `α` is finite and inhabited. Kept `local` so that downstream
files outside this module do not silently pick up uniform semantics for `spec α`. -/
noncomputable local instance instIsUniformSpec [Fintype α] [Inhabited α] :
    IsUniformSpec (spec α) := IsUniformSpec.ofFintypeInhabited _

/-! ## Adversary -/

section Adversary

/-- An adversary in the Merkle tree extractability game, packaged as a single
two-phase object: a committing phase that produces a claimed root together with
auxiliary state, and an opening phase that consumes the auxiliary state to
produce a (leaf index, leaf value, authentication path) triple. -/
structure Adversary (α : Type) (s : Skeleton) where
  /-- Auxiliary state carried from the committing phase to the opening phase. -/
  AuxState : Type
  /-- Committing phase: produce a claimed root and auxiliary state. -/
  commit : OracleComp (spec α) (α × AuxState)
  /-- Opening phase: given the auxiliary state, produce a leaf index, claimed
  leaf value, and authentication path. -/
  opening : AuxState →
      OracleComp (spec α)
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)

/-- The combined two-phase execution of `𝒜` has total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton}
    (𝒜 : Adversary α s) (qb : ℕ) : Prop :=
  IsTotalQueryBound
    (do
      let (_root, aux) ← 𝒜.commit
      let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
      pure ())
    qb

end Adversary

/-! ## Extractability game -/

section ExtractabilityGame

variable [DecidableEq α]

/--
The child-decomposition function used by the Merkle-tree `extractor`. Given a `cache`
and a node value `a`, look up the first query in `cache` whose response is `a` and return
its input pair; if no such entry exists, return `none`.
-/
def extractorChildren
    (cache : (spec α).QueryLog) (a : α) : Option (α × α) :=
  match cache.find? (fun ⟨_, r⟩ => r == a) with
  | none => none
  | some ⟨(x, y), _⟩ => some (x, y)

/--
The extraction algorithm for Merkle trees: from a query log `cache`, a `root`, and a
skeleton `s`, build a partial tree of type `FullData (Option α) s` by walking down from
`root`. A node with value `some a` looks up the unique log entry whose response is `a`
and uses its input pair as the children's values; in every other case (no matching entry,
or the parent is already `none`) both children are `none`. Implemented as
`optionPopulateDown` driven by `extractorChildren`.
-/
def extractor
    (s : Skeleton) (cache : (spec α).QueryLog) (root : α) :
    FullData (Option α) s :=
  optionPopulateDown s (extractorChildren cache) root

/--
The game for extractability.

This is represented as a single `OracleComp`
that runs the committing adversary, extractor, opening adversary, and verifier in sequence and
returns the transcript of the execution.
-/
def extractabilityGame
    {s : Skeleton}
    (𝒜 : Adversary α s) :
    OracleComp (spec α)
      (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  do
    let ((root, aux), queryLog) ← 𝒜.commit.withQueryLog
    let extractedTree := extractor s queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedProof := generateProof extractedTree idx
    let verified ← verifyProof idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩)

/--
The event that the adversary wins the extractability game:
verification passes but the extracted leaf or proof does not match.
-/
def AdversaryWinsExtractabilityGame {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop
  | (_, _, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) =>
    verified ∧
    (not (leaf = extractedTree.get idx.toNodeIndex)
    ∨ not (proof.toList.map Option.some = extractedProof.toList))

/-- If the query log's first entry with response `root` is the pair `⟨(x, y), root⟩`,
then the extractor at an internal skeleton unfolds to that node's two children using
`x` and `y` as the new "ancestor" values for the left and right subtrees. -/
private lemma extractor_internal_eq_of_find?_eq
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root x y : α)
    (h_find : log.find? (fun ⟨_, r⟩ => r == root) =
                some ⟨(x, y), root⟩) :
    extractor (Skeleton.internal sl sr) log root =
      FullData.internal (some root) (extractor sl log x) (extractor sr log y) := by
  have h_children : extractorChildren log root = some (x, y) := by
    change (match log.find? _ with | none => none | some ⟨(x, y), _⟩ => some (x, y)) = _
    rw [h_find]
  simp only [extractor]
  rw [optionPopulateDown_internal, h_children]
  rfl

/--
Unfold `extractabilityGame` into a nested `bind` whose outer prefix logs the committing
adversary's queries alongside the opening adversary's output, and whose continuation runs
`verifyProof` and assembles the transcript. This is the definitional rearrangement used to
expose the prefix as a target for query-bound reasoning.
-/
private lemma extractabilityGame_eq_bind_verifyProof
    {s : Skeleton} (𝒜 : Adversary α s) :
    extractabilityGame 𝒜 =
      (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
        𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) >>=
      fun (⟨⟨root, aux⟩, queryLog⟩, ⟨idx, leaf, proof⟩) =>
        verifyProof idx leaf root proof >>= fun verified =>
          pure (root, aux,
                ⟨idx, leaf, proof,
                 extractor s queryLog root,
                 generateProof (extractor s queryLog root) idx,
                 verified⟩) := by
  unfold extractabilityGame
  simp only [bind_assoc, pure_bind]

omit [DecidableEq α] in
/--
Project the logged-prefix of `extractabilityGame` onto `Unit`: discarding both the
committed root/aux and the query log of the committing adversary recovers the plain
measurement used to express the combined query bound.
-/
private lemma extractabilityGame_logged_prefix_map_unit_eq
    {s : Skeleton} (𝒜 : Adversary α s) :
    (fun _ => ()) <$>
        (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
          𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) =
      (do let (_root, aux) ← 𝒜.commit
          let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
          pure ()) := by
  simpa [map_bind, map_pure] using loggingOracle.run_simulateQ_bind_fst 𝒜.commit
    (fun (_, aux) => 𝒜.opening aux >>= fun _ => pure ())

/--
If the adversary `𝒜` has two-phase total query bound `qb`, then the full extractability
game has total query bound `qb + s.depth`.

The extra `s.depth` accounts for the `verifyProof` step, which traverses the path from the
queried leaf to the root, making at most `s.depth` oracle queries.
-/
theorem extractabilityGame_isTotalQueryBound
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityGame 𝒜) (qb + s.depth) := by
  rw [extractabilityGame_eq_bind_verifyProof]
  refine isTotalQueryBound_bind (n₁ := qb) (n₂ := s.depth) ?_
    fun (⟨⟨root, _aux⟩, _queryLog⟩, ⟨idx, leaf, proof⟩) =>
      isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
        (verifyProof_isTotalQueryBound_skeleton_depth idx leaf root proof) (fun _ => trivial)
  exact (isQueryBound_iff_of_map_eq
      (extractabilityGame_logged_prefix_map_unit_eq 𝒜)
      (fun _ b => 0 < b) (fun _ b => b - 1)).mpr h

private lemma extractorChildren_eq_none_of_find?_eq_none
    {log_c : (spec α).QueryLog} {a : α}
    (hf : log_c.find? (fun ⟨_, r⟩ => r == a) = none) :
    extractorChildren log_c a = none := by
  change (match log_c.find? _ with | none => none | some ⟨(x, y), _⟩ => some (x, y)) = none
  rw [hf]

/--
If a particular transcript is in the support of the extractability game with the query log,
then the log has subsets `log_c` (containing the committing adversary's queries)
and `log_v` (containing the verifier's queries),
such that the proof verification step passes emitting `log_v`,
and the extractor and proof generation steps `log_c`
yield the same extracted tree and proof as the transcript.
-/
private lemma extractabilityGame_support_decompose
    {s : Skeleton} (𝒜 : Adversary α s)
    {root : α} {aux : 𝒜.AuxState} {idx : SkeletonLeafIndex s} {leaf : α}
    {proof : List.Vector α idx.depth}
    {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth}
    {log : (spec α).QueryLog}
    (hsup : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractabilityGame 𝒜).withQueryLog) :
    ∃ log_c log_v : (spec α).QueryLog,
      (true, log_v) ∈ support
          (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog ∧
      (∀ q, q ∈ log_v → q ∈ log) ∧
      (∀ q, q ∈ log_c → q ∈ log) ∧
      extractedTree = extractor s log_c root ∧
      extractedProof = generateProof (extractor s log_c root) idx := by
  unfold extractabilityGame at hsup
  simp only [OracleComp.withQueryLog_bind, mem_support_bind_iff, support_map,
    Set.mem_image] at hsup
  obtain ⟨⟨⟨root_c, aux_c⟩, log_c⟩, h_c, ⟨_, _⟩,
    ⟨⟨⟨idx_o, leaf_o, proof_o⟩, _⟩, _, ⟨_, _⟩,
      ⟨⟨_, log_v⟩, h_vp, ⟨_, _⟩, h_p, h_eq_p⟩, h_eq_v⟩, h_eq_co⟩ := hsup
  rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_p
  obtain ⟨h_p1, rfl⟩ := h_p
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_co h_eq_v h_eq_p
  obtain ⟨h_eq_co1, h_eq_co2⟩ := h_eq_co
  obtain ⟨h_eq_v1, h_eq_v2⟩ := h_eq_v
  obtain ⟨h_eq_p1, h_eq_p2⟩ := h_eq_p
  rw [← h_eq_v1, ← h_eq_p1, h_p1] at h_eq_co1
  simp only [Prod.mk.injEq] at h_eq_co1
  obtain ⟨rfl, rfl, h_sigma_eq⟩ := h_eq_co1
  obtain ⟨rfl, h_rest_eq⟩ := Sigma.mk.inj h_sigma_eq
  simp only [heq_eq_eq, Prod.mk.injEq] at h_rest_eq
  obtain ⟨rfl, rfl, h_tree_eq, h_proof_ext_eq, rfl⟩ := h_rest_eq
  rw [OracleComp.withQueryLog_self_log_eq 𝒜.commit h_c] at h_tree_eq h_proof_ext_eq
  refine ⟨log_c, log_v, h_vp, fun q hq => ?_, fun q hq => ?_,
    h_tree_eq.symm, h_proof_ext_eq.symm⟩ <;>
    rw [← h_eq_co2, ← h_eq_v2, ← h_eq_p2]
  · grind [List.mem_append_right, List.mem_append_left]
  · grind [List.mem_append_left]

/--
If `root` is not the response of any query in `log`,
then the extractor at an internal skeleton is `none`.
-/
private lemma extractor_internal_get_eq_none_of_find?_eq_none
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root : α)
    (idx : SkeletonNodeIndex sl ⊕ SkeletonNodeIndex sr)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = none) :
    (extractor (Skeleton.internal sl sr) log root).get
        (idx.elim SkeletonNodeIndex.ofLeft SkeletonNodeIndex.ofRight) = none := by
  simp only [extractor]
  rw [optionPopulateDown_internal, extractorChildren_eq_none_of_find?_eq_none hf]
  cases idx <;>
    exact populateDown_none_get_eq_none (Option.bindPair (extractorChildren log)) rfl _

end ExtractabilityGame

private lemma singleHash_withQueryLog
    (a b : α) :
    (singleHash (m := OracleComp (spec α)) a b).withQueryLog =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>=
        fun u => pure (u, ([⟨(a, b), u⟩] : (spec α).QueryLog)) := by
  have h : (singleHash (m := OracleComp (spec α)) a b) =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) := by
    change liftM ((spec α).query (a, b)) >>= pure = _
    rw [bind_pure]
  rw [h, OracleComp.withQueryLog_query]

private lemma getPutativeRoot_step_withQueryLog_decompose
    (prog : OracleComp (spec α) α) (mkPair : α → α × α)
    (r : α) (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
      (prog >>= fun a => let (l, r') := mkPair a; singleHash l r').withQueryLog) :
    ∃ a log_a, (a, log_a) ∈ support prog.withQueryLog
      ∧ log_v = log_a ++ [⟨mkPair a, r⟩] := by
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨a, log_a⟩, h_rec, hmem⟩ := hmem
  rw [singleHash_withQueryLog, support_map, Set.mem_image] at hmem
  obtain ⟨⟨_, _⟩, h_q, h_eq2⟩ := hmem
  rw [mem_support_bind_iff] at h_q
  obtain ⟨_, _, h_pure⟩ := h_q
  obtain ⟨rfl, rfl⟩ := h_pure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq2
  exact ⟨a, log_a, h_rec, rfl⟩

/--
Predicate stating that `log` contains a hash chain from `leaf` (combined with the
sibling values in `proof`) up to `root` along the path determined by `idx`.
-/
def ChainInLog {s : Skeleton} (log : (spec α).QueryLog) (leaf root : α) :
    (idx : SkeletonLeafIndex s) → List.Vector α idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : α,
        (⟨(ancestor, proof.head), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : α,
        (⟨(proof.head, ancestor), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxRight proof.tail

private lemma chainInLog_mono {s : Skeleton} (idx : SkeletonLeafIndex s)
    {log1 log2 : (spec α).QueryLog} {root leaf : α}
    {proof : List.Vector α idx.depth}
    (h_sub : ∀ q, q ∈ log1 → q ∈ log2)
    (h_chain : ChainInLog log1 leaf root idx proof) :
    ChainInLog log2 leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact h_chain
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, h_mem, h_rec⟩ := h_chain
    exact ⟨ancestor, h_sub _ h_mem, ih h_rec⟩

private lemma chainInLog_of_mem_support_getPutativeRoot
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) (r : α)
    (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof).withQueryLog) :
    ChainInLog log_v leaf r idx proof := by
  induction idx generalizing r log_v with
  | ofLeaf =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
        SkeletonLeafIndex.ofLeaf leaf proof) = pure leaf from rfl,
      OracleComp.withQueryLog_pure, mem_support_pure_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    simp only [ChainInLog]
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail)
        (fun a => (a, proof.head)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail)
        (fun a => (proof.head, a)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩

/--
If a particular transcript is in the support of a successful `verifyProof` computation
with the query log,
then that log contains a hash chain from `root` down to `leaf`.
-/
private lemma chainInLog_of_mem_support_verifyProof
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (log_v : (spec α).QueryLog)
    (hmem : (true, log_v) ∈ support
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog) :
    ChainInLog log_v leaf root idx proof := by
  rw [show verifyProof (m := OracleComp (spec α)) idx leaf root proof =
      (do let r ← getPutativeRoot (m := OracleComp (spec α)) idx leaf proof
          pure (r == root)) from rfl,
    OracleComp.withQueryLog_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨r, log_g⟩, h_g, hmem⟩ := hmem
  rw [support_map, Set.mem_image] at hmem
  obtain ⟨⟨b, log_x⟩, h_x, h_eq⟩ := hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
  obtain ⟨h_b_eq, rfl⟩ := Prod.mk.inj h_x
  obtain rfl : r = root := by grind
  have := chainInLog_of_mem_support_getPutativeRoot idx leaf proof r log_g h_g
  grind

/-- **Log-level binding (Collision Lemma at the log level).** Log-formalized
analog of `getPutativeRootWithHash_binding_collision`: two distinct openings
`(x, proof₁) ≠ (y, proof₂)` of the same `root` at the same index, both
witnessed by hash chains `ChainInLog` in the same `log`, force `log` to
contain a hash collision (two log entries with equal responses but distinct
inputs). -/
theorem logHasCollision_of_chainInLog_of_ne
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root x y : α)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (hne : (x, proof₁) ≠ (y, proof₂))
    (hc₁ : ChainInLog log x root idx proof₁)
    (hc₂ : ChainInLog log y root idx proof₂) :
    LogHasCollision log := by
  induction idx generalizing root x y with
  | ofLeaf =>
    exact absurd (Prod.ext (hc₁.trans hc₂.symm) (List.Vector.ext (fun i => i.elim0))) hne
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (a₁, proof₁.head) = (a₂, proof₂.head)
    · obtain ⟨rfl, hhead⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact congrArg (Prod.mk _) <| by
        rw [← proof₁.cons_head_tail, ← proof₂.cons_head_tail]
        exact congr (congrArg _ hhead) htail
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (proof₁.head, a₁) = (proof₂.head, a₂)
    · obtain ⟨hhead, rfl⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact congrArg (Prod.mk _) <| by
        rw [← proof₁.cons_head_tail, ← proof₂.cons_head_tail]
        exact congr (congrArg _ hhead) htail
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)

/-- Post-IH assembly for the `ofLeft` case of `chainInLog_of_extractor_get_ne_none`.
Given a recursive witness on the left subtree (with ancestor `x`), repackage it
into the witness for the full internal node, using the log entry `⟨(x, y), root⟩`
and consing the sibling `y` onto the extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_left
    [DecidableEq α]
    {sl sr : Skeleton} (idxLeft : SkeletonLeafIndex sl)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxLeft.depth,
        (extractor sl log x).get idxLeft.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sl log x) idxLeft).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf x idxLeft extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofLeft (right := sr) idxLeft) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  have h_decomp := extractor_internal_eq_of_find?_eq sl sr log root x y hf
  rw [h_decomp]
  refine ⟨extLeaf, y ::ᵥ extProof, h_extLeaf, ?_, x, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sr log y).getRootValue = some y :=
    optionPopulateDown_getRootValue _ _
  change ((extractor sr log y).getRootValue ::ᵥ
      generateProof (extractor sl log x) idxLeft).toList =
    map some (y ::ᵥ extProof).toList
  rw [h_root_value]
  change some y :: (generateProof (extractor sl log x) idxLeft).toList =
    some y :: map some extProof.toList
  exact congrArg (fun proof => some y :: proof) h_extProof

/-- Post-IH assembly for the `ofRight` case of `chainInLog_of_extractor_get_ne_none`.
Symmetric to `chainInLog_of_extractor_internal_step_left`: the recursive witness
lives on the right subtree (ancestor `y`) and the sibling `x` is consed onto the
extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_right
    [DecidableEq α]
    {sl sr : Skeleton} (idxRight : SkeletonLeafIndex sr)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxRight.depth,
        (extractor sr log y).get idxRight.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sr log y) idxRight).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf y idxRight extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofRight (left := sl) idxRight).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofRight (left := sl) idxRight).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofRight (left := sl) idxRight)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofRight (left := sl) idxRight) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  have h_decomp := extractor_internal_eq_of_find?_eq sl sr log root x y hf
  rw [h_decomp]
  refine ⟨extLeaf, x ::ᵥ extProof, h_extLeaf, ?_, y, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sl log x).getRootValue = some x :=
    optionPopulateDown_getRootValue _ _
  change ((extractor sl log x).getRootValue ::ᵥ
      generateProof (extractor sr log y) idxRight).toList =
    map some (x ::ᵥ extProof).toList
  rw [h_root_value]
  change some x :: (generateProof (extractor sr log y) idxRight).toList =
    some x :: map some extProof.toList
  exact congrArg (fun proof => some x :: proof) h_extProof

/-- **Extractor recovery to a log chain.** When the extractor's path at `idx`
is intact (the value there is `≠ none`), the extracted leaf value and proof
form a hash chain `ChainInLog` in the log. The conclusion bundles three
facts: the extracted leaf (`extLeaf`), the recovered authentication path
(`extProof`), and a chain witness in `log` connecting them to `root`. -/
theorem chainInLog_of_extractor_get_ne_none
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root : α)
    (h_ne_none : (extractor s log root).get idx.toNodeIndex ≠ none) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α idx.depth,
      (extractor s log root).get idx.toNodeIndex = some extLeaf ∧
      (generateProof (extractor s log root) idx).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root idx extProof := by
  induction idx generalizing root with
  | ofLeaf => exact ⟨root, ⟨[], rfl⟩, rfl, rfl, rfl⟩
  | @ofLeft sl sr idxLeft ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inl idxLeft.toNodeIndex) hf) h_ne_none
    have hr : r = root := by grind [find?_eq_some_iff_getElem]
    rw [hr] at hf
    exact chainInLog_of_extractor_internal_step_left idxLeft log root x y hf
      (ih x (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))
  | @ofRight sl sr idxRight ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inr idxRight.toNodeIndex) hf) h_ne_none
    have hr : r = root := by grind [find?_eq_some_iff_getElem]
    rw [hr] at hf
    exact chainInLog_of_extractor_internal_step_right idxRight log root x y hf
      (ih y (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))

private theorem extractabilityGame_not_logHasCollision_match
    [DecidableEq α]
    {s : Skeleton} (𝒜 : Adversary α s)
    {root : α} {aux : 𝒜.AuxState} {idx : SkeletonLeafIndex s} {leaf : α}
    {proof : List.Vector α idx.depth}
    {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth}
    {log : (spec α).QueryLog}
    (h_not_logHasCollision : ¬ LogHasCollision log)
    (h_ne_none : extractedTree.get idx.toNodeIndex ≠ none)
    (hsupport : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractabilityGame 𝒜).withQueryLog) :
    extractedTree.get idx.toNodeIndex = some leaf ∧
      proof.toList.map some = extractedProof.toList := by
  obtain ⟨log_c, log_v, h_vp, h_sub_v, h_sub_c, h_tree_eq, h_proof_ext_eq⟩ :=
    extractabilityGame_support_decompose 𝒜 hsupport
  have h_chain_log : ChainInLog log leaf root idx proof :=
    chainInLog_mono idx h_sub_v
      (chainInLog_of_mem_support_verifyProof idx leaf root proof log_v h_vp)
  obtain ⟨extLeaf, extProof, h_extLeaf_eq, h_extProof_eq, h_extChain_lc⟩ :=
    chainInLog_of_extractor_get_ne_none idx log_c root (h_tree_eq ▸ h_ne_none)
  by_cases hpair : (extLeaf, extProof) = (leaf, proof)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact ⟨h_tree_eq.symm ▸ h_extLeaf_eq, by rw [h_proof_ext_eq, h_extProof_eq]⟩
  · exact absurd (logHasCollision_of_chainInLog_of_ne idx log root extLeaf leaf
      extProof proof hpair (chainInLog_mono idx h_sub_c h_extChain_lc) h_chain_log)
      h_not_logHasCollision

/--
The probability that a single hash evaluates to a specific root value
(without any prior queries)
is the reciprocal of the range size.
-/
private lemma probOutput_singleHash_eq_inv_card
    [Fintype α] [Inhabited α]
    (a b root : α) :
    Pr[= root | (singleHash (m := OracleComp (spec α)) a b
                  : OracleComp (spec α) α)] =
      (Fintype.card α : ENNReal)⁻¹ := by
  have h : (singleHash (m := OracleComp (spec α)) a b : OracleComp (spec α) α) =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) := by
    change (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>= pure = _
    rw [bind_pure]
  rw [h, probOutput_query (spec := spec α) (a, b) root]

/--
The probability that `getPutativeRoot` evaluates to a specific root value at a positive-depth index
(without any prior queries) is the reciprocal of the range size.
-/
private lemma probOutput_getPutativeRoot_eq_inv_card_of_pos_depth
    [Fintype α] [Inhabited α]
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
    simp_rw [fun a => probOutput_singleHash_eq_inv_card a proof.head root,
      ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  | @ofRight sl sr idxRight =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
              (SkeletonLeafIndex.ofRight idxRight) leaf proof
              : OracleComp (spec α) α) =
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail) >>=
          fun a => (singleHash proof.head a : OracleComp (spec α) α) from rfl,
      probOutput_bind_eq_tsum]
    simp_rw [fun a => probOutput_singleHash_eq_inv_card proof.head a root,
      ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

/--
The probability that `verifyProof` evaluates to `true` at a positive-depth index
(without any prior queries) is the reciprocal of the range size.
-/
private lemma probEvent_verifyProof_eq_true_eq_inv_card_of_pos_depth
    [DecidableEq α] [Fintype α] [Inhabited α]
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
    [DecidableEq α] [Fintype α] [Inhabited α]
    {s : Skeleton} (idx : SkeletonLeafIndex s) (leaf root : α)
    (proof : List.Vector α idx.depth) (log_c : (spec α).QueryLog) :
    Pr[fun verified : Bool => verified = true ∧
         (extractor s log_c root).get idx.toNodeIndex = none |
       (verifyProof (m := OracleComp (spec α)) idx leaf root proof
         : OracleComp (spec α) Bool)] ≤
      (Fintype.card α : ENNReal)⁻¹ := by
  by_cases h_get : (extractor s log_c root).get idx.toNodeIndex = none
  · have h_pos : 0 < idx.depth := by
      cases idx with
      | ofLeaf =>
        exfalso
        exact Option.some_ne_none _ h_get
      | ofLeft _ => exact Nat.succ_pos _
      | ofRight _ => exact Nat.succ_pos _
    refine (probEvent_mono'' (q := fun b : Bool => b = true) ?_).trans
      (probEvent_verifyProof_eq_true_eq_inv_card_of_pos_depth h_pos leaf root proof).le
    rintro _ ⟨h_v, _⟩; exact h_v
  · refine probEvent_eq_zero ?_ |>.le.trans (zero_le)
    rintro _ _ ⟨_, h⟩; exact h_get h

private theorem extractabilityGame_verified_extractor_none_le_inv_card
    [DecidableEq α] [Fintype α] [Inhabited α]
    {s : Skeleton} (𝒜 : Adversary α s) :
    Pr[(fun x : (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) ×
      (spec α).QueryLog =>
        let ⟨⟨_, _, idx, _, _, extractedTree, _, verified⟩, _⟩ := x
        verified = true ∧ extractedTree.get idx.toNodeIndex = none) |
      (extractabilityGame 𝒜).withQueryLog] ≤
        (1 : ENNReal) / (Fintype.card α : ENNReal) := by
  rw [one_div]
  change Pr[((fun vals : α × 𝒜.AuxState ×
            ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
             FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) =>
            let ⟨_, _, idx, _, _, extractedTree, _, verified⟩ := vals
            verified = true ∧ extractedTree.get idx.toNodeIndex = none) ∘ Prod.fst) |
        (extractabilityGame 𝒜).withQueryLog] ≤ _
  rw [probEvent_withQueryLog,
    show extractabilityGame 𝒜 = (do
        let ((root, aux), queryLog) ← 𝒜.commit.withQueryLog
        let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
        let verified ← verifyProof idx leaf root proof
        pure (root, aux,
          ⟨idx, leaf, proof,
           extractor s queryLog root,
           generateProof (extractor s queryLog root) idx,
           verified⟩)) by unfold extractabilityGame; rfl]
  refine probEvent_bind_le_of_forall_le fun ⟨⟨root, aux⟩, log_c⟩ _ => ?_
  refine probEvent_bind_le_of_forall_le fun ⟨idx, leaf, proof⟩ _ => ?_
  dsimp only
  rw [show (fun verified : Bool => pure (root, aux, _) :
        Bool → OracleComp (spec α) _) = pure ∘ _ from rfl, probEvent_bind_pure_comp]
  exact probEvent_verifyProof_extractor_none_le_inv_card idx leaf root proof log_c

private theorem extractabilityGame_not_logHasCollision_wins_le_inv_card
    [DecidableEq α] [Fintype α] [Inhabited α]
    {s : Skeleton} (𝒜 : Adversary α s) :
    Pr[fun (vals, log) =>
        ¬ LogHasCollision log ∧ AdversaryWinsExtractabilityGame vals |
      (extractabilityGame 𝒜).withQueryLog] ≤
        (1 : ENNReal) / (Fintype.card α : ENNReal) := by
  refine le_trans (probEvent_mono ?_)
    (extractabilityGame_verified_extractor_none_le_inv_card 𝒜)
  rintro ⟨vals, log⟩ hsupport ⟨h_not_logHasCollision, h_adv_wins⟩
  obtain ⟨root, aux, idx, leaf, proof, extractedTree, extractedProof, verified⟩ := vals
  obtain ⟨rfl, h_disagree⟩ := h_adv_wins
  refine ⟨rfl, ?_⟩
  by_contra h_ne_none
  obtain ⟨h_eq_leaf, h_map⟩ :=
    extractabilityGame_not_logHasCollision_match 𝒜
      h_not_logHasCollision h_ne_none hsupport
  simp [h_map, h_eq_leaf] at h_disagree

/--
The extractability theorem for Merkle trees.

Adapting from the SNARGs book Lemma 18.5.1:

For any adversary `𝒜` whose committing and opening phases together obey the two-phase total
query bound `qb`, if the game runs `𝒜.commit` and `𝒜.opening`, and the `extractor` algorithm
is run on the resulting cache and root, then with probability at most κ does `𝒜` "win the
extractability game", i.e. simultaneously

* the merkle tree verification passes on the proof from `𝒜.opening`
* but the extracted (leaf value, proof) pair
  does not match the adversary's (leaf value, proof) pair

Where κ is 1/|α| * ((qb + s.depth)^2 / 2 + 1).
-/
theorem extractability [DecidableEq α] [Fintype α] [Inhabited α]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h_IsQueryBound_qb : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame |
        extractabilityGame 𝒜] ≤
        ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α)
        + 1 / (Fintype.card α)
    := by
  calc
    -- Rewrite the game to include the combined query log.
    _ = Pr[AdversaryWinsExtractabilityGame ∘ Prod.fst |
          (extractabilityGame 𝒜).withQueryLog] :=
      (probEvent_withQueryLog _ _).symm
    -- Split: bad event implies collision, or no-collision with bad event.
    _ ≤ Pr[fun (vals, log) =>
            LogHasCollision log ∨
            (¬ LogHasCollision log ∧ AdversaryWinsExtractabilityGame vals) |
          (extractabilityGame 𝒜).withQueryLog] :=
      probEvent_mono'' fun ⟨_, _⟩ => by tauto
    -- Union bound.
    _ ≤ Pr[fun (vals, log) => LogHasCollision log |
            (extractabilityGame 𝒜).withQueryLog] +
        Pr[fun (vals, log) =>
            ¬ LogHasCollision log ∧ AdversaryWinsExtractabilityGame vals |
          (extractabilityGame 𝒜).withQueryLog] :=
      probEvent_or_le ..
    -- Birthday bound on the collision probability.
    _ ≤ ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α) +
        Pr[fun (vals, log) =>
            ¬ LogHasCollision log ∧ AdversaryWinsExtractabilityGame vals |
          (extractabilityGame 𝒜).withQueryLog] := by
      gcongr
      convert OracleComp.probEvent_logCollision_le_birthday_total (spec := spec α)
        (extractabilityGame 𝒜) (qb + s.depth)
        (extractabilityGame_isTotalQueryBound 𝒜 qb h_IsQueryBound_qb)
        (fun _ => le_rfl) using 2
      push_cast; rfl
    -- Bound the no-collision bad event probability.
    _ ≤ ((qb + s.depth) ^ 2 : ENNReal) / (2 * Fintype.card α) +
        1 / (Fintype.card α) := by
      have h' := extractabilityGame_not_logHasCollision_wins_le_inv_card 𝒜
      gcongr
      norm_cast

end InductiveMerkleTree
