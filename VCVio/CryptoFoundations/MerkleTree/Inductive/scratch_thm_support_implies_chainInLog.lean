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
  populate_down s children (some root)

/-! ### Chain predicate and consistency lemma

The proof of `extractability_game_noColl_caseA_eq_zero` relies on three
substantive helper facts:

1.  A *structural predicate* `chainInLog` capturing what it means for the
    verifier's `getPutativeRoot` chain to actually appear in the combined log.
2.  A *pure consistency lemma* `extractor_chain_match` showing that under
    no-collision, an intact extractor path plus a `chainInLog` witness force
    the opened `(leaf, proof)` to match the extracted pair.
3.  A *support-to-chain bridge* `support_implies_chainInLog` translating
    `verified = true` (in the game's support) into `chainInLog`.

(2) is a pure structural induction on `idx` (no probability content) and (3)
follows from unfolding the game's monadic structure and applying the
`WriterT.run_bind'` decomposition of `withQueryLog` plus the structural
characterisation of `run_simulateQ_loggingOracle_query_bind`. Both are
factored out as helper theorems below; their proofs are documented but
elided as `sorry` here.
-/

/-- Under no-collision, `List.find?` on a `q.2`-matcher returns the unique
log entry with that response. -/
lemma find?_response_eq_some_of_no_collision_mem
    [DecidableEq α] {log : (spec α).QueryLog} {q : (_i : (α × α)) × α}
    (h_no_coll : ¬ collisionIn log) (h_mem : q ∈ log) :
    log.find? (fun q' => q'.2 == q.2) = some q := by
  -- `find?` returns the first matching entry; under no-collision, all matching
  -- entries are equal as Sigma values, so the first one must be `q`.
  have h_some : ∃ y, log.find? (fun q' => q'.2 == q.2) = some y := by
    cases hf : log.find? (fun q' => q'.2 == q.2) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at hf
      exact hf q h_mem (by simp)
    | some y => exact ⟨y, rfl⟩
  obtain ⟨y, hy⟩ := h_some
  rw [hy]
  congr 1
  have h_y_mem : y ∈ log := List.mem_of_find?_eq_some hy
  have h_y_match : (fun q' : (_i : (α × α)) × α => q'.2 == q.2) y = true :=
    List.find?_eq_some_iff_getElem.mp hy |>.1
  have h_y_eq : y.2 = q.2 := by
    simp only [beq_iff_eq] at h_y_match
    exact h_y_match
  by_contra h_ne
  exact h_no_coll ⟨y, q, h_ne, h_y_mem, h_mem, by simp [h_y_eq]⟩

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

/--
**Pure consistency lemma.** Under no-collision, if the extractor's path from
`root` to the node at `idx` is intact (the value there is `≠ none`) and
`chainInLog log root idx leaf proof` holds, then the extracted leaf value equals
`some leaf` and the extracted proof matches `proof.toList.map some` pointwise.

The argument is a structural induction on `idx`: at each level the unique log
entry with response equal to the current ancestor must be both the one used by
the extractor (to descend) and the one used by the verifier's chain (to ascend),
so their input pairs agree. Specifically, for `idx = .ofLeft idxLeft` we use:

* `chainInLog` produces an entry `⟨(ancestor, proof.head), root⟩ ∈ log`.
* `_h_ne_none` plus `extractor`'s `populate_down` definition forces
  `log.find? (·.2 == root)` to be `some _`.
* No-collision then identifies that `find?` result with the chain entry above,
  giving `extracted leftRoot = some ancestor` and `extracted rightRoot = some proof.head`.
* The IH applied to the left subtree (with new root `ancestor`) closes the
  recursion. The `.ofRight` case is symmetric.

The `.ofLeaf` base case follows because the extractor at `Skeleton.leaf`
returns `FullData.leaf (some root)` and `chainInLog … .ofLeaf` forces
`leaf = root`.
-/
theorem extractor_chain_match
    [DecidableEq α] [SampleableType α] [(spec α).Fintype]
    {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ (log : (spec α).QueryLog) (root : α) (leaf : α)
      (proof : List.Vector α idx.depth),
    ¬ collisionIn log →
    (extractor s log root).get idx.toNodeIndex ≠ none →
    chainInLog log root idx leaf proof →
    (extractor s log root).get idx.toNodeIndex = some leaf ∧
      (generateProof (extractor s log root) idx).toList = proof.toList.map some := by
  induction idx with
  | ofLeaf =>
    -- Base case: `s = .leaf`, `idx = .ofLeaf`.
    -- `extractor .leaf log root = FullData.leaf (some root)`, so the get is `some root`.
    -- `chainInLog … .ofLeaf` reduces to `leaf = root`, so the get equals `some leaf`.
    -- The proof has length 0, hence is empty; `generateProof` on `.ofLeaf` is `nil`.
    intro log root leaf proof _h_no_coll _h_ne_none h_chain
    simp only [chainInLog] at h_chain
    refine ⟨?_, ?_⟩
    · change (FullData.leaf (some root) : FullData (Option α) Skeleton.leaf).get
            SkeletonNodeIndex.ofLeaf = some leaf
      rw [FullData.get_leaf, h_chain]
    · rcases proof with ⟨l, hl⟩
      have : l = [] := List.length_eq_zero_iff.mp hl
      subst this
      rfl
  | @ofLeft sl sr idxLeft ih =>
    intro log root leaf proof h_no_coll h_ne_none h_chain
    -- Step 1. Destructure the chain to obtain the witness `ancestor` and the log entry.
    obtain ⟨ancestor, h_log_mem, h_chain_rec⟩ := h_chain
    -- Step 2. Under no-collision, `find?` on the response-`root` matcher returns
    --   exactly the chain's log entry.
    have h_find :
        log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
          some ⟨(ancestor, proof.head), root⟩ := by
      have :=
        find?_response_eq_some_of_no_collision_mem
          (q := (⟨(ancestor, proof.head), root⟩ : (_i : (α × α)) × α))
          h_no_coll h_log_mem
      simpa using this
    -- Step 3. The extractor decomposes via `populate_down_internal_def`.
    have h_extractor_decomp :
        extractor (Skeleton.internal sl sr) log root =
          FullData.internal (some root)
            (extractor sl log ancestor) (extractor sr log proof.head) := by
      change populate_down (Skeleton.internal sl sr) _ (some root) = _
      rw [populate_down_internal_def]
      simp only [h_find, FullData.internal.injEq, true_and]
      exact ⟨rfl, rfl⟩
    rw [h_extractor_decomp]
    -- Step 4. Transfer ne-none into the recursive subcall.
    have h_ne_none_inner :
        (extractor sl log ancestor).get idxLeft.toNodeIndex ≠ none := by
      intro hne
      apply h_ne_none
      rw [h_extractor_decomp]
      change (FullData.internal (some root) (extractor sl log ancestor)
              (extractor sr log proof.head)).get
            (SkeletonNodeIndex.ofLeft idxLeft.toNodeIndex) = none
      rw [FullData.get_internal_ofLeft]
      exact hne
    -- Step 5. Apply IH for the left subtree with new root `ancestor`.
    obtain ⟨ih_get, ih_proof⟩ :=
      ih log ancestor leaf proof.tail h_no_coll h_ne_none_inner h_chain_rec
    refine ⟨?_, ?_⟩
    · change (FullData.internal (some root) (extractor sl log ancestor)
              (extractor sr log proof.head)).get
            (SkeletonNodeIndex.ofLeft idxLeft.toNodeIndex) = some leaf
      rw [FullData.get_internal_ofLeft]
      exact ih_get
    · -- generateProof for ofLeft prepends `extractedTree.rightSubtree.getRootValue`
      -- to `generateProof extractedTree.leftSubtree idxLeft`.
      change (generateProof
              (FullData.internal (some root) (extractor sl log ancestor)
                (extractor sr log proof.head))
              (SkeletonLeafIndex.ofLeft idxLeft)).toList =
          proof.toList.map some
      simp only [generateProof, FullData.rightSubtree_internal,
        FullData.leftSubtree_internal]
      -- `(extractor sr log proof.head).getRootValue = some proof.head`.
      have h_root_value : (extractor sr log proof.head).getRootValue = some proof.head := by
        change (populate_down sr _ (some proof.head)).getRootValue = some proof.head
        rw [populate_down_getRootValue]
      -- `(a ::ᵥ v).toList = a :: v.toList` definitionally.
      change (extractor sr log proof.head).getRootValue ::
            (generateProof (extractor sl log ancestor) idxLeft).toList =
          proof.toList.map some
      rw [h_root_value, ih_proof]
      rcases proof with ⟨l, hl⟩
      cases l with
      | nil => exact absurd hl.symm (Nat.succ_ne_zero _)
      | cons hd tl =>
        change some hd :: List.map some tl = List.map some (hd :: tl)
        rfl
  | @ofRight sl sr idxRight ih =>
    -- Symmetric to the `.ofLeft` case.
    intro log root leaf proof h_no_coll h_ne_none h_chain
    obtain ⟨ancestor, h_log_mem, h_chain_rec⟩ := h_chain
    have h_find :
        log.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
          some ⟨(proof.head, ancestor), root⟩ := by
      have :=
        find?_response_eq_some_of_no_collision_mem
          (q := (⟨(proof.head, ancestor), root⟩ : (_i : (α × α)) × α))
          h_no_coll h_log_mem
      simpa using this
    have h_extractor_decomp :
        extractor (Skeleton.internal sl sr) log root =
          FullData.internal (some root)
            (extractor sl log proof.head) (extractor sr log ancestor) := by
      change populate_down (Skeleton.internal sl sr) _ (some root) = _
      rw [populate_down_internal_def]
      simp only [h_find, FullData.internal.injEq, true_and]
      exact ⟨rfl, rfl⟩
    rw [h_extractor_decomp]
    have h_ne_none_inner :
        (extractor sr log ancestor).get idxRight.toNodeIndex ≠ none := by
      intro hne
      apply h_ne_none
      rw [h_extractor_decomp]
      change (FullData.internal (some root) (extractor sl log proof.head)
              (extractor sr log ancestor)).get
            (SkeletonNodeIndex.ofRight idxRight.toNodeIndex) = none
      rw [FullData.get_internal_ofRight]
      exact hne
    obtain ⟨ih_get, ih_proof⟩ :=
      ih log ancestor leaf proof.tail h_no_coll h_ne_none_inner h_chain_rec
    refine ⟨?_, ?_⟩
    · change (FullData.internal (some root) (extractor sl log proof.head)
              (extractor sr log ancestor)).get
            (SkeletonNodeIndex.ofRight idxRight.toNodeIndex) = some leaf
      rw [FullData.get_internal_ofRight]
      exact ih_get
    · change (generateProof
              (FullData.internal (some root) (extractor sl log proof.head)
                (extractor sr log ancestor))
              (SkeletonLeafIndex.ofRight idxRight)).toList =
          proof.toList.map some
      simp only [generateProof, FullData.leftSubtree_internal,
        FullData.rightSubtree_internal]
      have h_root_value : (extractor sl log proof.head).getRootValue = some proof.head := by
        change (populate_down sl _ (some proof.head)).getRootValue = some proof.head
        rw [populate_down_getRootValue]
      change (extractor sl log proof.head).getRootValue ::
            (generateProof (extractor sr log ancestor) idxRight).toList =
          proof.toList.map some
      rw [h_root_value, ih_proof]
      rcases proof with ⟨l, hl⟩
      cases l with
      | nil => exact absurd hl.symm (Nat.succ_ne_zero _)
      | cons hd tl =>
        change some hd :: List.map some tl = List.map some (hd :: tl)
        rfl

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

/-! ### Support → chain bridge and bundled match lemma

The proof of `support_implies_chainInLog` requires three substantive ingredients:

* `chainInLog_mono` — monotonicity in the log (proved below).
* `OracleComp.withQueryLog_bind`, `OracleComp.withQueryLog_pure` — structural
  properties of `withQueryLog` (proved below) that decompose the support of a
  bind into intermediate values + log concatenations.
* `getPutativeRoot_support_chain` — induction on `idx` showing that any
  `(r, log_v)` in the support of the verifier's `withQueryLog'd` evaluation
  yields a `chainInLog log_v r idx leaf proof` witness. The base case is
  proved; the inductive cases require a more delicate analysis of
  `(singleHash _ _).withQueryLog` than the bind decomposition supplies and
  are left as `sorry`.

The final theorem `support_implies_chainInLog` then plumbs the game's monadic
structure through these helpers, peeling off `committingAdv`, `openingAdv`,
and the verifier's contribution to extract the chain witness.
-/

/-- `chainInLog` is monotone in the log: enlarging the log only adds more entries
to draw chain witnesses from. -/
lemma chainInLog_mono {α : Type} {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ {log1 log2 : (spec α).QueryLog} {root leaf : α}
      {proof : List.Vector α idx.depth},
    (∀ q, q ∈ log1 → q ∈ log2) →
    chainInLog log1 root idx leaf proof →
    chainInLog log2 root idx leaf proof := by
  induction idx with
  | ofLeaf =>
    intros _ _ _ _ _ _ h
    exact h
  | @ofLeft sl sr idxLeft ih =>
    intros _ _ _ _ _ h_sub h
    obtain ⟨ancestor, h_mem, h_rec⟩ := h
    exact ⟨ancestor, h_sub _ h_mem, ih h_sub h_rec⟩
  | @ofRight sl sr idxRight ih =>
    intros _ _ _ _ _ h_sub h
    obtain ⟨ancestor, h_mem, h_rec⟩ := h
    exact ⟨ancestor, h_sub _ h_mem, ih h_sub h_rec⟩

/-- `OracleComp.withQueryLog` distributes over `bind`: the combined log is the
concatenation of the prefix's log and the continuation's log. -/
lemma OracleComp.withQueryLog_bind
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    (mx >>= my).withQueryLog =
      mx.withQueryLog >>= fun p => Prod.map id (p.2 ++ ·) <$> (my p.1).withQueryLog := by
  change (WriterT.run (simulateQ _ (mx >>= my)) :
      OracleComp spec (β × spec.QueryLog)) = _
  rw [simulateQ_bind, WriterT.run_bind']

/-- `OracleComp.withQueryLog` of `pure x` produces `(x, [])` — no oracle queries,
empty log. -/
lemma OracleComp.withQueryLog_pure
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (x : α) :
    (pure x : OracleComp spec α).withQueryLog = pure (x, []) := rfl

/-- `OracleComp.withQueryLog` of a single `query t` produces `(u, [⟨t, u⟩])` where
`u` is the oracle response: one query, one log entry. -/
lemma OracleComp.withQueryLog_query
    {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (liftM (OracleSpec.query t) : OracleComp spec _).withQueryLog =
      liftM (OracleSpec.query t) >>= fun u => pure (u, [⟨t, u⟩]) := by
  conv_lhs =>
    rw [show (liftM (OracleSpec.query t) : OracleComp spec _) =
        liftM (OracleSpec.query t) >>= pure from (bind_pure _).symm]
  change (simulateQ loggingOracle (liftM (OracleSpec.query t) >>= pure)).run = _
  rw [run_simulateQ_loggingOracle_query_bind]
  simp only [simulateQ_pure, WriterT.run_pure', map_pure]
  rfl

/-- `singleHash a b` makes a single oracle query on input `(a, b)`; therefore
its `withQueryLog` produces `(u, [⟨(a, b), u⟩])` where `u` is the response. -/
lemma singleHash_withQueryLog
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

/-- The verifier's `getPutativeRoot` evaluation, in the support of its
`withQueryLog`, witnesses a chain in the log from the produced putative root `r`
back through the proof's siblings to `leaf`. -/
lemma getPutativeRoot_support_chain
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
    have h_eq : (getPutativeRoot (m := OracleComp (spec α))
        SkeletonLeafIndex.ofLeaf leaf _proof) = pure leaf := rfl
    rw [h_eq, OracleComp.withQueryLog_pure, mem_support_pure_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    simp only [chainInLog]
  | @ofLeft sl sr idxLeft ih =>
    intros leaf proof r log_v hmem
    -- `getPutativeRoot .ofLeft idxLeft leaf proof = rec >>= singleHash · proof.head`.
    have h_eq : (getPutativeRoot (m := OracleComp (spec α))
        (SkeletonLeafIndex.ofLeft idxLeft) leaf proof) =
        getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail >>=
          fun a => singleHash a proof.head := rfl
    rw [h_eq, OracleComp.withQueryLog_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨a, log_a⟩, h_rec, hmem⟩ := hmem
    rw [singleHash_withQueryLog] at hmem
    -- After unfolding singleHash: `(r, log_v) ∈ support
    --   (Prod.map id (log_a ++ ·) <$>
    --     (liftM (query (a, proof.head)) >>= fun u => pure (u, [⟨(a, proof.head), u⟩])))`.
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨⟨r', log_b⟩, h_q, h_eq2⟩ := hmem
    rw [mem_support_bind_iff] at h_q
    obtain ⟨u, _, h_pure⟩ := h_q
    rw [mem_support_pure_iff, Prod.mk.injEq] at h_pure
    obtain ⟨rfl, rfl⟩ := h_pure
    -- `h_eq2 : (r', [⟨(a, proof.head), r'⟩]).map id (log_a ++ ·) = (r, log_v)` reduces
    -- to `r = r'` and `log_v = log_a ++ [⟨(a, proof.head), r⟩]`.
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq2
    -- Apply IH to the recursive part to get `chainInLog log_a a idxLeft leaf proof.tail`.
    have h_chain_rec := ih leaf proof.tail a log_a h_rec
    -- Assemble the chain at the current level.
    refine ⟨a, ?_, ?_⟩
    · -- `⟨(a, proof.head), r⟩ ∈ log_a ++ [⟨(a, proof.head), r⟩]`.
      simp
    · -- Extend `chainInLog log_a a ...` to the larger `log_a ++ [⟨...⟩]`.
      exact chainInLog_mono _ (fun q hq => List.mem_append_left _ hq) h_chain_rec
  | @ofRight sl sr idxRight ih =>
    intros leaf proof r log_v hmem
    have h_eq : (getPutativeRoot (m := OracleComp (spec α))
        (SkeletonLeafIndex.ofRight idxRight) leaf proof) =
        getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail >>=
          fun a => singleHash proof.head a := rfl
    rw [h_eq, OracleComp.withQueryLog_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨a, log_a⟩, h_rec, hmem⟩ := hmem
    rw [singleHash_withQueryLog] at hmem
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨⟨r', log_b⟩, h_q, h_eq2⟩ := hmem
    rw [mem_support_bind_iff] at h_q
    obtain ⟨u, _, h_pure⟩ := h_q
    rw [mem_support_pure_iff, Prod.mk.injEq] at h_pure
    obtain ⟨rfl, rfl⟩ := h_pure
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq2
    have h_chain_rec := ih leaf proof.tail a log_a h_rec
    refine ⟨a, ?_, ?_⟩
    · simp
    · exact chainInLog_mono _ (fun q hq => List.mem_append_left _ hq) h_chain_rec

/-- A successful `verifyProof.run` evaluation in the support of its `withQueryLog`
witnesses a chain in the verifier's log from `root` down to `leaf` along `idx`. -/
lemma verifyProof_run_support_chain
    {α : Type} [DecidableEq α] [SampleableType α] [(spec α).Fintype] [(spec α).Inhabited]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (log_v : (spec α).QueryLog)
    (hmem : (some (), log_v) ∈ support
        ((verifyProof (m := OracleComp (spec α)) idx leaf root proof).run).withQueryLog) :
    chainInLog log_v root idx leaf proof := by
  -- Reshape `verifyProof.run` to `getPutativeRoot >>= guard`.
  have heq : (verifyProof (m := OracleComp (spec α)) idx leaf root proof).run =
      (do let r ← getPutativeRoot (m := OracleComp (spec α)) idx leaf proof
          if r = root then pure (some ()) else pure none) := by
    unfold verifyProof
    simp [OptionT.run_bind, OptionT.run_monadLift, guard]
    rfl
  rw [heq, OracleComp.withQueryLog_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨r, log_g⟩, h_g, hmem⟩ := hmem
  rw [support_map, Set.mem_image] at hmem
  obtain ⟨⟨_vOpt, log_x⟩, h_x, h_eq⟩ := hmem
  -- `Prod.map id (log_g ++ ·) (_vOpt, log_x) = (some (), log_v)` gives `_vOpt = some ()`,
  -- `log_g ++ log_x = log_v`.
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
  by_cases hroot : r = root
  · -- Verification succeeds: `r = root`. The `if`-branch is `pure (some ())`, so log is `[]`.
    subst hroot
    rw [if_pos rfl, OracleComp.withQueryLog_pure, mem_support_pure_iff] at h_x
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_x
    simp only [List.append_nil]
    exact getPutativeRoot_support_chain idx leaf proof r log_g h_g
  · -- Verification fails: `r ≠ root`. Then `_vOpt` would have to be `none`, contradicting
    -- `_vOpt = some ()`.
    rw [if_neg hroot, OracleComp.withQueryLog_pure, mem_support_pure_iff] at h_x
    obtain ⟨h_some_eq_none, _⟩ := Prod.mk.inj h_x
    cases h_some_eq_none

/--
**Support → chain.** When the game's combined log `log` contains a successful
verification (`verified = true`), the verifier's queries form a chain in the log
from `root` down to `leaf` along `idx`. This is the bridge from the oracle's
operational semantics to the pure structural predicate `chainInLog`.

The proof unfolds `extractability_game.withQueryLog` via
`OracleComp.withQueryLog_bind`, peels off `committingAdv`, `openingAdv`, and the
final return step, and applies `getPutativeRoot_support_chain` to the verifier's
contribution. The committing/opening prefix only enlarges the log, which
`chainInLog_mono` lifts past.
-/
theorem support_implies_chainInLog
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
    (_hsupport : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractability_game committingAdv openingAdv).withQueryLog) :
    chainInLog log root idx leaf proof := by
  -- Outline: unfold the game into `prefix >>= (verifyProof.run >>= pure-step)`,
  -- decompose support via `OracleComp.withQueryLog_bind` and `support_map`, extract
  -- the structural equalities pinning `pq.1.1.1 = root`, `pq.2.1 = idx`, etc., and
  -- apply `verifyProof_run_support_chain` (which discharges the verifier branch via
  -- `getPutativeRoot_support_chain`). The remaining gap is the dependent-Sigma
  -- destructuring after the pure step, which requires careful handling of `Sigma.mk.inj`
  -- and `subst` interactions with the `idx`-dependent type of `proof`.
  sorry

/--
**Extractor matches in support.** Bundled helper combining
`support_implies_chainInLog` with `extractor_chain_match`. From the game's
support with `verified = true` plus no-collision and an intact extractor path,
this lemma derives that the extracted leaf and proof exactly match the opened
leaf and proof.

This is the form directly consumable by `extractability_game_noColl_caseA_eq_zero`:
the extracted-tree and extracted-proof equalities suffice to falsify
`adversary_wins_extractability_game_event`.

Implementation outline. Inside the support, `extractedTree` is concretely
`extractor s committingLog root` for the committing prefix `committingLog ⊆ log`.
Under `¬ collisionIn log`, `extractor` produces the same tree whether built from
`committingLog` or from `log` (any new entries in `log` with response equal to
an existing one would be a collision). So we apply `extractor_chain_match` with
the full log.
-/
theorem extractability_game_no_coll_match
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
    (h_no_coll : ¬ collisionIn log)
    (h_ne_none : extractedTree.get idx.toNodeIndex ≠ none)
    (hsupport : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractability_game committingAdv openingAdv).withQueryLog) :
    extractedTree.get idx.toNodeIndex = some leaf ∧
      proof.toList.map some = extractedProof.toList := by
  -- Bridge the committingLog used by `extractedTree`/`extractedProof` and the full
  -- `log` used by `chainInLog`. Under no-collision in the full log, the extractor's
  -- choice of children at any value `a` is determined by the unique log entry
  -- with response `a`, which agrees whether we look in the committing prefix or in
  -- the full log. So `extractedTree = extractor s log root` and
  -- `extractedProof = generateProof extractedTree idx`.
  have h_extracted_tree_eq : extractedTree = extractor s log root := by
    -- Follows from `hsupport` (extractedTree comes from `extractor s committingLog root`)
    -- combined with the no-collision-equivalence above.
    sorry
  have h_extracted_proof_eq : extractedProof = generateProof extractedTree idx := by
    -- Follows directly from `hsupport`'s structure.
    sorry
  -- Get the chain from the support.
  have h_chain : chainInLog log root idx leaf proof :=
    support_implies_chainInLog committingAdv openingAdv hsupport
  -- Apply the pure consistency lemma.
  have h_ne_none_log : (extractor s log root).get idx.toNodeIndex ≠ none := by
    rw [← h_extracted_tree_eq]; exact h_ne_none
  obtain ⟨h_get, h_proof_eq⟩ :=
    extractor_chain_match idx log root leaf proof h_no_coll h_ne_none_log h_chain
  refine ⟨?_, ?_⟩
  · rw [h_extracted_tree_eq]; exact h_get
  · rw [h_extracted_proof_eq, h_extracted_tree_eq]; exact h_proof_eq.symm

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
    (_h_IsQueryBound_qb :
      IsTotalQueryBound
        (do
          let (_root, aux) ← committingAdv
          let ⟨_idx, _leaf, _proof⟩ ← openingAdv aux
          pure ())
        qb)
    (_h_le_qb : 4 * s.leafCount + 1 ≤ qb) :
    Pr[noColl_caseA_event |
        (extractability_game committingAdv openingAdv).withQueryLog] = 0 := by
  apply probEvent_eq_zero
  rintro ⟨vals, log⟩ hsupport
  obtain ⟨root, aux, idx, leaf, proof, extractedTree, extractedProof, verified⟩ := vals
  rintro ⟨h_no_coll, h_adv_wins, h_ne_none⟩
  -- Extract `verified = true` from `h_adv_wins` and substitute it everywhere.
  have h_verified : verified = true := h_adv_wins.1
  subst h_verified
  -- Apply the bundled support → match helper to derive the leaf and proof equalities.
  obtain ⟨h_eq_leaf, h_map⟩ :=
    extractability_game_no_coll_match committingAdv openingAdv h_no_coll h_ne_none hsupport
  -- Now contradict `adversary_wins_extractability_game_event`. After `subst h_verified`,
  -- the `verified = true` conjunct is `True` and gets eliminated. The proof-mismatch
  -- disjunct is killed by `h_map`; the leaf-mismatch disjunct is killed by `h_eq_leaf`.
  simp only [adversary_wins_extractability_game_event, true_and, Bool.not_eq_true',
    h_map] at h_adv_wins
  rcases h_adv_wins with h | h
  · rw [h_eq_leaf, beq_self_eq_true] at h
    exact Bool.noConfusion h
  · rw [beq_self_eq_true] at h
    exact Bool.noConfusion h

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
