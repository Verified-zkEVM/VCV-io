-- Scratch: prove the two sorries in `extractability_game_no_coll_match`.
import VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/-- If `populate_down` is called with input value `none` (under a `children`
function that maps `none` to `(none, none)`), then every node of the resulting
tree has value `none`. -/
lemma populate_down_none_get_eq_none {s : Skeleton}
    (children : Option α → Option α × Option α)
    (h_none : children none = (none, none))
    (idx : SkeletonNodeIndex s) :
    (populate_down s children none).get idx = none := by
  induction s with
  | leaf => cases idx; rfl
  | internal sl sr ihL ihR =>
    cases idx with
    | ofInternal => rfl
    | ofLeft idxL =>
      rw [populate_down_internal_def, FullData.get_internal_ofLeft]
      have : (children none).1 = none := by rw [h_none]
      rw [this]
      exact ihL idxL
    | ofRight idxR =>
      rw [populate_down_internal_def, FullData.get_internal_ofRight]
      have : (children none).2 = none := by rw [h_none]
      rw [this]
      exact ihR idxR

/-- A localized abbreviation for the `extractor`'s children function over a log. -/
private def extractorChildren [DecidableEq α]
    (log_c : (spec α).QueryLog) :
    Option α → Option α × Option α := fun node =>
  match node with
  | none => (none, none)
  | some a =>
    match log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == a) with
    | none => (none, none)
    | some q => (some q.1.1, some q.1.2)

@[simp] private lemma extractorChildren_none [DecidableEq α]
    (log_c : (spec α).QueryLog) :
    extractorChildren log_c none = (none, none) := rfl

private lemma extractor_eq_populate [DecidableEq α] [SampleableType α]
    [(spec α).Fintype]
    (s : Skeleton) (log_c : (spec α).QueryLog) (root : α) :
    extractor s log_c root = populate_down s (extractorChildren log_c) (some root) := rfl

private lemma extractorChildren_some [DecidableEq α]
    (log_c : (spec α).QueryLog) (a : α) :
    extractorChildren log_c (some a) =
      match log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == a) with
      | none => (none, none)
      | some q => (some q.1.1, some q.1.2) := rfl

/-- If the extractor's path to `idx` is intact in `log_c`, then any chain in
the larger collision-free `log` from `root` along `idx` also lives in `log_c`. -/
theorem chainInLog_restrict
    [DecidableEq α] [SampleableType α] [(spec α).Fintype]
    {s : Skeleton} (idx : SkeletonLeafIndex s) :
    ∀ (log log_c : (spec α).QueryLog) (root : α) (leaf : α)
      (proof : List.Vector α idx.depth),
    (∀ q, q ∈ log_c → q ∈ log) →
    ¬ collisionIn log →
    (extractor s log_c root).get idx.toNodeIndex ≠ none →
    chainInLog log root idx leaf proof →
    chainInLog log_c root idx leaf proof := by
  induction idx with
  | ofLeaf =>
    intros _ _ _ _ _ _ _ _ h_chain
    exact h_chain
  | @ofLeft sl sr idxLeft ih =>
    intros log log_c root leaf proof h_sub h_no_coll h_ne_none h_chain
    obtain ⟨ancestor, h_log_mem, h_chain_rec⟩ := h_chain
    -- Step 1: derive `log_c.find? (·.2 == root) = some _` from path-intactness.
    have h_find_some :
        ∃ q, log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) = some q := by
      rcases hf : log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) with _ | q
      · exfalso
        apply h_ne_none
        rw [extractor_eq_populate, populate_down_internal_def]
        change (FullData.internal (some root)
            (populate_down sl (extractorChildren log_c)
              (extractorChildren log_c (some root)).1)
            (populate_down sr (extractorChildren log_c)
              (extractorChildren log_c (some root)).2)).get
            (SkeletonNodeIndex.ofLeft idxLeft.toNodeIndex) = none
        rw [FullData.get_internal_ofLeft]
        have hch : extractorChildren log_c (some root) = (none, none) := by
          rw [extractorChildren_some, hf]
        rw [show (extractorChildren log_c (some root)).1 = none from by rw [hch]]
        exact populate_down_none_get_eq_none (extractorChildren log_c)
          (extractorChildren_none log_c) idxLeft.toNodeIndex
      · exact ⟨q, rfl⟩
    obtain ⟨q_c, h_find_c⟩ := h_find_some
    -- Step 2: q_c ∈ log_c (hence ∈ log), and q_c.2 = root.
    have h_qc_mem_lc : q_c ∈ log_c := List.mem_of_find?_eq_some h_find_c
    have h_qc_mem_log : q_c ∈ log := h_sub _ h_qc_mem_lc
    have h_qc_resp : q_c.2 = root := by
      have h := List.find?_eq_some_iff_getElem.mp h_find_c |>.1
      simp only [beq_iff_eq] at h
      exact h
    -- Step 3: by no-collision in `log` and the chain entry, q_c equals the chain entry.
    have h_qc_eq : q_c = ⟨(ancestor, proof.head), root⟩ := by
      by_contra h_ne
      apply h_no_coll
      refine ⟨q_c, ⟨(ancestor, proof.head), root⟩, h_ne, h_qc_mem_log, h_log_mem, ?_⟩
      simp [h_qc_resp]
    -- Step 4: the chain entry is in log_c.
    have h_chain_entry_in_lc :
        (⟨(ancestor, proof.head), root⟩ : (_i : (α × α)) × α) ∈ log_c := by
      rw [← h_qc_eq]; exact h_qc_mem_lc
    -- Step 5: rewrite the extractor decomposition with concrete values.
    have h_find_c' :
        log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
          some ⟨(ancestor, proof.head), root⟩ := by
      rw [h_find_c, h_qc_eq]
    have h_extr_decomp :
        extractor (Skeleton.internal sl sr) log_c root =
          FullData.internal (some root)
            (extractor sl log_c ancestor) (extractor sr log_c proof.head) := by
      rw [extractor_eq_populate, populate_down_internal_def]
      have hch : extractorChildren log_c (some root) =
          (some ancestor, some proof.head) := by
        rw [extractorChildren_some, h_find_c']
      rw [show (extractorChildren log_c (some root)).1 = some ancestor from by rw [hch],
          show (extractorChildren log_c (some root)).2 = some proof.head from by rw [hch]]
      rfl
    -- Step 6: path-intactness pushes into the left subtree.
    have h_ne_none_inner :
        (extractor sl log_c ancestor).get idxLeft.toNodeIndex ≠ none := by
      intro hne
      apply h_ne_none
      rw [h_extr_decomp]
      change (FullData.internal (some root)
          (extractor sl log_c ancestor) (extractor sr log_c proof.head)).get
        (SkeletonNodeIndex.ofLeft idxLeft.toNodeIndex) = none
      rw [FullData.get_internal_ofLeft]
      exact hne
    -- Step 7: recurse.
    have h_chain_inner :=
      ih log log_c ancestor leaf proof.tail h_sub h_no_coll h_ne_none_inner h_chain_rec
    refine ⟨ancestor, h_chain_entry_in_lc, h_chain_inner⟩
  | @ofRight sl sr idxRight ih =>
    intros log log_c root leaf proof h_sub h_no_coll h_ne_none h_chain
    obtain ⟨ancestor, h_log_mem, h_chain_rec⟩ := h_chain
    have h_find_some :
        ∃ q, log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) = some q := by
      rcases hf : log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) with _ | q
      · exfalso
        apply h_ne_none
        rw [extractor_eq_populate, populate_down_internal_def]
        change (FullData.internal (some root)
            (populate_down sl (extractorChildren log_c)
              (extractorChildren log_c (some root)).1)
            (populate_down sr (extractorChildren log_c)
              (extractorChildren log_c (some root)).2)).get
            (SkeletonNodeIndex.ofRight idxRight.toNodeIndex) = none
        rw [FullData.get_internal_ofRight]
        have hch : extractorChildren log_c (some root) = (none, none) := by
          rw [extractorChildren_some, hf]
        rw [show (extractorChildren log_c (some root)).2 = none from by rw [hch]]
        exact populate_down_none_get_eq_none (extractorChildren log_c)
          (extractorChildren_none log_c) idxRight.toNodeIndex
      · exact ⟨q, rfl⟩
    obtain ⟨q_c, h_find_c⟩ := h_find_some
    have h_qc_mem_lc : q_c ∈ log_c := List.mem_of_find?_eq_some h_find_c
    have h_qc_mem_log : q_c ∈ log := h_sub _ h_qc_mem_lc
    have h_qc_resp : q_c.2 = root := by
      have h := List.find?_eq_some_iff_getElem.mp h_find_c |>.1
      simp only [beq_iff_eq] at h
      exact h
    have h_qc_eq : q_c = ⟨(proof.head, ancestor), root⟩ := by
      by_contra h_ne
      apply h_no_coll
      refine ⟨q_c, ⟨(proof.head, ancestor), root⟩, h_ne, h_qc_mem_log, h_log_mem, ?_⟩
      simp [h_qc_resp]
    have h_chain_entry_in_lc :
        (⟨(proof.head, ancestor), root⟩ : (_i : (α × α)) × α) ∈ log_c := by
      rw [← h_qc_eq]; exact h_qc_mem_lc
    have h_find_c' :
        log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) =
          some ⟨(proof.head, ancestor), root⟩ := by
      rw [h_find_c, h_qc_eq]
    have h_extr_decomp :
        extractor (Skeleton.internal sl sr) log_c root =
          FullData.internal (some root)
            (extractor sl log_c proof.head) (extractor sr log_c ancestor) := by
      rw [extractor_eq_populate, populate_down_internal_def]
      have hch : extractorChildren log_c (some root) =
          (some proof.head, some ancestor) := by
        rw [extractorChildren_some, h_find_c']
      rw [show (extractorChildren log_c (some root)).1 = some proof.head from by rw [hch],
          show (extractorChildren log_c (some root)).2 = some ancestor from by rw [hch]]
      rfl
    have h_ne_none_inner :
        (extractor sr log_c ancestor).get idxRight.toNodeIndex ≠ none := by
      intro hne
      apply h_ne_none
      rw [h_extr_decomp]
      change (FullData.internal (some root)
          (extractor sl log_c proof.head) (extractor sr log_c ancestor)).get
        (SkeletonNodeIndex.ofRight idxRight.toNodeIndex) = none
      rw [FullData.get_internal_ofRight]
      exact hne
    have h_chain_inner :=
      ih log log_c ancestor leaf proof.tail h_sub h_no_coll h_ne_none_inner h_chain_rec
    refine ⟨ancestor, h_chain_entry_in_lc, h_chain_inner⟩

/-- The two log layers produced by `oa.withQueryLog.withQueryLog` agree on every
support point: simulating `loggingOracle` over `oa.withQueryLog` records the
same queries the inner `withQueryLog` already recorded. -/
lemma withQueryLog_self_log_eq
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) :
    ∀ {v : α} {l₁ l₂ : spec.QueryLog},
      ((v, l₁), l₂) ∈ support oa.withQueryLog.withQueryLog →
      l₁ = l₂ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intros v l₁ l₂ hmem
      change ((v, l₁), l₂) ∈ support
        ((pure x : OracleComp spec α).withQueryLog.withQueryLog) at hmem
      rw [OracleComp.withQueryLog_pure, OracleComp.withQueryLog_pure,
        mem_support_pure_iff] at hmem
      obtain ⟨hv1, hl2⟩ := Prod.mk.inj hmem
      obtain ⟨_, hl1⟩ := Prod.mk.inj hv1
      subst hl1; subst hl2
      rfl
  | query_bind t mx ih =>
      intros v l₁ l₂ hmem
      -- The outer `withQueryLog` decomposes `(do let p ← (liftM q).withQueryLog; ...)
      -- .withQueryLog` via `withQueryLog_bind`.
      change ((v, l₁), l₂) ∈ support
        (((liftM (OracleSpec.query t) : OracleComp spec _) >>=
          fun u => mx u).withQueryLog.withQueryLog) at hmem
      rw [OracleComp.withQueryLog_bind] at hmem
      rw [OracleComp.withQueryLog_bind] at hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨u₁, log_q1⟩, log_q2⟩, h₁, hmem⟩ := hmem
      -- `h₁` is in support of `(liftM q).withQueryLog.withQueryLog`.
      -- Apply withQueryLog_query to peel off the inner.
      rw [OracleComp.withQueryLog_query] at h₁
      -- Now `(liftM q >>= fun u => pure (u, [⟨q, u⟩])).withQueryLog`. Use bind.
      rw [OracleComp.withQueryLog_bind] at h₁
      rw [mem_support_bind_iff] at h₁
      obtain ⟨⟨u₂, log_qa⟩, h₁a, h₁b⟩ := h₁
      -- h₁a in (liftM q).withQueryLog. Use withQueryLog_query.
      rw [OracleComp.withQueryLog_query, mem_support_bind_iff] at h₁a
      obtain ⟨u, hu_q, h_pa⟩ := h₁a
      rw [mem_support_pure_iff, Prod.mk.injEq] at h_pa
      obtain ⟨h_u2_eq, h_qa_eq⟩ := h_pa
      subst h_u2_eq; subst h_qa_eq
      -- h₁b: `((u₁, log_q1), log_q2) ∈ support (Prod.map id ([⟨t,u⟩] ++ ·) <$> (pure (u, [⟨t, u⟩])).withQueryLog)`.
      rw [support_map, Set.mem_image] at h₁b
      obtain ⟨⟨⟨u', l_inner⟩, l_outer⟩, h_pure, h_eq_b⟩ := h₁b
      rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_pure
      obtain ⟨h_pure1, h_pure2⟩ := h_pure
      obtain ⟨h_pure1a, h_pure1b⟩ := Prod.mk.inj h_pure1
      subst h_pure1a; subst h_pure1b; subst h_pure2
      simp only [Prod.map_apply, id_eq, Prod.mk.injEq, List.append_nil] at h_eq_b
      obtain ⟨⟨h_eq_b1a, h_eq_b1b⟩, h_eq_b2⟩ := h_eq_b
      subst h_eq_b1a; subst h_eq_b1b; subst h_eq_b2
      -- Now `hmem` is in support of `Prod.map id (log_q2 ++ ·) <$> (Prod.map id (l ++ ·) <$> (mx u).withQueryLog).withQueryLog`.
      rw [support_map, Set.mem_image] at hmem
      obtain ⟨⟨⟨v', l₁'⟩, l₂'⟩, h_inner_outer, h_eq⟩ := hmem
      simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq
      obtain ⟨⟨h_eq_v', h_eq_l₁'⟩, h_eq_l₂⟩ := h_eq
      subst h_eq_v'; subst h_eq_l₁'; subst h_eq_l₂
      simp only at h_inner_outer
      -- `h_inner_outer` is now in support of `(Prod.map id ([⟨t,u'⟩] ++ ·) <$> (mx u').withQueryLog).withQueryLog`.
      -- Rewrite the inner `<$>` as a bind to expose the inner `.withQueryLog.withQueryLog` for IH.
      rw [show (Prod.map id (fun x => ([⟨t, u'⟩] ++ x : (spec).QueryLog)) <$>
              (mx u').withQueryLog) =
            ((mx u').withQueryLog >>=
              fun p => pure (Prod.map id (fun x => [⟨t, u'⟩] ++ x) p))
          from by rw [map_eq_pure_bind]] at h_inner_outer
      rw [OracleComp.withQueryLog_bind] at h_inner_outer
      rw [mem_support_bind_iff] at h_inner_outer
      obtain ⟨⟨⟨v', l₁'⟩, l₂'⟩, h_inner, h_rest⟩ := h_inner_outer
      rw [support_map, Set.mem_image] at h_rest
      obtain ⟨⟨pX, lX⟩, h_pX, h_eq_X⟩ := h_rest
      rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_pX
      obtain ⟨h_pX1, h_pX2⟩ := h_pX
      subst h_pX1; subst h_pX2
      simp only [Prod.map_apply, id_eq, List.append_nil, Prod.mk.injEq] at h_eq_X
      obtain ⟨⟨h_eq_X1a, h_eq_X1b⟩, h_eq_X2⟩ := h_eq_X
      subst h_eq_X1a; subst h_eq_X1b; subst h_eq_X2
      have h_ih := ih u' h_inner
      rw [h_ih]

/-- Test version of `extractability_game_no_coll_match` (replaces the two
sorries in the main file). -/
theorem extractability_game_no_coll_match'
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
  -- Decompose `hsupport` via the same pattern as `support_implies_chainInLog` to
  -- expose `log_c` (committingAdv's log), `log_o` (openingAdv's log), `log_v`
  -- (verifyProof's log), and the equalities relating `extractedTree` /
  -- `extractedProof` to the committing log.
  have hsup := hsupport
  unfold extractability_game at hsup
  rw [OracleComp.withQueryLog_bind] at hsup
  rw [mem_support_bind_iff] at hsup
  obtain ⟨⟨⟨root_c, aux_c⟩, log_c⟩, h_c, hsup⟩ := hsup
  rw [support_map, Set.mem_image] at hsup
  obtain ⟨⟨resCO, log_co⟩, h_co, h_eq_co⟩ := hsup
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_co
  obtain ⟨h_eq_co1, h_eq_co2⟩ := h_eq_co
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at h_co
  obtain ⟨⟨⟨idx_o, leaf_o, proof_o⟩, log_o⟩, h_o, h_co⟩ := h_co
  rw [support_map, Set.mem_image] at h_co
  obtain ⟨⟨resV, log_v_inner⟩, h_v, h_eq_v⟩ := h_co
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_v
  obtain ⟨h_eq_v1, h_eq_v2⟩ := h_eq_v
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at h_v
  obtain ⟨⟨verifiedOpt, log_v⟩, h_vp, h_v⟩ := h_v
  rw [support_map, Set.mem_image] at h_v
  obtain ⟨⟨_unit, log_p⟩, h_p, h_eq_p⟩ := h_v
  rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_p
  obtain ⟨h_p1, h_p2⟩ := h_p
  subst h_p2
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_p
  obtain ⟨h_eq_p1, h_eq_p2⟩ := h_eq_p
  rw [← h_eq_p1, h_p1] at h_eq_v1
  rw [← h_eq_v1] at h_eq_co1
  simp only [Prod.mk.injEq] at h_eq_co1
  obtain ⟨h_root_eq, h_aux_eq, h_sigma_eq⟩ := h_eq_co1
  subst h_root_eq
  subst h_aux_eq
  obtain ⟨h_idx_eq, h_rest_eq⟩ := Sigma.mk.inj h_sigma_eq
  subst h_idx_eq
  simp only [heq_eq_eq, Prod.mk.injEq] at h_rest_eq
  obtain ⟨h_leaf_eq, h_proof_eq, h_tree_eq, h_proof_ext_eq, h_isSome_eq⟩ := h_rest_eq
  subst h_leaf_eq
  subst h_proof_eq
  -- Bridge `aux_c = log_c`: the inner queryLog (paired with the result of
  -- `committingAdv.withQueryLog`) equals the outer queryLog from the second
  -- `withQueryLog`. This is `withQueryLog_self_log_eq` applied to `committingAdv`.
  have h_aux_eq_log_c : aux_c = log_c :=
    withQueryLog_self_log_eq committingAdv h_c
  rw [h_aux_eq_log_c] at h_tree_eq h_proof_ext_eq h_eq_v1 h_p1 h_sigma_eq h_c
  -- Now: `extractedTree = extractor s log_c root_c.1` and
  -- `extractedProof = generateProof (extractor s log_c root_c.1) idx_o`.
  -- Also `log = log_c ++ log_o ++ log_v ++ []` (modulo the trivial empty `log_p`).
  -- We need `log_c ⊆ log`.
  have h_log_eq : log = log_c ++ log_o ++ log_v := by
    rw [← h_eq_co2, ← h_eq_v2, ← h_eq_p2]
    simp [List.append_nil]
  have h_sub : ∀ q, q ∈ log_c → q ∈ log := by
    intro q hq
    rw [h_log_eq]
    exact List.mem_append_left _ (List.mem_append_left _ hq)
  -- Get the chain in `log`.
  have h_chain : chainInLog log root_c.1 idx_o leaf_o proof_o :=
    support_implies_chainInLog committingAdv openingAdv hsupport
  -- The extracted tree equals `extractor s log_c root_c.1`.
  -- Use this to transfer `h_ne_none` to `log_c`.
  have h_ne_none_lc :
      (extractor s log_c root_c.1).get idx_o.toNodeIndex ≠ none := by
    rw [h_tree_eq]; exact h_ne_none
  -- Restrict the chain to `log_c`.
  have h_chain_lc : chainInLog log_c root_c.1 idx_o leaf_o proof_o :=
    chainInLog_restrict idx_o log log_c root_c.1 leaf_o proof_o
      h_sub h_no_coll h_ne_none_lc h_chain
  -- No-collision on `log_c` (subset of collision-free `log`).
  have h_no_coll_lc : ¬ collisionIn log_c := by
    intro ⟨q1, q2, hne, hm1, hm2, hresp⟩
    exact h_no_coll ⟨q1, q2, hne, h_sub _ hm1, h_sub _ hm2, hresp⟩
  -- Apply the pure consistency lemma.
  obtain ⟨h_get, h_proof_eq⟩ :=
    extractor_chain_match idx_o log_c root_c.1 leaf_o proof_o
      h_no_coll_lc h_ne_none_lc h_chain_lc
  refine ⟨?_, ?_⟩
  · rw [← h_tree_eq]; exact h_get
  · rw [← h_proof_ext_eq]
    exact h_proof_eq.symm

end InductiveMerkleTree
