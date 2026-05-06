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
    -- The `children` function used by the extractor over `log_c`.
    set children : Option α → Option α × Option α := fun node =>
      match node with
      | none => (none, none)
      | some a =>
        match log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == a) with
        | none => (none, none)
        | some q => (some q.1.1, some q.1.2)
    have h_children_none : children none = (none, none) := rfl
    have h_extr_eq :
        extractor (Skeleton.internal sl sr) log_c root =
          populate_down (Skeleton.internal sl sr) children (some root) := rfl
    -- Step 1: derive `log_c.find? (·.2 == root) = some _` from path-intactness.
    have h_find_some :
        ∃ q, log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) = some q := by
      rcases hf : log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) with _ | q
      · exfalso
        apply h_ne_none
        rw [h_extr_eq, populate_down_internal_def, FullData.get_internal_ofLeft]
        have hch : children (some root) = (none, none) := by
          show (match log_c.find? (fun q' => q'.2 == root) with
            | none => (none, none)
            | some q => (some q.1.1, some q.1.2)) = (none, none)
          rw [hf]
        rw [show (children (some root)).1 = none from by rw [hch]]
        exact populate_down_none_get_eq_none children h_children_none idxLeft.toNodeIndex
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
      rw [h_extr_eq, populate_down_internal_def]
      have hch1 : (children (some root)).1 = some ancestor := by
        show (match log_c.find? (fun q' => q'.2 == root) with
          | none => (none, none)
          | some q => (some q.1.1, some q.1.2)).1 = some ancestor
        rw [h_find_c']
      have hch2 : (children (some root)).2 = some proof.head := by
        show (match log_c.find? (fun q' => q'.2 == root) with
          | none => (none, none)
          | some q => (some q.1.1, some q.1.2)).2 = some proof.head
        rw [h_find_c']
      rw [hch1, hch2]
      rfl
    -- Step 6: path-intactness pushes into the left subtree.
    have h_ne_none_inner :
        (extractor sl log_c ancestor).get idxLeft.toNodeIndex ≠ none := by
      intro hne
      apply h_ne_none
      rw [h_extr_decomp, FullData.get_internal_ofLeft]
      exact hne
    -- Step 7: recurse.
    have h_chain_inner :=
      ih log log_c ancestor leaf proof.tail h_sub h_no_coll h_ne_none_inner h_chain_rec
    refine ⟨ancestor, h_chain_entry_in_lc, h_chain_inner⟩
  | @ofRight sl sr idxRight ih =>
    intros log log_c root leaf proof h_sub h_no_coll h_ne_none h_chain
    obtain ⟨ancestor, h_log_mem, h_chain_rec⟩ := h_chain
    set children : Option α → Option α × Option α := fun node =>
      match node with
      | none => (none, none)
      | some a =>
        match log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == a) with
        | none => (none, none)
        | some q => (some q.1.1, some q.1.2)
    have h_children_none : children none = (none, none) := rfl
    have h_extr_eq :
        extractor (Skeleton.internal sl sr) log_c root =
          populate_down (Skeleton.internal sl sr) children (some root) := rfl
    have h_find_some :
        ∃ q, log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) = some q := by
      rcases hf : log_c.find? (fun q' : (_i : (α × α)) × α => q'.2 == root) with _ | q
      · exfalso
        apply h_ne_none
        rw [h_extr_eq, populate_down_internal_def, FullData.get_internal_ofRight]
        have hch : children (some root) = (none, none) := by
          show (match log_c.find? (fun q' => q'.2 == root) with
            | none => (none, none)
            | some q => (some q.1.1, some q.1.2)) = (none, none)
          rw [hf]
        rw [show (children (some root)).2 = none from by rw [hch]]
        exact populate_down_none_get_eq_none children h_children_none idxRight.toNodeIndex
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
      rw [h_extr_eq, populate_down_internal_def]
      have hch1 : (children (some root)).1 = some proof.head := by
        show (match log_c.find? (fun q' => q'.2 == root) with
          | none => (none, none)
          | some q => (some q.1.1, some q.1.2)).1 = some proof.head
        rw [h_find_c']
      have hch2 : (children (some root)).2 = some ancestor := by
        show (match log_c.find? (fun q' => q'.2 == root) with
          | none => (none, none)
          | some q => (some q.1.1, some q.1.2)).2 = some ancestor
        rw [h_find_c']
      rw [hch1, hch2]
      rfl
    have h_ne_none_inner :
        (extractor sr log_c ancestor).get idxRight.toNodeIndex ≠ none := by
      intro hne
      apply h_ne_none
      rw [h_extr_decomp, FullData.get_internal_ofRight]
      exact hne
    have h_chain_inner :=
      ih log log_c ancestor leaf proof.tail h_sub h_no_coll h_ne_none_inner h_chain_rec
    refine ⟨ancestor, h_chain_entry_in_lc, h_chain_inner⟩

end InductiveMerkleTree
