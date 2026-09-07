/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor

/-!
# Online Evolution of Merkle Extraction

The central causal bridge for multi-extractability is local: if appending one fresh query/response
entry changes extraction of an already recorded root, then the new response was already a live
target immediately before it was sampled. This module proves that statement directly from the
extractor's first-matching-entry semantics.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open BinaryTree

variable {Query Address Y : Type} [DecidableEq Address] [DecidableEq Y]

private lemma children_append_singleton_of_eq_some
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (log : MerkleTreeExtractor.QueryLog Query Y) (address : Address) (root : Y)
    (children : Y × Y) (entry : (_ : Query) × Y)
    (h : MerkleTreeExtractor.children view log address root = some children) :
    MerkleTreeExtractor.children view (log ++ [entry]) address root = some children := by
  unfold MerkleTreeExtractor.children at h ⊢
  rw [List.find?_append]
  cases hfind : List.find?
      (fun entry => view.address entry.1 == address && entry.2 == root) log with
  | none => simp [hfind] at h
  | some found => simpa [hfind] using h

private lemma children_append_singleton_some_of_none_response_eq_root
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (log : MerkleTreeExtractor.QueryLog Query Y) (address : Address) (root response : Y)
    (query : Query) (children : Y × Y)
    (hbefore : MerkleTreeExtractor.children view log address root = none)
    (hafter : MerkleTreeExtractor.children view (log ++ [⟨query, response⟩]) address root =
      some children) :
    response = root := by
  unfold MerkleTreeExtractor.children at hbefore hafter
  have hfind : List.find?
      (fun entry => view.address entry.1 == address && entry.2 == root) log = none := by
    cases h : List.find?
        (fun entry => view.address entry.1 == address && entry.2 == root) log with
    | none => rfl
    | some entry => simp [h] at hbefore
  cases hpredicate : (view.address query == address && response == root) with
  | false =>
      simp only [List.find?_append, hfind, Option.none_or, List.find?_singleton,
        hpredicate] at hafter
      simp at hafter
  | true =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hpredicate
      exact hpredicate.2

private lemma children_append_singleton_eq_of_mem
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (log : MerkleTreeExtractor.QueryLog Query Y) (address : Address) (root : Y)
    (entry : (_ : Query) × Y) (hmem : entry ∈ log) :
    MerkleTreeExtractor.children view (log ++ [entry]) address root =
      MerkleTreeExtractor.children view log address root := by
  unfold MerkleTreeExtractor.children
  rw [List.find?_append]
  cases hfind : List.find?
      (fun candidate => view.address candidate.1 == address && candidate.2 == root) log with
  | some found => simp
  | none =>
      have hpredicate := (List.find?_eq_none.mp hfind) entry hmem
      simp [hpredicate]

/-- Re-appending an entry already present in the log cannot change extraction. In a caching/logging
execution this rules out cache hits as witnesses to the adjacent-step evolution theorem. -/
theorem tree_append_singleton_eq_of_mem
    (view : MerkleTreeExtractor.QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (entry : (_ : Query) × Y) (hmem : entry ∈ log) :
    MerkleTreeExtractor.tree view s addressKey (log ++ [entry]) root =
      MerkleTreeExtractor.tree view s addressKey log root := by
  induction s generalizing root with
  | leaf => rfl
  | internal left right ihLeft ihRight =>
      have hchildren := children_append_singleton_eq_of_mem
        view log (addressKey .ofInternal) root entry hmem
      simp only [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt]
      rw [hchildren]
      cases hbefore : MerkleTreeExtractor.children view log
          (addressKey .ofInternal) root with
      | none => rfl
      | some children =>
          obtain ⟨leftRoot, rightRoot⟩ := children
          have hleft := ihLeft (fun address => addressKey (.ofLeft address)) leftRoot
          have hright := ihRight (fun address => addressKey (.ofRight address)) rightRoot
          change MerkleTreeExtractor.treeAt view left
              (fun address => addressKey (.ofLeft address)) (log ++ [entry]) leftRoot =
            MerkleTreeExtractor.treeAt view left
              (fun address => addressKey (.ofLeft address)) log leftRoot at hleft
          change MerkleTreeExtractor.treeAt view right
              (fun address => addressKey (.ofRight address)) (log ++ [entry]) rightRoot =
            MerkleTreeExtractor.treeAt view right
              (fun address => addressKey (.ofRight address)) log rightRoot at hright
          change
            FullData.internal (some root)
                (MerkleTreeExtractor.treeAt view left
                  (fun address => addressKey (.ofLeft address)) (log ++ [entry]) leftRoot)
                (MerkleTreeExtractor.treeAt view right
                  (fun address => addressKey (.ofRight address)) (log ++ [entry]) rightRoot) =
              FullData.internal (some root)
                (MerkleTreeExtractor.treeAt view left
                  (fun address => addressKey (.ofLeft address)) log leftRoot)
                (MerkleTreeExtractor.treeAt view right
                  (fun address => addressKey (.ofRight address)) log rightRoot)
          rw [hleft, hright]

/-- Appending one entry can change extraction only when its response was a live target before the
append. The target set is computed from the pre-sample log, so the statement is causal and can be
fed to an online random-oracle stopping argument. -/
theorem tree_ne_append_singleton_implies_response_mem_targets
    (view : MerkleTreeExtractor.QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (query : Query) (response : Y)
    (hne : MerkleTreeExtractor.tree view s addressKey log root ≠
      MerkleTreeExtractor.tree view s addressKey (log ++ [⟨query, response⟩]) root) :
    response ∈ MerkleTreeExtractor.targets view s addressKey log root := by
  induction s generalizing root with
  | leaf =>
      exact absurd rfl hne
  | internal left right ihLeft ihRight =>
      simp only [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt] at hne
      cases hbefore : MerkleTreeExtractor.children view log (addressKey .ofInternal) root with
      | none =>
          cases hafter : MerkleTreeExtractor.children view (log ++ [⟨query, response⟩])
              (addressKey .ofInternal) root with
          | none => simp [hbefore, hafter] at hne
          | some children =>
              have hresponse := children_append_singleton_some_of_none_response_eq_root
                view log (addressKey .ofInternal) root response query children hbefore hafter
              simp [MerkleTreeExtractor.targets, hbefore, hresponse]
      | some children =>
          have hafter := children_append_singleton_of_eq_some view log
            (addressKey .ofInternal) root children ⟨query, response⟩ hbefore
          obtain ⟨leftRoot, rightRoot⟩ := children
          rw [hbefore, hafter] at hne
          change
            FullData.internal (some root)
                (MerkleTreeExtractor.treeAt view left
                  (fun address => addressKey (.ofLeft address)) log leftRoot)
                (MerkleTreeExtractor.treeAt view right
                  (fun address => addressKey (.ofRight address)) log rightRoot) ≠
              FullData.internal (some root)
                (MerkleTreeExtractor.treeAt view left
                  (fun address => addressKey (.ofLeft address))
                  (log ++ [⟨query, response⟩]) leftRoot)
                (MerkleTreeExtractor.treeAt view right
                  (fun address => addressKey (.ofRight address))
                  (log ++ [⟨query, response⟩]) rightRoot) at hne
          simp only [MerkleTreeExtractor.targets, hbefore, List.mem_cons,
            List.mem_append]
          by_cases hleft :
              MerkleTreeExtractor.treeAt view left
                  (fun address => addressKey (.ofLeft address)) log leftRoot =
                MerkleTreeExtractor.treeAt view left
                  (fun address => addressKey (.ofLeft address))
                  (log ++ [⟨query, response⟩]) leftRoot
          · have hright :
                MerkleTreeExtractor.treeAt view right
                    (fun address => addressKey (.ofRight address)) log rightRoot ≠
                  MerkleTreeExtractor.treeAt view right
                    (fun address => addressKey (.ofRight address))
                    (log ++ [⟨query, response⟩]) rightRoot := by
              intro hright
              apply hne
              rw [hleft, hright]
            exact Or.inr (Or.inr (ihRight
              (fun address => addressKey (.ofRight address)) rightRoot hright))
          · exact Or.inr (Or.inl (ihLeft
              (fun address => addressKey (.ofLeft address)) leftRoot hleft))

/-- If a suffix changes extraction, some first changing entry in that suffix has a response in
the live target set computed strictly before that entry. The decomposition exposes the causal
prefix needed by an online stopping argument. -/
theorem tree_ne_append_implies_exists_live_hit
    (view : MerkleTreeExtractor.QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log suffix : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (hne : MerkleTreeExtractor.tree view s addressKey log root ≠
      MerkleTreeExtractor.tree view s addressKey (log ++ suffix) root) :
    ∃ before entry rest,
      suffix = before ++ entry :: rest ∧
        entry.2 ∈ MerkleTreeExtractor.targets view s addressKey (log ++ before) root := by
  induction suffix generalizing log with
  | nil => simp at hne
  | cons entry suffix ih =>
      by_cases hfirst : MerkleTreeExtractor.tree view s addressKey log root ≠
          MerkleTreeExtractor.tree view s addressKey (log ++ [entry]) root
      · refine ⟨[], entry, suffix, rfl, ?_⟩
        simpa using tree_ne_append_singleton_implies_response_mem_targets
          view s addressKey log root entry.1 entry.2 hfirst
      · have hfirstEq : MerkleTreeExtractor.tree view s addressKey log root =
            MerkleTreeExtractor.tree view s addressKey (log ++ [entry]) root :=
          not_ne_iff.mp hfirst
        have htail : MerkleTreeExtractor.tree view s addressKey (log ++ [entry]) root ≠
            MerkleTreeExtractor.tree view s addressKey ((log ++ [entry]) ++ suffix) root := by
          intro heq
          apply hne
          rw [hfirstEq, heq]
          simp [List.append_assoc]
        obtain ⟨before, changingEntry, rest, hsuffix, htarget⟩ :=
          ih (log ++ [entry]) htail
        refine ⟨entry :: before, changingEntry, rest, ?_, ?_⟩
        · simp [hsuffix]
        · simpa [List.append_assoc] using htarget

/-- The reached-target list is a semantic projection of the extracted partial tree.  In
particular, two logs producing the same extracted tree expose the same targets even when their
irrelevant query entries differ. -/
theorem MerkleTreeExtractor.targets_eq_of_tree_eq
    (view : MerkleTreeExtractor.QueryView Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (leftLog rightLog : MerkleTreeExtractor.QueryLog Query Y) (leftRoot rightRoot : Y)
    (htree : MerkleTreeExtractor.tree view s addressKey leftLog leftRoot =
      MerkleTreeExtractor.tree view s addressKey rightLog rightRoot) :
    MerkleTreeExtractor.targets view s addressKey leftLog leftRoot =
      MerkleTreeExtractor.targets view s addressKey rightLog rightRoot := by
  induction s generalizing leftRoot rightRoot with
  | leaf =>
      simpa [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt,
        MerkleTreeExtractor.targets] using htree
  | internal left right ihLeft ihRight =>
      cases hleft : MerkleTreeExtractor.children view leftLog
          (addressKey .ofInternal) leftRoot <;>
        cases hright : MerkleTreeExtractor.children view rightLog
          (addressKey .ofInternal) rightRoot
      · simpa [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt,
          MerkleTreeExtractor.targets, hleft, hright] using htree
      · simp only [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hleft, hright,
          Option.some.injEq, FullData.internal.injEq] at htree
        have himpossible := congrArg FullData.getRootValue htree.2.1
        simp [MerkleTreeExtractor.treeAt_getRootValue] at himpossible
      · simp only [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hleft, hright,
          Option.some.injEq, FullData.internal.injEq] at htree
        have himpossible := congrArg FullData.getRootValue htree.2.1
        simp [MerkleTreeExtractor.treeAt_getRootValue] at himpossible
      · rename_i leftChildren rightChildren
        obtain ⟨leftLeft, leftRight⟩ := leftChildren
        obtain ⟨rightLeft, rightRight⟩ := rightChildren
        simp only [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hleft, hright,
          Option.some.injEq, FullData.internal.injEq] at htree
        simp only [MerkleTreeExtractor.targets, hleft, hright]
        rw [htree.1]
        rw [ihLeft (fun position => addressKey (.ofLeft position)) _ _ htree.2.1]
        rw [ihRight (fun position => addressKey (.ofRight position)) _ _ htree.2.2]

end MerkleTreeMultiExtractability
