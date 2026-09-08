/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor
import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Transcript extractor for inductive Merkle trees

This file contains the pure, executable extraction algorithm used by the Merkle-tree
extractability games. Given a claimed root and the committing phase's hash-query log, the
extractor follows response-to-input links down the existing `Skeleton` and returns a partial
tree `FullData (Option α) s`.

The extractor makes no oracle calls. At a node labelled `a`, `children` selects the first
logged query `(x, y)` whose response is `a`. If no such query exists, `tree` leaves the
corresponding descendants unknown. On collision-free logs, the selected preimage is unique,
so the use of `List.find?` does not introduce an additional choice.

The `targets` function follows the same response-link recurrence and exposes the labels used by
the probability proof to identify the finite set of random-oracle answers that could change the
extracted tree.
-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec BinaryTree

variable {α : Type}

namespace Extractor

variable [DecidableEq α]

/-- View an unaddressed `(left, right)` query as the unit-key specialization of the generic
Merkle extractor. -/
def queryView : MerkleTreeExtractor.QueryView (α × α) Unit α where
  address _ := ()
  input := id

/-- Recover the children of `a` from the first logged hash query whose response is `a`. -/
def children (log : (spec α).QueryLog) (a : α) : Option (α × α) :=
  MerkleTreeExtractor.children queryView log () a

/--
Reconstruct the partial Merkle tree rooted at `root` from a hash-query log.

The root is always present. Descendants are present exactly while the log contains a chain of
queries whose responses match the labels reached from the root.
-/
def tree (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    FullData (Option α) s :=
  MerkleTreeExtractor.tree queryView s (fun _ => ()) log root

/-- The leaf and authentication path exposed by an extracted partial tree at `idx`.

This remains a structure, rather than an alias of the generic extractor's wrapper, to preserve
the existing qualified constructor and projection API. -/
structure Opening (α : Type) {s : Skeleton} (idx : SkeletonLeafIndex s) where
  /-- The extracted leaf, or `none` if the transcript does not reach it. -/
  leaf : Option α
  /-- The extracted sibling path; unknown siblings are represented by `none`. -/
  proof : List.Vector (Option α) idx.depth

/-- Inspect the leaf and authentication path extracted at `idx`. -/
def opening {s : Skeleton} (tree : FullData (Option α) s)
    (idx : SkeletonLeafIndex s) : Opening α idx where
  leaf := tree.get idx.toNodeIndex
  proof := generateProof tree idx

/-- The non-dummy labels reached by extraction from `root`. -/
def targets (s : Skeleton) (log : (spec α).QueryLog) (root : α) : List α :=
  MerkleTreeExtractor.targets queryView s (fun _ => ()) log root

@[simp]
theorem tree_leaf (log : (spec α).QueryLog) (root : α) :
    tree .leaf log root = FullData.leaf (some root) := by
  rfl

@[simp]
theorem tree_getRootValue (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    (tree s log root).getRootValue = some root := by
  exact MerkleTreeExtractor.treeAt_getRootValue queryView s (fun _ => ()) log root

/-- If no logged response equals `a`, extraction cannot recover its children. -/
theorem children_eq_none_of_find?_eq_none (log : (spec α).QueryLog) (a : α)
    (hfind : log.find? (fun ⟨_, response⟩ => response == a) = none) :
    children log a = none := by
  simp [children, MerkleTreeExtractor.children, queryView, hfind]

omit [DecidableEq α] in
private theorem populateDown_none_eq (s : Skeleton)
    (f : Option α → Option α × Option α) (hf : f none = (none, none)) :
    populateDown s f none =
      populateDown s (fun _ : Option α => (none, none)) none := by
  induction s with
  | leaf => rfl
  | internal left right ihLeft ihRight =>
      simp [populateDown_internal_def, hf, ihLeft, ihRight]

/-- The internal-node equation when the log does not determine children for `root`. -/
theorem tree_internal_of_children_eq_none (left right : Skeleton)
    (log : (spec α).QueryLog) (root : α) (hchildren : children log root = none) :
    tree (.internal left right) log root =
      FullData.internal (some root)
        (populateDown left (Option.bindPair (children log)) none)
        (populateDown right (Option.bindPair (children log)) none) := by
  change MerkleTreeExtractor.children queryView log () root = none at hchildren
  simp only [tree, MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hchildren]
  rw [populateDown_none_eq left (Option.bindPair (children log)) rfl,
    populateDown_none_eq right (Option.bindPair (children log)) rfl]

/-- The internal-node equation when the log determines children `(x, y)` for `root`. -/
theorem tree_internal_of_children_eq_some (left right : Skeleton)
    (log : (spec α).QueryLog) (root x y : α)
    (hchildren : children log root = some (x, y)) :
    tree (.internal left right) log root =
      FullData.internal (some root) (tree left log x) (tree right log y) := by
  change MerkleTreeExtractor.children queryView log () root = some (x, y) at hchildren
  simp [tree, MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hchildren]

@[simp]
theorem targets_leaf (log : (spec α).QueryLog) (root : α) :
    targets .leaf log root = [root] := rfl

@[simp]
theorem root_mem_targets (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    root ∈ targets s log root :=
  MerkleTreeExtractor.root_mem_targets queryView s (fun _ => ()) log root

theorem targets_internal_of_children_eq_none (left right : Skeleton)
    (log : (spec α).QueryLog) (root : α) (hchildren : children log root = none) :
    targets (.internal left right) log root = [root] := by
  change MerkleTreeExtractor.children queryView log () root = none at hchildren
  simpa [targets] using
    (MerkleTreeExtractor.targets_internal_of_children_eq_none queryView left right
      (fun _ => ()) log root hchildren)

theorem targets_internal_of_children_eq_some (left right : Skeleton)
    (log : (spec α).QueryLog) (root x y : α)
    (hchildren : children log root = some (x, y)) :
    targets (.internal left right) log root =
      root :: (targets left log x ++ targets right log y) := by
  change MerkleTreeExtractor.children queryView log () root = some (x, y) at hchildren
  simpa [targets] using
    (MerkleTreeExtractor.targets_internal_of_children_eq_some queryView left right
      (fun _ => ()) log root x y hchildren)

omit [DecidableEq α] in
@[simp]
theorem opening_leaf {s : Skeleton} (tree : FullData (Option α) s)
    (idx : SkeletonLeafIndex s) :
    (opening tree idx).leaf = tree.get idx.toNodeIndex := rfl

omit [DecidableEq α] in
@[simp]
theorem opening_proof {s : Skeleton} (tree : FullData (Option α) s)
    (idx : SkeletonLeafIndex s) :
    (opening tree idx).proof = generateProof tree idx := rfl

/-- If the first logged preimage of `root` is `(x, y)`, extraction recurses from `x` and `y`. -/
theorem tree_internal_eq_of_find?_eq (left right : Skeleton)
    (log : (spec α).QueryLog) (root x y : α)
    (hfind : log.find? (fun ⟨_, response⟩ => response == root) =
      some ⟨(x, y), root⟩) :
    tree (.internal left right) log root =
      FullData.internal (some root) (tree left log x) (tree right log y) := by
  apply tree_internal_of_children_eq_some
  simp [children, MerkleTreeExtractor.children, queryView, hfind]

/-- A full binary skeleton with `L` leaves exposes at most `2L - 1` extractor targets. -/
theorem targets_length_le (s : Skeleton) (log : (spec α).QueryLog) (root : α) :
    (targets s log root).length ≤ 2 * s.leafCount - 1 :=
  MerkleTreeExtractor.targets_length_le queryView s (fun _ => ()) log root

/-- Every extractor target is the claimed root or one component of a logged hash input. -/
theorem mem_targets_root_or_log_input (s : Skeleton) (log : (spec α).QueryLog)
    (root : α) {target : α} (htarget : target ∈ targets s log root) :
    target = root ∨ ∃ entry ∈ log, target = entry.1.1 ∨ target = entry.1.2 := by
  simpa [queryView] using
    (MerkleTreeExtractor.mem_targets_root_or_log_input queryView s (fun _ => ()) log root htarget)

end Extractor

/-! Legacy names retained so downstream users can migrate to the explicit extractor namespace. -/

/-- Compatibility alias for `Extractor.children`. -/
abbrev extractorChildren [DecidableEq α] := Extractor.children (α := α)

/-- Compatibility alias for `Extractor.tree`. -/
abbrev extractor [DecidableEq α] := Extractor.tree (α := α)

end InductiveMerkleTree
