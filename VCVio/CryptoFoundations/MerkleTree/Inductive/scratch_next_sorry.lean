-- Scratch file for proving the two sorries in extractability_game_no_coll_match.
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
  | leaf =>
    cases idx
    rfl
  | internal sl sr ihL ihR =>
    cases idx with
    | ofInternal => rfl
    | ofLeft idxL =>
      change (populate_down (.internal sl sr) children none).get
        (SkeletonNodeIndex.ofLeft idxL) = none
      rw [populate_down_internal_def, FullData.get_internal_ofLeft]
      have : (children none).1 = none := by rw [h_none]
      rw [this]
      exact ihL idxL
    | ofRight idxR =>
      change (populate_down (.internal sl sr) children none).get
        (SkeletonNodeIndex.ofRight idxR) = none
      rw [populate_down_internal_def, FullData.get_internal_ofRight]
      have : (children none).2 = none := by rw [h_none]
      rw [this]
      exact ihR idxR

end InductiveMerkleTree
