/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters, Bolton Bailey
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Fin.Basic

/-!
# Counting ordered pairs in `Fin n × Fin n`

The number of strictly increasing pairs `(i, j)` with `i < j` drawn from `Fin n` is the
binomial coefficient `n.choose 2`. This is the combinatorial core of the union-bound step in
birthday-style arguments, where the collision event ranges over the unordered pairs of query
positions.
-/

@[expose] public section

open Finset

namespace Finset

/-- The strictly-increasing pairs over `Fin m` are counted by the Gauss sum `∑_{k < m} k`. -/
theorem card_filter_fst_lt_snd_eq_sum_range (m : ℕ) :
    (univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card = ∑ k ∈ range m, k := by
  induction m with
  | zero => simp
  | succ k ih =>
    -- TODO: This proof is long and maybe unneeded.
    rw [Finset.sum_range_succ, ← ih]
    -- Split the increasing pairs of `Fin (k+1)` into those landing in the `Fin k` block
    -- (via `castSucc`) and the new pairs of the form `(i, last k)`.
    suffices hsplit :
        (univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2)).card =
          (univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).card + k by omega
    let emb : Fin k × Fin k ↪ Fin (k + 1) × Fin (k + 1) :=
      ⟨fun p => (p.1.castSucc, p.2.castSucc), fun a b h => by
        simp only [Prod.ext_iff, Fin.castSucc_inj] at h; exact Prod.ext h.1 h.2⟩
    let newEmb : Fin k ↪ Fin (k + 1) × Fin (k + 1) :=
      ⟨fun i => (i.castSucc, Fin.last k), fun a b h => by
        simp only [Prod.ext_iff, Fin.castSucc_inj, and_true] at h; exact h⟩
    have hunion :
        univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2) =
          (univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb ∪ univ.map newEmb := by
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_map, emb, newEmb, Function.Embedding.coeFn_mk]
      constructor
      · intro hij
        by_cases hj : j = Fin.last k
        · subst hj; right
          exact ⟨i.castPred (Fin.ne_last_of_lt hij), by ext <;> simp [Fin.castSucc_castPred]⟩
        · left
          have hj' : j ≠ Fin.last k := hj
          have hi' : i ≠ Fin.last k :=
            Fin.ne_last_of_lt (lt_trans hij (lt_of_le_of_ne (Fin.le_last j) hj'))
          refine ⟨(i.castPred hi', j.castPred hj'), ?_, ?_⟩
          · exact Fin.castPred_lt_castPred hij hj'
          · ext <;> simp [Fin.castSucc_castPred]
      · rintro (⟨⟨a, b⟩, hab, heq⟩ | ⟨a, heq⟩)
        · have h1 := congr_arg Prod.fst heq
          have h2 := congr_arg Prod.snd heq
          simp only at h1 h2
          rw [← h1, ← h2]
          exact Fin.castSucc_lt_castSucc_iff.mpr hab
        · have h1 := congr_arg Prod.fst heq
          have h2 := congr_arg Prod.snd heq
          simp only at h1 h2
          rw [← h1, ← h2]
          exact Fin.castSucc_lt_last a
    have hdisj : Disjoint
        ((univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb) (univ.map newEmb) := by
      rw [Finset.disjoint_left]
      intro ⟨x, y⟩ hmem1 hmem2
      simp only [Finset.mem_map, Finset.mem_univ, true_and, newEmb,
        Function.Embedding.coeFn_mk] at hmem1 hmem2
      obtain ⟨⟨a, b⟩, _, heq1⟩ := hmem1
      obtain ⟨c, heq2⟩ := hmem2
      have h1 := congr_arg Prod.snd heq1
      have h2 := congr_arg Prod.snd heq2
      simp only at h1 h2
      rw [← h1] at h2
      exact absurd h2.symm (Fin.castSucc_ne_last b)
    rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]

/-- The number of strictly increasing pairs `(i, j)` with `i < j` in `Fin n × Fin n`
is the binomial coefficient `n.choose 2`. -/
theorem card_filter_fst_lt_snd (n : ℕ) :
    (univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card = n.choose 2 := by
  rw [card_filter_fst_lt_snd_eq_sum_range n, Nat.choose_two_right, Finset.sum_range_id]

end Finset
