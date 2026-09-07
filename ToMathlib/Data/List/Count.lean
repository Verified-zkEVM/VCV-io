/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Counting predicates over lists, `Fin`, and arrays

`List.countP` as a sum over indices, the `Fin` form, and the `Array` corollary.
-/

public section

/-- Summing `1` over list indices that satisfy a predicate is just `countP` applied to `p`. -/
lemma List.countP_eq_sum_fin_ite {α : Type*} (xs : List α) (p : α → Bool) :
    (∑ i : Fin xs.length, if p xs[i] then 1 else 0) = xs.countP p := by
  induction xs with
  | nil => {
    simp only [length_nil, Finset.univ_eq_empty, Finset.sum_boole, Fin.getElem_fin,
      Finset.filter_empty, Finset.card_empty, CharP.cast_eq_zero, countP_nil]
  }
  | cons x xs h => {
    rw [List.countP_cons, ← h]
    refine (Fin.sum_univ_succ _).trans ((add_comm _ _).trans ?_)
    congr 1
  }

lemma List.countP_finRange_getElem {α : Type} (l : List α) (p : α → Bool) :
    (List.finRange l.length).countP (fun i => p l[↑i]) = l.countP p := by
  conv_rhs => rw [← List.map_getElem_finRange l]
  rw [List.countP_map]; rfl

lemma Fin.card_eq_countP_mem {n : ℕ} (s : Finset (Fin n)) :
    s.card = Fin.countP (· ∈ s) := by
  simp [Fin.countP_eq_countP_map_finRange, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]

lemma Array.card_eq_countP {α : Type} (as : Array α)
    (p : α → Prop) [DecidablePred p] :
    ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size)).card =
      as.countP (fun a => decide (p a)) := by
  rw [← Array.countP_toList]
  rw [← List.map_getElem_finRange as.toList, List.countP_map]
  have hcard := Fin.card_eq_countP_mem ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size))
  rw [Fin.countP_eq_countP_map_finRange] at hcard
  convert hcard using 1
  simp only [Array.length_toList, Array.getElem_toList]
  congr 1
  funext i
  simp
