/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ToMathlib.Data.List.Count

/-!
# Counting predicates over `Vector`

The number of indices of a core `Vector` at which a predicate holds, and the `count`
specialisation.
-/

public section

section VectorCounting

variable {α : Type}

lemma _root_.Vector.card_eq_countP {n : ℕ}
    (xs : Vector α n) (p : α → Prop) [DecidablePred p] :
    ({i : Fin n | p xs[↑i]} : Finset (Fin n)).card =
      xs.countP (fun a => decide (p a)) := by
  rcases xs with ⟨as, hs⟩
  calc
    ({i : Fin n | p as[↑i]} : Finset (Fin n)).card =
        ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size)).card := by
          refine Finset.card_nbij (i := Fin.cast hs.symm) ?hi ?hinj ?hsurj
          · intro i hi
            simp at hi ⊢
            simpa [Fin.cast_val_eq_self] using hi
          · intro i hi j hj hij
            exact Fin.cast_injective hs.symm hij
          · intro j hj
            refine ⟨Fin.cast hs j, ?_, ?_⟩
            · simp at hj ⊢
              simpa [Fin.cast_cast] using hj
            · simp
    _ = as.countP (fun a => decide (p a)) := Array.card_eq_countP as p
    _ = (Vector.mk as hs).countP (fun a => decide (p a)) := by simp [Vector.countP_mk]

lemma _root_.Vector.card_eq_count [DecidableEq α] {n : ℕ}
    (xs : Vector α n) (x : α) :
    ({i : Fin n | x = xs[↑i]} : Finset (Fin n)).card = xs.count x := by
  rw [Vector.count_eq_countP]
  have hbeq : (fun y : α => y == x) = fun y => decide (x = y) := by
    funext y
    simp [beq_eq_decide, eq_comm]
  rw [hbeq]
  simpa using (Vector.card_eq_countP xs (p := fun y => x = y))

end VectorCounting
