/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ToMathlib.Data.Vector.Count

/-!
# Lemmas about `List.Vector`

Injectivity of `cons`, `getElem` against `get`, `toList` as `ofFn`, and counting the
indices at which a predicate holds.
-/

public section

section List.Vector

open List (Vector)

-- mathlib?
lemma List.injective2_cons {α : Type*} : Function.Injective2 (List.cons (α := α)) := by
  simp [Function.Injective2]

lemma Vector.injective2_cons {α : Type*} {n : ℕ} :
    Function.Injective2 (Vector.cons : α → List.Vector α n → List.Vector α (n + 1)) := by
  simp [Function.Injective2, Vector.eq_cons_iff]

@[simp]
lemma Vector.getElem_eq_get {α n} (xs : List.Vector α n) (i : ℕ) (h : i < n) :
  xs[i]'h = xs.get ⟨i, h⟩ := rfl

lemma List.Vector.toList_eq_ofFn_get {α : Type} {n : ℕ}
    (xs : List.Vector α n) : xs.toList = List.ofFn xs.get := by
  apply List.ext_getElem
  · simp [List.Vector.toList_length]
  · intro i hi1 hi2
    rw [show xs.toList[i] = xs.get ⟨i, by simpa [List.Vector.toList_length] using hi1⟩ by
        simpa using (List.Vector.get_eq_get_toList xs
          ⟨i, by simpa [List.Vector.toList_length] using hi1⟩).symm]
    simp [List.getElem_ofFn (f := xs.get) (i := i) hi2]

end List.Vector

section ListVectorCounting

lemma List.Vector.card_eq_countP {α : Type} {n : ℕ}
    (xs : List.Vector α n) (p : α → Prop) [DecidablePred p] :
    ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
      xs.toList.countP (fun a => decide (p a)) := by
  let ys : _root_.Vector α n := _root_.Vector.ofFn xs.get
  have hcard : ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
      ({i : Fin n | p ys[↑i]} : Finset (Fin n)).card := by
    simp [ys, _root_.Vector.getElem_ofFn]
  have hcount : ys.countP (fun a => decide (p a)) =
      xs.toList.countP (fun a => decide (p a)) := by
    rw [← _root_.Vector.countP_toList]
    simp [ys, _root_.Vector.toList_ofFn, List.Vector.toList_eq_ofFn_get]
  calc
    ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
        ({i : Fin n | p ys[↑i]} : Finset (Fin n)).card := hcard
    _ = ys.countP (fun a => decide (p a)) := _root_.Vector.card_eq_countP ys p
    _ = xs.toList.countP (fun a => decide (p a)) := hcount

lemma List.Vector.card_eq_count {α : Type} [DecidableEq α] {n : ℕ}
    (xs : List.Vector α n) (x : α) :
    ({i : Fin n | x = xs.get i} : Finset (Fin n)).card = xs.toList.count x := by
  have h := List.Vector.card_eq_countP xs (p := fun a => x = a)
  have hcount : xs.toList.count x = xs.toList.countP (fun a => decide (x = a)) := by
    rw [List.count_eq_countP]
    congr 1
    funext y
    simp [BEq.beq, eq_comm]
  exact h.trans hcount.symm

end ListVectorCounting
