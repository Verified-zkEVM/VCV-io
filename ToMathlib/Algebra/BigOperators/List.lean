/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# List products of constants

`(xs.map fun _ => c).prod = c ^ xs.length`.
-/

public section

@[simp]
lemma List.prod_map_const {α M : Type*} [CommMonoid M] (xs : List α) (c : M) :
    (xs.map (fun _ => c)).prod = c ^ xs.length := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.prod_cons, ih,
      List.length_cons, pow_succ, mul_comm]
