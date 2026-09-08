/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Infinite sums over `Option` and along a `cast`
-/

public section

universe u

open Classical in
lemma tsum_option {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T2Space α]
    (f : Option β → α) (hf : Summable (Function.update f none 0)) :
    ∑' x : Option β, f x = f none + ∑' x : β, f (some x) := by
  refine (Summable.tsum_eq_add_tsum_ite' none hf).trans ?_
  refine congr_arg (f none + ·) ?_
  refine tsum_eq_tsum_of_ne_zero_bij (fun x ↦ some x.1) ?_ ?_ ?_
  · intro x y
    simp [SetCoe.ext_iff]
  · intro x
    cases x <;> simp
  · simp

theorem tsum_cast {α β : Type u} {f : α → ENNReal} {g : β → ENNReal}
    (h : α = β) (h' : ∀ a, f a = g (cast h a)) :
      (∑' (a : α), f a) = (∑' (b : β), g b) := by
  subst h; simp [h']
