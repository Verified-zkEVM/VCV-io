/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.Distributions.Uniform

/-!
# Lemmas about `PMF`

The monad-instance unfolding equations, extensionality off a single point, and uniform
distributions under bijections.
-/

public section

universe u

lemma PMF.apply_eq_one_sub_tsum_ite {α} [DecidableEq α] (p : PMF α) (x : α) :
    p x = 1 - (∑' y, if y = x then 0 else p y) := by
  rw [← p.tsum_coe]
  rw [Summable.tsum_eq_add_tsum_ite' x ENNReal.summable]
  refine ENNReal.eq_sub_of_add_eq' ?_ rfl
  simp only [ne_eq, ENNReal.add_eq_top, apply_ne_top, false_or]
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  refine le_trans ?_ (le_of_eq p.tsum_coe)
  refine ENNReal.tsum_le_tsum fun x => ?_
  aesop

open Classical in
/-- Two `PMF` that agree on all but one point are actually equal. -/
lemma PMF.ext_forall_ne {α} {p q : PMF α} (x : α)
    (h : ∀ y ≠ x, p y = q y) : p = q := by
  refine PMF.ext fun y => ?_
  by_cases hy : y = x
  · rw [p.apply_eq_one_sub_tsum_ite, q.apply_eq_one_sub_tsum_ite]
    subst hy
    simp_all only [ne_eq, not_false_eq_true]
  · refine h y hy

@[simp]
lemma PMF.monad_pure_eq_pure {α : Type u} (x : α) :
    (Pure.pure x : PMF α) = PMF.pure x := rfl

@[simp]
lemma PMF.monad_bind_eq_bind {α β : Type u}
      (p : PMF α) (q : α → PMF β) : p >>= q = p.bind q := rfl

open Classical in
lemma PMF.uniformOfFintype_map_of_bijective {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  have heq := Fintype.card_congr (Equiv.ofBijective f hf)
  ext x; obtain ⟨a, rfl⟩ := hf.2 x
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, heq, hf.1.eq_iff, eq_comm (a := a)]
  convert tsum_ite_eq a (fun _ : α => ((Fintype.card β : ENNReal)⁻¹))

open Classical in
/-- This doesn't get applied properly without `Classical` so add with high priority. -/
@[simp high] lemma PMF.some_map_apply_some {α} (p : PMF α) (x : α) :
    (p.map Option.some) (some x) = p x := by simp
