/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Finite sums over `Function.update` and scaled indicators

Rewriting `∑ i, Function.update f j v i` in terms of `∑ i, f i`, the filtered variants, and
`Finset.sum_boole'` for a scaled indicator.
-/

public section

open Finset in
/-- Updating one coordinate by `+1` increases the total sum by exactly one. -/
lemma sum_update_succ_count {ι : Type} [Fintype ι] [DecidableEq ι]
    (counts : ι → ℕ) (i : ι) :
    ∑ j : ι, Function.update counts i (counts i + 1) j =
      (∑ j : ι, counts j) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  omega

/-- Updating one coordinate of a `ℕ`-valued function by `-1` at a positive-valued coordinate
decreases the total sum by exactly one. -/
lemma sum_update_pred {ι : Type*} [Fintype ι] [DecidableEq ι]
    {qc : ι → ℕ} {t : ι} (ht : 0 < qc t) :
    ∑ i, Function.update qc t (qc t - 1) i = (∑ i, qc i) - 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ t), ← Finset.sum_erase_add _ _ (Finset.mem_univ t),
    Finset.sdiff_singleton_eq_erase]
  omega

/-- Filtered sum after updating a `ℕ`-valued function by `-1` at a positive-valued coordinate
inside the filter. -/
lemma sum_filter_update_of_pred_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → Prop} [DecidablePred p] {qc : ι → ℕ} {t : ι} (hpt : p t) (hqt : 0 < qc t) :
    ∑ i ∈ Finset.univ.filter p, Function.update qc t (qc t - 1) i =
      (∑ i ∈ Finset.univ.filter p, qc i) - 1 := by
  have htmem : t ∈ Finset.univ.filter p :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩
  rw [Finset.sum_update_of_mem htmem, ← Finset.sum_erase_add _ _ htmem,
    Finset.sdiff_singleton_eq_erase]
  omega

/-- Updating a `ℕ`-valued function at an index outside the filter leaves the filtered sum
unchanged. -/
lemma sum_filter_update_of_not_pred {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → Prop} [DecidablePred p] {qc : ι → ℕ} {t : ι} (hpt : ¬ p t) :
    ∑ i ∈ Finset.univ.filter p, Function.update qc t (qc t - 1) i =
      ∑ i ∈ Finset.univ.filter p, qc i := by
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hit : i ≠ t := fun heq => hpt (heq ▸ (Finset.mem_filter.mp hi).2)
  rw [Function.update_of_ne hit]

open ENNReal

@[simp] lemma Finset.sum_boole' {ι β : Type*} [AddCommMonoid β] (r : β)
    (p) [DecidablePred p] (s : Finset ι) :
    (∑ x ∈ s, if p x then r else 0 : β) = (s.filter p).card • r :=
calc (∑ x ∈ s, if p x then r else 0 : β) = (∑ x ∈ s, if p x then 1 else 0 : ℕ) • r :=
    by simp only [← Finset.sum_nsmul_assoc, ite_smul, one_smul, zero_smul]
  _ = (s.filter p).card • r := by simp only [sum_boole, Nat.cast_id]
