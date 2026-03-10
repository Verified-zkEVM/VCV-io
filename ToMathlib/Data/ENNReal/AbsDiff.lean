/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Symmetric Absolute Difference and Supporting Lemmas for `ℝ≥0∞`

This file defines `ENNReal.absDiff`, a symmetric absolute difference on extended non-negative
reals using truncating subtraction, and proves supporting lemmas about `tsum` and `absDiff`
interactions. These are the building blocks for total variation distance on `PMF`.

## Main definitions

- `ENNReal.absDiff a b` — `(a - b) + (b - a)`, a symmetric absolute difference in `ℝ≥0∞`

## Main results

- `ENNReal.absDiff_toReal` — connection to real-valued absolute difference
- `ENNReal.absDiff_triangle` — triangle inequality
- `ENNReal.absDiff_tsum_le` — subadditivity of `absDiff` over infinite sums
- `ENNReal.absDiff_mul_right_le` — `|ac - bc| ≤ |a - b| · c`
- `ENNReal.tsum_fiber` — fiber decomposition for `ℝ≥0∞`-valued sums
-/

@[expose] public section

noncomputable section

open ENNReal

namespace ENNReal

/-- Symmetric absolute difference in `ℝ≥0∞`, defined via truncating subtraction.
Satisfies `absDiff a b = |a.toReal - b.toReal|` when both are finite. -/
protected def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) + (b - a)

@[simp] lemma absDiff_self (a : ℝ≥0∞) : ENNReal.absDiff a a = 0 := by
  simp [ENNReal.absDiff]

lemma absDiff_comm (a b : ℝ≥0∞) : ENNReal.absDiff a b = ENNReal.absDiff b a := by
  simp [ENNReal.absDiff, add_comm]

lemma absDiff_le_add (a b : ℝ≥0∞) : ENNReal.absDiff a b ≤ a + b :=
  add_le_add tsub_le_self tsub_le_self

private lemma tsub_le_tsub_add_tsub (a b c : ℝ≥0∞) : a - c ≤ (a - b) + (b - c) := by
  rw [tsub_le_iff_right]
  calc a ≤ (a - b) + b := le_tsub_add
    _ ≤ (a - b) + ((b - c) + c) := by gcongr; exact le_tsub_add
    _ = ((a - b) + (b - c)) + c := (add_assoc _ _ _).symm

lemma absDiff_triangle (a b c : ℝ≥0∞) :
    ENNReal.absDiff a c ≤ ENNReal.absDiff a b + ENNReal.absDiff b c := by
  unfold ENNReal.absDiff
  calc (a - c) + (c - a)
      ≤ ((a - b) + (b - c)) + ((c - b) + (b - a)) :=
        add_le_add (tsub_le_tsub_add_tsub a b c) (tsub_le_tsub_add_tsub c b a)
    _ = ((a - b) + (b - a)) + ((b - c) + (c - b)) := by ring

lemma absDiff_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (ENNReal.absDiff a b).toReal = |a.toReal - b.toReal| := by
  rcases le_total a b with hab | hab
  · have h1 : a - b = 0 := tsub_eq_zero_of_le hab
    have h2 : a.toReal ≤ b.toReal := (toReal_le_toReal ha hb).mpr hab
    simp only [ENNReal.absDiff, h1, zero_add, abs_of_nonpos (sub_nonpos.mpr h2), neg_sub]
    exact toReal_sub_of_le hab hb
  · have h1 : b - a = 0 := tsub_eq_zero_of_le hab
    have h2 : b.toReal ≤ a.toReal := (toReal_le_toReal hb ha).mpr hab
    simp only [ENNReal.absDiff, h1, add_zero, abs_of_nonneg (sub_nonneg.mpr h2)]
    exact toReal_sub_of_le hab ha

lemma absDiff_tsub_tsub {a b c : ℝ≥0∞} (ha : a ≤ c) (hb : b ≤ c) (hc : c ≠ ⊤) :
    ENNReal.absDiff (c - a) (c - b) = ENNReal.absDiff a b := by
  have hca_ne : c - a ≠ ⊤ := ne_top_of_le_ne_top hc tsub_le_self
  have hcb_ne : c - b ≠ ⊤ := ne_top_of_le_ne_top hc tsub_le_self
  rcases le_total a b with hab | hab
  · have hcb_le_ca : c - b ≤ c - a := tsub_le_tsub_left hab c
    simp only [ENNReal.absDiff, tsub_eq_zero_of_le hab, tsub_eq_zero_of_le hcb_le_ca, add_zero,
      zero_add]
    rw [show c - a = (c - b) + (b - a) from (tsub_add_tsub_cancel hb hab).symm]
    exact ENNReal.add_sub_cancel_left hcb_ne
  · have hca_le_cb : c - a ≤ c - b := tsub_le_tsub_left hab c
    simp only [ENNReal.absDiff, tsub_eq_zero_of_le hab, tsub_eq_zero_of_le hca_le_cb, add_zero,
      zero_add]
    rw [show c - b = (c - a) + (a - b) from (tsub_add_tsub_cancel ha hab).symm]
    exact ENNReal.add_sub_cancel_left hca_ne

@[simp] lemma absDiff_eq_zero {a b : ℝ≥0∞} : ENNReal.absDiff a b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : a - b = 0 := by exact_mod_cast (add_eq_zero.mp h).1
    have h2 : b - a = 0 := by exact_mod_cast (add_eq_zero.mp h).2
    exact le_antisymm (tsub_eq_zero_iff_le.mp h1) (tsub_eq_zero_iff_le.mp h2)
  · rintro rfl; exact absDiff_self _

/-! ### Tsum inequalities -/

lemma tsum_tsub_le_tsum_tsub {α : Type*} (a b : α → ℝ≥0∞) :
    ∑' x, a x - ∑' x, b x ≤ ∑' x, (a x - b x) := by
  rw [tsub_le_iff_right]
  calc ∑' x, a x ≤ ∑' x, ((a x - b x) + b x) :=
        ENNReal.tsum_le_tsum fun x => le_tsub_add
    _ = ∑' x, (a x - b x) + ∑' x, b x := ENNReal.tsum_add

lemma absDiff_tsum_le {α : Type*} (a b : α → ℝ≥0∞) :
    ENNReal.absDiff (∑' x, a x) (∑' x, b x) ≤ ∑' x, ENNReal.absDiff (a x) (b x) := by
  unfold ENNReal.absDiff
  calc (∑' x, a x - ∑' x, b x) + (∑' x, b x - ∑' x, a x)
      ≤ ∑' x, (a x - b x) + ∑' x, (b x - a x) :=
        add_le_add (tsum_tsub_le_tsum_tsub a b) (tsum_tsub_le_tsum_tsub b a)
    _ = ∑' x, ((a x - b x) + (b x - a x)) := ENNReal.tsum_add.symm

/-! ### Multiplication inequality -/

private lemma tsub_mul_le (a b c : ℝ≥0∞) : a * c - b * c ≤ (a - b) * c := by
  rw [tsub_le_iff_right]
  calc a * c ≤ ((a - b) + b) * c := by gcongr; exact le_tsub_add
    _ = (a - b) * c + b * c := add_mul _ _ _

lemma absDiff_mul_right_le (a b c : ℝ≥0∞) :
    ENNReal.absDiff (a * c) (b * c) ≤ ENNReal.absDiff a b * c := by
  simp only [ENNReal.absDiff]
  calc a * c - b * c + (b * c - a * c)
      ≤ (a - b) * c + (b - a) * c :=
        add_le_add (tsub_mul_le a b c) (tsub_mul_le b a c)
    _ = ((a - b) + (b - a)) * c := (add_mul _ _ _).symm

/-! ### Fiber decomposition -/

lemma tsum_fiber {α β : Type*} [DecidableEq β] (f : α → β) (g : α → ℝ≥0∞) :
    ∑' y, ∑' x, (if f x = y then g x else 0) = ∑' x, g x := by
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  simp only [eq_comm (a := f x)]
  exact tsum_ite_eq (f x) (fun _ => g x)

end ENNReal
