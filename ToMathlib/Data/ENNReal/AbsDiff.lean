/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak

/-!
# Symmetric Absolute Difference and Supporting Lemmas for `ℝ≥0∞`

This file defines `ENNReal.absDiff`, a symmetric absolute difference on extended non-negative
reals using truncating subtraction, and proves supporting lemmas about `tsum` and `absDiff`
interactions. These are the building blocks for total variation distance on `PMF`.

## Main definitions

- `ENNReal.absDiff a b` — `(a - b) + (b - a)`, a symmetric absolute difference in `ℝ≥0∞`

## Main results

- `ENNReal.absDiff_eq_edist` — `absDiff` is Mathlib's `edist` on `ℝ≥0∞` (the weak extended metric)
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

/-- `absDiff` is the extended distance Mathlib puts on `ℝ≥0∞` (through `WithTop ℝ≥0`, a weak
extended metric: `⊤` is at distance `⊤` from every finite point and `0` from itself). Mathlib has
no closed form for that `edist` yet, so this is the bridge from the truncated-subtraction spelling
to `edist` and its `WeakPseudoEMetricSpace` lemmas. -/
lemma absDiff_eq_edist (a b : ℝ≥0∞) : ENNReal.absDiff a b = edist a b := by
  induction a with
  | top => induction b with
    | top => simp [ENNReal.absDiff]; rfl
    | coe b => simp [ENNReal.absDiff]; rfl
  | coe a => induction b with
    | top => simp [ENNReal.absDiff]; rfl
    | coe b =>
      change _ = ((edist a b : ℝ≥0∞))
      rw [edist_nndist, ENNReal.absDiff, ← ENNReal.coe_sub, ← ENNReal.coe_sub, ← ENNReal.coe_add,
        NNReal.nndist_eq]
      congr 1
      rcases le_total a b with h | h <;> simp [tsub_eq_zero_of_le h]

lemma absDiff_triangle (a b c : ℝ≥0∞) :
    ENNReal.absDiff a c ≤ ENNReal.absDiff a b + ENNReal.absDiff b c := by
  simp only [absDiff_eq_edist]
  exact WeakPseudoEMetricSpace.edist_triangle a b c

/-- `|a - b| + 2·min a b = a + b`, the truncated-subtraction form of the identity that splits a
total mass into its overlap and its discrepancy. -/
lemma absDiff_add_two_mul_min (a b : ℝ≥0∞) :
    ENNReal.absDiff a b + 2 * (a ⊓ b) = a + b := by
  have h1 : a - b + a ⊓ b = a := tsub_add_min
  have h2 : b - a + b ⊓ a = b := tsub_add_min
  rw [ENNReal.absDiff, two_mul]
  calc a - b + (b - a) + (a ⊓ b + a ⊓ b)
      = (a - b + a ⊓ b) + ((b - a) + b ⊓ a) := by rw [inf_comm b a]; ac_rfl
    _ = a + b := by rw [h1, h2]

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
  rw [absDiff_eq_edist]
  exact ⟨WeakEMetricSpace.eq_of_edist_eq_zero, fun h => h ▸ WeakPseudoEMetricSpace.edist_self a⟩

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
