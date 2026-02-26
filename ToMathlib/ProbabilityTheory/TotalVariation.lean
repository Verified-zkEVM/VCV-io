/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Total Variation Distance for PMFs

This file defines total variation distance on probability mass functions and provides a
`MetricSpace` instance for `PMF α`.

We follow the Mathlib convention of providing both an `ℝ≥0∞`-valued version (`etvDist`) and
an `ℝ`-valued version (`tvDist`), connected by `tvDist = etvDist.toReal`.

## Main definitions

- `ENNReal.absDiff a b` — symmetric absolute difference in `ℝ≥0∞`
- `PMF.etvDist p q : ℝ≥0∞` — extended TV distance on PMFs
- `PMF.tvDist p q : ℝ` — TV distance on PMFs
- `PMF.instMetricSpace` — `MetricSpace` instance on `PMF α` via TV distance

## Main results

- `PMF.tvDist_self`, `PMF.tvDist_comm`, `PMF.tvDist_nonneg`
- `PMF.tvDist_triangle` — triangle inequality
- `PMF.tvDist_le_one` — TV distance is bounded by 1
- `PMF.tvDist_eq_zero_iff` — TV distance is zero iff the PMFs are equal
- `PMF.etvDist_option_punit` — closed form for binary distributions
-/

noncomputable section

open ENNReal

/-! ## ENNReal.absDiff -/

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

end ENNReal

/-! ## PMF.tvDist -/

namespace PMF

variable {α : Type*}

/-- Extended total variation distance on PMFs, valued in `ℝ≥0∞`.
Defined as `(1/2) * ∑' x, |p(x) - q(x)|` using `ℝ≥0∞`-valued absolute difference. -/
protected def etvDist (p q : PMF α) : ℝ≥0∞ :=
  (∑' x, ENNReal.absDiff (p x) (q x)) / 2

/-- Total variation distance on PMFs. -/
protected def tvDist (p q : PMF α) : ℝ := (p.etvDist q).toReal

lemma tvDist_def (p q : PMF α) : p.tvDist q = (p.etvDist q).toReal := rfl

/-! ### Properties of etvDist -/

@[simp] lemma etvDist_self (p : PMF α) : p.etvDist p = 0 := by
  simp [PMF.etvDist]

lemma etvDist_comm (p q : PMF α) : p.etvDist q = q.etvDist p := by
  simp only [PMF.etvDist, ENNReal.absDiff_comm]

lemma etvDist_triangle (p q r : PMF α) :
    p.etvDist r ≤ p.etvDist q + q.etvDist r := by
  simp only [PMF.etvDist, ENNReal.div_add_div_same]
  exact ENNReal.div_le_div_right
    (calc ∑' x, ENNReal.absDiff (p x) (r x)
        ≤ ∑' x, (ENNReal.absDiff (p x) (q x) + ENNReal.absDiff (q x) (r x)) :=
          ENNReal.tsum_le_tsum fun x => ENNReal.absDiff_triangle (p x) (q x) (r x)
      _ = ∑' x, ENNReal.absDiff (p x) (q x) + ∑' x, ENNReal.absDiff (q x) (r x) :=
          ENNReal.tsum_add) _

lemma etvDist_le_one (p q : PMF α) : p.etvDist q ≤ 1 := by
  calc p.etvDist q = (∑' x, ENNReal.absDiff (p x) (q x)) / 2 := rfl
    _ ≤ (∑' x, (p x + q x)) / 2 :=
        ENNReal.div_le_div_right
          (ENNReal.tsum_le_tsum fun x => ENNReal.absDiff_le_add (p x) (q x)) _
    _ = (∑' x, p x + ∑' x, q x) / 2 := by rw [ENNReal.tsum_add]
    _ = (1 + 1) / 2 := by rw [p.tsum_coe, q.tsum_coe]
    _ = 2 / 2 := by norm_num
    _ = 1 := ENNReal.div_self two_ne_zero ofNat_ne_top

lemma etvDist_ne_top (p q : PMF α) : p.etvDist q ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (etvDist_le_one p q)

@[simp] lemma etvDist_eq_zero_iff {p q : PMF α} : p.etvDist q = 0 ↔ p = q := by
  simp only [PMF.etvDist, ENNReal.div_eq_zero_iff, ofNat_ne_top, or_false]
  rw [ENNReal.tsum_eq_zero]
  exact ⟨fun h => PMF.ext fun x => (ENNReal.absDiff_eq_zero.mp (h x)),
    fun h => by subst h; simp⟩

/-! ### Properties of tvDist -/

@[simp] lemma tvDist_self (p : PMF α) : p.tvDist p = 0 := by
  simp [PMF.tvDist]

lemma tvDist_comm (p q : PMF α) : p.tvDist q = q.tvDist p := by
  simp only [PMF.tvDist, etvDist_comm]

lemma tvDist_nonneg (p q : PMF α) : 0 ≤ p.tvDist q :=
  ENNReal.toReal_nonneg

lemma tvDist_triangle (p q r : PMF α) :
    p.tvDist r ≤ p.tvDist q + q.tvDist r := by
  rw [PMF.tvDist, PMF.tvDist, PMF.tvDist,
    ← ENNReal.toReal_add (etvDist_ne_top p q) (etvDist_ne_top q r)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨etvDist_ne_top p q, etvDist_ne_top q r⟩)
    (etvDist_triangle p q r)

lemma tvDist_le_one (p q : PMF α) : p.tvDist q ≤ 1 := by
  rw [PMF.tvDist, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono one_ne_top (etvDist_le_one p q)

@[simp] lemma tvDist_eq_zero_iff {p q : PMF α} : p.tvDist q = 0 ↔ p = q := by
  rw [PMF.tvDist, ENNReal.toReal_eq_zero_iff, etvDist_eq_zero_iff]
  simp [etvDist_ne_top]

/-! ### MetricSpace instance -/

noncomputable instance instMetricSpace : MetricSpace (PMF α) where
  dist := PMF.tvDist
  edist := PMF.etvDist
  dist_self := PMF.tvDist_self
  dist_comm := PMF.tvDist_comm
  dist_triangle := PMF.tvDist_triangle
  eq_of_dist_eq_zero h := tvDist_eq_zero_iff.mp h
  edist_dist p q := (ENNReal.ofReal_toReal (etvDist_ne_top p q)).symm

@[simp] lemma dist_eq_tvDist (p q : PMF α) : dist p q = p.tvDist q := rfl

@[simp] lemma edist_eq_etvDist (p q : PMF α) : edist p q = p.etvDist q := rfl

/-! ### Specialization to `Option PUnit` (binary distributions) -/

section OptionPUnit

variable (p q : PMF (Option PUnit))

private lemma pmf_none_eq (p : PMF (Option PUnit)) :
    p none = 1 - p (some ()) := by
  have h := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_unique] at h
  exact (ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top p _) h.symm).symm

lemma etvDist_option_punit :
    p.etvDist q = ENNReal.absDiff (p (some ())) (q (some ())) := by
  simp only [PMF.etvDist]
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_unique]
  rw [pmf_none_eq p, pmf_none_eq q,
    ENNReal.absDiff_tsub_tsub (PMF.coe_le_one p _) (PMF.coe_le_one q _) one_ne_top]
  rw [show ENNReal.absDiff (p (some ())) (q (some ())) +
      ENNReal.absDiff (p (some ())) (q (some ())) =
      2 * ENNReal.absDiff (p (some ())) (q (some ())) from by ring,
    mul_div_assoc]
  simp [ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top]

lemma tvDist_option_punit :
    p.tvDist q = |(p (some ())).toReal - (q (some ())).toReal| := by
  simp only [PMF.tvDist, etvDist_option_punit]
  exact ENNReal.absDiff_toReal (ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one p _))
    (ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one q _))

end OptionPUnit

end PMF
