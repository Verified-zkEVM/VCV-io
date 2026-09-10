/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.EvalDist.MeasureTVDist

/-!
# Discrete compatibility bridges for the measure semantics

This module connects the canonical discrete measure reading of a computation
(`discreteEvalDist`, the primary measure semantics taken at the top σ-algebra) with the
executable discrete probability surface (`Pr[= x | mx]`, `Pr[p | mx]`, `𝒮[…]`, and the
monadic `tvDist`). Definitions stated against `discreteEvalDist` and `discreteTVDist` can be
proved and consumed through the traditional notation via these bridges, without being restated
against the finite-distribution backend.

The central fact is `SPMF.toMeasure_etvDist`: on a discrete space, the largest event
discrepancy between two successful-output measures (`Measure.etvDist`, the sup-over-events
form) agrees with the `L¹/2` total variation of the underlying option-valued mass functions.
Both sides equal `max P N`, where `P` and `N` are the one-sided mass discrepancies; the
missing-mass (`none`) coordinate of the option backend contributes exactly `|P - N|`, which
is what the sup form recovers through complementation. Its corollaries transport
total-variation statements between `Measure.tvDist` on successful-output measures and the
executable total variation, subsuming the previously special-cased one-point observation
space.
-/

@[expose] public section

noncomputable section

open MeasureTheory ENNReal

universe u v

variable {α : Type u}

namespace SPMF

variable [MeasurableSpace α] [DiscreteMeasurableSpace α] (p q : SPMF α)

/-- On a discrete space the successful-output measure of a set is the sum of its point
masses. -/
lemma toMeasure_apply_eq_tsum_indicator (s : Set α) :
    p.toMeasure s = ∑' x, s.indicator (fun y => p y) x := by
  rw [p.toMeasure_apply, p.toPMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable]
  simp [Set.indicator_image (Option.some_injective _), Function.comp_def,
    p.apply_eq_toPMF_some]

/-- The total successful mass of an `SPMF` is at most one. -/
lemma tsum_apply_le_one : ∑' x, p x ≤ 1 :=
  p.toMeasure_apply_univ.symm.trans_le p.toMeasure_apply_univ_le_one

/-- One half of `toMeasure_etvDist`: the positive mass discrepancy is attained as an event
discrepancy of the successful-output measures. -/
private lemma tsum_tsub_le_etvDist_toMeasure :
    ∑' x, (p x - q x) ≤ Measure.etvDist p.toMeasure q.toMeasure := by
  classical
  have hSm : MeasurableSet {x : α | q x < p x} := MeasurableSet.of_discrete
  refine le_trans ?_ (Measure.absDiff_apply_le_etvDist p.toMeasure q.toMeasure hSm)
  have hqfin : ∑' x, ({x : α | q x < p x}.indicator (fun y => q y) x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top one_ne_top ?_
    exact le_trans (ENNReal.tsum_le_tsum fun x => Set.indicator_le_self _ _ x)
      q.tsum_apply_le_one
  have hpt : ∀ x, {x : α | q x < p x}.indicator (fun y => q y) x ≤
      {x : α | q x < p x}.indicator (fun y => p y) x := by
    intro x
    by_cases hx : x ∈ {x : α | q x < p x}
    · simpa [Set.indicator_of_mem hx] using le_of_lt hx
    · simp [Set.indicator_of_notMem hx]
  have key : p.toMeasure {x : α | q x < p x} - q.toMeasure {x : α | q x < p x} =
      ∑' x, (p x - q x) := by
    rw [p.toMeasure_apply_eq_tsum_indicator, q.toMeasure_apply_eq_tsum_indicator]
    have hsplit : ∑' x, ({x : α | q x < p x}.indicator (fun y => p y) x) =
        (∑' x, ({x : α | q x < p x}.indicator (fun y => p y) x -
          {x : α | q x < p x}.indicator (fun y => q y) x)) +
          ∑' x, ({x : α | q x < p x}.indicator (fun y => q y) x) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun x => (tsub_add_cancel_of_le (hpt x)).symm
    rw [hsplit, ENNReal.add_sub_cancel_right hqfin]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ {x : α | q x < p x}
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx,
        tsub_eq_zero_of_le (not_lt.mp (Set.notMem_ofPred_iff.mp hx))]
  calc ∑' x, (p x - q x)
      = p.toMeasure {x : α | q x < p x} - q.toMeasure {x : α | q x < p x} := key.symm
    _ ≤ ENNReal.absDiff (p.toMeasure {x : α | q x < p x})
        (q.toMeasure {x : α | q x < p x}) := le_self_add

/-- On a discrete space, the sup-over-events total variation of the successful-output measures
is the `L¹/2` total variation of the underlying option-valued mass functions.

Both sides equal `max P N` for the one-sided discrepancies `P = ∑' x, (p x - q x)` and
`N = ∑' x, (q x - p x)`: the missing-mass coordinate of the option backend contributes
exactly `|P - N|`, which the sup form recovers by passing to complements. -/
theorem toMeasure_etvDist :
    Measure.etvDist p.toMeasure q.toMeasure = p.toPMF.etvDist q.toPMF := by
  classical
  have hpmass : ∑' x, p x ≤ 1 := p.tsum_apply_le_one
  have hqmass : ∑' x, q x ≤ 1 := q.tsum_apply_le_one
  have hPle : (∑' x, (p x - q x)) ≤ 1 :=
    le_trans (ENNReal.tsum_le_tsum fun x => tsub_le_self) hpmass
  have hNle : (∑' x, (q x - p x)) ≤ 1 :=
    le_trans (ENNReal.tsum_le_tsum fun x => tsub_le_self) hqmass
  have hmain : Measure.etvDist p.toMeasure q.toMeasure =
      (∑' x, (p x - q x)) ⊔ (∑' x, (q x - p x)) := by
    refine le_antisymm (iSup_le fun s => ?_)
      (sup_le (p.tsum_tsub_le_etvDist_toMeasure q)
        (Measure.etvDist_comm p.toMeasure q.toMeasure ▸
          q.tsum_tsub_le_etvDist_toMeasure p))
    have h1 : p.toMeasure s.1 - q.toMeasure s.1 ≤ ∑' x, (p x - q x) := by
      rw [p.toMeasure_apply_eq_tsum_indicator, q.toMeasure_apply_eq_tsum_indicator]
      refine le_trans (ENNReal.tsum_tsub_le_tsum_tsub _ _)
        (ENNReal.tsum_le_tsum fun x => ?_)
      by_cases hx : x ∈ s.1
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have h2 : q.toMeasure s.1 - p.toMeasure s.1 ≤ ∑' x, (q x - p x) := by
      rw [p.toMeasure_apply_eq_tsum_indicator, q.toMeasure_apply_eq_tsum_indicator]
      refine le_trans (ENNReal.tsum_tsub_le_tsum_tsub _ _)
        (ENNReal.tsum_le_tsum fun x => ?_)
      by_cases hx : x ∈ s.1
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rcases le_total (p.toMeasure s.1) (q.toMeasure s.1) with hle | hle
    · calc ENNReal.absDiff (p.toMeasure s.1) (q.toMeasure s.1)
          = 0 + (q.toMeasure s.1 - p.toMeasure s.1) := by
            rw [ENNReal.absDiff, tsub_eq_zero_of_le hle]
        _ ≤ ∑' x, (q x - p x) := by simpa using h2
        _ ≤ _ := le_sup_right
    · calc ENNReal.absDiff (p.toMeasure s.1) (q.toMeasure s.1)
          = (p.toMeasure s.1 - q.toMeasure s.1) + 0 := by
            rw [ENNReal.absDiff, tsub_eq_zero_of_le hle]
        _ ≤ ∑' x, (p x - q x) := by simpa using h1
        _ ≤ _ := le_sup_left
  have hswap : (∑' x, p x) + ∑' x, (q x - p x) = (∑' x, q x) + ∑' x, (p x - q x) := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    rcases le_total (p x) (q x) with h | h
    · rw [add_tsub_cancel_of_le h, tsub_eq_zero_of_le h, add_zero]
    · rw [add_tsub_cancel_of_le h, tsub_eq_zero_of_le h, add_zero]
  have hnone : ENNReal.absDiff (p.toPMF none) (q.toPMF none) =
      ENNReal.absDiff (∑' x, (p x - q x)) (∑' x, (q x - p x)) := by
    rw [p.toPMF_none_eq_one_sub_tsum, q.toPMF_none_eq_one_sub_tsum]
    rw [show (∑' x, p.toPMF (some x)) = ∑' x, p x from rfl,
      show (∑' x, q.toPMF (some x)) = ∑' x, q x from rfl,
      ENNReal.absDiff_tsub_tsub hpmass hqmass one_ne_top]
    exact ENNReal.absDiff_eq_absDiff_of_add_eq_add
      (ne_top_of_le_ne_top one_ne_top hpmass) (ne_top_of_le_ne_top one_ne_top hqmass)
      (ne_top_of_le_ne_top one_ne_top hPle) (ne_top_of_le_ne_top one_ne_top hNle) hswap
  have hsome : ∑' x : α, ENNReal.absDiff (p.toPMF (some x)) (q.toPMF (some x)) =
      (∑' x, (p x - q x)) + ∑' x, (q x - p x) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun x => rfl
  rw [hmain, PMF.etvDist, tsum_option _ ENNReal.summable, hnone, hsome,
    ENNReal.absDiff_add_add_eq_two_mul_sup, mul_div_assoc,
    ENNReal.mul_div_cancel two_ne_zero (by simp)]

/-- Real-valued form of `toMeasure_etvDist`: on a discrete space, total variation of the
successful-output measures agrees with the executable `SPMF` total variation. -/
theorem toMeasure_tvDist : Measure.tvDist p.toMeasure q.toMeasure = p.tvDist q :=
  congrArg ENNReal.toReal (p.toMeasure_etvDist q)

/-- The measure and executable total variations have the same zero-distance relation on a
discrete space. In particular, transporting a perfect-indistinguishability proof across
`SPMF.toMeasure` is lossless. -/
theorem toMeasure_tvDist_eq_zero_iff :
    Measure.tvDist p.toMeasure q.toMeasure = 0 ↔ p.tvDist q = 0 := by
  rw [p.toMeasure_tvDist q]

end SPMF

/-! ## Bridges between `discreteEvalDist` and the executable notation

The canonical discrete measure reading of a computation in a monad with the
finite-distribution semantics is definitionally the successful-output measure of its `SPMF`
denotation at the top σ-algebra. These lemmas restate its point masses, event masses,
injectivity, and total variation through the traditional `Pr[…]` / `𝒮[…]` / `tvDist`
surface. -/

section discreteEvalDist

variable {m : Type u → Type v} [MonadLiftT m SPMF]

private lemma discreteMeasurableSpace_top :
    @DiscreteMeasurableSpace α ⊤ :=
  @DiscreteMeasurableSpace.mk α ⊤ fun _ => MeasurableSpace.measurableSet_top

private lemma measurableSingletonClass_top :
    @MeasurableSingletonClass α ⊤ :=
  @MeasurableSingletonClass.mk α ⊤ fun _ => MeasurableSpace.measurableSet_top

/-- The canonical discrete measure reading assigns each singleton its output probability. -/
@[simp]
lemma discreteEvalDist_apply_singleton (mx : m α) (x : α) :
    discreteEvalDist mx {x} = Pr[= x | mx] := by
  let _instM : MeasurableSpace α := ⊤
  have _instS : MeasurableSingletonClass α := measurableSingletonClass_top
  exact (𝒮[mx]).toMeasure_apply_singleton x

/-- The canonical discrete measure reading assigns each event its traditional probability. -/
lemma discreteEvalDist_apply_setOf (mx : m α) (p : α → Prop) :
    discreteEvalDist mx {x | p x} = Pr[p | mx] := by
  let _instM : MeasurableSpace α := ⊤
  have _instD : DiscreteMeasurableSpace α := discreteMeasurableSpace_top
  exact ((𝒮[mx]).toMeasure_apply {x | p x}).trans (probEvent_def mx p).symm

/-- Total variation of canonical discrete measure readings is the legacy monadic total
variation. -/
lemma discreteTVDist_eq_tvDist (mx my : m α) :
    discreteTVDist mx my = tvDist mx my := by
  let _instM : MeasurableSpace α := ⊤
  have _instD : DiscreteMeasurableSpace α := discreteMeasurableSpace_top
  exact (𝒮[mx]).toMeasure_tvDist 𝒮[my]

/-- Two computations have equal canonical discrete measure readings exactly when their
executable denotations agree. -/
lemma discreteEvalDist_eq_iff (mx my : m α) :
    discreteEvalDist mx = discreteEvalDist my ↔ 𝒮[mx] = 𝒮[my] := by
  rw [← discreteTVDist_eq_zero_iff, discreteTVDist_eq_tvDist, tvDist_eq_zero_iff]

end discreteEvalDist
