/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Probability Lemmas About Monad Operations

This file contains lemmas about `evalDist` applied to monadic operations like `pure` and `bind`.
-/

open OracleSpec OracleComp Option ENNReal Function

section scratch

universe u v w

section bind_congr

-- TODO: we should have tactics for this kind of thing

variable {ι : Type v} {spec : OracleSpec ι} {α β γ δ : Type u} [spec.FiniteRange]

lemma probFailure_bind_congr (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x ∈ oa.support, [⊥|ob x] = [⊥|oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  rw [probFailure_bind_eq_tsum, probFailure_bind_eq_tsum]
  congr 1
  apply tsum_congr
  intro x
  by_cases hx : x ∈ oa.support
  · rw [h x hx]
  · simp [(probOutput_eq_zero_iff oa x).mpr hx]

lemma probFailure_bind_congr' (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x, [⊥|ob x] = [⊥|oc x]) : [⊥|oa >>= ob] = [⊥|oa >>= oc] :=
  probFailure_bind_congr oa fun x _ ↦ h x

lemma probOutput_bind_congr {oa : OracleComp spec α} {ob₁ ob₂ : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ oa.support, [=y|ob₁ x] = [=y|ob₂ x]) :
    [=y|oa >>= ob₁] = [=y|oa >>= ob₂] := by
  simp only [OracleComp.probOutput_bind_eq_tsum_subtype]
  exact tsum_congr fun x ↦ congrArg (fun z ↦ [=↑x|oa] * z) (h x x.2)

lemma probOutput_bind_congr' (oa : OracleComp spec α) {ob₁ ob₂ : α → OracleComp spec β} (y : β)
    (h : ∀ x, [=y|ob₁ x] = [=y|ob₂ x]) :
    [=y|oa >>= ob₁] = [=y|oa >>= ob₂] :=
  probOutput_bind_congr (fun x _ ↦ h x)

lemma probOutput_bind_mono {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ} {y : β} {z : γ}
    (h : ∀ x ∈ oa.support, [=y|ob x] ≤ [=z|oc x]) :
    [= y | oa >>= ob] ≤ [= z | oa >>= oc] := by
  rw [OracleComp.probOutput_bind_eq_tsum, OracleComp.probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : x ∈ oa.support
  · exact mul_le_mul_left' (h x hx) _
  · simp [probOutput_eq_zero' oa x hx]

lemma probOutput_bind_congr_div_const {oa : OracleComp spec α}
    {ob₁ ob₂ : α → OracleComp spec β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ oa.support, [=y|ob₁ x] = [=y|ob₂ x] / r) :
    [=y|oa >>= ob₁] = [=y|oa >>= ob₂] / r := by
  have h_div :
      ∑' x : α, [=x|oa] * [=y|ob₁ x] = ∑' x : α, [=x|oa] * ([=y|ob₂ x] / r) := by
    refine tsum_congr fun x ↦ ?_
    by_cases hx : x ∈ oa.support
    · grind
    · simp [probOutput_def, (evalDist_apply_eq_zero_iff oa (some x)).mpr hx]
  convert h_div using 1
  · apply OracleComp.probOutput_bind_eq_tsum
  · rw [show ∑' x : α, [=x|oa] * ([=y|ob₂ x] / r) = (∑' x : α, [=x|oa] * [=y|ob₂ x]) / r by
      simpa only [div_eq_mul_inv, mul_comm, mul_left_comm] using ENNReal.tsum_mul_left,
      OracleComp.probOutput_bind_eq_tsum]

lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [=y|ob x] = [=z₁|oc₁ x] + [=z₂|oc₂ x]) :
    [=y|oa >>= ob] = [=z₁|oa >>= oc₁] + [=z₂|oa >>= oc₂] := by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ oa.support
  · rw [h x hx, left_distrib]
  · simp only [probOutput_eq_zero _ _ hx, zero_mul, zero_add]

lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [=y|ob x] ≤ [=z₁|oc₁ x] + [=z₂|oc₂ x]) :
    [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
  have h_tsum :
      ∑' x, [=x|oa] * [=y|ob x] ≤ ∑' x, [=x|oa] * ([=z₁|oc₁ x] + [=z₂|oc₂ x]) :=
    ENNReal.tsum_le_tsum fun x ↦ by
      by_cases hx : x ∈ oa.support
      · exact mul_le_mul_left' (h x hx) _
      · simp [probOutput_eq_zero' oa x hx]
  simp_all [probOutput_bind_eq_tsum, mul_add, Summable.tsum_add]

lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [=z₁|oc₁ x] + [=z₂|oc₂ x] ≤ [=y|ob x]) :
    [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
  rw [probOutput_bind_eq_tsum_subtype, probOutput_bind_eq_tsum_subtype,
    probOutput_bind_eq_tsum_subtype, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a ↦ by rw [← mul_add]; exact mul_le_mul_left' (h a a.2) _

lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] - [= z₂ | oc₂ x]) :
    [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] := by
  sorry

lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [=z₁|oc₁ x] - [=z₂|oc₂ x] ≤ [=y|ob x]) :
    [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
  simp_all only [probOutput_bind_eq_tsum_subtype, tsub_le_iff_right]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [← mul_add]; exact mul_le_mul_left' (h x x.2) _

end bind_congr

end scratch
