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

section bind_congr -- TODO: we should have tactics for this kind of thing

variable {ι : Type v} {spec : OracleSpec ι} {α β γ δ : Type u} [spec.FiniteRange]

lemma probFailure_bind_congr (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x ∈ oa.support, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  sorry

lemma probFailure_bind_congr' (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
    (h : ∀ x, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
  sorry

lemma probOutput_bind_congr {oa : OracleComp spec α} {ob₁ ob₂ : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x]) :
    [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
  sorry

lemma probOutput_bind_congr' (oa : OracleComp spec α) {ob₁ ob₂ : α → OracleComp spec β} (y : β)
    (h : ∀ x, [= y | ob₁ x] = [= y | ob₂ x]) :
    [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
  sorry

lemma probOutput_bind_mono {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ} {y : β} {z : γ}
    (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z | oc x]) :
    [= y | oa >>= ob] ≤ [= z | oa >>= oc] := by
  sorry

lemma probOutput_bind_congr_div_const {oa : OracleComp spec α}
    {ob₁ ob₂ : α → OracleComp spec β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x] / r) :
    [= y | oa >>= ob₁] = [= y | oa >>= ob₂] / r := by
  sorry

lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= y | ob x] = [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
    [= y | oa >>= ob] = [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
  simp [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ oa.support
  · simp [h x hx, left_distrib]
  · simp [probOutput_eq_zero _ _ hx]

lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
    [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
  sorry

lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
      {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] + [= z₂ | oc₂ x] ≤ [= y | ob x]) :
    [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
  sorry

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
    (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] - [= z₂ | oc₂ x] ≤ [= y | ob x]) :
    [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
  sorry

end bind_congr

end scratch
