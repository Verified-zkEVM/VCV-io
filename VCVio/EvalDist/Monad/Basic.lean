/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Evaluation Distributions of Computations with `Bind`

File for lemmas about `evalDist` and `support` involving the monadic `bind` and `pure`.
-/
universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [HasSPMF m]

open ENNReal

@[simp] lemma probOutput_pure [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by simp [probOutput_def]

@[simp] lemma probOutput_pure_self (x : α) :
    Pr[= x | (pure x : m α)] = 1 := by simp [probOutput_def]

@[simp] lemma probFailure_pure (x : α) : Pr[⊥ | (pure x : m α)] = 0 := by
  simp [probFailure_def]

lemma probOutput_pure_eq_indicator (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator (M := ℝ≥0∞) {y} (Function.const _ 1) x := by
  simp only [probOutput_def, evalDist_pure, OptionT.run_pure, PMF.monad_pure_eq_pure,
    PMF.pure_apply, Option.some.injEq, Set.indicator, Set.mem_singleton_iff, Function.const_apply]
  rw [Option.some_inj]
  rfl

section bind

variable (mx : m α) (my : α → m β)

lemma probOutput_bind_eq_tsum (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput, tsum_option _ ENNReal.summable, Option.elimM]

end bind

lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [HasSPMF m]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[p | mx] := by
  rw [probEvent_eq_tsum_indicator]
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun α => ?_
  simp [Set.indicator]
  congr
  rw [eq_true_eq_id]
  rfl

-- section bind_congr -- TODO: we should have tactics for this kind of thing

-- variable {ι : Type v} {spec : OracleSpec ι} {α β γ δ : Type u} [spec.Fintype]

-- lemma probFailure_bind_congr (oa : OracleComp spec α)
--     {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
--     (h : ∀ x ∈ oa.support, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
--   sorry

-- lemma probFailure_bind_congr' (oa : OracleComp spec α)
--     {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
--     (h : ∀ x, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
--   sorry

-- lemma probOutput_bind_congr {oa : OracleComp spec α} {ob₁ ob₂ : α → OracleComp spec β} {y : β}
--     (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x]) :
--     [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
--   sorry

-- lemma probOutput_bind_congr' (oa : OracleComp spec α) {ob₁ ob₂ : α → OracleComp spec β} (y : β)
--     (h : ∀ x, [= y | ob₁ x] = [= y | ob₂ x]) :
--     [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
--   sorry

-- lemma probOutput_bind_mono {oa : OracleComp spec α}
--     {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ} {y : β} {z : γ}
--     (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z | oc x]) :
--     [= y | oa >>= ob] ≤ [= z | oa >>= oc] := by
--   sorry

-- lemma probOutput_bind_congr_div_const {oa : OracleComp spec α}
--     {ob₁ ob₂ : α → OracleComp spec β} {y : β} {r : ℝ≥0∞}
--     (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x] / r) :
--     [= y | oa >>= ob₁] = [= y | oa >>= ob₂] / r := by
--   sorry

-- lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= y | ob x] = [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
--     [= y | oa >>= ob] = [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
--   simp [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
--   refine tsum_congr fun x => ?_
--   by_cases hx : x ∈ oa.support
--   · simp [h x hx, left_distrib]
--   · simp [probOutput_eq_zero _ _ hx]

-- lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
--     [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
--   sorry

-- lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] + [= z₂ | oc₂ x] ≤ [= y | ob x]) :
--     [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
--   sorry

-- lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] - [= z₂ | oc₂ x]) :
--     [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] := by
--   sorry

-- lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] - [= z₂ | oc₂ x] ≤ [= y | ob x]) :
--     [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
--   sorry

-- end bind_congr
