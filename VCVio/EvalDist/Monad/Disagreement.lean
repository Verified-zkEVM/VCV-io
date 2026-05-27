/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Monad.Basic

/-!
# Disagreement-Aware Additive Bind Bounds

A family of bind-bound lemmas charging an exceptional set ("disagreement") to its mass
plus per-point slack. They are the workhorses behind coupled game-hopping proofs that need
to bound `Pr[q | mx >>= my]` by `Pr[q | mx >>= oc]` plus a small additive term.

These statements are framed for any monad `m` with `[HasEvalSPMF m]`; the canonical
specialisation is `m = ProbComp`.

## Main results

* `probEvent_bind_le_add_of_disagree` — 2-way base case.
* `probEvent_bind_le_add_bad_of_disagree` — 3-way with bad-event side.
* `probEvent_bind_le_add_bad_of_disagree'` — 3-way with per-step bad term in the IH.
* `probEvent_bind_le_add_bad_disagree` — 4-way merge.
-/

universe u v

open ENNReal

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [HasEvalSPMF m]

/-- **Disagreement-aware additive bind bound.** If the disagreement set `D` has probability at
most `ε₁` under `mx`, and off `D` the continuation `my` is within `ε₂` of the reference
continuation `oc`, then `Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + ε₁ + ε₂`. The exceptional set `D`
is charged its full mass `ε₁`; everywhere else the per-point gap `ε₂` is paid. -/
lemma probEvent_bind_le_add_of_disagree {mx : m α}
    {my oc : α → m β} {q : β → Prop} {D : α → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (hD : Pr[ D | mx] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[ q | my x] ≤ Pr[ q | oc x] + ε₂) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] + ε₁ + ε₂ := by
  classical
  have := Classical.decPred q
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + (if D x then Pr[= x | mx] else 0) + Pr[= x | mx] * ε₂) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · simp only [if_pos hDx]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] := mul_one _
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] + Pr[= x | mx] * ε₂ := by
                  refine le_add_right (le_add_left le_rfl)
          · simp only [if_neg hDx, add_zero]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + ε₂) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * ε₂ := left_distrib ..
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, if D x then Pr[= x | mx] else 0) + (∑' x, Pr[= x | mx] * ε₂) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x]) + ε₁ + ε₂ := by
        refine add_le_add (add_le_add le_rfl ?_) ?_
        · rw [← probEvent_eq_tsum_ite]; exact hD
        · rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-- **Three-way disagreement-aware additive bind bound (hop A).** A coupled three-world variant of
`probEvent_bind_le_add_of_disagree`: the three worlds share the sampling computation `mx`, and at
each shared sample `x`, off the disagreement set `D` the `my`-world is bounded by the `oc`-world
plus the per-step slack `ε`, while on `D` the `ob`-world (the bad world) already fires its event
`r` with probability `1`. The conclusion charges the disagreement to `Pr[r | mx >>= ob]`. -/
lemma probEvent_bind_le_add_bad_of_disagree {mx : m α}
    {my : α → m β} {oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → Pr[ r | ob x] = 1)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[ q | my x] ≤ Pr[ q | oc x] + ε) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] + Pr[ r | mx >>= ob] + ε := by
  classical
  have := Classical.decPred q
  have := Classical.decPred r
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + Pr[= x | mx] * Pr[r | ob x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] * Pr[r | ob x] := by rw [hbad x hx hDx]
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := le_add_right (le_add_left le_rfl)
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + ε) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * ε := left_distrib ..
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := by
                  rw [add_right_comm]
                  exact le_add_right le_rfl
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + (∑' x, Pr[= x | mx] * ε) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + ε := by
        refine add_le_add le_rfl ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-- **Four-way disagreement-aware additive bind bound (hop A).** A strengthening of
`probEvent_bind_le_add_bad_of_disagree`: the per-step inductive hypothesis itself carries a
bad-event term, so off the disagreement set `D` the `my`-world is bounded by the `oc`-world plus the
*per-shared-sample* bad probability `Pr[r | ob x]` plus the slack `ε`. On `D` the `ob`-world already
fires `r` with probability `1`. Both cases are charged into the aggregate `Pr[r | mx >>= ob]`, so
the conclusion is the same shape as the three-way bound. -/
lemma probEvent_bind_le_add_bad_of_disagree' {mx : m α}
    {my : α → m β} {oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → Pr[ r | ob x] = 1)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[ q | my x] ≤ Pr[ q | oc x] + Pr[ r | ob x] + ε) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] + Pr[ r | mx >>= ob] + ε := by
  classical
  have := Classical.decPred q
  have := Classical.decPred r
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + Pr[= x | mx] * Pr[r | ob x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] * Pr[r | ob x] := by rw [hbad x hx hDx]
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := le_add_right (le_add_left le_rfl)
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + Pr[r | ob x] + ε) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := by rw [left_distrib, left_distrib]
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + (∑' x, Pr[= x | mx] * ε) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + ε := by
        refine add_le_add le_rfl ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-- **Four-way disagreement+bad additive bind bound.** A merge of
`probEvent_bind_le_add_of_disagree` with the three-world `probEvent_bind_le_add_bad_of_disagree`:
the disagreement set `D` (a *table-level* exceptional set, not a bad event) is charged its full
mass `ε₁`; everywhere off `D` the `my`-world is bounded by the `oc`-world plus the per-shared-sample
bad probability `Pr[r | ob x]` plus the slack `ε₂`. -/
lemma probEvent_bind_le_add_bad_disagree {mx : m α}
    {my : α → m β} {oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (hD : Pr[ D | mx] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[ q | my x] ≤ Pr[ q | oc x] + Pr[ r | ob x] + ε₂) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] + Pr[ r | mx >>= ob] + ε₁ + ε₂ := by
  classical
  have := Classical.decPred q
  have := Classical.decPred r
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + Pr[= x | mx] * Pr[r | ob x] + (if D x then Pr[= x | mx] else 0)
            + Pr[= x | mx] * ε₂) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · simp only [if_pos hDx]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] := mul_one _
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] + Pr[= x | mx] * ε₂ := by
                  calc Pr[= x | mx]
                      = 0 + 0 + Pr[= x | mx] + 0 := by ring
                    _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                          + Pr[= x | mx] + Pr[= x | mx] * ε₂ := by
                        gcongr <;> exact zero_le _
          · simp only [if_neg hDx, add_zero]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + Pr[r | ob x] + ε₂) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε₂ := by rw [left_distrib, left_distrib]
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x])
          + (∑' x, if D x then Pr[= x | mx] else 0) + (∑' x, Pr[= x | mx] * ε₂) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + ε₁ + ε₂ := by
        refine add_le_add (add_le_add le_rfl ?_) ?_
        · rw [← probEvent_eq_tsum_ite]; exact hD
        · rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one
