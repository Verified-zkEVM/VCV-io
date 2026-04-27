/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.StateSeparating.Advantage

/-!
# State-separating handlers: identical-until-bad

Identical-until-bad wrappers for `QueryImpl.Stateful` handlers whose state is
of the form `σ × Bool`, with the Boolean component acting as the bad flag.
-/

open ENNReal OracleSpec OracleComp ProbComp
open OracleComp.ProgramLogic.Relational

namespace QueryImpl.Stateful

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ} {σ : Type}

/-- A stateful handler preserves a state invariant as long as the bad flag has not fired. -/
def PreservesNoBadInvariant (h : QueryImpl.Stateful unifSpec E (σ × Bool))
    (Inv : σ → Prop) : Prop :=
  ∀ (t : E.Domain) (p : σ × Bool), p.2 = false → Inv p.1 →
    ∀ z ∈ support ((h t).run p), Inv z.2.1

/-- State-dependent ε-perturbed identical-until-bad with output bad flag. -/
theorem advantage_le_expectedQuerySlack_plus_probEvent_bad
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤
        querySlack s)
    (h_step_eq_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (h₀ t).run p = (h₁ t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : OracleComp.IsQueryBoundP A chargedQuery queryBudget) :
    ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A)
      ≤ expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false)
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ h₀ A).run (s_init, false)] := by
  set sim₀ : ProbComp Bool := (simulateQ h₀ A).run' (s_init, false) with hsim₀_def
  set sim₁ : ProbComp Bool := (simulateQ h₁ A).run' (s_init, false) with hsim₁_def
  have hrun₀ : h₀.runProb (s_init, false) A = sim₀ := by
    simp [runProb, run, hsim₀_def]
  have hrun₁ : h₁.runProb (s_init, false) A = sim₁ := by
    simp [runProb, run, hsim₁_def]
  have h_adv_le_tv :
      h₀.advantage (s_init, false) h₁ (s_init, false) A ≤ tvDist sim₀ sim₁ := by
    unfold QueryImpl.Stateful.advantage ProbComp.boolDistAdvantage
    rw [hrun₀, hrun₁]
    exact abs_probOutput_toReal_sub_le_tvDist sim₀ sim₁
  have h_ofreal_adv :
      ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A) ≤
        ENNReal.ofReal (tvDist sim₀ sim₁) :=
    ENNReal.ofReal_le_ofReal h_adv_le_tv
  have h_bridge :
      ENNReal.ofReal (tvDist sim₀ sim₁)
        ≤ expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false)
          + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
              (simulateQ h₀ A).run (s_init, false)] := by
    rw [hsim₀_def, hsim₁_def]
    exact ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad
      h₀ h₁ chargedQuery querySlack h_step_tv_charged h_step_eq_uncharged
        h_mono₀ A h_bound s_init
  exact le_trans h_ofreal_adv h_bridge

/-- Constant-ε identical-until-bad with output bad flag. -/
theorem advantage_le_queryBound_mul_slack_plus_probEvent_bad
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤
        querySlack)
    (h_step_eq_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (h₀ t).run p = (h₁ t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : OracleComp.IsQueryBoundP A chargedQuery queryBudget) :
    ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A)
      ≤ queryBudget * querySlack
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ h₀ A).run (s_init, false)] := by
  refine le_trans
    (advantage_le_expectedQuerySlack_plus_probEvent_bad
      h₀ h₁ s_init chargedQuery (fun _ => querySlack)
      h_step_tv_charged h_step_eq_uncharged h_mono₀ A h_bound) ?_
  gcongr
  exact expectedQuerySlack_const_le_queryBudget_mul h₀ chargedQuery querySlack A h_bound
    (s_init, false)

/-! ### Invariant-gated variants -/

/-- Invariant-gated state-dependent ε-perturbed identical-until-bad.

The costly-step TV hypothesis is required only for states satisfying `Inv`.
The generated query-slack function charges the intended `ε s` on invariant states and
the conservative fallback cost `1` elsewhere. -/
theorem advantage_le_expectedQuerySlack_plus_probEvent_bad_of_inv
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (Inv : σ → Prop) [DecidablePred Inv]
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ), Inv s →
      ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤
        querySlack s)
    (h_step_eq_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (h₀ t).run p = (h₁ t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : OracleComp.IsQueryBoundP A chargedQuery queryBudget) :
    ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A)
      ≤ expectedQuerySlack h₀ chargedQuery
          (fun s => if Inv s then querySlack s else 1) A queryBudget (s_init, false)
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ h₀ A).run (s_init, false)] := by
  refine advantage_le_expectedQuerySlack_plus_probEvent_bad
    h₀ h₁ s_init chargedQuery (fun s => if Inv s then querySlack s else 1) ?_
    h_step_eq_uncharged h_mono₀ A h_bound
  intro t hSt s
  by_cases hs : Inv s
  · simpa [hs] using h_step_tv_charged t hSt s hs
  · simpa [hs] using
      ENNReal.ofReal_le_ofReal (tvDist_le_one ((h₀ t).run (s, false))
        ((h₁ t).run (s, false)))

/-- Invariant-preserving state-dependent ε-perturbed identical-until-bad.

If the real handler preserves `Inv` from the initial no-bad state, then the
fallback branch in the invariant-gated cost is unreachable, so the final
expected-cost term uses the tight query-slack function `ε`. -/
theorem advantage_le_expectedQuerySlack_plus_probEvent_bad_of_inv_preserved
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (Inv : σ → Prop)
    (h_init_inv : Inv s_init)
    (h_pres : h₀.PreservesNoBadInvariant Inv)
    (chargedQuery : E.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : E.Domain), chargedQuery t → ∀ (s : σ), Inv s →
      ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤
        querySlack s)
    (h_step_eq_uncharged : ∀ (t : E.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (h₀ t).run p = (h₁ t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {queryBudget : ℕ}
    (h_bound : OracleComp.IsQueryBoundP A chargedQuery queryBudget) :
    ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A)
      ≤ expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false)
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ h₀ A).run (s_init, false)] := by
  classical
  have h_bridge := advantage_le_expectedQuerySlack_plus_probEvent_bad_of_inv
    h₀ h₁ s_init Inv chargedQuery querySlack h_step_tv_charged h_step_eq_uncharged
      h_mono₀ A h_bound
  have h_cost_eq :
      expectedQuerySlack h₀ chargedQuery (fun s => if Inv s then querySlack s else 1)
          A queryBudget (s_init, false)
        = expectedQuerySlack h₀ chargedQuery querySlack A queryBudget (s_init, false) :=
    expectedQuerySlack_eq_of_inv h₀ chargedQuery Inv
      (ε := fun s => if Inv s then querySlack s else 1) (ε' := querySlack)
      (fun s hs => by simp [hs]) h_pres A queryBudget (s_init, false)
      (by intro _; exact h_init_inv)
  simpa [h_cost_eq] using h_bridge

end QueryImpl.Stateful
