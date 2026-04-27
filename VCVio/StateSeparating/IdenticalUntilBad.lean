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

/-- State-dependent ε-perturbed identical-until-bad with output bad flag. -/
theorem advantage_le_expectedSCost_plus_probEvent_bad
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (p : σ × Bool),
      (h₀ t).run p = (h₁ t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b)) :
    ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A)
      ≤ expectedSCost h₀ S ε A qS (s_init, false)
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
        ≤ expectedSCost h₀ S ε A qS (s_init, false)
          + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
              (simulateQ h₀ A).run (s_init, false)] := by
    rw [hsim₀_def, hsim₁_def]
    exact ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad
      h₀ h₁ S ε h_step_tv_S h_step_eq_nS h_mono₀ A h_qb s_init
  exact le_trans h_ofreal_adv h_bridge

/-- Constant-ε identical-until-bad with output bad flag. -/
theorem advantage_le_qSeps_plus_probEvent_bad
    (h₀ h₁ : QueryImpl.Stateful unifSpec E (σ × Bool))
    (s_init : σ)
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤ ε)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (p : σ × Bool),
      (h₀ t).run p = (h₁ t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((h₀ t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b)) :
    ENNReal.ofReal (h₀.advantage (s_init, false) h₁ (s_init, false) A)
      ≤ qS * ε
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ h₀ A).run (s_init, false)] := by
  refine le_trans
    (advantage_le_expectedSCost_plus_probEvent_bad
      h₀ h₁ s_init S (fun _ => ε)
      h_step_tv_S h_step_eq_nS h_mono₀ A h_qb) ?_
  gcongr
  exact expectedSCost_const_le_qS_mul h₀ S ε A h_qb (s_init, false)

end QueryImpl.Stateful
