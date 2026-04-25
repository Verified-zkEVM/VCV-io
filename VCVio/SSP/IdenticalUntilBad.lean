/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.SSP.Advantage

/-!
# State-Separating Proofs: Identical-Until-Bad

This file lifts the state-dependent ε-perturbed identical-until-bad TV-distance bridge
(`ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad` in
`VCVio.ProgramLogic.Relational.SimulateQ`) from raw `simulateQ`-pairs to SSP `Package`-pairs,
producing the SSP-flavoured statement that the **distinguishing advantage** between two
games is bounded by the **expected cumulative ε-cost** plus the **bad-event probability**.

The two SSP wrappers in this file are
* `Package.advantage_le_expectedSCost_plus_probEvent_bad` — the **state-dep ε** wrapper:
  per-step ε is allowed to depend on the input state, so the cumulative cost is captured by
  the recursively-defined `expectedSCost` rather than by a constant `qS · ε`.
* `Package.advantage_le_qSeps_plus_probEvent_bad` — the **constant-ε** corollary, derived
  from the state-dep version via `expectedSCost_const_le_qS_mul`. This is the SSP analogue
  of the existing `tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad`.

Both wrappers assume the two games share the same internal state type `σ × Bool` (where the
`Bool` component is the bad flag), and that their `init` deterministically lands in
`(s_init, false)` for a fixed `s_init : σ`. This is the typical SSP "identical-until-bad"
shape: the bad flag is part of the package state, set by some specific export query (e.g.
the programming-RO collision check), and the state otherwise tracks game bookkeeping.

## Bound shape

Specifically, with the two packages

* `G₀ G₁ : Package unifSpec E (σ × Bool)` initialised to `pure (s_init, false)`,
* a "costly" query predicate `S : E.Domain → Prop` distinguishing perturbed queries from
  free ones,
* a per-state cost `ε : σ → ℝ≥0∞` bounding the per-step TV gap on costly queries from a
  no-bad input state,

the wrapper concludes (in `ENNReal` form, since `expectedSCost` is `ℝ≥0∞`-valued):

```
ENNReal.ofReal (G₀.advantage G₁ A)
  ≤ expectedSCost G₀.impl S ε A qS (s_init, false)
    + Pr[fun z => z.2.2 = true | (simulateQ G₀.impl A).run (s_init, false)]
```

Users that have a finiteness witness for the right-hand side recover a real-valued
inequality via `ENNReal.toReal`.
-/

universe uₑ

open ENNReal OracleSpec OracleComp ProbComp
open OracleComp.ProgramLogic.Relational

namespace VCVio.SSP

namespace Package

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ} {σ : Type}

/-- **SSP state-dep ε-perturbed identical-until-bad with output bad flag.**

Lifts `ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad` to two SSP
packages `G₀, G₁ : Package unifSpec E (σ × Bool)` whose init deterministically lands in
the fixed no-bad state `(s_init, false)`. The advantage `G₀.advantage G₁ A` is bounded by
`expectedSCost G₀.impl S ε A qS (s_init, false) + Pr[bad | (simulateQ G₀.impl A).run …]`.

The hypotheses come in three flavours, mirroring the underlying simulateQ-level lemma:
* `h_step_tv_S` — on a costly (`S t`) query from a no-bad input state, the two impls are
  ε-close in TV distance with ε allowed to depend on the inner state `s : σ`;
* `h_step_eq_nS` — on a free (`¬ S t`) query, the two impls are pointwise equal (no
  perturbation, no budget consumption, no contribution to the bound);
* `h_mono₀` — bad-flag monotonicity for `G₀`'s impl, used internally to discharge the
  bad-input branch via `Pr[bad | sim] = 1 ≥ tvDist`.

`h_qb` constrains the adversary `A` to make at most `qS` costly queries (free queries are
unconstrained), via the `IsQueryBound` parameterised by `if S t then 0 < b else True` and
`if S t then b - 1 else b`. -/
theorem advantage_le_expectedSCost_plus_probEvent_bad
    (G₀ G₁ : Package unifSpec E (σ × Bool))
    (s_init : σ) (h_init₀ : G₀.init = pure (s_init, false))
    (h_init₁ : G₁.init = pure (s_init, false))
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((G₀.impl t).run (s, false)) ((G₁.impl t).run (s, false))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (p : σ × Bool),
      (G₀.impl t).run p = (G₁.impl t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((G₀.impl t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b)) :
    ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ expectedSCost G₀.impl S ε A qS (s_init, false)
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ G₀.impl A).run (s_init, false)] := by
  set sim₀ : ProbComp Bool := (simulateQ G₀.impl A).run' (s_init, false) with hsim₀_def
  set sim₁ : ProbComp Bool := (simulateQ G₁.impl A).run' (s_init, false) with hsim₁_def
  have hrun₀ : G₀.runProb A = sim₀ := by
    simp [Package.runProb, Package.run, h_init₀, hsim₀_def]
  have hrun₁ : G₁.runProb A = sim₁ := by
    simp [Package.runProb, Package.run, h_init₁, hsim₁_def]
  have h_adv_le_tv :
      G₀.advantage G₁ A ≤ tvDist sim₀ sim₁ := by
    unfold Package.advantage ProbComp.boolDistAdvantage
    rw [hrun₀, hrun₁]
    exact abs_probOutput_toReal_sub_le_tvDist sim₀ sim₁
  have h_ofreal_adv :
      ENNReal.ofReal (G₀.advantage G₁ A) ≤ ENNReal.ofReal (tvDist sim₀ sim₁) :=
    ENNReal.ofReal_le_ofReal h_adv_le_tv
  have h_bridge :
      ENNReal.ofReal (tvDist sim₀ sim₁)
        ≤ expectedSCost G₀.impl S ε A qS (s_init, false)
          + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
              (simulateQ G₀.impl A).run (s_init, false)] := by
    rw [hsim₀_def, hsim₁_def]
    exact ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad
      G₀.impl G₁.impl S ε h_step_tv_S h_step_eq_nS h_mono₀ A h_qb s_init
  exact le_trans h_ofreal_adv h_bridge

/-- **SSP constant-ε identical-until-bad with output bad flag.**

The constant-ε corollary of `advantage_le_expectedSCost_plus_probEvent_bad`, derived by
specialising `ε := fun _ => ε_const` and bounding `expectedSCost` by `qS · ε_const` via
`expectedSCost_const_le_qS_mul`. This is the SSP analogue of
`ofReal_tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad`, and the natural choice
when the per-step ε does not depend on the input state. -/
theorem advantage_le_qSeps_plus_probEvent_bad
    (G₀ G₁ : Package unifSpec E (σ × Bool))
    (s_init : σ) (h_init₀ : G₀.init = pure (s_init, false))
    (h_init₁ : G₁.init = pure (s_init, false))
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((G₀.impl t).run (s, false)) ((G₁.impl t).run (s, false))) ≤ ε)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (p : σ × Bool),
      (G₀.impl t).run p = (G₁.impl t).run p)
    (h_mono₀ : ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((G₀.impl t).run p), z.2.2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b)) :
    ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ qS * ε
        + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ G₀.impl A).run (s_init, false)] := by
  refine le_trans
    (advantage_le_expectedSCost_plus_probEvent_bad
      G₀ G₁ s_init h_init₀ h_init₁ S (fun _ => ε)
      h_step_tv_S h_step_eq_nS h_mono₀ A h_qb) ?_
  gcongr
  exact expectedSCost_const_le_qS_mul G₀.impl S ε A h_qb (s_init, false)

end Package

end VCVio.SSP
