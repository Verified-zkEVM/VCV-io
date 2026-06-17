/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.ProbComp

/-!
# ε-Cell First-Fire Probe Bound

This file generalizes the *first-fire probe bound* from a uniform per-cell value to an arbitrary
sampler `oa : ProbComp R` whose every outcome has probability at most `ε`. Where the uniform
development (`FirstFire.lean`) charges a state-dependent `1 / (|R| - S.card)` per genuine probe and
needs an exact telescope to fold the growing exclusion sets, the ε-development charges a single
uniform `ε` per genuine probe, valid in *every* state. The first-fire telescope therefore collapses
to a plain union bound: an adaptive `q`-probe strategy fires with probability at most `q · ε`.

## The model

A probe targets a *cell* `d : D`. Each cell carries a value drawn from `oa`; the adversary never
sees the value, only the boolean reply "does cell `d` hold `a`?" to a probe `(d, a)`. We model the
genuine probe memorylessly: each genuine probe draws a fresh sample `v ← oa` and replies
`decide (v = a)`. Because the per-outcome bound `∀ r, Pr[= r | oa] ≤ ε` holds unconditionally, the
fresh-draw model is a sound upper bound for any state-conditioned commitment law (the conditioning
that inflates a re-targeted cell's firing probability in the uniform case is, in the ε-case,
already absorbed into the hypothesis `hε`, which bounds *every* outcome's mass).

## Main results

* `probeStepEps` / `probeManyEps` : the single-probe and adaptive `q`-probe programs.
* `probEvent_probeStepEps_le` : a single probe fires with probability at most `ε`.
* `probEvent_probeManyEps_le` : the adaptive first-fire union bound `Pr[fire] ≤ q · ε`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

variable {D R : Type} [DecidableEq R]

/-- One ε-probe at cell `d` (the cell index is carried only for documentation/adaptivity) with
target `a`: draw a fresh value `v ← oa` and reply whether `v = a`. The genuine-fire flag is exactly
this boolean. -/
noncomputable def probeStepEps (oa : ProbComp R) (a : R) : ProbComp Bool :=
  (fun v => decide (v = a)) <$> oa

/-- A single ε-probe fires with probability at most `ε`, in *any* state, whenever every outcome of
`oa` has mass at most `ε`. -/
theorem probEvent_probeStepEps_le {oa : ProbComp R} {ε : ℝ≥0∞} (a : R)
    (hε : ∀ r : R, Pr[= r | oa] ≤ ε) :
    Pr[ (fun b : Bool => b = true) | probeStepEps oa a ] ≤ ε := by
  rw [probeStepEps, probEvent_map]
  have hpred : ((fun b : Bool => b = true) ∘ fun v : R => decide (v = a)) = fun v : R => v = a := by
    funext v
    rw [Function.comp_apply, decide_eq_true_eq]
  rw [hpred, probEvent_eq_eq_probOutput]
  exact hε a

/-- An adaptive `q`-probe ε-program: the strategy `σ` maps the list of boolean replies seen so far
to the next probe target, and the program returns whether some probe fired. Each step draws a fresh
sample from `oa` and OR-s the reply onto the tail. -/
noncomputable def probeManyEps (oa : ProbComp R) : ℕ → (List Bool → R) → ProbComp Bool
  | 0, _ => pure false
  | q + 1, σ =>
    probeStepEps oa (σ []) >>= fun b =>
      (fun b' => b || b') <$> probeManyEps oa q fun h => σ (b :: h)

@[simp]
theorem probeManyEps_zero (oa : ProbComp R) (σ : List Bool → R) :
    probeManyEps oa 0 σ = pure false := rfl

theorem probeManyEps_succ (oa : ProbComp R) (q : ℕ) (σ : List Bool → R) :
    probeManyEps oa (q + 1) σ =
      probeStepEps oa (σ []) >>= fun b =>
        (fun b' => b || b') <$> probeManyEps oa q fun h => σ (b :: h) := rfl

/-- **ε-cell first-fire bound.** An adaptive strategy issuing `q` probes against a sampler whose
every outcome has mass at most `ε` fires with probability at most `q · ε`. The per-step charge is a
uniform `ε` (`probEvent_probeStepEps_le`), valid in every state, so the union bound is exact: there
is no growing exclusion set to telescope. -/
theorem probEvent_probeManyEps_le {oa : ProbComp R} {ε : ℝ≥0∞} (hε : ∀ r : R, Pr[= r | oa] ≤ ε)
    (q : ℕ) (σ : List Bool → R) :
    Pr[ (fun b : Bool => b = true) | probeManyEps oa q σ ] ≤ (q : ℝ≥0∞) * ε := by
  induction q generalizing σ with
  | zero => simp
  | succ q ih =>
    rw [probeManyEps_succ, probEvent_bind_eq_tsum]
    -- Split on the head reply `b`. Genuine head fire (`b = true`) is charged `ε`; on a head miss
    -- (`b = false`) the OR collapses to the tail, charged `q · ε` by the inductive hypothesis.
    have hsplit : ∀ b : Bool,
        Pr[= b | probeStepEps oa (σ [])] *
          Pr[ (fun c : Bool => c = true) |
            (fun b' => b || b') <$> probeManyEps oa q fun h => σ (b :: h)] ≤
          (if b = true then ε else (q : ℝ≥0∞) * ε) := by
      intro b
      cases b with
      | true =>
        -- The OR is constantly `true`, so the event holds with probability `1`; the head reaches
        -- `true` with probability at most `ε`.
        simp only [Bool.true_or]
        refine le_trans (mul_le_mul' (le_refl _) probEvent_le_one) ?_
        rw [mul_one,
          show Pr[= true | probeStepEps oa (σ [])] =
            Pr[ (fun c : Bool => c = true) | probeStepEps oa (σ [])] from
            (probEvent_eq_eq_probOutput _ true).symm]
        exact probEvent_probeStepEps_le _ hε
      | false =>
        -- The OR collapses to the tail; the head mass is at most `1`.
        simp only [if_neg (by simp : ¬ (false = true)), Bool.false_or, probEvent_map]
        have htail : Pr[ ((fun c : Bool => c = true) ∘ fun b' => b') |
            probeManyEps oa q fun h => σ (false :: h)] ≤ (q : ℝ≥0∞) * ε := by
          have : ((fun c : Bool => c = true) ∘ fun b' : Bool => b') =
              fun c : Bool => c = true := rfl
          rw [this]; exact ih _
        exact le_trans (mul_le_mul' probOutput_le_one htail) (one_mul _).le
    refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
    rw [tsum_bool, if_pos rfl, if_neg (by simp : ¬ (false = true))]
    rw [Nat.cast_succ, add_mul, one_mul, add_comm]

end OracleComp
