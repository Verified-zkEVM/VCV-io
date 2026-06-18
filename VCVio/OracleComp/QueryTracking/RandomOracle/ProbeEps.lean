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

/-! ## Hidden-target adaptive first-fire bound

The companion of `probeManyEps` for the *same-target-reused* regime. Where `probeManyEps`
redraws a fresh sample `v ← oa` at **every** probe (the memoryless, deferred-sampling model),
`hiddenReadMany` draws a single hidden target `w ← oa` **once** and lets an adaptive `q`-read
strategy probe that *fixed* `w` repeatedly. This is the structure of an eager run that commits a
sampled key into its state at draw time and then exposes it only through later membership tests:
the key's value is hidden until the first hit, so up to the first hit the read points are fixed
(determined by the all-miss reply history) and independent of `w`. Averaging over the single hidden
draw — without ever conditioning on the drawn value — gives the same union bound `q · ε`. -/

/-- Adaptive `q`-read game against a FIXED hidden target `w`: the strategy `σ` maps the list of
boolean replies (hit/miss) seen so far to the next read point, and the game fires (returns `true`)
iff some read equals `w`. The target `w` is reused across all reads; it is drawn once, outside this
program (see `hiddenReadMany`). -/
noncomputable def readMany (w : R) : ℕ → (List Bool → R) → Bool
  | 0, _ => false
  | q + 1, σ =>
    let b := decide (σ [] = w)
    b || readMany w q (fun h => σ (b :: h))

/-- The hidden-target game: draw the target `w ← oa` **once**, then run `q` adaptive reads against
that fixed `w`. -/
noncomputable def hiddenReadMany (oa : ProbComp R) (q : ℕ) (σ : List Bool → R) : ProbComp Bool :=
  oa >>= fun w => pure (readMany w q σ)

/-- **Fixed read points before the first hit.** A FIXED-target adaptive read game fires iff the
hidden target `w` equals one of the `q` read points reached along the all-miss history
`σ (List.replicate j false)`. The point: those read points do **not** depend on `w` (until a hit,
every reply is a miss, so the history is `replicate j false`), which is exactly what turns the
averaged firing probability into a plain union bound. -/
theorem readMany_true_iff (w : R) (q : ℕ) (σ : List Bool → R) :
    readMany w q σ = true ↔ ∃ j < q, w = σ (List.replicate j false) := by
  induction q generalizing σ with
  | zero => simp [readMany]
  | succ q ih =>
    rw [readMany]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact ⟨0, Nat.succ_pos q, by simpa using h.symm⟩
      · by_cases hhead : σ [] = w
        · exact ⟨0, Nat.succ_pos q, hhead.symm⟩
        · rw [decide_eq_false (by simpa using hhead)] at h
          obtain ⟨j, hj, hwj⟩ := (ih (fun h => σ (false :: h))).1 h
          exact ⟨j + 1, Nat.succ_lt_succ hj, by simpa [List.replicate_succ] using hwj⟩
    · rintro ⟨j, hj, hwj⟩
      cases j with
      | zero => left; simpa using hwj.symm
      | succ j =>
        by_cases hhead : σ [] = w
        · exact Or.inl hhead
        · refine Or.inr ?_
          rw [decide_eq_false (by simpa using hhead)]
          exact (ih (fun h => σ (false :: h))).2
            ⟨j, Nat.lt_of_succ_lt_succ hj, by simpa [List.replicate_succ] using hwj⟩

/-- **Hidden-target adaptive first-fire bound.** A FIXED target `w ← oa` drawn **once** and probed
by `q` adaptive reads fires with probability at most `q · ε`, whenever every outcome of `oa` has
mass at most `ε`. The averaging is over the single hidden draw; we never condition on `w`. Because
the read points are fixed by the all-miss history (`readMany_true_iff`), the firing event is the
union of the `q` fixed singletons `{w = σ (replicate j false)}`, each of mass at most `ε`. This is
the same-target-reused sibling of `probEvent_probeManyEps_le`. -/
theorem probEvent_hiddenReadMany_le {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr[= r | oa] ≤ ε) (q : ℕ) (σ : List Bool → R) :
    Pr[ (fun b : Bool => b = true) | hiddenReadMany oa q σ ] ≤ (q : ℝ≥0∞) * ε := by
  rw [hiddenReadMany, probEvent_bind_eq_tsum]
  have hstep : ∀ w : R,
      Pr[= w | oa] * Pr[(fun b => b = true) | (pure (readMany w q σ) : ProbComp Bool)]
        ≤ ∑ j ∈ Finset.range q,
            if w = σ (List.replicate j false) then Pr[= w | oa] else 0 := by
    intro w
    by_cases hfire : readMany w q σ = true
    · rw [probEvent_pure]
      simp only [hfire, if_true, mul_one]
      obtain ⟨j, hj, hwj⟩ := (readMany_true_iff w q σ).1 hfire
      calc Pr[= w | oa]
          = (if w = σ (List.replicate j false) then Pr[= w | oa] else 0) := by rw [if_pos hwj]
        _ ≤ ∑ j ∈ Finset.range q,
              if w = σ (List.replicate j false) then Pr[= w | oa] else 0 :=
            Finset.single_le_sum
              (f := fun j => if w = σ (List.replicate j false) then Pr[= w | oa] else 0)
              (fun i _ => by positivity) (Finset.mem_range.2 hj)
    · rw [probEvent_pure, if_neg hfire, mul_zero]
      exact zero_le'
  refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc ∑ j ∈ Finset.range q, ∑' w : R,
          (if w = σ (List.replicate j false) then Pr[= w | oa] else 0)
      ≤ ∑ j ∈ Finset.range q, ε := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [tsum_eq_single (σ (List.replicate j false))
          (by intro b hb; rw [if_neg hb])]
        rw [if_pos rfl]
        exact hε _
    _ = (q : ℝ≥0∞) * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The multi-key fixed-target game: a list `ws` of hidden keys, each probed by the same `q`
adaptive reads; fires iff some read hits some key. Used to model the eager ghost run, whose ghost
cache accumulates one sampled key per rejected signing attempt. -/
noncomputable def readManyList (ws : List R) (q : ℕ) (σ : List Bool → R) : Bool :=
  ws.any (fun w => readMany w q σ)

/-- The list game fires iff some individual key's game fires. -/
theorem readManyList_true_iff (ws : List R) (q : ℕ) (σ : List Bool → R) :
    readManyList ws q σ = true ↔ ∃ w ∈ ws, readMany w q σ = true := by
  simp [readManyList, List.any_eq_true]

end OracleComp
