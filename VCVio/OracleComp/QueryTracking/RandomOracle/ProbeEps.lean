/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.OracleComp.ProbComp

/-!
# ε-Cell First-Fire Bound

This file develops the *first-fire bound* for a hidden value drawn from an arbitrary sampler
`oa : ProbComp R` whose every outcome has probability at most `ε`. Where the uniform development
(`FirstFire.lean`) charges a state-dependent `1 / (|R| - S.card)` per genuine read and needs an
exact telescope to fold the growing exclusion sets, the ε-development charges a single uniform `ε`
per read, valid in *every* state. The first-fire telescope collapses to a plain union bound: an
adaptive `q`-read strategy fires with probability at most `q · ε`.

## The model

A hidden target `w ← oa` is drawn **once** and committed into the run's state; an adaptive
`q`-read strategy `σ : List Bool → R`, mapping the boolean reply history (hit/miss) to the next
read point, then probes that fixed `w`, firing as soon as some read equals `w`. Up to the first
hit the read points are fixed by the all-miss history and independent of `w`, so averaging over
the single hidden draw — without ever conditioning on the drawn value — bounds the firing
probability by the union of `q` fixed singletons, each of mass at most `ε`. This models an eager
run that commits a sampled key at draw time and exposes it only through later membership tests.
Because the per-outcome bound `∀ r, Pr[= r | oa] ≤ ε` holds unconditionally, the bound is valid
in every state.

## Main results

* `hiddenReadMany` / `probEvent_hiddenReadMany_le` : the single-target adaptive read game and its
  first-fire union bound `Pr[fire] ≤ q · ε`.
* `hiddenReadList` / `probEvent_hiddenReadList_le` : the per-attempt-fresh-target list game and
  its union bound.
* `probEvent_bind_fire_le_of_gen` : the deferred-sampling fire bound whose marginal is a
  hidden-target read, against an opaque continuation.
* `drawList` : the explicit i.i.d. front-tape form of the per-attempt draws.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

variable {R : Type} [DecidableEq R]

/-! ## Hidden-target adaptive first-fire bound

`hiddenReadMany` draws a single hidden target `w ← oa` **once** and lets an adaptive `q`-read
strategy probe that *fixed* `w` repeatedly. This is the structure of an eager run that commits a
sampled key into its state at draw time and then exposes it only through later membership tests:
the key's value is hidden until the first hit, so up to the first hit the read points are fixed
(determined by the all-miss reply history) and independent of `w`. Averaging over the single hidden
draw — without ever conditioning on the drawn value — gives the union bound `q · ε`. -/

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
union of the `q` fixed singletons `{w = σ (replicate j false)}`, each of mass at most `ε`. -/
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
      exact zero_le
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

/-- Appending a fixed OR-flag `q` to a Boolean draw raises the firing probability by at most the
mass of `q` (i.e. `1` when `q = true`, `0` otherwise) over the residual draw. -/
theorem probEvent_bind_const_or_pure (q : Bool) (mb : ProbComp Bool) :
    Pr[(fun c : Bool => c = true) | mb >>= fun b => pure (q || b)]
      ≤ Pr[(fun c : Bool => c = true) | (pure q : ProbComp Bool)]
        + Pr[(fun c : Bool => c = true) | mb] := by
  cases q with
  | true => simp
  | false => simp

/-- The probabilistic multi-key game: draw `n` hidden targets independently from `oa`, one per
rejected signing attempt, and probe each by the same `q` adaptive reads; fire iff some read hits
some target. This is the accumulating-ghost-cache form of `hiddenReadMany`. -/
noncomputable def hiddenReadList (oa : ProbComp R) (q : ℕ) (σ : List Bool → R) :
    ℕ → ProbComp Bool
  | 0 => pure false
  | n + 1 => do
    let w ← oa
    let b ← hiddenReadList oa q σ n
    pure (readMany w q σ || b)

/-- **Multi-key hidden-target first-fire bound.** Drawing `n` independent hidden targets from `oa`
(each outcome of mass at most `ε`) and probing each by `q` adaptive reads fires with probability at
most `n · q · ε`. Proved by induction on `n`: the head key's contribution is the single-target
bound `probEvent_hiddenReadMany_le` (`≤ q · ε`), the tail's is the inductive hypothesis
(`≤ n · q · ε`), combined by the OR-append step `probEvent_bind_const_or_pure`. This is the form
that bounds the eager ghost run's bad probability once the run is factored so that each rejected
signing attempt's key draw is read off as an independent `hiddenReadMany` target. -/
theorem probEvent_hiddenReadList_le {oa : ProbComp R} {ε : ℝ≥0∞} (hε : ∀ r : R, Pr[= r | oa] ≤ ε)
    (q : ℕ) (σ : List Bool → R) (n : ℕ) :
    Pr[(fun b : Bool => b = true) | hiddenReadList oa q σ n] ≤ (n : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) := by
  induction n with
  | zero => simp [hiddenReadList]
  | succ n ih =>
    rw [hiddenReadList, probEvent_bind_eq_tsum]
    have hsplit : ∀ w : R,
        Pr[= w | oa] * Pr[(fun c : Bool => c = true) |
            hiddenReadList oa q σ n >>= fun b => pure (readMany w q σ || b)]
          ≤ Pr[= w | oa] * Pr[(fun c : Bool => c = true) | (pure (readMany w q σ) : ProbComp Bool)]
            + Pr[= w | oa] * Pr[(fun c : Bool => c = true) | hiddenReadList oa q σ n] := by
      intro w
      rw [← mul_add]
      gcongr
      exact probEvent_bind_const_or_pure (readMany w q σ) (hiddenReadList oa q σ n)
    refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
    rw [ENNReal.tsum_add]
    have h1 : (∑' w : R, Pr[= w | oa] *
        Pr[(fun c : Bool => c = true) | (pure (readMany w q σ) : ProbComp Bool)])
        = Pr[(fun b : Bool => b = true) | hiddenReadMany oa q σ] := by
      rw [hiddenReadMany, probEvent_bind_eq_tsum]
    have h2 : (∑' w : R, Pr[= w | oa] *
        Pr[(fun c : Bool => c = true) | hiddenReadList oa q σ n])
        ≤ Pr[(fun c : Bool => c = true) | hiddenReadList oa q σ n] := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
    rw [h1]
    calc Pr[(fun b : Bool => b = true) | hiddenReadMany oa q σ]
          + (∑' w : R, Pr[= w | oa] *
              Pr[(fun c : Bool => c = true) | hiddenReadList oa q σ n])
        ≤ (q : ℝ≥0∞) * ε + (n : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) :=
          add_le_add (probEvent_hiddenReadMany_le hε q σ) (le_trans h2 ih)
      _ = (↑(n + 1) : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) := by push_cast; ring

/-! ## Averaging the key count and the run-factorization bridge

The multi-key bound `probEvent_hiddenReadList_le` is stated for a *fixed* number of keys `n`. In
the intended application the key count is itself random (one ghost key is drawn per *rejected*
signing attempt), so the closing step averages the bound over a key-count distribution
`kn : ProbComp ℕ`, yielding `E[n] · q · ε`. The final bridge
`probEvent_le_of_eq_bind_hiddenReadList`
packages the union-bound side of the *direct route*: once a run's bad marginal is exhibited as a
`kn >>= hiddenReadList oa q σ` game (the deferred-sampling factorization), the bound is immediate.
-/

/-- **Averaged multi-key hidden-target bound.** When the number of independently drawn hidden keys
is itself sampled from `kn : ProbComp ℕ`, the firing probability of the multi-key game is at most
`E[n] · q · ε`, where `E[n] = ∑' n, Pr[= n | kn] · n` is the expected key count. This is the
averaging step (`C3`) of the direct route: it folds the fixed-`n` bound
`probEvent_hiddenReadList_le` against the key-count distribution. Combined with an expected-count
bound `E[n] ≤ qS / (1 - p)` it gives the target `qS · q · ε / (1 - p)`. -/
theorem probEvent_bind_hiddenReadList_le {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr[= r | oa] ≤ ε) (q : ℕ) (σ : List Bool → R) (kn : ProbComp ℕ) :
    Pr[(fun b : Bool => b = true) | kn >>= fun n => hiddenReadList oa q σ n]
      ≤ (∑' n : ℕ, Pr[= n | kn] * (n : ℝ≥0∞)) * ((q : ℝ≥0∞) * ε) := by
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [mul_assoc]
  gcongr
  exact probEvent_hiddenReadList_le hε q σ n

/-- **Direct-route union-bound bridge.** If an arbitrary run `run : ProbComp β` with a bad
event `bad : β → Prop` has its bad marginal exhibited as the averaged multi-key hidden-target game
`kn >>= hiddenReadList oa q σ` — i.e. the deferred-sampling factorization that pulls the run's
hidden key draws into an independent front block, reading each off as a `hiddenReadMany` target
probed by the `q` subsequent adaptive reads — then the run's bad probability is bounded by the
expected-count union bound `E[n] · q · ε`.

This is the reusable closing lemma of the direct route: the entire remaining content is supplied as
the hypothesis `hfac`, the distributional equality between the run's bad indicator and the abstract
game. Establishing `hfac` is the deferred-sampling commutation (factoring the run's per-key draws to
the front so the pre-first-hit reads become the deterministic strategy `σ`); the union-bound side it
feeds into is fully discharged here via `probEvent_bind_hiddenReadList_le`. -/
theorem probEvent_le_of_eq_bind_hiddenReadList {β : Type} {run : ProbComp β} {bad : β → Prop}
    {oa : ProbComp R} {ε : ℝ≥0∞} (hε : ∀ r : R, Pr[= r | oa] ≤ ε)
    (q : ℕ) (σ : List Bool → R) (kn : ProbComp ℕ)
    (hfac : Pr[bad | run]
      ≤ Pr[(fun b : Bool => b = true) | kn >>= fun n => hiddenReadList oa q σ n]) :
    Pr[bad | run] ≤ (∑' n : ℕ, Pr[= n | kn] * (n : ℝ≥0∞)) * ((q : ℝ≥0∞) * ε) :=
  hfac.trans (probEvent_bind_hiddenReadList_le hε q σ kn)

/-! ## Single output-irrelevant draw deferral

The lemmas above take the read strategy `σ` (and, in `hiddenReadList`, the key count) as already
*extracted* data. The genuine new content of the sound route is the **deferral primitive**: lifting
a single hidden draw out of an arbitrary run when that draw is used *only output-irrelevantly* —
i.e. it influences neither the run's visible output nor the read points, only the boolean "fire"
flag computed by membership tests against an adaptive read sequence.

The key observation (cf. `ghostHybridImpl_proj_trans`: the ghost cache is a per-step deterministic
projection of the single ghost-blind run, and the read answer is independent of the ghost value) is
that such a draw can be *deferred* past its continuation. Concretely, a run `oa >>= k` whose
continuation `k w` is built from a `w`-free generator `gen` (producing both the visible output and
the read strategy) with `w` entering only through `readMany w q σ`, has its fire-marginal equal to
that of the deferred game `gen >>= fun p => oa >>= fun w => …`. Each generated branch is then a
`hiddenReadMany` game on a *fixed* strategy `p.2`, charged `q · ε` by
`probEvent_hiddenReadMany_le`. This converts "front-load the draw across the opaque continuation"
into a local `bind`-commutation, the tractable route. -/

/-- **Bind-commutation for an output-irrelevant draw.** When the continuation `k w` is `gen >>= fun
p => pure (p.1, readMany w q p.2)` — a `w`-free generator `gen` producing both the visible output
`p.1` and the read strategy `p.2`, with the hidden draw `w` entering only through the fixed read
game `readMany w q p.2` — the fire-marginal of the run `oa >>= k` is unchanged by deferring the
draw of `w` to *after* `gen`. This is the local deferral step that replaces the abstract
"front-load across the fold" with a `PMF.bind`-commutation, proved here directly at the
`probEvent` level via `ENNReal.tsum_comm`. -/
theorem probEvent_bind_fire_eq_defer {α : Type} (oa : ProbComp R)
    (q : ℕ) (gen : ProbComp (α × (List Bool → R))) (k : R → ProbComp (α × Bool))
    (hk : ∀ w : R, k w = gen >>= fun p => pure (p.1, readMany w q p.2)) :
    Pr[(fun z : α × Bool => z.2 = true) | oa >>= k]
      = Pr[(fun z : α × Bool => z.2 = true) |
          gen >>= fun p => oa >>= fun w =>
            (pure (p.1, readMany w q p.2) : ProbComp (α × Bool))] := by
  have hL : Pr[(fun z : α × Bool => z.2 = true) | oa >>= k]
      = ∑' (w : R) (p : α × (List Bool → R)),
          Pr[= w | oa] * (Pr[= p | gen] *
            Pr[(fun z : α × Bool => z.2 = true) |
              (pure (p.1, readMany w q p.2) : ProbComp (α × Bool))]) := by
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun w => ?_
    rw [hk w, probEvent_bind_eq_tsum, ENNReal.tsum_mul_left]
  have hR : Pr[(fun z : α × Bool => z.2 = true) |
          gen >>= fun p => oa >>= fun w =>
            (pure (p.1, readMany w q p.2) : ProbComp (α × Bool))]
      = ∑' (p : α × (List Bool → R)) (w : R),
          Pr[= p | gen] * (Pr[= w | oa] *
            Pr[(fun z : α × Bool => z.2 = true) |
              (pure (p.1, readMany w q p.2) : ProbComp (α × Bool))]) := by
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun p => ?_
    rw [probEvent_bind_eq_tsum, ENNReal.tsum_mul_left]
  rw [hL, hR, ENNReal.tsum_comm]
  refine tsum_congr fun p => tsum_congr fun w => ?_
  ring

/-- **Single output-irrelevant draw first-fire bound (structural form).** A run `oa >>= k` that
draws one hidden value `w ← oa` (each outcome of mass at most `ε`) and feeds it to a continuation
`k w = gen >>= fun p => pure (p.1, readMany w q p.2)` — a `w`-free generator `gen` producing the
visible output and the read strategy, with `w` entering *only* through the fixed read game — fires
with probability at most `q · ε`.

This is the reusable single-draw deferral primitive of the sound route. It formalizes
"output-irrelevant draw ⇒ the read points are a fixed strategy independent of `w`" by demanding the
continuation factor through a `w`-free `gen`; the proof defers the draw past `gen`
(`probEvent_bind_fire_eq_defer`) so each generated branch becomes a `hiddenReadMany` game on a fixed
strategy `p.2`, charged `q · ε` by `probEvent_hiddenReadMany_le`. Stage B lifts the `n`-interleaved
draws by induction with `gen` carrying the remaining draws; Stage C instantiates `gen`/`k` for the
ghost-blind run via the projection `ghostHybridImpl_proj_trans`. -/
theorem probEvent_bind_fire_le_of_gen {α : Type} {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr[= r | oa] ≤ ε) (q : ℕ) (gen : ProbComp (α × (List Bool → R)))
    (k : R → ProbComp (α × Bool))
    (hk : ∀ w : R, k w = gen >>= fun p => pure (p.1, readMany w q p.2)) :
    Pr[(fun z : α × Bool => z.2 = true) | oa >>= k] ≤ (q : ℝ≥0∞) * ε := by
  rw [probEvent_bind_fire_eq_defer oa q gen k hk]
  refine probEvent_bind_le_of_forall_le fun p _ => ?_
  have hinner : Pr[(fun z : α × Bool => z.2 = true) |
        oa >>= fun w => (pure (p.1, readMany w q p.2) : ProbComp (α × Bool))]
      = Pr[(fun b : Bool => b = true) | hiddenReadMany oa q p.2] := by
    rw [hiddenReadMany, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun w => ?_
    rw [probEvent_pure, probEvent_pure]
  rw [hinner]
  exact probEvent_hiddenReadMany_le hε q p.2

/-- **Single output-irrelevant draw first-fire bound (marginal form).** The convenience special
case of `probEvent_bind_fire_le_of_gen` for a run `oa >>= k` whose continuation's fire-marginal is,
for *every* hidden value `w`, exactly that of the fixed read game `readMany w q σ` against a single
strategy `σ` independent of `w`. Whenever every outcome of `oa` has mass at most `ε`, the run fires
with probability at most `q · ε`.

Use this form when the deferred read strategy is a *fixed* `σ` (the simplest output-irrelevant
case); use the structural `probEvent_bind_fire_le_of_gen` when the strategy is itself produced by
`w`-free randomness. -/
theorem probEvent_bind_fire_le_of_marginal_eq_readMany {α : Type} {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr[= r | oa] ≤ ε) (q : ℕ) (σ : List Bool → R) (k : R → ProbComp (α × Bool))
    (hmarg : ∀ w : R, Pr[(fun z : α × Bool => z.2 = true) | k w]
      = Pr[(fun b : Bool => b = true) | (pure (readMany w q σ) : ProbComp Bool)]) :
    Pr[(fun z : α × Bool => z.2 = true) | oa >>= k] ≤ (q : ℝ≥0∞) * ε := by
  have hcongr : Pr[(fun z : α × Bool => z.2 = true) | oa >>= k]
      = Pr[(fun b : Bool => b = true) | hiddenReadMany oa q σ] := by
    rw [hiddenReadMany, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    exact tsum_congr fun w => by rw [hmarg w]
  rw [hcongr]
  exact probEvent_hiddenReadMany_le hε q σ

/-! ## Iterated draws: the explicit front-block key list

Stage A defers a *single* output-irrelevant draw. `drawList` lifts this to `n` interleaved draws
by collecting them into an explicit front block: draw a list of `n` independent keys up front,
against which a run's hidden draws can be exhibited and then charged by the abstract
`hiddenReadList` union bound. -/

/-- Draw a list of `n` independent keys from `oa` (the front block of the deferred-sampling
factorization). The keys are the hidden targets; the list length is the key count `n`. -/
noncomputable def drawList (oa : ProbComp R) : ℕ → ProbComp (List R)
  | 0 => pure []
  | n + 1 => do
      let w ← oa
      let ws ← drawList oa n
      pure (w :: ws)

omit [DecidableEq R] in
/-- The front-block draw never fails: it only ever draws from `oa` (which is failure-free) and
returns, so `drawList oa n` has zero failure mass. -/
lemma probFailure_drawList (oa : ProbComp R) (n : ℕ) :
    Pr[⊥ | drawList oa n] = 0 := by
  induction n with
  | zero => simp [drawList]
  | succ n _ => rw [drawList]; simp

omit [DecidableEq R] in
/-- Total output mass of the front-block draw is `1` (it never fails). -/
lemma tsum_probOutput_drawList_eq_one (oa : ProbComp R) (n : ℕ) :
    (∑' ws : List R, Pr[= ws | drawList oa n]) = 1 :=
  tsum_probOutput_eq_one' (probFailure_drawList oa n)

end OracleComp
