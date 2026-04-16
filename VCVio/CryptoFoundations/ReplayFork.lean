/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.Fork
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Replay-Based Forking

This file adds an additive replay-based fork path beside the existing seed-based
forking infrastructure in `VCVio.CryptoFoundations.Fork`.

The key idea is to record a first-run `QueryLog`, then replay that transcript
exactly up to a selected fork point while changing one distinguished oracle
answer. This is meant to support settings such as Fiat-Shamir where ambient
randomness should be replayed by transcript rather than by pre-generated seed
coverage.
-/

open OracleSpec OracleComp

namespace QueryLog

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

/-- The `n`-th answer in the log for queries to oracle `t`, if it exists. -/
def getQueryValue? (log : QueryLog spec) (t : ι) (n : Nat) : Option (spec.Range t) := by
  match (log.getQ (· = t))[n]? with
  | none => exact none
  | some ⟨t', u⟩ =>
      if h : t' = t then
        exact some (by cases h; exact u)
      else
        exact none

end QueryLog

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
variable [spec.DecidableEq]

/-- Replay state for the second run of a replay-based fork.

`trace` is the first-run transcript, `cursor` tracks how much of that transcript
has been matched so far, `distinguishedCount` counts how many queries to the
forked oracle family have already been replayed, and `observed` stores the
actual second-run transcript. -/
structure ReplayForkState (spec : OracleSpec ι) (i : ι) where
  trace : QueryLog spec
  cursor : Nat
  distinguishedCount : Nat
  forkQuery : Nat
  replacement : spec.Range i
  forkConsumed : Bool
  mismatch : Bool
  observed : QueryLog spec

namespace ReplayForkState

variable {i : ι}

/-- Initial replay state before the second run starts. -/
def init (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    ReplayForkState spec i where
  trace := trace
  cursor := 0
  distinguishedCount := 0
  forkQuery := forkQuery
  replacement := replacement
  forkConsumed := false
  mismatch := false
  observed := []

/-- The next entry in the logged first-run transcript, if any. -/
def nextEntry? (st : ReplayForkState spec i) :
    Option ((t : ι) × spec.Range t) :=
  st.trace[st.cursor]?

/-- Record an observed query-answer pair in the second-run log. -/
def noteObserved (st : ReplayForkState spec i) (t : ι) (u : spec.Range t) :
    ReplayForkState spec i :=
  { st with observed := st.observed.logQuery t u }

/-- Mark the replay as having deviated from the first-run prefix. -/
def markMismatch (st : ReplayForkState spec i) : ReplayForkState spec i :=
  { st with mismatch := true }

end ReplayForkState

/-- Replay oracle for the second run of a replay-based fork.

Before the fork point, the oracle must match the logged first-run transcript
exactly. At the selected distinguished query it returns the replacement answer.
Once the fork point has been consumed, or once replay has mismatched the logged
prefix, the oracle falls through to the live ambient oracle. -/
def replayOracle (i : ι) :
    QueryImpl spec (StateT (ReplayForkState spec i) (OracleComp spec)) := fun t => do
  let st ← get
  if st.forkConsumed || st.mismatch then
    let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
    set (st.noteObserved t u)
    pure u
  else
    match st.nextEntry? with
    | none =>
        let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
        set ((st.markMismatch).noteObserved t u)
        pure u
    | some ⟨t', u'⟩ =>
        if hsame : t = t' then
          let logged : spec.Range t := by
            cases hsame
            exact u'
          if hti : t = i then
            if hfork : st.distinguishedCount = st.forkQuery then
              let replacement : spec.Range t := by
                cases hti
                exact st.replacement
              let st' : ReplayForkState spec i :=
                { st with
                  cursor := st.cursor + 1
                  distinguishedCount := st.distinguishedCount + 1
                  forkConsumed := true
                  observed := st.observed.logQuery t replacement }
              set st'
              pure replacement
            else
              let st' : ReplayForkState spec i :=
                { st with
                  cursor := st.cursor + 1
                  distinguishedCount := st.distinguishedCount + 1
                  observed := st.observed.logQuery t logged }
              set st'
              pure logged
          else
            let st' : ReplayForkState spec i :=
              { st with
                cursor := st.cursor + 1
                observed := st.observed.logQuery t logged }
            set st'
            pure logged
        else
          let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
          set ((st.markMismatch).noteObserved t u)
          pure u

/-- Run `main` with query logging. This is the first-run object for replay forks. -/
@[reducible]
def replayFirstRun (main : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  (simulateQ (loggingOracle (spec := spec)) main).run

omit [DecidableEq ι] [spec.DecidableEq] in
@[simp]
lemma fst_map_replayFirstRun (main : OracleComp spec α) :
    Prod.fst <$> replayFirstRun main = main := by
  simpa [replayFirstRun, OracleComp.withQueryLog, loggingOracle] using
    (loggingOracle.fst_map_run_simulateQ (spec := spec) main)

/-- Replay the second run against a fixed first-run log, fork point, and
replacement answer, returning both the final output and replay state. -/
def replayRunWithTraceValue (main : OracleComp spec α) (i : ι)
    (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    OracleComp spec (α × ReplayForkState spec i) := do
  let init := ReplayForkState.init trace forkQuery replacement
  (simulateQ (replayOracle i) main).run init

/-- Deterministic replay-fork core with the first-run output and transcript fixed.

This mirrors `forkWithSeedValue`: the first-run result and replacement answer are
inputs, while the second run may still make live oracle calls after the fork
point. -/
def forkReplayWithTraceValue (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (first : α × QueryLog spec) (u : spec.Range i) :
    OracleComp spec (Option (α × α)) := do
  let x₁ := first.1
  match cf x₁ with
  | none => pure none
  | some s =>
      match QueryLog.getQueryValue? first.2 i ↑s with
      | none => pure none
      | some logged =>
          if logged = u then
            pure none
          else
            let (x₂, st) ← replayRunWithTraceValue main i first.2 ↑s u
            if st.mismatch || !st.forkConsumed then
              pure none
            else if cf x₂ = some s then
              pure (some (x₁, x₂))
            else
              pure none

/-- Additive replay-based fork operation.

The first run is obtained via `withQueryLog`. The second run then replays that
transcript exactly up to the selected distinguished query, replacing exactly one
answer at that query. -/
def forkReplay (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec] :
    OracleComp spec (Option (α × α)) := do
  let first ← replayFirstRun main
  match cf first.1 with
  | none => pure none
  | some _ =>
      let u ← liftComp ($ᵗ spec.Range i) spec
      forkReplayWithTraceValue main qb i cf first u

@[simp]
lemma forkReplayWithTraceValue_eq_none_of_cf_none
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (first : α × QueryLog spec) (u : spec.Range i)
    (h : cf first.1 = none) :
    forkReplayWithTraceValue main qb i cf first u = pure none := by
  simp [forkReplayWithTraceValue, h]

end OracleComp
