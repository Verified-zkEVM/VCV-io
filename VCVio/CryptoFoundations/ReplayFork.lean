/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SeededFork
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Replay-Based Forking

This file adds an additive replay-based fork path beside the existing seed-based
forking infrastructure in `VCVio.CryptoFoundations.SeededFork`.

The key idea is to record a first-run `QueryLog`, then replay that transcript
exactly up to a selected fork point while changing one distinguished oracle
answer. This is meant to support settings such as Fiat-Shamir where ambient
randomness should be replayed by transcript rather than by pre-generated seed
coverage.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal Function Finset

open scoped OracleSpec.PrimitiveQuery

namespace QueryLog

variable {ι : Type} {spec : OracleSpec ι}

/-- The query input at position `n` in the full interleaved log, if it exists. -/
def inputAt? (log : QueryLog spec) (n : Nat) : Option ι :=
  Sigma.fst <$> log[n]?

/-- The `n`-th answer in the log for queries to oracle `t`, if it exists. -/
def getQueryValue? [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat) :
    Option (spec.Range t) :=
  match (log.getQ (· = t))[n]? with
  | none => none
  | some ⟨t', u⟩ => if h : t' = t then some (h ▸ u) else none

@[simp]
lemma inputAt?_logQuery_of_lt (log : QueryLog spec) (t : ι) (u : spec.Range t) {n : Nat}
    (hn : n < log.length) :
    inputAt? (log.logQuery t u) n = inputAt? log n := by
  simp [inputAt?, QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hn]

@[simp]
lemma inputAt?_logQuery_self (log : QueryLog spec) (t : ι) (u : spec.Range t) :
    inputAt? (log.logQuery t u) log.length = some t := by
  simp [inputAt?, QueryLog.logQuery, QueryLog.singleton]

/-- Decompose `getQ` across a `logQuery` step. -/
lemma getQ_logQuery (log : QueryLog spec) (t : ι) (u : spec.Range t)
    (p : ι → Prop) [DecidablePred p] :
    (log.logQuery t u).getQ p = log.getQ p ++ (if p t then [⟨t, u⟩] else []) := by
  simp [QueryLog.logQuery, QueryLog.singleton]

/-- If `getQueryValue? log t n = some u`, then the `n`-th `t`-filtered entry of
`log` is `⟨t, u⟩`. -/
lemma getQ_getElem?_eq_of_getQueryValue?_eq_some [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : getQueryValue? log t n = some u) :
    (log.getQ (· = t))[n]? = some ⟨t, u⟩ := by
  rcases hopt : (log.getQ (· = t))[n]? with _ | ⟨t', u'⟩
  · simp [getQueryValue?, hopt] at h
  · obtain rfl : t' = t := by by_contra ht; simp [getQueryValue?, hopt, ht] at h
    simpa [getQueryValue?, hopt] using h

/-- Converse: if the `n`-th `t`-filtered entry is `⟨t, u⟩`, then
`getQueryValue? log t n = some u`. -/
lemma getQueryValue?_eq_some_of_getQ_getElem? [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : (log.getQ (· = t))[n]? = some ⟨t, u⟩) :
    getQueryValue? log t n = some u := by
  simp [getQueryValue?, h]

/-- Every entry of `log.getQ (· = t)` has its first component equal to `t`. -/
lemma getQ_eq_mem [spec.DecidableEq] (log : QueryLog spec) (t : ι)
    {entry : (t' : ι) × spec.Range t'} (h : entry ∈ log.getQ (· = t)) :
    entry.1 = t := by
  induction log <;> grind [QueryLog.getQ_cons, QueryLog.getQ_nil]

/-- If the `t`-filtered log has at least `n + 1` entries, then `getQueryValue? log t n`
is `some _`. -/
lemma getQueryValue?_isSome_of_lt [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat)
    (h : n < (log.getQ (· = t)).length) :
    (getQueryValue? log t n).isSome := by
  simp [getQueryValue?, List.getElem?_eq_getElem h, getQ_eq_mem log t (List.getElem_mem h)]

/-- Prepending an entry whose oracle index does not match `t` leaves the `t`-indexed
view of the log unchanged. -/
lemma getQueryValue?_cons_of_ne [spec.DecidableEq]
    (entry : (t' : ι) × spec.Range t') (log : QueryLog spec) (t : ι) (n : Nat)
    (h : entry.1 ≠ t) :
    getQueryValue? (entry :: log) t n = getQueryValue? log t n := by
  simp [getQueryValue?, QueryLog.getQ_cons, h]

/-- The first entry of `getQueryValue? (⟨t, u⟩ :: log) t 0` is the prepended value. -/
lemma getQueryValue?_cons_self_zero [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) :
    getQueryValue? (⟨t, u⟩ :: log) t 0 = some u :=
  getQueryValue?_eq_some_of_getQ_getElem? _ _ _ _ (by simp [QueryLog.getQ_cons])

/-- Prepending a matching `⟨t, _⟩` entry shifts later `t`-indexed lookups by one. -/
lemma getQueryValue?_cons_self_succ [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) (n : Nat) :
    getQueryValue? (⟨t, u⟩ :: log) t (n + 1) = getQueryValue? log t n := by
  simp [getQueryValue?, QueryLog.getQ_cons]

/-- The prefix of `log` up to (but not including) the `s`-th `i`-query.

If `log` has fewer than `s + 1` queries to `i`, this returns the entire `log`. This is
the replay analogue of `QuerySeed.takeAtIndex` and is the key slicing operator used in
the Cauchy-Schwarz step of the replay forking bound. -/
def takeBeforeForkAt [spec.DecidableEq] :
    QueryLog spec → ι → ℕ → QueryLog spec
  | [], _, _ => []
  | ⟨t, u⟩ :: tl, i, 0 =>
      if t = i then [] else ⟨t, u⟩ :: takeBeforeForkAt tl i 0
  | ⟨t, u⟩ :: tl, i, s + 1 =>
      if t = i then ⟨t, u⟩ :: takeBeforeForkAt tl i s
      else ⟨t, u⟩ :: takeBeforeForkAt tl i (s + 1)

@[simp]
lemma takeBeforeForkAt_nil [spec.DecidableEq] (i : ι) (s : ℕ) :
    takeBeforeForkAt ([] : QueryLog spec) i s = [] := rfl

lemma takeBeforeForkAt_cons_of_ne [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (tl : QueryLog spec) (i : ι) (s : ℕ) (h : t ≠ i) :
    takeBeforeForkAt (⟨t, u⟩ :: tl) i s = ⟨t, u⟩ :: takeBeforeForkAt tl i s := by
  cases s <;> simp [takeBeforeForkAt, h]

lemma takeBeforeForkAt_cons_self_zero [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (tl : QueryLog spec) :
    takeBeforeForkAt (⟨t, u⟩ :: tl) t 0 = [] := by
  simp [takeBeforeForkAt]

lemma takeBeforeForkAt_cons_self_succ [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (tl : QueryLog spec) (s : ℕ) :
    takeBeforeForkAt (⟨t, u⟩ :: tl) t (s + 1) = ⟨t, u⟩ :: takeBeforeForkAt tl t s := by
  simp [takeBeforeForkAt]

/-- The prefix `takeBeforeForkAt log i s` has at most `s` queries to `i`. -/
lemma countQ_takeBeforeForkAt_le [spec.DecidableEq]
    (log : QueryLog spec) (i : ι) (s : ℕ) :
    (takeBeforeForkAt log i s).countQ (· = i) ≤ s := by
  induction log generalizing s with
  | nil => simp [QueryLog.countQ]
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      by_cases h : t = i
      · subst h
        cases s with
        | zero => simp [takeBeforeForkAt_cons_self_zero, QueryLog.countQ]
        | succ s =>
            simp only [takeBeforeForkAt_cons_self_succ, QueryLog.countQ, QueryLog.getQ_cons,
              ↓reduceIte, List.length_cons]
            simpa only [QueryLog.countQ] using Nat.succ_le_succ (ih s)
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ h]
        simpa only [QueryLog.countQ, QueryLog.getQ_cons, if_neg h] using ih s

/-- If `log` contains at least `s + 1` queries to `i`, then `takeBeforeForkAt log i s` has
exactly `s` queries to `i`. -/
lemma countQ_takeBeforeForkAt_eq [spec.DecidableEq] (log : QueryLog spec) (i : ι) (s : ℕ)
    (h : s < (log.getQ (· = i)).length) :
    (takeBeforeForkAt log i s).countQ (· = i) = s := by
  induction log generalizing s with
  | nil => simp [QueryLog.getQ] at h
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      by_cases ht : t = i
      · subst ht
        cases s with
        | zero => simp [takeBeforeForkAt_cons_self_zero, QueryLog.countQ, QueryLog.getQ]
        | succ s =>
            simp only [takeBeforeForkAt_cons_self_succ, QueryLog.countQ, QueryLog.getQ_cons,
              ↓reduceIte, List.length_cons] at h ⊢
            grind [QueryLog.countQ]
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ ht]
        simp only [QueryLog.countQ, QueryLog.getQ_cons, if_neg ht] at h ⊢
        simpa [QueryLog.countQ] using ih s h

/-- `takeBeforeForkAt log i s` is a prefix of `log`. -/
lemma takeBeforeForkAt_prefix [spec.DecidableEq]
    (log : QueryLog spec) (i : ι) (s : ℕ) :
    (takeBeforeForkAt log i s) <+: log := by
  induction log generalizing s with
  | nil => simp
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      rcases eq_or_ne t i with rfl | h
      · cases s with
        | zero => simp [takeBeforeForkAt_cons_self_zero]
        | succ s =>
            rw [takeBeforeForkAt_cons_self_succ]
            exact List.cons_prefix_cons.mpr ⟨rfl, ih s⟩
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ h]
        exact List.cons_prefix_cons.mpr ⟨rfl, ih s⟩

/-- `getQueryValue?` on the truncation at index `i` position `s` is `none`: the prefix
has fewer than `s + 1` entries at oracle `i`. -/
lemma getQueryValue?_takeBeforeForkAt_self [spec.DecidableEq]
    (log : QueryLog spec) (i : ι) (s : ℕ) :
    getQueryValue? (takeBeforeForkAt log i s) i s = none := by
  unfold getQueryValue?
  rw [List.getElem?_eq_none_iff.mpr
    (by simpa [QueryLog.countQ] using countQ_takeBeforeForkAt_le log i s)]

/-- If `log` has at most `s` entries of type `i`, then truncating `log` at position `s`
leaves it unchanged: there is no `s`-th `i`-entry to truncate before. -/
lemma takeBeforeForkAt_of_getQ_length_le [spec.DecidableEq] (log : QueryLog spec) (i : ι) (s : ℕ)
    (h : (log.getQ (· = i)).length ≤ s) :
    takeBeforeForkAt log i s = log := by
  induction log generalizing s with
  | nil => simp
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      by_cases ht : t = i
      · subst ht
        cases s with
        | zero => simp at h
        | succ s => rw [takeBeforeForkAt_cons_self_succ, ih s (by simp_all)]
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ ht, ih s (by simp_all)]

end QueryLog

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

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
def replayOracle [spec.DecidableEq] (i : ι) :
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
  (simulateQ spec.loggingOracle main).run

@[simp]
lemma fst_map_replayFirstRun (main : OracleComp spec α) :
    Prod.fst <$> replayFirstRun main = main := by
  simpa [replayFirstRun, OracleComp.withQueryLog, loggingOracle] using
    (loggingOracle.fst_map_run_simulateQ (spec := spec) main)

@[simp]
lemma probEvent_fst_replayFirstRun [IsUniformSpec spec]
    (main : OracleComp spec α) (p : α → Prop) :
    Pr[ fun z => p z.1 | replayFirstRun main] = Pr[ p | main] := by
  simp [replayFirstRun]

@[simp]
lemma probOutput_fst_map_replayFirstRun [IsUniformSpec spec]
    (main : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> replayFirstRun main] = Pr[= x | main] := by
  simp [replayFirstRun]

/-- Replay the second run against a fixed first-run log, fork point, and
replacement answer, returning both the final output and replay state. -/
def replayRunWithTraceValue [spec.DecidableEq] (main : OracleComp spec α) (i : ι)
    (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    OracleComp spec (α × ReplayForkState spec i) := do
  let init := ReplayForkState.init trace forkQuery replacement
  (simulateQ (replayOracle i) main).run init

/-- Deterministic replay-fork core with the first-run output and transcript fixed.

This mirrors `seededForkWithSeedValue`: the first-run result and replacement answer are
inputs, while the second run may still make live oracle calls after the fork
point. -/
def forkReplayWithTraceValue [spec.DecidableEq] (main : OracleComp spec α)
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
def forkReplay [spec.DecidableEq] (main : OracleComp spec α)
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
    [spec.DecidableEq]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (first : α × QueryLog spec) (u : spec.Range i)
    (h : cf first.1 = none) :
    forkReplayWithTraceValue main qb i cf first u = pure none := by
  simp [forkReplayWithTraceValue, h]

/-!
### Live-mode α-marginal

Once the replay oracle has transitioned into "live mode" (either `forkConsumed = true`
after the fork fired, or `mismatch = true` after a trace mismatch or exhaustion), every
subsequent query simply falls through to the ambient `query t` and records the answer in
`observed`. In particular, the α-component of the simulated computation coincides with
`main` itself: the state only records observations and does not influence the output.

These lemmas are used in the B1 faithfulness proofs (`evalDist_uniform_bind_fst_replay
RunWithTraceValue_takeBeforeForkAt` and `tsum_probOutput_replayFirstRun_weight_take
BeforeForkAt`): after the fork point on either side (full log vs. truncated log), both
computations enter live mode, and the α-marginal collapses to `evalDist main`.
-/

/-- Live mode is preserved by `noteObserved`: neither `forkConsumed` nor `mismatch` is
touched by recording an observation. -/
lemma ReplayForkState.noteObserved_live_iff {i : ι}
    (st : ReplayForkState spec i) (t : ι) (u : spec.Range t) :
    (st.noteObserved t u).forkConsumed = st.forkConsumed ∧
      (st.noteObserved t u).mismatch = st.mismatch := by
  simp [ReplayForkState.noteObserved]

/-- **Live-mode α-marginal.** Starting from a replay state in live mode
(`forkConsumed = true` or `mismatch = true`), the α-component of running the replay
oracle on `main` equals `main` itself. The state only accumulates observations; it has
no effect on the α-distribution. -/
lemma fst_map_simulateQ_replayOracle_of_live [spec.DecidableEq]
    (i : ι) (main : OracleComp spec α) :
    ∀ (st : ReplayForkState spec i), (st.forkConsumed = true ∨ st.mismatch = true) →
      (Prod.fst <$> (simulateQ (replayOracle i) main).run st : OracleComp spec α) = main := by
  induction main using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    intro st hst
    have hlive : (st.forkConsumed || st.mismatch) = true := by simp [hst]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    have hstep : (replayOracle (spec := spec) i t).run st =
        (do
          let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
          pure (u, st.noteObserved t u)) := by
      unfold replayOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hlive, if_true,
        bind_pure_comp, StateT.run_monadLift, monadLift_eq_self, StateT.run_map,
        StateT.run_set, map_pure]
      rfl
    rw [hstep]
    simp only [bind_pure_comp, map_bind, monadLift_eq_self, bind_map_left]
    exact bind_congr fun u =>
      ih u (st.noteObserved t u) (by simpa [ReplayForkState.noteObserved] using hst)

/-- α-marginal form of `fst_map_simulateQ_replayOracle_of_live`, specialized to the
`evalDist` level. Once in live mode, the α-output distribution of the replay run is
`evalDist main`. -/
lemma evalDist_fst_map_simulateQ_replayOracle_of_live [spec.DecidableEq] [IsUniformSpec spec]
    (i : ι) (main : OracleComp spec α) (st : ReplayForkState spec i)
    (hst : st.forkConsumed = true ∨ st.mismatch = true) :
    𝒟[(Prod.fst <$> (simulateQ (replayOracle i) main).run st : OracleComp spec α)] = 𝒟[main] :=
  congrArg evalDist (fst_map_simulateQ_replayOracle_of_live i main st hst)

section support

/-- Prefix-style replay invariant: the consumed prefix of `observed` matches the consumed prefix of
`trace` at the level of query inputs, and if the fork has not fired yet then `observed` has no
extra suffix beyond that prefix.

The `values` clause additionally pins down values on the non-fork positions: for every position
`n` strictly before the fork (or every position `< cursor` when the fork has not yet fired),
`observed[n]? = trace[n]?`, i.e., both the input oracle and the stored response agree. At the
fork position itself the value in `observed` is the replacement, so only the input agrees.

The `distinguishedCount_eq` and `fork_position` clauses pin down the position of the fork entry
in the filtered `i`-log: while pre-fork with no mismatch, `distinguishedCount` counts the number
of `i`-type entries in `observed`; once the fork has fired, the entry at position `cursor - 1`
in `observed` is exactly the `forkQuery`-th (0-indexed) `i`-type entry, i.e., the prefix
`observed.take (cursor - 1)` contains exactly `forkQuery` entries of type `i`. -/
def ReplayPrefixInvariant [spec.DecidableEq] (i : ι) (st : ReplayForkState spec i) : Prop :=
  st.cursor ≤ st.trace.length ∧
  st.cursor ≤ st.observed.length ∧
  (∀ n, n < st.cursor →
    QueryLog.inputAt? st.observed n = QueryLog.inputAt? st.trace n) ∧
  (st.forkConsumed = false → st.mismatch = false → st.observed.length = st.cursor) ∧
  (st.forkConsumed = true →
    0 < st.cursor ∧ QueryLog.inputAt? st.trace (st.cursor - 1) = some i) ∧
  (∀ n, n < (if st.forkConsumed then st.cursor - 1 else st.cursor) →
    st.observed[n]? = st.trace[n]?) ∧
  (st.forkConsumed = false → st.mismatch = false →
    st.distinguishedCount = (st.observed.getQ (· = i)).length) ∧
  (st.forkConsumed = true →
    (QueryLog.getQ (st.observed.take (st.cursor - 1)) (· = i)).length = st.forkQuery)

namespace ReplayPrefixInvariant

variable [spec.DecidableEq] {i : ι}

lemma init (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    ReplayPrefixInvariant i (ReplayForkState.init trace forkQuery replacement) := by
  refine ⟨by simp [ReplayForkState.init], by simp [ReplayForkState.init], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (Nat.not_lt_zero n hn).elim
  · intro hfork hmismatch
    simp [ReplayForkState.init]
  · intro hfork
    simp [ReplayForkState.init] at hfork
  · intro n hn
    simp [ReplayForkState.init] at hn
  · intro _ _
    simp [ReplayForkState.init, QueryLog.getQ]
  · intro hfork
    simp [ReplayForkState.init] at hfork

end ReplayPrefixInvariant

private lemma replayOracle_preservesPrefixInvariant_markMismatch_aux [spec.DecidableEq]
    (i t : ι) {st : ReplayForkState spec i} (u : spec.Range t)
    (hcursorTrace : st.cursor ≤ st.trace.length) (hcursorObs : st.cursor ≤ st.observed.length)
    (hprefix : ∀ n, n < st.cursor →
      QueryLog.inputAt? st.observed n = QueryLog.inputAt? st.trace n)
    (hvalues : ∀ n, n < (if st.forkConsumed then st.cursor - 1 else st.cursor) →
      st.observed[n]? = st.trace[n]?)
    (hflags : st.forkConsumed = false ∧ st.mismatch = false) :
    ReplayPrefixInvariant i (st.markMismatch.noteObserved t u) := by
  refine ⟨hcursorTrace, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch,
      QueryLog.logQuery, QueryLog.singleton] using
        (Nat.le_trans hcursorObs (Nat.le_succ st.observed.length))
  · intro n hn
    have hnobs : n < st.observed.length := lt_of_lt_of_le hn hcursorObs
    calc
      QueryLog.inputAt? (st.markMismatch.noteObserved t u).observed n
        = QueryLog.inputAt? st.observed n := by
            simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using
              (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := t) (u := u)
                (n := n) hnobs)
      _ = QueryLog.inputAt? st.trace n := hprefix n hn
  · intro _ hm
    simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch] at hm
  · intro hfc
    have hfc' : st.forkConsumed = true := by
      simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using hfc
    simp [hflags.1] at hfc'
  · intro n hn
    have hn' : n < st.cursor := by
      simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch, hflags.1] using hn
    have hnobs : n < st.observed.length := Nat.lt_of_lt_of_le hn' hcursorObs
    change (st.observed.logQuery t u)[n]? = st.trace[n]?
    rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
    exact hvalues n (by rw [hflags.1]; simpa using hn')
  · intro _ hm
    simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch] at hm
  · intro hfc
    have hfc' : st.forkConsumed = true := by
      simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using hfc
    simp [hflags.1] at hfc'

/-- Per-query preservation of the replay prefix invariant: a single
`replayOracle i t` step starting from any state satisfying
`ReplayPrefixInvariant` produces a state still satisfying it.

Made `protected` (formerly `private`) so the `Std.Do.Triple` bridge in
`VCVio/CryptoFoundations/ReplayForkStdDo.lean` can lift this to a per-query
spec consumable by `mvcgen`. -/
protected lemma replayOracle_preservesPrefixInvariant [spec.DecidableEq]
    (i t : ι) {st : ReplayForkState spec i}
    {z : spec.Range t × ReplayForkState spec i}
    (hInv : ReplayPrefixInvariant i st)
    (hz : z ∈ support ((replayOracle i t).run st)) :
    ReplayPrefixInvariant i z.2 := by
  rcases hInv with ⟨hcursorTrace, hcursorObs, hprefix, hlen, hforked, hvalues, hdcount, hforkpos⟩
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hlive : st.forkConsumed || st.mismatch
  · simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
      monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
      support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
      Set.image_univ, Set.mem_range] at hz
    rcases hz with ⟨u, hu, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hcursorTrace
    · exact Nat.le_trans hcursorObs <|
        by simp [ReplayForkState.noteObserved, QueryLog.logQuery, QueryLog.singleton]
    · intro n hn
      have hnobs : n < st.observed.length := lt_of_lt_of_le hn hcursorObs
      calc
        QueryLog.inputAt? (st.noteObserved t u).observed n
          = QueryLog.inputAt? st.observed n := by
              simpa [ReplayForkState.noteObserved] using
                (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := t) (u := u) (n := n)
                  hnobs)
        _ = QueryLog.inputAt? st.trace n := hprefix n hn
    · intro hfc hm
      simp only [ReplayForkState.noteObserved] at hfc hm
      simp [hfc, hm] at hlive
    · intro hfc
      simpa [ReplayForkState.noteObserved] using hforked hfc
    · intro n hn
      have hn' : n < (if st.forkConsumed then st.cursor - 1 else st.cursor) := by
        simpa [ReplayForkState.noteObserved] using hn
      have hn_cur : n < st.cursor := by
        split_ifs at hn' with hfc
        · exact Nat.lt_of_lt_of_le hn' (Nat.sub_le _ _)
        · exact hn'
      have hnobs : n < st.observed.length := Nat.lt_of_lt_of_le hn_cur hcursorObs
      change (st.observed.logQuery t u)[n]? = st.trace[n]?
      rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
      exact hvalues n hn'
    · intro hfc hm
      simp only [ReplayForkState.noteObserved] at hfc hm
      simp [hfc, hm] at hlive
    · intro hfc
      have hfc' : st.forkConsumed = true := by
        simpa [ReplayForkState.noteObserved] using hfc
      have hsub : st.cursor - 1 ≤ st.observed.length :=
        Nat.le_trans (Nat.sub_le _ _) hcursorObs
      change (QueryLog.getQ
        ((st.observed.logQuery t u).take (st.cursor - 1)) (· = i)).length = st.forkQuery
      rw [QueryLog.logQuery, QueryLog.singleton, List.take_append_of_le_length hsub]
      simpa using hforkpos hfc'
  · simp only [hlive, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, dite_eq_ite] at hz
    cases hnext : st.nextEntry? with
    | none =>
        simp only [hnext, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
            bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
            Set.range_id, Set.image_univ, Set.mem_range] at hz
        rcases hz with ⟨u, hu, rfl⟩
        have hflags : st.forkConsumed = false ∧ st.mismatch = false := by
          cases hfc0 : st.forkConsumed <;> cases hm0 : st.mismatch
          · constructor <;> simp
          · simp [hfc0, hm0] at hlive
          · simp [hfc0, hm0] at hlive
          · simp [hfc0, hm0] at hlive
        exact replayOracle_preservesPrefixInvariant_markMismatch_aux i t u hcursorTrace
          hcursorObs hprefix hvalues hflags
    | some entry =>
        rcases entry with ⟨t', u'⟩
        have hflags : st.forkConsumed = false ∧ st.mismatch = false := by
          cases hfc0 : st.forkConsumed <;> cases hm0 : st.mismatch
          · constructor
            · rfl
            · rfl
          · simp [hfc0, hm0] at hlive
          · simp [hfc0, hm0] at hlive
          · simp [hfc0, hm0] at hlive
        have hObsEq : st.observed.length = st.cursor := hlen hflags.1 hflags.2
        by_cases hsame : t = t'
        · cases hsame
          by_cases hti : t = i
          · cases hti
            by_cases hfork : st.distinguishedCount = st.forkQuery
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              have hlt : st.cursor < st.trace.length := by
                have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                  simpa [ReplayForkState.nextEntry?] using hnext
                exact (List.getElem?_eq_some_iff).1 hsome |>.1
              refine ⟨Nat.succ_le_of_lt hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp [QueryLog.logQuery, QueryLog.singleton, hObsEq]
              · intro n hn
                by_cases hEq : n = st.cursor
                · subst hEq
                  have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                    simpa [ReplayForkState.nextEntry?] using hnext
                  have htrace : QueryLog.inputAt? st.trace st.cursor = some i := by
                    simp [QueryLog.inputAt?, hsome]
                  calc
                    QueryLog.inputAt?
                        { st with
                          cursor := st.cursor + 1
                          distinguishedCount := st.distinguishedCount + 1
                          forkConsumed := true
                          observed := st.observed.logQuery i st.replacement }.observed st.cursor
                      = some i := by
                          simpa [hObsEq] using
                            (QueryLog.inputAt?_logQuery_self (log := st.observed)
                              (t := i) (u := st.replacement))
                    _ = QueryLog.inputAt? st.trace st.cursor := by simpa using htrace.symm
                · have hn' : n < st.cursor := by
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn' | hn'
                    · exact hn'
                    · exact (hEq hn').elim
                  have hnobs : n < st.observed.length := by simpa [hObsEq] using hn'
                  calc
                    QueryLog.inputAt?
                        { st with
                          cursor := st.cursor + 1
                          distinguishedCount := st.distinguishedCount + 1
                          forkConsumed := true
                          observed := st.observed.logQuery i st.replacement }.observed n
                      = QueryLog.inputAt? st.observed n := by
                          simpa using
                            (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := i)
                              (u := st.replacement) (n := n) hnobs)
                    _ = QueryLog.inputAt? st.trace n := hprefix n hn'
              · intro hfc hm
                simp at hfc
              · intro hfc
                constructor
                · simp
                · have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                    simpa [ReplayForkState.nextEntry?] using hnext
                  simp [QueryLog.inputAt?, hsome]
              · intro n hn
                have hn' : n < st.cursor := by
                  simpa [Nat.add_sub_cancel] using hn
                have hnobs : n < st.observed.length := by simpa [hObsEq] using hn'
                change (st.observed.logQuery i st.replacement)[n]? = st.trace[n]?
                rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
                exact hvalues n (by rw [hflags.1]; simpa using hn')
              · intro hfc hm
                simp at hfc
              · intro _
                have hdc_old : st.distinguishedCount =
                    (st.observed.getQ (· = i)).length := hdcount hflags.1 hflags.2
                have hdc_fq : st.distinguishedCount = st.forkQuery := hfork
                change (QueryLog.getQ ((st.observed.logQuery i st.replacement).take
                    (st.cursor + 1 - 1)) (· = i)).length = st.forkQuery
                simp only [Nat.add_sub_cancel]
                rw [QueryLog.logQuery, QueryLog.singleton,
                  show st.cursor = st.observed.length from hObsEq.symm, List.take_left]
                exact hdc_old.symm.trans hdc_fq
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              have hlt : st.cursor < st.trace.length := by
                have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                  simpa [ReplayForkState.nextEntry?] using hnext
                exact (List.getElem?_eq_some_iff).1 hsome |>.1
              refine ⟨Nat.succ_le_of_lt hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp [QueryLog.logQuery, QueryLog.singleton, hObsEq]
              · intro n hn
                by_cases hEq : n = st.cursor
                · subst hEq
                  have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                    simpa [ReplayForkState.nextEntry?] using hnext
                  simp [QueryLog.inputAt?, QueryLog.logQuery, QueryLog.singleton, hObsEq, hsome]
                · have hn' : n < st.cursor := by
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn' | hn'
                    · exact hn'
                    · exact (hEq hn').elim
                  have hnobs : n < st.observed.length := by simpa [hObsEq] using hn'
                  calc
                    QueryLog.inputAt?
                        { st with
                          cursor := st.cursor + 1
                          distinguishedCount := st.distinguishedCount + 1
                          observed := st.observed.logQuery i u' }.observed n
                      = QueryLog.inputAt? st.observed n := by
                          simpa using
                            (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := i)
                              (u := u') (n := n) hnobs)
                    _ = QueryLog.inputAt? st.trace n := hprefix n hn'
              · intro hfc hm
                simp [hflags.1, hflags.2, QueryLog.logQuery, QueryLog.singleton, hObsEq] at hfc hm ⊢
              · intro hfc
                simp [hflags.1] at hfc
              · intro n hn
                have hn' : n < st.cursor + 1 := by
                  simpa [hflags.1] using hn
                change (st.observed.logQuery i u')[n]? = st.trace[n]?
                by_cases hEq : n = st.cursor
                · subst hEq
                  have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                    simpa [ReplayForkState.nextEntry?] using hnext
                  rw [QueryLog.logQuery, QueryLog.singleton,
                    List.getElem?_append_right (by simp [hObsEq])]
                  simp [hObsEq, hsome]
                · have hn'' : n < st.cursor := by
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hn' with hn'' | hn''
                    · exact hn''
                    · exact (hEq hn'').elim
                  have hnobs : n < st.observed.length := by simpa [hObsEq] using hn''
                  rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
                  exact hvalues n (by rw [hflags.1]; simpa using hn'')
              · intro _ _
                have hdc_old := hdcount hflags.1 hflags.2
                change st.distinguishedCount + 1 =
                    ((st.observed.logQuery i u').getQ (· = i)).length
                rw [QueryLog.getQ_logQuery]
                simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil,
                  zero_add, Nat.add_right_cancel_iff]
                exact hdc_old
              · intro hfc
                simp [hflags.1] at hfc
          · simp only [hnext, ↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure,
              support_pure, Set.mem_singleton_iff] at hz
            rcases hz with rfl
            have hlt : st.cursor < st.trace.length := by
              have hsome : st.trace[st.cursor]? = some ⟨t, u'⟩ := by
                simpa [ReplayForkState.nextEntry?] using hnext
              exact (List.getElem?_eq_some_iff).1 hsome |>.1
            refine ⟨Nat.succ_le_of_lt hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [QueryLog.logQuery, QueryLog.singleton, hObsEq]
            · intro n hn
              by_cases hEq : n = st.cursor
              · subst hEq
                have hsome : st.trace[st.cursor]? = some ⟨t, u'⟩ := by
                  simpa [ReplayForkState.nextEntry?] using hnext
                simp [QueryLog.inputAt?, QueryLog.logQuery, QueryLog.singleton, hObsEq, hsome]
              · have hn' : n < st.cursor := by
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn' | hn'
                  · exact hn'
                  · exact (hEq hn').elim
                have hnobs : n < st.observed.length := by simpa [hObsEq] using hn'
                calc
                  QueryLog.inputAt?
                      { st with
                        cursor := st.cursor + 1,
                        observed := st.observed.logQuery t u' }.observed n
                    = QueryLog.inputAt? st.observed n := by
                        simpa using
                          (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := t)
                            (u := u') (n := n) hnobs)
                  _ = QueryLog.inputAt? st.trace n := hprefix n hn'
            · intro hfc hm
              simp [hflags.1, hflags.2, QueryLog.logQuery, QueryLog.singleton, hObsEq] at hfc hm ⊢
            · intro hfc
              simp [hflags.1] at hfc
            · intro n hn
              have hn' : n < st.cursor + 1 := by
                simpa [hflags.1] using hn
              change (st.observed.logQuery t u')[n]? = st.trace[n]?
              by_cases hEq : n = st.cursor
              · subst hEq
                have hsome : st.trace[st.cursor]? = some ⟨t, u'⟩ := by
                  simpa [ReplayForkState.nextEntry?] using hnext
                rw [QueryLog.logQuery, QueryLog.singleton,
                  List.getElem?_append_right (by simp [hObsEq])]
                simp [hObsEq, hsome]
              · have hn'' : n < st.cursor := by
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hn' with hn'' | hn''
                  · exact hn''
                  · exact (hEq hn'').elim
                have hnobs : n < st.observed.length := by simpa [hObsEq] using hn''
                rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
                exact hvalues n (by rw [hflags.1]; simpa using hn'')
            · intro _ _
              have hdc_old := hdcount hflags.1 hflags.2
              change st.distinguishedCount = ((st.observed.logQuery t u').getQ (· = i)).length
              rw [QueryLog.getQ_logQuery, if_neg hti]
              simpa using hdc_old
            · intro hfc
              simp [hflags.1] at hfc
        · simp only [hnext, hsame, ↓reduceDIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
            Functor.map_map, support_map, support_liftM, OracleQuery.input_query,
            OracleQuery.cont_query, Set.range_id, Set.image_univ, Set.mem_range] at hz
          rcases hz with ⟨u, hu, rfl⟩
          exact replayOracle_preservesPrefixInvariant_markMismatch_aux i t u hcursorTrace
            hcursorObs hprefix hvalues hflags

/-- Every reachable replay state preserves the logged query-input prefix up to `cursor`. -/
theorem replayRunWithTraceValue_preservesPrefixInvariant [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    ReplayPrefixInvariant i z.2 := by
  unfold replayRunWithTraceValue at hz
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := replayOracle i)
    (inv := ReplayPrefixInvariant i)
    (hinv := fun t _ hs _ hy ↦
      OracleComp.replayOracle_preservesPrefixInvariant (i := i) (t := t) hs hy)
    main (ReplayForkState.init trace forkQuery replacement)
    (ReplayPrefixInvariant.init (i := i) trace forkQuery replacement) z hz

/-- Support-level replay-prefix lemma: before `cursor`, the second run queries the same oracle
inputs as the logged first-run transcript. -/
lemma replayRunWithTraceValue_prefix_input_eq [IsUniformSpec spec] [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    {n : Nat} (hn : n < z.2.cursor) :
    QueryLog.inputAt? z.2.observed n = QueryLog.inputAt? z.2.trace n :=
  (replayRunWithTraceValue_preservesPrefixInvariant _ _ _ _ _ hz).2.2.1 n hn

/-- Support-level value-agreement lemma: before the effective fork position (i.e., before
`cursor - 1` once the fork has fired, or before `cursor` while it has not), the second-run
`observed` log agrees with the first-run `trace` log on both the query input and the stored
response. This strengthens `replayRunWithTraceValue_prefix_input_eq` and is the key lemma
for arguing that the adversary's query transcript prior to the fork is identical across
the two runs. -/
lemma replayRunWithTraceValue_prefix_getElem?_eq [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    {n : Nat}
    (hn : n < (if z.2.forkConsumed then z.2.cursor - 1 else z.2.cursor)) :
    z.2.observed[n]? = z.2.trace[n]? :=
  (replayRunWithTraceValue_preservesPrefixInvariant _ _ _ _ _ hz).2.2.2.2.2.1 n hn

/-- Extract the "fork-position count" invariant: once the fork has fired, the prefix of `observed`
up to the fork position contains exactly `st.forkQuery` entries of type `i`. This pins down where
the replacement entry sits in the filtered `i`-log. -/
lemma replayRunWithTraceValue_forkConsumed_imp_prefix_count [IsUniformSpec spec] [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    (hfork : z.2.forkConsumed = true) :
    (QueryLog.getQ (z.2.observed.take (z.2.cursor - 1)) (· = i)).length = z.2.forkQuery :=
  (replayRunWithTraceValue_preservesPrefixInvariant _ _ _ _ _ hz).2.2.2.2.2.2.2 hfork

/-- If replay has consumed the fork point, the last consumed log entry is the distinguished query
input `i`. This is the pathwise "same target" fact used downstream. -/
lemma replayRunWithTraceValue_forkConsumed_imp_last_input [IsUniformSpec spec] [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    (hfork : z.2.forkConsumed = true) :
    0 < z.2.cursor ∧
      QueryLog.inputAt? z.2.trace (z.2.cursor - 1) = some i ∧
      QueryLog.inputAt? z.2.observed (z.2.cursor - 1) = some i := by
  obtain ⟨hpos, htrace⟩ := (replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz).2.2.2.2.1 hfork
  exact ⟨hpos, htrace, (replayRunWithTraceValue_prefix_input_eq
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz (n := z.2.cursor - 1) (by lia)).trans htrace⟩

/-- The replay oracle never mutates the immutable parameters `forkQuery`, `replacement`,
or `trace`.

Made `protected` (formerly `private`) so the `Std.Do.Triple` bridge in
`VCVio/CryptoFoundations/ReplayForkStdDo.lean` can lift this to a per-query
spec consumable by `mvcgen`. -/
protected lemma replayOracle_immutable_params [spec.DecidableEq]
    (i : ι) (t : ι) {st : ReplayForkState spec i}
    {z : spec.Range t × ReplayForkState spec i}
    (hz : z ∈ support (((replayOracle i) t).run st :
      OracleComp spec (spec.Range t × ReplayForkState spec i))) :
    z.2.forkQuery = st.forkQuery ∧ z.2.replacement = st.replacement ∧
      z.2.trace = st.trace := by
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hlive : st.forkConsumed || st.mismatch
  · simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
        monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
        support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
        Set.range_id, Set.image_univ, Set.mem_range] at hz
    rcases hz with ⟨u, _, rfl⟩
    simp [ReplayForkState.noteObserved]
  · simp only [hlive, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, dite_eq_ite] at hz
    cases hnext : st.nextEntry? with
    | none =>
        simp only [hnext, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
            bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
            Set.range_id, Set.image_univ, Set.mem_range] at hz
        rcases hz with ⟨u, _, rfl⟩
        simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]
    | some entry =>
        rcases entry with ⟨t', u'⟩
        by_cases hsame : t = t'
        · cases hsame
          by_cases hti : t = i
          · cases hti
            by_cases hfork : st.distinguishedCount = st.forkQuery <;>
              · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                  map_pure, support_pure, Set.mem_singleton_iff] at hz
                rcases hz with rfl
                exact ⟨rfl, rfl, rfl⟩
          · simp only [hnext, ↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure,
                support_pure, Set.mem_singleton_iff] at hz
            rcases hz with rfl
            exact ⟨rfl, rfl, rfl⟩
        · simp only [hnext, hsame, ↓reduceDIte, StateT.run_bind, StateT.run_monadLift,
              monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
              Functor.map_map, support_map, support_liftM, OracleQuery.input_query,
              OracleQuery.cont_query, Set.range_id, Set.image_univ, Set.mem_range] at hz
          rcases hz with ⟨u, _, rfl⟩
          simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]

private lemma replayRunWithTraceValue_immutable_params [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.forkQuery = forkQuery ∧ z.2.replacement = replacement ∧ z.2.trace = trace := by
  unfold replayRunWithTraceValue at hz
  let stInit : ReplayForkState spec i := ReplayForkState.init trace forkQuery replacement
  have hparams :
      z.2.forkQuery = stInit.forkQuery ∧ z.2.replacement = stInit.replacement ∧
        z.2.trace = stInit.trace :=
    OracleComp.simulateQ_run_preserves_inv_of_query (impl := replayOracle i)
      (inv := fun st ↦ st.forkQuery = stInit.forkQuery ∧
        st.replacement = stInit.replacement ∧ st.trace = stInit.trace)
      (hinv := fun t _ hs _ hy ↦
        have hstep := OracleComp.replayOracle_immutable_params (i := i) (t := t) hy
        ⟨hstep.1.trans hs.1, hstep.2.1.trans hs.2.1, hstep.2.2.trans hs.2.2⟩)
      main stInit ⟨rfl, rfl, rfl⟩ z (by simpa [stInit] using hz)
  simpa [ReplayForkState.init] using hparams

/-- Every reachable replay state keeps the immutable `forkQuery` parameter equal to its
initial value. -/
lemma replayRunWithTraceValue_forkQuery_eq [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.forkQuery = forkQuery :=
  (replayRunWithTraceValue_immutable_params main i trace forkQuery replacement hz).1

/-- Every reachable replay state keeps the immutable `replacement` parameter equal to its
initial value. -/
lemma replayRunWithTraceValue_replacement_eq [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.replacement = replacement :=
  (replayRunWithTraceValue_immutable_params main i trace forkQuery replacement hz).2.1

/-- Every reachable replay state keeps the immutable `trace` parameter equal to its
initial value. -/
lemma replayRunWithTraceValue_trace_eq [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.trace = trace :=
  (replayRunWithTraceValue_immutable_params main i trace forkQuery replacement hz).2.2

/-- Second replay invariant: once the fork has fired, the `forkQuery`-th entry among
distinguished-oracle queries in the observed log is exactly the replacement value.

Before the fork fires and before any mismatch, `distinguishedCount` exactly tracks the number
of `i`-entries in `observed`. Once the fork fires, position `forkQuery` in the `i`-filtered
observed log is permanently pinned to `replacement`. -/
def ReplayReplacementInvariant [spec.DecidableEq] (i : ι) (st : ReplayForkState spec i) :
    Prop :=
  (st.forkConsumed = false → st.mismatch = false →
    (st.observed.getQ (· = i)).length = st.distinguishedCount) ∧
  (st.forkConsumed = true →
    (st.observed.getQ (· = i))[st.forkQuery]?
      = some (⟨i, st.replacement⟩ : (t : ι) × spec.Range t))

namespace ReplayReplacementInvariant

variable [spec.DecidableEq] {i : ι}

lemma init (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    ReplayReplacementInvariant i
      (ReplayForkState.init trace forkQuery replacement) := by
  refine ⟨?_, ?_⟩
  · intro _ _
    simp [ReplayForkState.init]
  · intro hfork
    simp [ReplayForkState.init] at hfork

end ReplayReplacementInvariant

private lemma replayReplacementInvariant_markMismatch_noteObserved_aux [spec.DecidableEq]
    (i t : ι) (st : ReplayForkState spec i) (u : spec.Range t)
    (hfc : st.forkConsumed = false) :
    ReplayReplacementInvariant i (st.markMismatch.noteObserved t u) :=
  ⟨fun _ hm ↦ by simp [ReplayForkState.markMismatch, ReplayForkState.noteObserved] at hm,
    fun hfc' ↦ by
      simp [ReplayForkState.markMismatch, ReplayForkState.noteObserved, hfc] at hfc'⟩

/-- Per-query preservation of the replay replacement invariant.

Made `protected` (formerly `private`) so the `Std.Do.Triple` bridge in
`VCVio/CryptoFoundations/ReplayForkStdDo.lean` can lift this to a per-query
spec consumable by `mvcgen`. -/
protected lemma replayOracle_preservesReplacementInvariant [spec.DecidableEq]
    (i t : ι) {st : ReplayForkState spec i}
    (hInv : ReplayReplacementInvariant i st)
    {z : spec.Range t × ReplayForkState spec i}
    (hz : z ∈ support (((replayOracle i) t).run st :
      OracleComp spec (spec.Range t × ReplayForkState spec i))) :
    ReplayReplacementInvariant i z.2 := by
  obtain ⟨hPre, hPost⟩ := hInv
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hlive : st.forkConsumed || st.mismatch
  · simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
        monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
        support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
        Set.range_id, Set.image_univ, Set.mem_range] at hz
    rcases hz with ⟨u, _, rfl⟩
    dsimp only
    refine ⟨?_, ?_⟩
    · intro hfc hm
      simp only [ReplayForkState.noteObserved] at hfc hm
      rcases Bool.or_eq_true_iff.mp hlive with hfc' | hm'
      · exact (Bool.eq_false_iff.mp hfc hfc').elim
      · exact (Bool.eq_false_iff.mp hm hm').elim
    · intro hfc
      simp only [ReplayForkState.noteObserved] at hfc ⊢
      have hPostApp := hPost hfc
      rw [QueryLog.getQ_logQuery]
      by_cases ht : t = i
      · subst ht
        simp only [if_true]
        rw [List.getElem?_append_left]
        · exact hPostApp
        · have hlt : st.forkQuery < (st.observed.getQ (· = t)).length :=
            List.getElem?_eq_some_iff.mp hPostApp |>.1
          exact hlt
      · simp only [if_neg ht, List.append_nil]
        exact hPostApp
  · simp only [hlive, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, dite_eq_ite] at hz
    have hflags : st.forkConsumed = false ∧ st.mismatch = false :=
      Bool.or_eq_false_iff.mp (by simpa using hlive)
    cases hnext : st.nextEntry? with
    | none =>
        simp only [hnext, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
            bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
            Set.range_id, Set.image_univ, Set.mem_range] at hz
        rcases hz with ⟨u, _, rfl⟩
        exact replayReplacementInvariant_markMismatch_noteObserved_aux i t st u hflags.1
    | some entry =>
        rcases entry with ⟨t', u'⟩
        by_cases hsame : t = t'
        · cases hsame
          by_cases hti : t = i
          · cases hti
            by_cases hfork : st.distinguishedCount = st.forkQuery
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                  map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              dsimp only
              refine ⟨?_, ?_⟩
              · intro hfc' _
                simp at hfc'
              · intro _
                have hPreApp := hPre hflags.1 hflags.2
                rw [QueryLog.getQ_logQuery]
                simp only [if_true]
                rw [List.getElem?_append_right (by omega)]
                simp [hPreApp, hfork]
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                  map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              dsimp only
              refine ⟨?_, ?_⟩
              · intro _ _
                have hPreApp := hPre hflags.1 hflags.2
                rw [QueryLog.getQ_logQuery]
                simp only [if_true]
                simp [hPreApp]
              · intro hfc'
                simp [hflags.1] at hfc'
          · simp only [hnext, ↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure,
                support_pure, Set.mem_singleton_iff] at hz
            rcases hz with rfl
            dsimp only
            refine ⟨?_, ?_⟩
            · intro _ _
              have hPreApp := hPre hflags.1 hflags.2
              rw [QueryLog.getQ_logQuery]
              simp only [if_neg hti, List.append_nil]
              exact hPreApp
            · intro hfc'
              simp [hflags.1] at hfc'
        · simp only [hnext, hsame, ↓reduceDIte, StateT.run_bind, StateT.run_monadLift,
              monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
              Functor.map_map, support_map, support_liftM, OracleQuery.input_query,
              OracleQuery.cont_query, Set.range_id, Set.image_univ, Set.mem_range] at hz
          rcases hz with ⟨u, _, rfl⟩
          exact replayReplacementInvariant_markMismatch_noteObserved_aux i t st u hflags.1

/-- Every reachable replay state preserves the replacement invariant. -/
theorem replayRunWithTraceValue_preservesReplacementInvariant
    [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    ReplayReplacementInvariant i z.2 := by
  unfold replayRunWithTraceValue at hz
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := replayOracle i)
    (inv := ReplayReplacementInvariant i)
    (hinv := fun t _ hs _ hy ↦
      OracleComp.replayOracle_preservesReplacementInvariant (i := i) (t := t) hs hy)
    main (ReplayForkState.init trace forkQuery replacement)
    (ReplayReplacementInvariant.init (i := i) trace forkQuery replacement) z hz

/-- If the replay has consumed the fork and the fork point is `forkQuery`, then the
`forkQuery`-th distinguished-oracle entry in the observed log is exactly the replacement. -/
lemma replayRunWithTraceValue_getQueryValue?_observed_eq_replacement
    [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    (hfork : z.2.forkConsumed = true) :
    QueryLog.getQueryValue? z.2.observed i forkQuery = some replacement := by
  have hInv := replayRunWithTraceValue_preservesReplacementInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz
  have hfq : z.2.forkQuery = forkQuery :=
    replayRunWithTraceValue_forkQuery_eq (main := main) (i := i) (trace := trace)
      (forkQuery := forkQuery) (replacement := replacement) hz
  have hrep : z.2.replacement = replacement :=
    replayRunWithTraceValue_replacement_eq (main := main) (i := i) (trace := trace)
      (forkQuery := forkQuery) (replacement := replacement) hz
  exact QueryLog.getQueryValue?_eq_some_of_getQ_getElem? _ _ _ _ (hfq ▸ hrep ▸ hInv.2 hfork)

private lemma replayOracle_observed_eq_logQuery [spec.DecidableEq]
    (i : ι) (t : ι) {st : ReplayForkState spec i}
    {z : spec.Range t × ReplayForkState spec i}
    (hz : z ∈ support (((replayOracle i) t).run st :
      OracleComp spec (spec.Range t × ReplayForkState spec i))) :
    z.2.observed = st.observed.logQuery t z.1 := by
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hlive : st.forkConsumed || st.mismatch
  · simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
      monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
      support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
      Set.image_univ, Set.mem_range] at hz
    rcases hz with ⟨u, _, rfl⟩
    simp [ReplayForkState.noteObserved]
  · simp only [hlive, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, dite_eq_ite] at hz
    cases hnext : st.nextEntry? with
    | none =>
        simp only [hnext, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
            bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
            Set.range_id, Set.image_univ, Set.mem_range] at hz
        rcases hz with ⟨u, _, rfl⟩
        simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]
    | some entry =>
        rcases entry with ⟨t', u'⟩
        by_cases hsame : t = t'
        · cases hsame
          by_cases hti : t = i
          · cases hti
            by_cases hfork : st.distinguishedCount = st.forkQuery <;>
              · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                  map_pure, support_pure, Set.mem_singleton_iff] at hz
                rcases hz with rfl
                rfl
          · simp only [hnext, ↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure,
              support_pure, Set.mem_singleton_iff] at hz
            rcases hz with rfl
            rfl
        · simp only [hnext, hsame, ↓reduceDIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
            Functor.map_map, support_map, support_liftM, OracleQuery.input_query,
            OracleQuery.cont_query, Set.range_id, Set.image_univ, Set.mem_range] at hz
          rcases hz with ⟨u, _, rfl⟩
          simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]

private theorem replayRun_mem_support_replayFirstRun_append [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) {st₀ : ReplayForkState spec i}
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (((simulateQ (replayOracle i) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec i))) :
    ∃ log, (z.1, log) ∈ support (replayFirstRun main) ∧ z.2.observed = st₀.observed ++ log := by
  induction main using OracleComp.inductionOn generalizing st₀ z with
  | pure x => refine ⟨[], ?_, ?_⟩ <;> simp_all [replayFirstRun]
  | query_bind t oa ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨us, hus, hzcont⟩ := hz
      rcases ih (u := us.1) (st₀ := us.2) (z := z) hzcont with ⟨log, hlog, hobs⟩
      refine ⟨⟨t, us.1⟩ :: log, ?_, ?_⟩
      · rw [replayFirstRun, OracleComp.run_simulateQ_loggingOracle_query_bind]
        simpa [replayFirstRun] using hlog
      · rw [hobs, replayOracle_observed_eq_logQuery (i := i) (t := t)
          (by simpa [simulateQ_query, OracleSpec.query_def] using hus)]
        simp [QueryLog.logQuery, QueryLog.singleton, List.append_assoc]

/-- Every replay run can be realized as a logged run with the same observed transcript. -/
theorem replayRunWithTraceValue_mem_support_replayFirstRun [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    (z.1, z.2.observed) ∈ support (replayFirstRun main) := by
  unfold replayRunWithTraceValue at hz
  rcases replayRun_mem_support_replayFirstRun_append
    (main := main) (i := i)
    (st₀ := ReplayForkState.init trace forkQuery replacement) hz with ⟨log, hlog, hobs⟩
  simpa [show z.2.observed = log by simpa [ReplayForkState.init] using hobs] using hlog

end support

section quantitative

variable [spec.DecidableEq]
variable [∀ i, SampleableType (spec.Range i)] [unifSpec ⊂ₒ spec]
variable [unifSpec ˡ⊂ₒ spec]

omit [∀ i, SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] in
private lemma replayOracle_step_isTotalQueryBound
    (i : ι) (t : ι) (st : ReplayForkState spec i) :
    IsTotalQueryBound (((replayOracle (spec := spec) i) t).run st) 1 := by
  classical
  have hquery : ∀ (upd : spec.Range t → ReplayForkState spec i),
      IsTotalQueryBound (liftM (spec.query t) >>= fun u =>
        (pure (u, upd u) : OracleComp spec (spec.Range t × ReplayForkState spec i))) 1 := by
    intro upd
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  unfold replayOracle
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hlive : st.forkConsumed || st.mismatch
  · simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
      monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map]
    exact hquery (fun u => st.noteObserved t u)
  · simp only [hlive, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, dite_eq_ite]
    cases hnext : st.nextEntry? with
    | none =>
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map]
        exact hquery (fun u => (st.markMismatch).noteObserved t u)
    | some entry =>
        rcases entry with ⟨t', u'⟩
        by_cases hsame : t = t'
        · cases hsame
          by_cases hti : t = i
          · cases hti
            by_cases hfork : st.distinguishedCount = st.forkQuery <;>
              · simp only [↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                  map_pure]
                exact trivial
          · simp only [↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure]
            exact trivial
        · simp only [↓reduceDIte, hsame, StateT.run_bind, StateT.run_monadLift,
            monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
            Functor.map_map]
          exact hquery (fun u => (st.markMismatch).noteObserved t u)

omit [∀ i, SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] in
private theorem isTotalQueryBound_replayRunWithTraceValue [IsUniformSpec spec]
    (main : OracleComp spec α) (n : ℕ)
    (hmain : IsTotalQueryBound main n)
    (i : ι) (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    IsTotalQueryBound (replayRunWithTraceValue main i trace forkQuery replacement) n := by
  unfold replayRunWithTraceValue
  exact IsTotalQueryBound.simulateQ_run_of_step (impl := replayOracle i) hmain
    (replayOracle_step_isTotalQueryBound i) _

omit [unifSpec ˡ⊂ₒ spec] in
private theorem cf_eq_of_mem_support_forkReplay
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) (x₁ x₂ : α)
    (h : some (x₁, x₂) ∈ support (forkReplay main qb i cf)) :
    ∃ s, cf x₁ = some s ∧ cf x₂ = some s := by
  simp only [forkReplay] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨first, -, h⟩ := h
  rcases hcf : cf first.1 with _ | s
  · simp_all
  · simp only [hcf] at h
    rw [mem_support_bind_iff] at h
    obtain ⟨u, -, h⟩ := h
    simp only [forkReplayWithTraceValue, hcf] at h
    rcases hq : QueryLog.getQueryValue? first.2 i ↑s with _ | logged
    · simp_all
    · simp only [hq] at h
      split_ifs at h with heq
      · simp_all
      · rw [mem_support_bind_iff] at h
        obtain ⟨z, -, h⟩ := h
        split_ifs at h with hbad hcf₂ <;> simp_all

omit [unifSpec ˡ⊂ₒ spec] in
private theorem probEvent_forkReplay_fst_eq_probEvent_pair [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) | forkReplay main qb i cf] =
      Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) |
        forkReplay main qb i cf] := by
  refine probEvent_ext ?_
  intro r hr
  rcases r with _ | ⟨x₁, x₂⟩
  · simp
  · rcases cf_eq_of_mem_support_forkReplay (main := main) (qb := qb) (i := i) (cf := cf)
      x₁ x₂ (by simpa using hr) with ⟨t, h₁, h₂⟩
    simp [h₁, h₂]

/-- Reachability hypothesis on the fork-index selector `cf`: whenever the first run
of `main` outputs `x` and the recorded log is `log`, every selected fork index
`s = cf x` actually corresponds to an `i`-query in `log` (i.e. the `s`-th `i`-query
exists in the log). This is needed for the replay forking lemma because, unlike
the seeded variant, `forkReplay`'s second run cannot fork at a position the first
run never reached. In FiatShamir-style applications `cf` extracts the index of a
recorded query, so this property holds by construction. -/
def CfReachable [spec.DecidableEq] (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : Prop :=
  ∀ {x : α} {log : QueryLog spec},
    (x, log) ∈ support (replayFirstRun main) →
    ∀ s : Fin (qb i + 1), cf x = some s →
      (QueryLog.getQueryValue? log i ↑s).isSome

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] in
private lemma replayOracle_preservesConsumed
    (i t : ι) {st : ReplayForkState spec i}
    (h_consumed : st.forkConsumed = true) (h_mismatch : st.mismatch = false)
    {z : spec.Range t × ReplayForkState spec i}
    (hz : z ∈ support ((replayOracle i t).run st)) :
    z.2.forkConsumed = true ∧ z.2.mismatch = false := by
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  have hlive : (st.forkConsumed || st.mismatch) = true := by simp [h_consumed]
  simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
    monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
    support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
    Set.range_id, Set.image_univ, Set.mem_range] at hz
  rcases hz with ⟨_, _, rfl⟩
  exact ⟨h_consumed, h_mismatch⟩

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] in
private theorem replayRun_preservesConsumed
    (main : OracleComp spec α) (idx : ι) {st₀ : ReplayForkState spec idx}
    (h_consumed : st₀.forkConsumed = true) (h_mismatch : st₀.mismatch = false)
    {z : α × ReplayForkState spec idx}
    (hz : z ∈ support (((simulateQ (replayOracle idx) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec idx))) :
    z.2.forkConsumed = true ∧ z.2.mismatch = false := by
  induction main using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
      exact ⟨h_consumed, h_mismatch⟩
  | query_bind t oa ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨us, hus, hzcont⟩ := hz
      have hus' : us ∈ support (((replayOracle idx) t).run st₀ :
          OracleComp spec (spec.Range t × ReplayForkState spec idx)) := by
        simpa [simulateQ_query, OracleSpec.query_def] using hus
      obtain ⟨h_consumed', h_mismatch'⟩ :=
        replayOracle_preservesConsumed (i := idx) (t := t) h_consumed h_mismatch hus'
      exact ih (u := us.1) (st₀ := us.2) h_consumed' h_mismatch' hzcont

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] in
private theorem replayRun_state_correct_aux
    (main : OracleComp spec α) (idx : ι) {st₀ : ReplayForkState spec idx}
    {x_first : α} {log_cont : QueryLog spec}
    (h_first : (x_first, log_cont) ∈ support (replayFirstRun main))
    (h_mismatch : st₀.mismatch = false)
    (h_obs_len : st₀.observed.length = st₀.cursor)
    (h_trace_drop : st₀.trace.drop st₀.cursor = log_cont)
    (h_forkConsumed : st₀.forkConsumed = false)
    (h_dlt : st₀.distinguishedCount ≤ st₀.forkQuery)
    (h_can_reach : st₀.forkQuery + 1 - st₀.distinguishedCount
      ≤ log_cont.countQ (· = idx))
    {z : α × ReplayForkState spec idx}
    (hz : z ∈ support (((simulateQ (replayOracle idx) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec idx))) :
    z.2.mismatch = false ∧ z.2.forkConsumed = true := by
  induction main using OracleComp.inductionOn generalizing st₀ x_first log_cont z with
  | pure x =>
      have hlog_nil : log_cont = [] := by
        simp only [replayFirstRun, simulateQ_pure, WriterT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h_first
        exact h_first.2
      subst hlog_nil
      simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil,
        Nat.le_zero] at h_can_reach
      lia
  | query_bind t oa ih =>
      rw [replayFirstRun, OracleComp.run_simulateQ_loggingOracle_query_bind,
        support_bind] at h_first
      simp only [Set.mem_iUnion, support_map, exists_prop] at h_first
      obtain ⟨u_first, _, p_first, hp_first, hp_eq⟩ := h_first
      obtain ⟨hx_eq, hlog_eq⟩ := Prod.mk.inj hp_eq
      set log_cont' := p_first.2
      have hlog_cont_eq : log_cont = ⟨t, u_first⟩ :: log_cont' := hlog_eq.symm
      have hp_first' : (p_first.1, log_cont') ∈ support (replayFirstRun (oa u_first)) :=
        hp_first
      have h_trace_drop' : st₀.trace.drop st₀.cursor = ⟨t, u_first⟩ :: log_cont' := by
        rw [h_trace_drop, hlog_cont_eq]
      have hcursor_lt : st₀.cursor < st₀.trace.length := by
        have hlen : (st₀.trace.drop st₀.cursor).length =
            st₀.trace.length - st₀.cursor := List.length_drop
        rw [h_trace_drop'] at hlen
        simp at hlen
        lia
      have h_next_entry : st₀.trace[st₀.cursor]? = some ⟨t, u_first⟩ := by
        have h0 : (st₀.trace.drop st₀.cursor)[0]? = some ⟨t, u_first⟩ := by
          rw [h_trace_drop']
          rfl
        rwa [List.getElem?_drop, Nat.add_zero] at h0
      have h_nextEntry_eq : st₀.nextEntry? = some ⟨t, u_first⟩ := h_next_entry
      have hdrop_succ : st₀.trace.drop (st₀.cursor + 1) = log_cont' := by
        have hd : st₀.trace.drop (st₀.cursor + 1) =
            (st₀.trace.drop st₀.cursor).drop 1 := by
          rw [List.drop_drop, Nat.add_comm]
        rw [hd, h_trace_drop']
        rfl
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hzcont⟩ := hz
      have hus' : us ∈ support (((replayOracle idx) t).run st₀ :
          OracleComp spec (spec.Range t × ReplayForkState spec idx)) := by
        simpa [simulateQ_query, OracleSpec.query_def] using hus
      unfold replayOracle at hus'
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus'
      have hlive_false : (st₀.forkConsumed || st₀.mismatch) = false := by
        simp [h_forkConsumed, h_mismatch]
      simp only [hlive_false, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        dite_eq_ite, h_nextEntry_eq, ↓reduceDIte] at hus'
      by_cases hti : t = idx
      · subst hti
        by_cases hfork : st₀.distinguishedCount = st₀.forkQuery
        · set st₁ : ReplayForkState spec t :=
            { st₀ with cursor := st₀.cursor + 1
                       distinguishedCount := st₀.forkQuery + 1
                       forkConsumed := true
                       observed := st₀.observed.logQuery t st₀.replacement } with hst₁
          have hus_eq : us = (st₀.replacement, st₁) := by
            simp only [hfork, ↓reduceDIte] at hus'
            simpa using hus'
          rw [hus_eq] at hzcont
          have h_consumed_new : st₁.forkConsumed = true := rfl
          have h_mismatch_new : st₁.mismatch = false := h_mismatch
          exact (replayRun_preservesConsumed (oa _) t (st₀ := st₁)
            h_consumed_new h_mismatch_new hzcont).symm
        · set st₁ : ReplayForkState spec t :=
            { st₀ with cursor := st₀.cursor + 1
                       distinguishedCount := st₀.distinguishedCount + 1
                       observed := st₀.observed.logQuery t u_first } with hst₁
          have hus_eq : us = (u_first, st₁) := by
            simp only [hfork, ↓reduceDIte] at hus'
            simpa using hus'
          rw [hus_eq] at hzcont
          have h_st₁_mismatch : st₁.mismatch = false := h_mismatch
          have h_st₁_obs_len : st₁.observed.length = st₁.cursor := by
            simp [st₁, QueryLog.logQuery, QueryLog.singleton, h_obs_len]
          have h_st₁_trace_drop : st₁.trace.drop st₁.cursor = log_cont' := hdrop_succ
          have h_st₁_forkConsumed : st₁.forkConsumed = false := h_forkConsumed
          have h_st₁_dlt : st₁.distinguishedCount ≤ st₁.forkQuery := by grind
          have hcount_cons :
              QueryLog.countQ (⟨t, u_first⟩ :: log_cont') (· = t) =
                log_cont'.countQ (· = t) + 1 := by
            simp [QueryLog.countQ, QueryLog.getQ_cons]
          have h_can_reach' : st₁.forkQuery + 1 - st₁.distinguishedCount
              ≤ log_cont'.countQ (· = t) := by
            rw [hlog_cont_eq, hcount_cons] at h_can_reach
            grind
          have hzcont' : z ∈ support (((simulateQ (replayOracle t) (oa u_first)).run st₁) :
              OracleComp spec (α × ReplayForkState spec t)) := by simpa using hzcont
          exact ih u_first hp_first' h_st₁_mismatch h_st₁_obs_len
            h_st₁_trace_drop h_st₁_forkConsumed h_st₁_dlt h_can_reach' hzcont'
      · set st₁ : ReplayForkState spec idx :=
          { st₀ with cursor := st₀.cursor + 1
                     observed := st₀.observed.logQuery t u_first } with hst₁
        have hus_eq : us = (u_first, st₁) := by
          simp only [hti, ↓reduceDIte] at hus'
          simpa using hus'
        rw [hus_eq] at hzcont
        have h_st₁_mismatch : st₁.mismatch = false := h_mismatch
        have h_st₁_obs_len : st₁.observed.length = st₁.cursor := by
          simp [st₁, QueryLog.logQuery, QueryLog.singleton, h_obs_len]
        have h_st₁_trace_drop : st₁.trace.drop st₁.cursor = log_cont' := hdrop_succ
        have h_st₁_forkConsumed : st₁.forkConsumed = false := h_forkConsumed
        have h_st₁_dlt : st₁.distinguishedCount ≤ st₁.forkQuery := h_dlt
        have hcount_cons :
            QueryLog.countQ (⟨t, u_first⟩ :: log_cont') (· = idx) =
              log_cont'.countQ (· = idx) := by
          simp [QueryLog.countQ, QueryLog.getQ_cons, hti]
        have h_can_reach' : st₁.forkQuery + 1 - st₁.distinguishedCount
            ≤ log_cont'.countQ (· = idx) := by
          rw [hlog_cont_eq, hcount_cons] at h_can_reach
          exact h_can_reach
        have hzcont' : z ∈ support (((simulateQ (replayOracle idx) (oa u_first)).run st₁) :
            OracleComp spec (α × ReplayForkState spec idx)) := by simpa using hzcont
        exact ih u_first hp_first' h_st₁_mismatch h_st₁_obs_len
          h_st₁_trace_drop h_st₁_forkConsumed h_st₁_dlt h_can_reach' hzcont'

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] in
/-- Replay correctness invariant: starting from a logged first run of `main` whose
log already records an `i`-query at position `↑s`, replaying `main` against that log
with substitution at the fork query always reaches the fork, so `forkConsumed = true`
and `mismatch = false` on every output state. -/
theorem replayRunWithTraceValue_state_correct
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    {x₁ : α} {log : QueryLog spec}
    (hlog : (x₁, log) ∈ support (replayFirstRun main))
    {s : Fin (qb i + 1)} (hcf : cf x₁ = some s)
    (hreach : CfReachable main qb i cf)
    (u : spec.Range i)
    {q : α × ReplayForkState spec i}
    (hq : q ∈ support (replayRunWithTraceValue main i log ↑s u)) :
    q.2.mismatch = false ∧ q.2.forkConsumed = true := by
  set st₀ := ReplayForkState.init log (forkQuery := ↑s) (replacement := u)
  have h_mismatch : st₀.mismatch = false := by simp [st₀, ReplayForkState.init]
  have h_obs_len : st₀.observed.length = st₀.cursor := by
    simp [st₀, ReplayForkState.init]
  have h_trace_drop : st₀.trace.drop st₀.cursor = log := by
    simp [st₀, ReplayForkState.init]
  have h_forkConsumed : st₀.forkConsumed = false := by
    simp [st₀, ReplayForkState.init]
  have h_dlt : st₀.distinguishedCount ≤ st₀.forkQuery := by
    simp [st₀, ReplayForkState.init]
  obtain ⟨logged, hlogged⟩ := Option.isSome_iff_exists.mp (hreach hlog s hcf)
  have h_count : (s : ℕ) + 1 ≤ log.countQ (· = i) := by
    have hgetQ : (log.getQ (· = i))[(s : ℕ)]? = some ⟨i, logged⟩ :=
      QueryLog.getQ_getElem?_eq_of_getQueryValue?_eq_some _ _ _ _ hlogged
    have hlt : (s : ℕ) < (log.getQ (· = i)).length :=
      (List.getElem?_eq_some_iff.1 hgetQ).1
    simpa [QueryLog.countQ] using Nat.succ_le_of_lt hlt
  have h_can_reach : st₀.forkQuery + 1 - st₀.distinguishedCount
      ≤ log.countQ (· = i) := by
    simpa only [st₀, ReplayForkState.init, Nat.sub_zero] using h_count
  have hq' : q ∈ support (((simulateQ (replayOracle i) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec i)) := by
    simpa [replayRunWithTraceValue, st₀] using hq
  exact replayRun_state_correct_aux (idx := i) (st₀ := st₀) (x_first := x₁)
    (log_cont := log) main hlog h_mismatch h_obs_len h_trace_drop
    h_forkConsumed h_dlt h_can_reach hq'

/-- No-guard replay composition returning the two `cf` projections. -/
private noncomputable def noGuardReplayComp
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) := do
  let p ← replayFirstRun main
  let u ← liftComp ($ᵗ spec.Range i) spec
  let q ← replayRunWithTraceValue main i p.2 ↑s u
  return some (cf p.1, cf q.1)

/-- Collision replay composition, succeeding when the replacement equals the logged answer. -/
private noncomputable def collisionReplayComp
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) := do
  let p ← replayFirstRun main
  let u ← liftComp ($ᵗ spec.Range i) spec
  if QueryLog.getQueryValue? p.2 i ↑s = some u then return cf p.1 else return none

private lemma probOutput_uniformGuard_le_aux [IsUniformSpec spec] (qb : ι → ℕ) (i : ι)
    (s : Fin (qb i + 1)) (val : Option (Fin (qb i + 1))) (lookup : Option (spec.Range i)) :
    Pr[= (some s : Option (Fin (qb i + 1))) | do
        let u ← liftComp ($ᵗ spec.Range i) spec
        if lookup = some u then return val else (return none : OracleComp spec _)] ≤
      (if val = some s then (1 : ℝ≥0∞) else 0) * (↑(Fintype.card (spec.Range i)))⁻¹ := by
  classical
  by_cases hval : val = some s
  · rcases lookup with _ | v
    · simp [hval]
    · have hcomp :
          Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if (some v : Option (spec.Range i)) = some u then
              return val else (return none : OracleComp spec _)]
            = Pr[= v | liftComp ($ᵗ spec.Range i) spec] := by
        rw [probOutput_bind_eq_tsum, tsum_eq_single v fun b hb => by simp [Ne.symm hb]]
        simp [hval]
      rw [hcomp, probOutput_liftComp, probOutput_uniformSample]
      simp [hval]
  · have hzero :
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let u ← liftComp ($ᵗ spec.Range i) spec
          if lookup = some u then
            return val else (return none : OracleComp spec _)] = 0 := by
      rw [probOutput_bind_eq_tsum]
      refine ENNReal.tsum_eq_zero.mpr fun u => mul_eq_zero.mpr <| Or.inr ?_
      simp [apply_ite (Pr[= some s | ·]), probOutput_pure, Ne.symm hval]
    rw [hzero]
    simp [hval]

private lemma probOutput_collisionReplay_le_main_div [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
        ↑(Fintype.card (spec.Range i)) := by
  classical
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have h_inner :
      ∀ (x₁ : α) (log : QueryLog spec),
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let u ← liftComp ($ᵗ spec.Range i) spec
          if QueryLog.getQueryValue? log i ↑s = some u then
            return cf x₁ else (return none : OracleComp spec _)] ≤
        (if cf x₁ = some s then (1 : ℝ≥0∞) else 0) * h⁻¹ := fun x₁ log =>
    probOutput_uniformGuard_le_aux qb i s (cf x₁) (QueryLog.getQueryValue? log i ↑s)
  calc
    Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s]
        = ∑' (p : α × QueryLog spec),
          Pr[= p | replayFirstRun main] *
            Pr[= (some s : Option (Fin (qb i + 1))) | do
              let u ← liftComp ($ᵗ spec.Range i) spec
              if QueryLog.getQueryValue? p.2 i ↑s = some u then
                return cf p.1 else (return none : OracleComp spec _)] := by
            simp only [collisionReplayComp]
            rw [probOutput_bind_eq_tsum]
    _ ≤ ∑' (p : α × QueryLog spec),
          Pr[= p | replayFirstRun main] *
            ((if cf p.1 = some s then (1 : ℝ≥0∞) else 0) * h⁻¹) := by
            refine ENNReal.tsum_le_tsum fun p => ?_
            exact mul_le_mul' le_rfl (h_inner p.1 p.2)
    _ = (∑' (p : α × QueryLog spec),
          Pr[= p | replayFirstRun main] *
            (if cf p.1 = some s then (1 : ℝ≥0∞) else 0)) * h⁻¹ := by
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun p => ?_
            ring
    _ = Pr[ fun p : α × QueryLog spec => cf p.1 = some s | replayFirstRun main] * h⁻¹ := by
            rw [probEvent_eq_tsum_ite]
            congr 1
            refine tsum_congr fun p => ?_
            by_cases hp : cf p.1 = some s <;> simp [hp]
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] * h⁻¹ := by
            congr 1
            calc
              Pr[ fun p : α × QueryLog spec => cf p.1 = some s | replayFirstRun main]
                  = Pr[ fun x : α => cf x = some s | main] := by
                    simpa using probEvent_fst_replayFirstRun (main := main)
                      (p := fun x : α => cf x = some s)
              _ = Pr[ fun y : Option (Fin (qb i + 1)) => y = some s | cf <$> main] := by
                    simpa [Function.comp] using
                      (probEvent_map (mx := main) (f := cf)
                        (q := fun y : Option (Fin (qb i + 1)) => y = some s)).symm
              _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] := by
                    simp [probEvent_eq_eq_probOutput
                      (mx := cf <$> main) (x := (some s : Option (Fin (qb i + 1))))]
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
          ↑(Fintype.card (spec.Range i)) := by
            rw [div_eq_mul_inv]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma replayOracle_run_lockstep_ne_i [spec.DecidableEq]
    (i t : ι) (u' : spec.Range t) (st : ReplayForkState spec i)
    (h_con : st.forkConsumed = false) (h_mis : st.mismatch = false)
    (h_next : st.nextEntry? = some ⟨t, u'⟩) (h_ti : t ≠ i) :
    (replayOracle i t).run st =
      (pure (u', { st with cursor := st.cursor + 1,
                           observed := st.observed.logQuery t u' }) :
        OracleComp spec (spec.Range t × ReplayForkState spec i)) := by
  simp_all [replayOracle, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma replayOracle_run_lockstep_i_pre_fork [spec.DecidableEq]
    (i : ι) (u' : spec.Range i) (st : ReplayForkState spec i)
    (h_con : st.forkConsumed = false) (h_mis : st.mismatch = false)
    (h_next : st.nextEntry? = some ⟨i, u'⟩)
    (h_fork : st.distinguishedCount ≠ st.forkQuery) :
    (replayOracle i i).run st =
      (pure (u', { st with cursor := st.cursor + 1,
                           distinguishedCount := st.distinguishedCount + 1,
                           observed := st.observed.logQuery i u' }) :
        OracleComp spec (spec.Range i × ReplayForkState spec i)) := by
  simp_all [replayOracle, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma replayOracle_run_fork_fires [spec.DecidableEq]
    (i : ι) (u' : spec.Range i) (st : ReplayForkState spec i)
    (h_con : st.forkConsumed = false) (h_mis : st.mismatch = false)
    (h_next : st.nextEntry? = some ⟨i, u'⟩)
    (h_fork : st.distinguishedCount = st.forkQuery) :
    (replayOracle i i).run st =
      (pure (st.replacement,
        { st with cursor := st.cursor + 1,
                   distinguishedCount := st.distinguishedCount + 1,
                   forkConsumed := true,
                   observed := st.observed.logQuery i st.replacement }) :
        OracleComp spec (spec.Range i × ReplayForkState spec i)) := by
  simp_all [replayOracle, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma replayOracle_run_nextEntry_none [spec.DecidableEq]
    (i t : ι) (st : ReplayForkState spec i)
    (h_con : st.forkConsumed = false) (h_mis : st.mismatch = false)
    (h_next : st.nextEntry? = none) :
    (replayOracle i t).run st =
      ((spec.query t : OracleComp spec (spec.Range t)) >>= fun u =>
        pure (u, (st.markMismatch).noteObserved t u)) := by
  simp_all [replayOracle, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma replayOracle_run_mismatch_ne [spec.DecidableEq]
    (i t t' : ι) (u' : spec.Range t') (st : ReplayForkState spec i)
    (h_con : st.forkConsumed = false) (h_mis : st.mismatch = false)
    (h_next : st.nextEntry? = some ⟨t', u'⟩) (h_tt : t ≠ t') :
    (replayOracle i t).run st =
      ((spec.query t : OracleComp spec (spec.Range t)) >>= fun u =>
        pure (u, (st.markMismatch).noteObserved t u)) := by
  simp_all [replayOracle, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma nextEntry?_eq_drop_head_aux (i : ι) (st : ReplayForkState spec i) :
    st.nextEntry? = (st.trace.drop st.cursor)[0]? := by
  rw [ReplayForkState.nextEntry?, List.getElem?_drop, Nat.add_zero]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma drop_cursor_succ_aux (i : ι) (st : ReplayForkState spec i) :
    st.trace.drop (st.cursor + 1) = (st.trace.drop st.cursor).drop 1 := by
  rw [List.drop_drop, Nat.add_comm]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma fst_map_replayOracle_run_live_bind_aux [spec.DecidableEq]
    (i t : ι) (oa : spec.Range t → OracleComp spec α) (st : ReplayForkState spec i)
    (h : (replayOracle i t).run st =
      ((spec.query t : OracleComp spec (spec.Range t)) >>= fun u =>
        pure (u, (st.markMismatch).noteObserved t u))) :
    (Prod.fst <$> ((replayOracle i t).run st >>= fun p =>
        (simulateQ (replayOracle i) (oa p.1)).run p.2) : OracleComp spec α) =
      (liftM (query t) >>= oa : OracleComp spec α) := by
  rw [h]
  simp only [monad_norm]
  exact bind_congr fun u' => fst_map_simulateQ_replayOracle_of_live i (oa u')
    ((st.markMismatch).noteObserved t u')
    (Or.inr (by simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]))

private theorem evalDist_uniform_bind_fst_simulateQ_replayOracle_run_coupled_aux
    [IsUniformSpec spec]
    (i : ι) (main : OracleComp spec α) :
    ∀ (stL stR : ReplayForkState spec i),
      stL.forkConsumed = false → stL.mismatch = false →
      stR.forkConsumed = false → stR.mismatch = false →
      stL.observed = stR.observed →
      stL.forkQuery = stR.forkQuery →
      stL.distinguishedCount = stR.distinguishedCount →
      stL.distinguishedCount ≤ stL.forkQuery →
      stR.trace.drop stR.cursor =
        QueryLog.takeBeforeForkAt (stL.trace.drop stL.cursor) i
          (stL.forkQuery - stL.distinguishedCount) →
      stL.forkQuery - stL.distinguishedCount <
        (QueryLog.getQ (stL.trace.drop stL.cursor) (· = i)).length →
      𝒟[(do
        let u ← liftComp ($ᵗ spec.Range i) spec
        Prod.fst <$> (simulateQ (replayOracle i) main).run
          {stL with replacement := u} : OracleComp spec α)] =
      𝒟[do
        let u ← liftComp ($ᵗ spec.Range i) spec
        Prod.fst <$> (simulateQ (replayOracle i) main).run
          {stR with replacement := u}] := by
  classical
  induction main using OracleComp.inductionOn with
  | pure x =>
    intro stL stR _ _ _ _ _ _ _ _ _ _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t oa ih =>
    intro stL stR h_Lcon h_Lmis h_Rcon h_Rmis h_obs h_fq h_dc h_dcle h_trace h_len
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    set d := stL.forkQuery - stL.distinguishedCount with hd_def
    rcases hL : stL.trace.drop stL.cursor with _ | ⟨⟨t₀, u'₀⟩, L_tail'⟩
    · exfalso
      rw [hL] at h_len
      simp [QueryLog.getQ] at h_len
    · have hL_cursor_lt : stL.cursor < stL.trace.length := by
        by_contra hge; push Not at hge
        rw [List.drop_of_length_le hge] at hL
        exact List.cons_ne_nil _ _ hL.symm
      have hL_next : stL.nextEntry? = some ⟨t₀, u'₀⟩ := by
        simp [nextEntry?_eq_drop_head_aux, hL]
      by_cases h_t₀ : t₀ = i
      · subst h_t₀
        by_cases hd0 : d = 0
        · have hR_trace : stR.trace.drop stR.cursor = [] := by
            rw [h_trace, hL, hd0, QueryLog.takeBeforeForkAt_cons_self_zero]
          have hR_next : stR.nextEntry? = none := by
            simp [nextEntry?_eq_drop_head_aux, hR_trace]
          have h_fork : stL.distinguishedCount = stL.forkQuery := by
            have h_sub_zero : stL.forkQuery - stL.distinguishedCount = 0 := hd_def ▸ hd0
            omega
          by_cases h_tt₀ : t = t₀
          · subst h_tt₀
            have hliveL : ∀ u : spec.Range t,
                (Prod.fst <$> ((replayOracle t t).run
                    ({stL with replacement := u} : ReplayForkState spec t) >>= fun p =>
                  (simulateQ (replayOracle t) (oa p.1)).run p.2) :
                  OracleComp spec α) = oa u := by
              intro u
              rw [replayOracle_run_fork_fires t u'₀
                ({stL with replacement := u} : ReplayForkState spec t)
                h_Lcon h_Lmis hL_next h_fork]
              simp only [pure_bind]
              exact fst_map_simulateQ_replayOracle_of_live t (oa u) _ (Or.inl rfl)
            have hliveR : ∀ u : spec.Range t,
                (Prod.fst <$> ((replayOracle t t).run
                    ({stR with replacement := u} : ReplayForkState spec t) >>= fun p =>
                  (simulateQ (replayOracle t) (oa p.1)).run p.2) :
                  OracleComp spec α) = (liftM (query t) >>= oa : OracleComp spec α) :=
              fun u => fst_map_replayOracle_run_live_bind_aux t t oa
                ({stR with replacement := u} : ReplayForkState spec t)
                (replayOracle_run_nextEntry_none t t _ h_Rcon h_Rmis hR_next)
            simp_rw [hliveL, hliveR]
            apply evalDist_ext; intro a
            conv_rhs => rw [probOutput_bind_const]
            have hne : Pr[⊥ | (liftComp ($ᵗ spec.Range t) spec :
                OracleComp spec (spec.Range t))] = 0 := by
              rw [probFailure_def, evalDist_liftComp, ← probFailure_def]
              exact probFailure_uniformSample _
            rw [hne, tsub_zero, one_mul]
            have heq : 𝒟[liftComp ($ᵗ spec.Range t) spec >>= oa] =
                𝒟[(spec.query t : OracleComp spec (spec.Range t)) >>= oa] := by
              rw [evalDist_bind, evalDist_bind, evalDist_liftComp, evalDist_uniformSample,
                evalDist_query]
            exact congrFun (congrArg DFunLike.coe heq) a
          · simp_rw [fun u => fst_map_replayOracle_run_live_bind_aux t₀ t oa
              ({stL with replacement := u} : ReplayForkState spec t₀)
              (replayOracle_run_mismatch_ne t₀ t t₀ u'₀ _ h_Lcon h_Lmis hL_next h_tt₀),
              fun u => fst_map_replayOracle_run_live_bind_aux t₀ t oa
              ({stR with replacement := u} : ReplayForkState spec t₀)
              (replayOracle_run_nextEntry_none t₀ t _ h_Rcon h_Rmis hR_next)]
        · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
          have hR_trace : stR.trace.drop stR.cursor =
              ⟨t₀, u'₀⟩ :: QueryLog.takeBeforeForkAt L_tail' t₀ (d - 1) := by
            rw [h_trace, hL]
            conv_lhs => rw [show d = (d - 1) + 1 from (Nat.sub_add_cancel hd1).symm]
            rw [QueryLog.takeBeforeForkAt_cons_self_succ]
          have hR_next : stR.nextEntry? = some ⟨t₀, u'₀⟩ := by
            simp [nextEntry?_eq_drop_head_aux, hR_trace]
          have h_fork_neL : stL.distinguishedCount ≠ stL.forkQuery := fun h_eq => by
            have : d = 0 := by rw [hd_def, h_eq]; exact Nat.sub_self _
            exact hd0 this
          have h_fork_neR : stR.distinguishedCount ≠ stR.forkQuery :=
            h_dc ▸ h_fq ▸ h_fork_neL
          by_cases h_tt₀ : t = t₀
          · subst h_tt₀
            set stL' : ReplayForkState spec t :=
              { stL with
                cursor := stL.cursor + 1
                distinguishedCount := stL.distinguishedCount + 1
                observed := stL.observed.logQuery t u'₀ } with hstL'_def
            set stR' : ReplayForkState spec t :=
              { stR with
                cursor := stR.cursor + 1
                distinguishedCount := stR.distinguishedCount + 1
                observed := stR.observed.logQuery t u'₀ } with hstR'_def
            have hstepL : ∀ u : spec.Range t,
                (replayOracle t t).run ({stL with replacement := u} : ReplayForkState spec t) =
                (pure (u'₀, { stL' with replacement := u }) :
                  OracleComp spec (spec.Range t × ReplayForkState spec t)) := by
              intro u
              have h := replayOracle_run_lockstep_i_pre_fork t u'₀
                ({stL with replacement := u} : ReplayForkState spec t)
                h_Lcon h_Lmis hL_next h_fork_neL
              convert h using 2
            have hstepR : ∀ u : spec.Range t,
                (replayOracle t t).run ({stR with replacement := u} : ReplayForkState spec t) =
                (pure (u'₀, { stR' with replacement := u }) :
                  OracleComp spec (spec.Range t × ReplayForkState spec t)) := by
              intro u
              have h := replayOracle_run_lockstep_i_pre_fork t u'₀
                ({stR with replacement := u} : ReplayForkState spec t)
                h_Rcon h_Rmis hR_next h_fork_neR
              convert h using 2
            simp_rw [hstepL, hstepR, pure_bind]
            have h_obs' : stL'.observed = stR'.observed := by simp [stL', stR', h_obs]
            have h_fq' : stL'.forkQuery = stR'.forkQuery := h_fq
            have h_dc' : stL'.distinguishedCount = stR'.distinguishedCount := by
              simp [stL', stR', h_dc]
            have h_dcle' : stL'.distinguishedCount ≤ stL'.forkQuery := by
              change stL.distinguishedCount + 1 ≤ stL.forkQuery
              omega
            have h_trace' : stR'.trace.drop stR'.cursor =
                QueryLog.takeBeforeForkAt (stL'.trace.drop stL'.cursor) t
                  (stL'.forkQuery - stL'.distinguishedCount) := by
              change stR.trace.drop (stR.cursor + 1) =
                QueryLog.takeBeforeForkAt (stL.trace.drop (stL.cursor + 1)) t
                  (stL.forkQuery - (stL.distinguishedCount + 1))
              have hLdrop : stL.trace.drop (stL.cursor + 1) = L_tail' := by
                simp [drop_cursor_succ_aux, hL]
              have hRdrop : stR.trace.drop (stR.cursor + 1) =
                  QueryLog.takeBeforeForkAt L_tail' t (d - 1) := by
                simp [drop_cursor_succ_aux, hR_trace]
              rw [hLdrop, hRdrop]
              congr 1
            have h_len' : stL'.forkQuery - stL'.distinguishedCount <
                (QueryLog.getQ (stL'.trace.drop stL'.cursor) (· = t)).length := by
              change stL.forkQuery - (stL.distinguishedCount + 1) <
                (QueryLog.getQ (stL.trace.drop (stL.cursor + 1)) (· = t)).length
              have hLdrop : stL.trace.drop (stL.cursor + 1) = L_tail' := by
                simp [drop_cursor_succ_aux, hL]
              rw [hLdrop]
              have hlen_expand :
                  (QueryLog.getQ (⟨t, u'₀⟩ :: L_tail' : QueryLog spec) (· = t)).length =
                    (QueryLog.getQ L_tail' (· = t)).length + 1 := by
                simp [QueryLog.getQ_cons]
              have hlen_orig : d <
                  (QueryLog.getQ (stL.trace.drop stL.cursor) (· = t)).length := h_len
              rw [hL] at hlen_orig
              rw [hlen_expand] at hlen_orig
              omega
            exact ih u'₀ stL' stR' h_Lcon h_Lmis h_Rcon h_Rmis h_obs' h_fq' h_dc' h_dcle'
              h_trace' h_len'
          · simp_rw [fun u => fst_map_replayOracle_run_live_bind_aux t₀ t oa
              ({stL with replacement := u} : ReplayForkState spec t₀)
              (replayOracle_run_mismatch_ne t₀ t t₀ u'₀ _ h_Lcon h_Lmis hL_next h_tt₀),
              fun u => fst_map_replayOracle_run_live_bind_aux t₀ t oa
              ({stR with replacement := u} : ReplayForkState spec t₀)
              (replayOracle_run_mismatch_ne t₀ t t₀ u'₀ _ h_Rcon h_Rmis hR_next h_tt₀)]
      · have hR_trace : stR.trace.drop stR.cursor =
            ⟨t₀, u'₀⟩ :: QueryLog.takeBeforeForkAt L_tail' i d := by
          rw [h_trace, hL, QueryLog.takeBeforeForkAt_cons_of_ne _ _ _ _ _ h_t₀]
        have hR_next : stR.nextEntry? = some ⟨t₀, u'₀⟩ := by
          simp [nextEntry?_eq_drop_head_aux, hR_trace]
        by_cases h_tt₀ : t = t₀
        · subst h_tt₀
          have h_ti : t ≠ i := h_t₀
          set stL' : ReplayForkState spec i :=
            { stL with
              cursor := stL.cursor + 1
              observed := stL.observed.logQuery t u'₀ } with hstL'_def
          set stR' : ReplayForkState spec i :=
            { stR with
              cursor := stR.cursor + 1
              observed := stR.observed.logQuery t u'₀ } with hstR'_def
          have hstepL : ∀ u : spec.Range i,
              (replayOracle i t).run ({stL with replacement := u} : ReplayForkState spec i) =
              (pure (u'₀, { stL' with replacement := u }) :
                OracleComp spec (spec.Range t × ReplayForkState spec i)) := by
            intro u
            have h := replayOracle_run_lockstep_ne_i i t u'₀
              ({stL with replacement := u} : ReplayForkState spec i)
              h_Lcon h_Lmis hL_next h_ti
            convert h using 2
          have hstepR : ∀ u : spec.Range i,
              (replayOracle i t).run ({stR with replacement := u} : ReplayForkState spec i) =
              (pure (u'₀, { stR' with replacement := u }) :
                OracleComp spec (spec.Range t × ReplayForkState spec i)) := by
            intro u
            have h := replayOracle_run_lockstep_ne_i i t u'₀
              ({stR with replacement := u} : ReplayForkState spec i)
              h_Rcon h_Rmis hR_next h_ti
            convert h using 2
          simp_rw [hstepL, hstepR, pure_bind]
          have h_obs' : stL'.observed = stR'.observed := by
            simp [stL', stR', h_obs]
          have h_fq' : stL'.forkQuery = stR'.forkQuery := h_fq
          have h_dc' : stL'.distinguishedCount = stR'.distinguishedCount := h_dc
          have h_dcle' : stL'.distinguishedCount ≤ stL'.forkQuery := h_dcle
          have h_trace' : stR'.trace.drop stR'.cursor =
              QueryLog.takeBeforeForkAt (stL'.trace.drop stL'.cursor) i
                (stL'.forkQuery - stL'.distinguishedCount) := by
            change stR.trace.drop (stR.cursor + 1) =
              QueryLog.takeBeforeForkAt (stL.trace.drop (stL.cursor + 1)) i d
            have hLdrop : stL.trace.drop (stL.cursor + 1) = L_tail' := by
              simp [drop_cursor_succ_aux, hL]
            have hRdrop : stR.trace.drop (stR.cursor + 1) =
                QueryLog.takeBeforeForkAt L_tail' i d := by
              simp [drop_cursor_succ_aux, hR_trace]
            rw [hLdrop, hRdrop]
          have h_len' : stL'.forkQuery - stL'.distinguishedCount <
              (QueryLog.getQ (stL'.trace.drop stL'.cursor) (· = i)).length := by
            change d < (QueryLog.getQ (stL.trace.drop (stL.cursor + 1)) (· = i)).length
            have hLdrop : stL.trace.drop (stL.cursor + 1) = L_tail' := by
              simp [drop_cursor_succ_aux, hL]
            rw [hLdrop]
            have hlen_expand :
                (QueryLog.getQ (⟨t, u'₀⟩ :: L_tail' : QueryLog spec) (· = i)).length =
                  (QueryLog.getQ L_tail' (· = i)).length := by
              rw [QueryLog.getQ_cons, if_neg h_ti]
            rw [← hlen_expand]
            have hlen_orig : d <
                (QueryLog.getQ (stL.trace.drop stL.cursor) (· = i)).length := h_len
            rwa [hL] at hlen_orig
          exact ih u'₀ stL' stR' h_Lcon h_Lmis h_Rcon h_Rmis h_obs' h_fq' h_dc' h_dcle'
            h_trace' h_len'
        · simp_rw [fun u => fst_map_replayOracle_run_live_bind_aux i t oa
              ({stL with replacement := u} : ReplayForkState spec i)
              (replayOracle_run_mismatch_ne i t t₀ u'₀ _ h_Lcon h_Lmis hL_next h_tt₀),
              fun u => fst_map_replayOracle_run_live_bind_aux i t oa
              ({stR with replacement := u} : ReplayForkState spec i)
              (replayOracle_run_mismatch_ne i t t₀ u'₀ _ h_Rcon h_Rmis hR_next h_tt₀)]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private theorem fst_map_simulateQ_replayOracle_both_noteObserved_aux [spec.DecidableEq]
    (i t : ι) (v : spec.Range t) (oa : OracleComp spec α)
    (stL stR : ReplayForkState spec i) :
    (Prod.fst <$> (simulateQ (replayOracle i) oa).run (stL.markMismatch.noteObserved t v) :
      OracleComp spec α) =
    Prod.fst <$> (simulateQ (replayOracle i) oa).run (stR.markMismatch.noteObserved t v) := by
  rw [fst_map_simulateQ_replayOracle_of_live i oa (stL.markMismatch.noteObserved t v) (Or.inr (by
        simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch])),
    fst_map_simulateQ_replayOracle_of_live i oa (stR.markMismatch.noteObserved t v) (Or.inr (by
        simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]))]

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private theorem fst_map_simulateQ_replayOracle_state_equiv [spec.DecidableEq]
    (i : ι) (oa : OracleComp spec α) :
    ∀ (stL stR : ReplayForkState spec i),
      stL.forkConsumed = stR.forkConsumed →
      stL.mismatch = stR.mismatch →
      stL.trace.drop stL.cursor = stR.trace.drop stR.cursor →
      stL.forkQuery - stL.distinguishedCount =
        stR.forkQuery - stR.distinguishedCount →
      stL.replacement = stR.replacement →
      stL.distinguishedCount ≤ stL.forkQuery →
      stR.distinguishedCount ≤ stR.forkQuery →
      (Prod.fst <$> (simulateQ (replayOracle i) oa).run stL :
        OracleComp spec α) =
      (Prod.fst <$> (simulateQ (replayOracle i) oa).run stR :
        OracleComp spec α) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro _ _ _ _ _ _ _ _ _
    simp
  | query_bind t oa ih =>
    intro stL stR h_fc h_mis h_trace h_diff h_repl h_dcleL h_dcleR
    by_cases h_live : stL.forkConsumed = true ∨ stL.mismatch = true
    · have h_liveR : stR.forkConsumed = true ∨ stR.mismatch = true :=
        h_live.imp (h_fc ▸ ·) (h_mis ▸ ·)
      rw [fst_map_simulateQ_replayOracle_of_live i
          (liftM (query t) >>= oa : OracleComp spec α) stL h_live,
        fst_map_simulateQ_replayOracle_of_live i
          (liftM (query t) >>= oa : OracleComp spec α) stR h_liveR]
    · push Not at h_live
      simp only [ne_eq, Bool.not_eq_true] at h_live
      obtain ⟨h_fcL, h_misL⟩ := h_live
      have h_fcR : stR.forkConsumed = false := h_fc ▸ h_fcL
      have h_misR : stR.mismatch = false := h_mis ▸ h_misL
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, StateT.run_bind]
      rcases hLdrop : stL.trace.drop stL.cursor with _ | ⟨⟨t', u'⟩, tail⟩
      · have hRdrop : stR.trace.drop stR.cursor = [] := h_trace ▸ hLdrop
        have hL_next : stL.nextEntry? = none := by
          simp [nextEntry?_eq_drop_head_aux, hLdrop]
        have hR_next : stR.nextEntry? = none := by
          simp [nextEntry?_eq_drop_head_aux, hRdrop]
        rw [replayOracle_run_nextEntry_none i t stL h_fcL h_misL hL_next,
          replayOracle_run_nextEntry_none i t stR h_fcR h_misR hR_next]
        simp only [bind_assoc, pure_bind, map_bind]
        exact bind_congr fun v =>
          fst_map_simulateQ_replayOracle_both_noteObserved_aux i t v (oa v) stL stR
      · have hRdrop : stR.trace.drop stR.cursor = ⟨t', u'⟩ :: tail := h_trace ▸ hLdrop
        have hL_next : stL.nextEntry? = some ⟨t', u'⟩ := by
          simp [nextEntry?_eq_drop_head_aux, hLdrop]
        have hR_next : stR.nextEntry? = some ⟨t', u'⟩ := by
          simp [nextEntry?_eq_drop_head_aux, hRdrop]
        by_cases h_tt' : t = t'
        · subst h_tt'
          by_cases h_ti : t = i
          · subst h_ti
            by_cases h_fork : stL.distinguishedCount = stL.forkQuery
            · have h_forkR : stR.distinguishedCount = stR.forkQuery := by omega
              rw [replayOracle_run_fork_fires t u' stL h_fcL h_misL hL_next h_fork,
                replayOracle_run_fork_fires t u' stR h_fcR h_misR hR_next h_forkR]
              simp only [pure_bind]
              rw [h_repl]
              rw [fst_map_simulateQ_replayOracle_of_live t (oa stR.replacement) _
                  (Or.inl rfl),
                fst_map_simulateQ_replayOracle_of_live t (oa stR.replacement) _
                  (Or.inl rfl)]
            · have h_forkR : stR.distinguishedCount ≠ stR.forkQuery := by omega
              rw [replayOracle_run_lockstep_i_pre_fork t u' stL h_fcL h_misL hL_next
                  h_fork,
                replayOracle_run_lockstep_i_pre_fork t u' stR h_fcR h_misR hR_next
                  h_forkR]
              simp only [pure_bind]
              set stL' : ReplayForkState spec t :=
                { stL with
                  cursor := stL.cursor + 1
                  distinguishedCount := stL.distinguishedCount + 1
                  observed := stL.observed.logQuery t u' } with h_stL'_def
              set stR' : ReplayForkState spec t :=
                { stR with
                  cursor := stR.cursor + 1
                  distinguishedCount := stR.distinguishedCount + 1
                  observed := stR.observed.logQuery t u' } with h_stR'_def
              have h_dcleL' : stL'.distinguishedCount ≤ stL'.forkQuery := by
                change stL.distinguishedCount + 1 ≤ stL.forkQuery
                omega
              have h_dcleR' : stR'.distinguishedCount ≤ stR'.forkQuery := by
                change stR.distinguishedCount + 1 ≤ stR.forkQuery
                omega
              have h_trace' : stL'.trace.drop stL'.cursor =
                  stR'.trace.drop stR'.cursor := by
                change stL.trace.drop (stL.cursor + 1) =
                  stR.trace.drop (stR.cursor + 1)
                simp [drop_cursor_succ_aux, hLdrop, hRdrop]
              have h_diff' : stL'.forkQuery - stL'.distinguishedCount =
                  stR'.forkQuery - stR'.distinguishedCount := by
                change stL.forkQuery - (stL.distinguishedCount + 1) =
                  stR.forkQuery - (stR.distinguishedCount + 1)
                omega
              exact ih u' stL' stR' h_fc h_mis h_trace' h_diff' h_repl
                h_dcleL' h_dcleR'
          · rw [replayOracle_run_lockstep_ne_i i t u' stL h_fcL h_misL hL_next h_ti,
              replayOracle_run_lockstep_ne_i i t u' stR h_fcR h_misR hR_next h_ti]
            simp only [pure_bind]
            set stL' : ReplayForkState spec i :=
              { stL with
                cursor := stL.cursor + 1
                observed := stL.observed.logQuery t u' } with h_stL'_def
            set stR' : ReplayForkState spec i :=
              { stR with
                cursor := stR.cursor + 1
                observed := stR.observed.logQuery t u' } with h_stR'_def
            have h_trace' : stL'.trace.drop stL'.cursor =
                stR'.trace.drop stR'.cursor := by
              change stL.trace.drop (stL.cursor + 1) =
                stR.trace.drop (stR.cursor + 1)
              simp [drop_cursor_succ_aux, hLdrop, hRdrop]
            exact ih u' stL' stR' h_fc h_mis h_trace' h_diff h_repl h_dcleL h_dcleR
        · rw [replayOracle_run_mismatch_ne i t t' u' stL h_fcL h_misL hL_next h_tt',
            replayOracle_run_mismatch_ne i t t' u' stR h_fcR h_misR hR_next h_tt']
          simp only [bind_assoc, pure_bind, map_bind]
          exact bind_congr fun v =>
            fst_map_simulateQ_replayOracle_both_noteObserved_aux i t v (oa v) stL stR

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private theorem fst_map_replayRunWithTraceValue_nil [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (s : ℕ) (u' : spec.Range i) :
    (Prod.fst <$> replayRunWithTraceValue main i [] s u' :
      OracleComp spec α) = main := by
  unfold replayRunWithTraceValue
  induction main using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    have hinit : (ReplayForkState.init ([] : QueryLog spec) s u' : ReplayForkState spec i) =
        { trace := [], cursor := 0, distinguishedCount := 0,
          forkQuery := s, replacement := u', forkConsumed := false,
          mismatch := false, observed := [] } := rfl
    have h_fc : (ReplayForkState.init ([] : QueryLog spec) s u' :
        ReplayForkState spec i).forkConsumed = false := by rw [hinit]
    have h_mis : (ReplayForkState.init ([] : QueryLog spec) s u' :
        ReplayForkState spec i).mismatch = false := by rw [hinit]
    have h_next : (ReplayForkState.init ([] : QueryLog spec) s u' :
        ReplayForkState spec i).nextEntry? = none := by
      rw [hinit]; rfl
    rw [replayOracle_run_nextEntry_none i t _ h_fc h_mis h_next]
    simp only [bind_assoc, pure_bind, map_bind]
    exact bind_congr fun v => fst_map_simulateQ_replayOracle_of_live i (oa v)
      (((ReplayForkState.init ([] : QueryLog spec) s u' :
          ReplayForkState spec i).markMismatch).noteObserved t v)
      (Or.inr (by
        simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch]))

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private theorem fst_map_replayRunWithTraceValue_query_bind_cons_ne [spec.DecidableEq]
    (i t : ι) (h_ti : t ≠ i)
    (oa : spec.Range t → OracleComp spec α)
    (u : spec.Range t) (τ : QueryLog spec) (s : ℕ) (u' : spec.Range i) :
    (Prod.fst <$> replayRunWithTraceValue
        ((spec.query t : OracleComp spec _) >>= oa)
        i (⟨t, u⟩ :: τ) s u' : OracleComp spec α) =
    Prod.fst <$> replayRunWithTraceValue (oa u) i τ s u' := by
  unfold replayRunWithTraceValue
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind]
  set stL : ReplayForkState spec i :=
    ReplayForkState.init (⟨t, u⟩ :: τ) s u' with hstL_def
  have h_fcL : stL.forkConsumed = false := rfl
  have h_misL : stL.mismatch = false := rfl
  have h_nextL : stL.nextEntry? = some ⟨t, u⟩ := by
    change (⟨t, u⟩ :: τ : QueryLog spec)[0]? = some ⟨t, u⟩
    rfl
  rw [replayOracle_run_lockstep_ne_i i t u stL h_fcL h_misL h_nextL h_ti]
  simp only [pure_bind]
  set stL' : ReplayForkState spec i :=
    { stL with cursor := stL.cursor + 1,
               observed := stL.observed.logQuery t u } with hstL'_def
  set stR : ReplayForkState spec i :=
    ReplayForkState.init τ s u' with hstR_def
  refine fst_map_simulateQ_replayOracle_state_equiv i (oa u) stL' stR
    rfl rfl ?_ ?_ rfl ?_ ?_
  · change (⟨t, u⟩ :: τ : QueryLog spec).drop (0 + 1) = τ.drop 0
    simp
  · rfl
  · exact Nat.zero_le _
  · exact Nat.zero_le _

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private theorem fst_map_replayRunWithTraceValue_query_bind_cons_self_succ
    [spec.DecidableEq]
    (i : ι) (oa : spec.Range i → OracleComp spec α)
    (u : spec.Range i) (τ : QueryLog spec) (k : ℕ) (u' : spec.Range i) :
    (Prod.fst <$> replayRunWithTraceValue
        ((spec.query i : OracleComp spec _) >>= oa)
        i (⟨i, u⟩ :: τ) (k + 1) u' : OracleComp spec α) =
    Prod.fst <$> replayRunWithTraceValue (oa u) i τ k u' := by
  unfold replayRunWithTraceValue
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind]
  set stL : ReplayForkState spec i :=
    ReplayForkState.init (⟨i, u⟩ :: τ) (k + 1) u' with hstL_def
  have h_fcL : stL.forkConsumed = false := rfl
  have h_misL : stL.mismatch = false := rfl
  have h_nextL : stL.nextEntry? = some ⟨i, u⟩ := by
    change (⟨i, u⟩ :: τ : QueryLog spec)[0]? = some ⟨i, u⟩
    rfl
  have h_fork : stL.distinguishedCount ≠ stL.forkQuery := by
    change (0 : ℕ) ≠ k + 1
    omega
  rw [replayOracle_run_lockstep_i_pre_fork i u stL h_fcL h_misL h_nextL h_fork]
  simp only [pure_bind]
  set stL' : ReplayForkState spec i :=
    { stL with cursor := stL.cursor + 1,
               distinguishedCount := stL.distinguishedCount + 1,
               observed := stL.observed.logQuery i u } with hstL'_def
  set stR : ReplayForkState spec i :=
    ReplayForkState.init τ k u' with hstR_def
  refine fst_map_simulateQ_replayOracle_state_equiv i (oa u) stL' stR
    rfl rfl ?_ ?_ rfl ?_ ?_
  · change (⟨i, u⟩ :: τ : QueryLog spec).drop (0 + 1) = τ.drop 0
    simp
  · change k + 1 - (0 + 1) = k - 0
    omega
  · change (0 + 1 : ℕ) ≤ k + 1
    omega
  · exact Nat.zero_le _

private lemma evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
    [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (log : QueryLog spec) (s : ℕ) :
    𝒟[(do
      let u ← liftComp ($ᵗ spec.Range i) spec
      Prod.fst <$> replayRunWithTraceValue main i log s u : OracleComp spec α)] =
    𝒟[do
      let u ← liftComp ($ᵗ spec.Range i) spec
      Prod.fst <$> replayRunWithTraceValue main i (QueryLog.takeBeforeForkAt log i s) s u] := by
  classical
  by_cases hlen : (log.getQ (· = i)).length ≤ s
  · rw [QueryLog.takeBeforeForkAt_of_getQ_length_le log i s hlen]
  · push Not at hlen
    set stL : ReplayForkState spec i := ReplayForkState.init log s default
      with hstL_def
    set stR : ReplayForkState spec i :=
      ReplayForkState.init (QueryLog.takeBeforeForkAt log i s) s default
      with hstR_def
    have hLcon : stL.forkConsumed = false := rfl
    have hLmis : stL.mismatch = false := rfl
    have hRcon : stR.forkConsumed = false := rfl
    have hRmis : stR.mismatch = false := rfl
    have hobs : stL.observed = stR.observed := rfl
    have hfq : stL.forkQuery = stR.forkQuery := rfl
    have hdc : stL.distinguishedCount = stR.distinguishedCount := rfl
    have hdcle : stL.distinguishedCount ≤ stL.forkQuery := by
      simp [stL, ReplayForkState.init]
    have htrL : stR.trace.drop stR.cursor =
        QueryLog.takeBeforeForkAt (stL.trace.drop stL.cursor) i
          (stL.forkQuery - stL.distinguishedCount) := by
      simp [stL, stR, ReplayForkState.init]
    have hlen' : stL.forkQuery - stL.distinguishedCount <
        (QueryLog.getQ (stL.trace.drop stL.cursor) (· = i)).length := by
      simpa [stL, ReplayForkState.init] using hlen
    have haux := evalDist_uniform_bind_fst_simulateQ_replayOracle_run_coupled_aux
      i main stL stR hLcon hLmis hRcon hRmis hobs hfq hdc hdcle htrL hlen'
    have hInitL : ∀ u : spec.Range i,
        ({stL with replacement := u} : ReplayForkState spec i) =
        ReplayForkState.init log s u :=
      fun u => by simp [stL, ReplayForkState.init]
    have hInitR : ∀ u : spec.Range i,
        ({stR with replacement := u} : ReplayForkState spec i) =
        ReplayForkState.init (QueryLog.takeBeforeForkAt log i s) s u :=
      fun u => by simp [stR, ReplayForkState.init]
    have hLeq : (do
        let u ← liftComp ($ᵗ spec.Range i) spec
        Prod.fst <$> replayRunWithTraceValue main i log s u : OracleComp spec α) =
        (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          Prod.fst <$> (simulateQ (replayOracle i) main).run
            ({stL with replacement := u}) : OracleComp spec α) := by
      unfold replayRunWithTraceValue
      exact bind_congr fun u => by rw [hInitL u]
    have hReq : (do
        let u ← liftComp ($ᵗ spec.Range i) spec
        Prod.fst <$> replayRunWithTraceValue main i
          (QueryLog.takeBeforeForkAt log i s) s u : OracleComp spec α) =
        (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          Prod.fst <$> (simulateQ (replayOracle i) main).run
            ({stR with replacement := u}) : OracleComp spec α) := by
      unfold replayRunWithTraceValue
      exact bind_congr fun u => by rw [hInitR u]
    rw [hLeq, hReq]
    exact haux

private lemma probOutput_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
    [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (log : QueryLog spec) (s : ℕ) (x : α) :
    Pr[= x | Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i log s u : OracleComp spec (α × _))] =
    Pr[= x | Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i (QueryLog.takeBeforeForkAt log i s) s u)] := by
  simp only [map_bind]
  exact congrFun (congrArg DFunLike.coe
    (evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt main i log s)) x

omit [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma tsum_probOutput_map_mul [IsUniformSpec spec] {γ δ : Type} (mn : OracleComp spec γ)
    (f : γ → δ) (g : δ → ℝ≥0∞) :
    ∑' y : δ, Pr[= y | (f <$> mn : OracleComp spec δ)] * g y =
    ∑' x : γ, Pr[= x | mn] * g (f x) := by
  classical
  simp_rw [probOutput_map_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  refine congrArg _ ?_
  refine (tsum_eq_single (f x) fun y hy => ?_).trans ?_
  · have : DecidableEq δ := Classical.decEq δ
    rw [probOutput_pure, if_neg hy, zero_mul]
  · rw [probOutput_pure_self, one_mul]

omit [unifSpec ˡ⊂ₒ spec] [spec.DecidableEq] in
private lemma probOutput_map_fst_bind_liftComp_congr [IsUniformSpec spec] {β σ : Type}
    (j : ι) (f : α → β) (y : β)
    (g : spec.Range j → OracleComp spec (α × σ)) (b : spec.Range j → OracleComp spec β)
    (hgb : ∀ u, (f <$> Prod.fst <$> g u : OracleComp spec β) = b u) :
    Pr[= y | f <$> Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range j) spec; g u : OracleComp spec (α × σ))] =
    Pr[= y | (do let u ← liftComp ($ᵗ spec.Range j) spec; b u : OracleComp spec β)] := by
  congr 1
  simp only [map_bind]
  exact bind_congr hgb

omit [spec.DecidableEq] in
private lemma probOutput_bind_liftComp_const [IsUniformSpec spec] {β : Type}
    (j : ι) (mb : OracleComp spec β) (y : β) :
    Pr[= y | (do let _u ← liftComp ($ᵗ spec.Range j) spec; mb : OracleComp spec β)] =
      Pr[= y | mb] := by
  rw [probOutput_bind_const]
  have hne : Pr[⊥ | (liftComp ($ᵗ spec.Range j) spec : OracleComp spec (spec.Range j))] = 0 := by
    rw [probFailure_def, evalDist_liftComp, ← probFailure_def]
    exact probFailure_uniformSample _
  rw [hne, tsub_zero, one_mul]

private lemma tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt [IsUniformSpec spec]
    {β : Type} (main : OracleComp spec α) (i : ι) (s : ℕ)
    (f : α → β) (y : β) (h : QueryLog spec → ℝ≥0∞) :
    ∑' p, Pr[= p | replayFirstRun main] *
      (h (QueryLog.takeBeforeForkAt p.2 i s) *
        Pr[= y | (f <$> (pure p.1 : OracleComp spec α) : OracleComp spec β)]) =
    ∑' p, Pr[= p | replayFirstRun main] *
      (h (QueryLog.takeBeforeForkAt p.2 i s) *
        Pr[= y | f <$> Prod.fst <$> (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          replayRunWithTraceValue main i
            (QueryLog.takeBeforeForkAt p.2 i s) s u :
              OracleComp spec (α × _))]) := by
  classical
  revert s h
  induction main using OracleComp.inductionOn with
  | pure a =>
    intro s h
    have hFR : (replayFirstRun (pure a : OracleComp spec α) :
        OracleComp spec (α × QueryLog spec)) = pure (a, []) := by
      simp [replayFirstRun]
    rw [hFR]
    refine tsum_congr fun p => ?_
    by_cases hp : p = (a, [])
    · subst hp
      simp only [probOutput_pure_self, QueryLog.takeBeforeForkAt_nil]
      congr 1
      have hcomp : ∀ u : spec.Range i,
          (f <$> Prod.fst <$> replayRunWithTraceValue
              (pure a : OracleComp spec α) i [] s u :
            OracleComp spec β) = (f <$> pure a : OracleComp spec β) := fun u => by
        unfold replayRunWithTraceValue
        simp [simulateQ_pure, StateT.run_pure, map_pure]
      rw [probOutput_map_fst_bind_liftComp_congr i f y _ _ hcomp,
        probOutput_bind_liftComp_const]
    · have : DecidableEq (α × QueryLog spec) := Classical.decEq _
      simp [probOutput_pure, hp]
  | query_bind t mx ih =>
    intro s h
    set main : OracleComp spec α := (spec.query t : OracleComp spec _) >>= mx with hmain_def
    have hFR : (replayFirstRun main : OracleComp spec (α × QueryLog spec)) =
        (query t : OracleComp spec _) >>= fun u =>
          (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i' : ι) × spec.Range i') :: p.2))
            <$> replayFirstRun (mx u) := by
      unfold replayFirstRun
      exact OracleComp.run_simulateQ_loggingOracle_query_bind t mx
    have swap : ∀ (g : α × QueryLog spec → ℝ≥0∞),
        ∑' p : α × QueryLog spec, Pr[= p | replayFirstRun main] * g p =
        ∑' u : spec.Range t,
          Pr[= u | (query t : OracleComp spec (spec.Range t))] *
            ∑' p' : α × QueryLog spec,
              Pr[= p' | replayFirstRun (mx u)] *
                g (p'.1, (⟨t, u⟩ : (i' : ι) × spec.Range i') :: p'.2) := by
      intro g
      rw [hFR]
      simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
      exact tsum_congr fun u => congrArg _ <|
        tsum_probOutput_map_mul (replayFirstRun (mx u))
          (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i' : ι) × spec.Range i') :: p.2)) g
    rw [swap fun p => h (QueryLog.takeBeforeForkAt p.2 i s) *
        Pr[= y | (f <$> (pure p.1 : OracleComp spec α) : OracleComp spec β)]]
    rw [swap fun p => h (QueryLog.takeBeforeForkAt p.2 i s) *
        Pr[= y | f <$> Prod.fst <$> (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          replayRunWithTraceValue main i
            (QueryLog.takeBeforeForkAt p.2 i s) s u :
              OracleComp spec (α × _))]]
    by_cases h_ti : t = i
    · subst h_ti
      cases s with
      | zero =>
        simp_rw [fun (u : spec.Range t) (p' : α × QueryLog spec) =>
          QueryLog.takeBeforeForkAt_cons_self_zero (spec := spec) t u p'.2]
        have hreplay_nil_map : ∀ (u' : spec.Range t),
            (f <$> Prod.fst <$> replayRunWithTraceValue main t ([] : QueryLog spec) 0 u' :
              OracleComp spec β) = (f <$> main : OracleComp spec β) := fun u' => by
          rw [fst_map_replayRunWithTraceValue_nil main t 0 u']
        have hPr_rhs : Pr[= y | f <$> Prod.fst <$> (do
              let u ← liftComp ($ᵗ spec.Range t) spec
              replayRunWithTraceValue main t ([] : QueryLog spec) 0 u :
                OracleComp spec (α × _))] =
            Pr[= y | (f <$> main : OracleComp spec β)] := by
          rw [probOutput_map_fst_bind_liftComp_congr t f y _ _ hreplay_nil_map,
            probOutput_bind_liftComp_const]
        simp_rw [hPr_rhs]
        have hfmain : Pr[= y | (f <$> main : OracleComp spec β)] =
            ∑' u : spec.Range t,
              Pr[= u | (query t : OracleComp spec (spec.Range t))] *
                Pr[= y | (f <$> mx u : OracleComp spec β)] := by
          have hmap : (f <$> main : OracleComp spec β) =
              (query t : OracleComp spec _) >>= fun u => (f <$> mx u : OracleComp spec β) := by
            rw [hmain_def]
            simp [map_bind]
          rw [hmap, probOutput_bind_eq_tsum]
        have hLHS_inner : ∀ (u : spec.Range t),
            ∑' p' : α × QueryLog spec,
              Pr[= p' | replayFirstRun (mx u)] *
                (h ([] : QueryLog spec) *
                  Pr[= y | (f <$> (pure p'.1 : OracleComp spec α) :
                    OracleComp spec β)]) =
            h ([] : QueryLog spec) * Pr[= y | (f <$> mx u : OracleComp spec β)] := fun u => by
          simp_rw [← mul_assoc, mul_comm _ (h ([] : QueryLog spec)), mul_assoc]
          rw [ENNReal.tsum_mul_left]
          refine congrArg _ ?_
          have hmap_mul := tsum_probOutput_map_mul (replayFirstRun (mx u))
            (Prod.fst : α × QueryLog spec → α)
            (fun a => Pr[= y | (f <$> (pure a : OracleComp spec α) :
              OracleComp spec β)])
          rw [← hmap_mul, fst_map_replayFirstRun]
          simp_rw [map_pure]
          rw [← probOutput_map_eq_tsum]
        have hRHS_inner : ∀ (u : spec.Range t),
            ∑' p' : α × QueryLog spec,
              Pr[= p' | replayFirstRun (mx u)] *
                (h ([] : QueryLog spec) *
                  Pr[= y | (f <$> main : OracleComp spec β)]) =
            h ([] : QueryLog spec) * Pr[= y | (f <$> main : OracleComp spec β)] := fun u => by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
        simp_rw [hLHS_inner, hRHS_inner]
        simp_rw [← mul_assoc, mul_comm _ (h ([] : QueryLog spec)), mul_assoc,
          ENNReal.tsum_mul_left]
        rw [← hfmain, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      | succ k =>
        simp_rw [fun (u : spec.Range t) (p' : α × QueryLog spec) =>
          QueryLog.takeBeforeForkAt_cons_self_succ (spec := spec) t u p'.2 k]
        have hreplay_step : ∀ (u : spec.Range t) (τ : QueryLog spec) (u' : spec.Range t),
            (f <$> Prod.fst <$> replayRunWithTraceValue main t
                ((⟨t, u⟩ : (i' : ι) × spec.Range i') :: τ) (k + 1) u' :
              OracleComp spec β) =
            (f <$> Prod.fst <$> replayRunWithTraceValue (mx u) t τ k u' :
              OracleComp spec β) := by
          intro u τ u'
          rw [hmain_def, fst_map_replayRunWithTraceValue_query_bind_cons_self_succ t mx u τ k u']
        have hPr_rhs : ∀ (u : spec.Range t) (p' : α × QueryLog spec),
            Pr[= y | f <$> Prod.fst <$> (do
              let u' ← liftComp ($ᵗ spec.Range t) spec
              replayRunWithTraceValue main t
                ((⟨t, u⟩ : (i' : ι) × spec.Range i') ::
                  QueryLog.takeBeforeForkAt p'.2 t k) (k + 1) u' :
                OracleComp spec (α × _))] =
            Pr[= y | f <$> Prod.fst <$> (do
              let u' ← liftComp ($ᵗ spec.Range t) spec
              replayRunWithTraceValue (mx u) t
                (QueryLog.takeBeforeForkAt p'.2 t k) k u' :
                OracleComp spec (α × _))] := by
          intro u p'
          rw [probOutput_map_fst_bind_liftComp_congr t f y _ _ fun u' => hreplay_step u _ u']
          simp only [map_bind]
        simp_rw [hPr_rhs]
        exact tsum_congr fun u => congrArg _ <|
          ih u k (fun τ => h ((⟨t, u⟩ : (i' : ι) × spec.Range i') :: τ))
    · simp_rw [fun (u : spec.Range t) (p' : α × QueryLog spec) =>
        QueryLog.takeBeforeForkAt_cons_of_ne (spec := spec) t u p'.2 i s h_ti]
      have hreplay_step : ∀ (u : spec.Range t) (τ : QueryLog spec) (u' : spec.Range i),
          (f <$> Prod.fst <$> replayRunWithTraceValue main i
              ((⟨t, u⟩ : (i' : ι) × spec.Range i') :: τ) s u' :
            OracleComp spec β) =
          (f <$> Prod.fst <$> replayRunWithTraceValue (mx u) i τ s u' :
            OracleComp spec β) := by
        intro u τ u'
        rw [hmain_def, fst_map_replayRunWithTraceValue_query_bind_cons_ne i t h_ti mx u τ s u']
      have hPr_rhs : ∀ (u : spec.Range t) (p' : α × QueryLog spec),
          Pr[= y | f <$> Prod.fst <$> (do
            let u' ← liftComp ($ᵗ spec.Range i) spec
            replayRunWithTraceValue main i
              ((⟨t, u⟩ : (i' : ι) × spec.Range i') ::
                QueryLog.takeBeforeForkAt p'.2 i s) s u' :
              OracleComp spec (α × _))] =
          Pr[= y | f <$> Prod.fst <$> (do
            let u' ← liftComp ($ᵗ spec.Range i) spec
            replayRunWithTraceValue (mx u) i
              (QueryLog.takeBeforeForkAt p'.2 i s) s u' :
              OracleComp spec (α × _))] := by
        intro u p'
        rw [probOutput_map_fst_bind_liftComp_congr i f y _ _ fun u' => hreplay_step u _ u']
        simp only [map_bind]
      simp_rw [hPr_rhs]
      exact tsum_congr fun u => congrArg _ <|
        ih u s (fun τ => h ((⟨t, u⟩ : (i' : ι) × spec.Range i') :: τ))

private lemma sq_probOutput_main_le_noGuardReplayComp [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= s | cf <$> main] ^ 2 ≤
      Pr[= (some (some s, some s) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          noGuardReplayComp main qb i cf s] := by
  classical
  set y : Option (Fin (qb i + 1)) := some s with hy_def
  set z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (y, y) with hz_def
  let Q : QueryLog spec → ℝ≥0∞ := fun τ =>
    Pr[= y | cf <$> Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i τ ↑s u : OracleComp spec (α × _))]
  let I : α → ℝ≥0∞ := fun x =>
    Pr[= y | (cf <$> (pure x : OracleComp spec α) :
      OracleComp spec (Option (Fin (qb i + 1))))]
  let w : α × QueryLog spec → ℝ≥0∞ := fun p => Pr[= p | replayFirstRun main]
  have hw_le_one : ∑' p, w p ≤ 1 := tsum_probOutput_le_one
  have hMain : (Pr[= y | cf <$> main] : ℝ≥0∞) = ∑' p, w p * I p.1 := by
    have h1 : (cf <$> main : OracleComp spec (Option (Fin (qb i + 1)))) =
        (fun p : α × QueryLog spec => cf p.1) <$> replayFirstRun main := by
      conv_lhs => rw [show main = Prod.fst <$> replayFirstRun main from
        (fst_map_replayFirstRun main).symm]
      simp only [Functor.map_map]
    rw [h1, probOutput_map_eq_tsum]
    refine tsum_congr fun p => ?_
    simp only [w, I, map_pure]
  have hMainTake : (Pr[= y | cf <$> main] : ℝ≥0∞) =
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) := by
    have hB1h := tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt
      (main := main) (i := i) (s := (↑s : ℕ)) (f := cf) (y := y) (h := fun _ => (1 : ℝ≥0∞))
    simp only [one_mul] at hB1h
    exact hMain.trans hB1h
  have hJensen :
      (∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) ^ 2 ≤
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w (fun p => Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) hw_le_one
  have hEq2 :
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 =
      ∑' p, w p * (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) * I p.1) := by
    have hB1h := tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt
      (main := main) (i := i) (s := (↑s : ℕ)) (f := cf) (y := y) (h := Q)
    have hsq_eq : ∀ p : α × QueryLog spec,
        w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 =
        Pr[= p | replayFirstRun main] *
          (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) *
            Pr[= y | cf <$> Prod.fst <$> (do
              let u ← liftComp ($ᵗ spec.Range i) spec
              replayRunWithTraceValue main i
                (QueryLog.takeBeforeForkAt p.2 i ↑s) ↑s u :
                  OracleComp spec (α × _))]) := fun p => by
      simp only [sq, w, Q]
    exact (tsum_congr hsq_eq).trans hB1h.symm
  have hFactor : Pr[= z | noGuardReplayComp main qb i cf s] =
      ∑' p, w p * (I p.1 * Q p.2) := by
    simp only [noGuardReplayComp, z, hz_def, y]
    rw [probOutput_bind_eq_tsum]
    refine tsum_congr fun p => ?_
    congr 1
    have hinner :
        (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          let q ← replayRunWithTraceValue main i p.2 ↑s u
          return some (cf p.1, cf q.1) :
            OracleComp spec (Option (Option (Fin (qb i + 1)) ×
              Option (Fin (qb i + 1))))) =
        some <$> ((cf p.1, ·) <$> (cf <$> Prod.fst <$> (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          replayRunWithTraceValue main i p.2 ↑s u))) := by
        simp [monad_norm]
    rw [hinner, probOutput_some_map_some, probOutput_prod_mk_snd_map]
    change (if (some s, some s).1 = cf p.1 then
        Pr[= (some s, some s).2 | (cf <$> Prod.fst <$> (do
          let u ← liftComp ($ᵗ spec.Range i) spec
          replayRunWithTraceValue main i p.2 ↑s u) :
            OracleComp spec (Option (Fin (qb i + 1))))] else 0) =
      I p.1 * Q p.2
    classical
    by_cases hp : cf p.1 = y
    · have h_eq : y = cf p.1 := hp.symm
      rw [if_pos h_eq]
      have hI : I p.1 = 1 := by
        simp only [I, map_pure, probOutput_pure]
        rw [if_pos hp.symm]
      rw [hI, one_mul]
    · have h_ne : y ≠ cf p.1 := fun h => hp h.symm
      rw [if_neg h_ne]
      have hI : I p.1 = 0 := by
        simp only [I, map_pure, probOutput_pure]
        rw [if_neg (fun h => hp h.symm)]
      rw [hI, zero_mul]
  have hFactorTrunc : Pr[= z | noGuardReplayComp main qb i cf s] =
      ∑' p, w p * (I p.1 * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) := by
    rw [hFactor]
    refine tsum_congr fun p => ?_
    congr 1
    congr 1
    simp only [Q]
    have hB1a := probOutput_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
      (main := main) (i := i) (log := p.2) (s := (↑s : ℕ))
    rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
    refine tsum_congr fun a => ?_
    rw [hB1a]
  have hfinal : (Pr[= y | cf <$> main] : ℝ≥0∞) ^ 2 ≤
      Pr[= z | noGuardReplayComp main qb i cf s] := by
    calc (Pr[= y | cf <$> main] : ℝ≥0∞) ^ 2
        = (∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) ^ 2 := by rw [hMainTake]
      _ ≤ ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 := hJensen
      _ = ∑' p, w p * (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) * I p.1) := hEq2
      _ = ∑' p, w p * (I p.1 * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) := by
            simp_rw [mul_comm (Q _) (I _)]
      _ = Pr[= z | noGuardReplayComp main qb i cf s] := hFactorTrunc.symm
  simpa only [hy_def, hz_def] using hfinal

omit [unifSpec ˡ⊂ₒ spec] in
private lemma noGuardReplayComp_le_forkReplay_add_collisionReplay [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : CfReachable main qb i cf) (s : Fin (qb i + 1)) :
    Pr[= (some (some s, some s) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          noGuardReplayComp main qb i cf s] ≤
      Pr[= (some (some s, some s) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          (fun r : Option (α × α) => r.map (Prod.map cf cf)) <$>
            forkReplay main qb i cf] +
      Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s] := by
  classical
  set z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
  set f : Option (α × α) → Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) :=
    fun r => r.map (Prod.map cf cf)
  show Pr[= z | noGuardReplayComp main qb i cf s] ≤
    Pr[= z | f <$> forkReplay main qb i cf] +
      Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s]
  simp only [noGuardReplayComp, collisionReplayComp, forkReplay, map_bind]
  refine (probOutput_bind_congr_le_add
    (mx := (replayFirstRun main : OracleComp spec (α × QueryLog spec)))
    (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
  intro p hp
  by_cases hcf_s : cf p.1 = some s
  · obtain ⟨logged, hlogged⟩ := Option.isSome_iff_exists.mp (hreach hp s hcf_s)
    simp only [hcf_s, map_bind]
    refine (probOutput_bind_congr_le_add
      (mx := (liftComp ($ᵗ spec.Range i) spec : OracleComp spec (spec.Range i)))
      (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
    intro u _hu
    have hforkUnfold :
        (fun r : Option (α × α) => r.map (Prod.map cf cf)) <$>
          forkReplayWithTraceValue main qb i cf p u =
        (if logged = u then
            (pure none : OracleComp spec (Option (Option (Fin (qb i + 1)) ×
              Option (Fin (qb i + 1)))))
          else
            replayRunWithTraceValue main i p.2 ↑s u >>= fun q =>
              if q.2.mismatch || !q.2.forkConsumed then pure none
              else if cf q.1 = some s then pure (some (some s, cf q.1))
              else pure none) := by
      unfold forkReplayWithTraceValue
      simp only [hcf_s, hlogged]
      split_ifs with hcoll
      · simp [map_pure]
      · rw [map_bind]
        congr 1
        ext q
        split_ifs with _ _ <;> simp [hcf_s]
    have hcollUnfold :
        (if QueryLog.getQueryValue? p.2 i ↑s = some u then
            (return (some s : Option (Fin (qb i + 1))) : OracleComp spec _)
          else return none) =
        (if logged = u then
            (return (some s : Option (Fin (qb i + 1))) : OracleComp spec _)
          else return none) := by
      by_cases hcoll : logged = u
      · simp [hlogged, hcoll]
      · have hne : QueryLog.getQueryValue? p.2 i ↑s ≠ some u := by
          rw [hlogged]
          exact fun habs => hcoll (Option.some_inj.mp habs)
        simp [hne, hcoll]
    rw [hforkUnfold, hcollUnfold]
    by_cases hcoll : logged = u
    · rw [if_pos hcoll, if_pos hcoll]
      calc Pr[= z | do
            let _q ← replayRunWithTraceValue main i p.2 ↑s u
            (pure (some (some s, cf _q.1)) : OracleComp spec _)]
          ≤ 1 := probOutput_le_one
        _ = 0 + 1 := by ring
        _ = Pr[= z | (pure none :
                OracleComp spec (Option (Option (Fin (qb i + 1)) ×
                  Option (Fin (qb i + 1)))))] +
            Pr[= (some s : Option (Fin (qb i + 1))) |
              (return some s : OracleComp spec _)] := by
          simp [z]
    · rw [if_neg hcoll, if_neg hcoll]
      have hstate : ∀ {q : α × ReplayForkState spec i},
          q ∈ support (replayRunWithTraceValue main i p.2 ↑s u) →
          q.2.mismatch = false ∧ q.2.forkConsumed = true :=
        fun hq => replayRunWithTraceValue_state_correct main qb i cf hp hcf_s hreach u hq
      have hL_eq :
          Pr[= z | do
            let q ← replayRunWithTraceValue main i p.2 ↑s u
            (pure (some (some s, cf q.1)) : OracleComp spec _)] =
          Pr[ fun q : α × ReplayForkState spec i => cf q.1 = some s |
                replayRunWithTraceValue main i p.2 ↑s u] := by
        rw [probEvent_eq_tsum_ite, probOutput_bind_eq_tsum]
        refine tsum_congr fun q => ?_
        simp only [probOutput_pure_eq_indicator, Set.indicator_apply,
          Set.mem_singleton_iff, Function.const_apply, z]
        by_cases hq : cf q.1 = some s <;> simp [hq, eq_comm]
      have hR_eq :
          Pr[= z |
            (replayRunWithTraceValue main i p.2 ↑s u >>= fun q =>
              if q.2.mismatch || !q.2.forkConsumed then
                (pure none : OracleComp spec (Option (Option (Fin (qb i + 1)) ×
                  Option (Fin (qb i + 1)))))
              else if cf q.1 = some s then pure (some (some s, cf q.1))
              else pure none)] =
          Pr[ fun q : α × ReplayForkState spec i => cf q.1 = some s |
                replayRunWithTraceValue main i p.2 ↑s u] := by
        rw [probEvent_eq_tsum_ite, probOutput_bind_eq_tsum]
        refine tsum_congr fun q => ?_
        by_cases hqmem : q ∈ support (replayRunWithTraceValue main i p.2 ↑s u)
        · obtain ⟨hmm, hfc⟩ := hstate hqmem
          simp only [hmm, hfc, Bool.or_false, Bool.not_true]
          by_cases hq : cf q.1 = some s <;> simp [hq, z]
        · have hzero : Pr[= q | replayRunWithTraceValue main i p.2 ↑s u] = 0 :=
            probOutput_eq_zero_of_not_mem_support hqmem
          rw [hzero]
          split_ifs <;> simp
      rw [hL_eq, hR_eq]
      exact le_add_of_nonneg_right (zero_le)
  · have hL :
        Pr[= z | do
          let _u ← liftComp ($ᵗ spec.Range i) spec
          let q ← replayRunWithTraceValue main i p.2 ↑s _u
          (pure (some (cf p.1, cf q.1)) : OracleComp spec _)] = 0 := by
      rw [probOutput_eq_zero_iff]
      intro hmem
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        z] at hmem
      obtain ⟨_, _, _, _, hh⟩ := hmem
      exact hcf_s (Prod.mk.inj (Option.some.inj hh)).1.symm
    rw [hL]
    exact zero_le

private theorem le_probOutput_forkReplay [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : CfReachable main qb i cf) (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h
      ≤ Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) |
          forkReplay main qb i cf] := by
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  rw [probEvent_forkReplay_fst_eq_probEvent_pair
        (main := main) (qb := qb) (i := i) (cf := cf)]
  let f : Option (α × α) → Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) :=
    fun r => r.map (Prod.map cf cf)
  let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
  have hRhsEq :
      Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) | forkReplay main qb i cf] =
        Pr[= z | f <$> forkReplay main qb i cf] := by
    calc
      Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) | forkReplay main qb i cf]
          = Pr[ fun r => f r = z | forkReplay main qb i cf] := by simp [f, z]
      _ = Pr[ fun x => x = z | f <$> forkReplay main qb i cf] := by
            simpa [Function.comp] using
              (probEvent_map (mx := forkReplay main qb i cf) (f := f)
                (q := fun x : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) =>
                  x = z)).symm
      _ = Pr[= z | f <$> forkReplay main qb i cf] := by
            simp [probEvent_eq_eq_probOutput
              (mx := f <$> forkReplay main qb i cf) (x := z)]
  rw [hRhsEq]
  have hCollision := probOutput_collisionReplay_le_main_div
    (main := main) (qb := qb) (i := i) (cf := cf) s
  have hLhsCollision :
      Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h ≤
        Pr[= s | cf <$> main] ^ 2 -
          Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s] :=
    tsub_le_tsub_left (by simpa [h] using hCollision) (Pr[= s | cf <$> main] ^ 2)
  refine le_trans hLhsCollision ?_
  have hNoGuardGeSquare := sq_probOutput_main_le_noGuardReplayComp
    (main := main) (qb := qb) (i := i) (cf := cf) s
  have hNoGuardLeAdd := noGuardReplayComp_le_forkReplay_add_collisionReplay
    (main := main) (qb := qb) (i := i) (cf := cf) hreach s
  have hNoGuardMinusLeRhs :
      Pr[= z | noGuardReplayComp main qb i cf s] -
          Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s] ≤
        Pr[= z | f <$> forkReplay main qb i cf] :=
    (tsub_le_iff_right).2 (by simpa [z, f] using hNoGuardLeAdd)
  exact le_trans
    (tsub_le_tsub_right (by simpa [z] using hNoGuardGeSquare)
      (Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s]))
    hNoGuardMinusLeRhs

omit [spec.DecidableEq] [∀ i, SampleableType (spec.Range i)] [unifSpec ⊂ₒ spec] in
private theorem forkReplay_precondition_le_one [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤ 1 :=
  seededFork_precondition_le_one main qb i cf

omit [unifSpec ˡ⊂ₒ spec] in
private lemma sum_probEvent_forkReplay_le_tsum_some [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    ∑ s : Fin (qb i + 1),
      Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) | forkReplay main qb i cf]
    ≤ ∑' (p : α × α), Pr[= some p | forkReplay main qb i cf] := by
  classical
  simp_rw [probEvent_eq_tsum_ite]
  have hsplit : ∀ s : Fin (qb i + 1),
      (∑' (r : Option (α × α)),
        if r.map (cf ∘ Prod.fst) = some (some s) then
          Pr[= r | forkReplay main qb i cf] else 0)
      = ∑' (p : α × α),
          if cf p.1 = some s then Pr[= some p | forkReplay main qb i cf] else 0 := by
    intro s
    simpa only [Option.map, comp_apply, reduceCtorEq, ite_false, zero_add,
      Option.some.injEq] using tsum_option (fun r : Option (α × α) =>
        if r.map (cf ∘ Prod.fst) = some (some s) then
          Pr[= r | forkReplay main qb i cf] else 0) ENNReal.summable
  simp_rw [hsplit]
  rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [tsum_fintype (L := .unconditional _)]
  rcases hcf : cf p.1 with _ | s₀
  · simp
  · rw [Finset.sum_eq_single s₀ (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
    simp

private theorem probOutput_none_forkReplay_le [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (hreach : CfReachable main qb i cf) :
    let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.Range i)
    let q := qb i + 1
    Pr[= none | forkReplay main qb i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  simp only
  set ps : Fin (qb i + 1) → ℝ≥0∞ := fun s => Pr[= (some s : Option _) | cf <$> main]
  set acc := ∑ s, ps s
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hacc_ne_top : acc ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top
      (sum_probOutput_some_le_one (mx := cf <$> main) (α := Fin (qb i + 1)))
  have htotal := probOutput_none_add_tsum_some (mx := forkReplay main qb i cf)
  rw [probFailure_of_liftM_PMF, tsub_zero] at htotal
  have hne_top : (∑' p, Pr[= some p | forkReplay main qb i cf]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (htotal ▸ le_add_self)
  have hPr_eq : Pr[= none | forkReplay main qb i cf] =
      1 - ∑' p, Pr[= some p | forkReplay main qb i cf] :=
    ENNReal.eq_sub_of_add_eq hne_top htotal
  calc Pr[= none | forkReplay main qb i cf]
    _ = 1 - ∑' p, Pr[= some p | forkReplay main qb i cf] := hPr_eq
    _ ≤ 1 - ∑ s, Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) |
            forkReplay main qb i cf] :=
        tsub_le_tsub_left (sum_probEvent_forkReplay_le_tsum_some main qb i cf) 1
    _ ≤ 1 - ∑ s, (ps s ^ 2 - ps s / h) :=
        tsub_le_tsub_left (Finset.sum_le_sum fun s _ =>
          le_probOutput_forkReplay main qb i cf hreach s) 1
    _ ≤ 1 - acc * (acc / ↑(qb i + 1) - h⁻¹) := by
        apply tsub_le_tsub_left _ 1
        have hcs := ENNReal.sq_sum_le_card_mul_sum_sq
          (Finset.univ : Finset (Fin (qb i + 1))) ps
        simp only [Finset.card_univ, Fintype.card_fin] at hcs
        calc acc * (acc / ↑(qb i + 1) - h⁻¹)
          _ = acc * (acc / ↑(qb i + 1)) - acc * h⁻¹ :=
              ENNReal.mul_sub (fun _ _ => hacc_ne_top)
          _ = acc ^ 2 / ↑(qb i + 1) - acc / h := by
              rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, sq, div_eq_mul_inv]
          _ ≤ (∑ s, ps s ^ 2) - acc / h := by
              gcongr
              rw [div_eq_mul_inv]
              have hn : ((qb i + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
              calc acc ^ 2 * (↑(qb i + 1))⁻¹
                  _ ≤ (↑(qb i + 1) * ∑ s, ps s ^ 2) * (↑(qb i + 1))⁻¹ := by gcongr
                  _ = ∑ s, ps s ^ 2 := by
                      rw [mul_assoc, mul_comm (∑ s, ps s ^ 2) _, ← mul_assoc,
                        ENNReal.mul_inv_cancel hn (by simp), one_mul]
          _ ≤ (∑ s, ps s ^ 2) - ∑ s, ps s / h := by
              gcongr
              simp_rw [div_eq_mul_inv]
              rw [← Finset.sum_mul]
          _ ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
              rw [tsub_le_iff_right]
              calc ∑ s, ps s ^ 2
                ≤ ∑ s, ((ps s ^ 2 - ps s / h) + ps s / h) :=
                    Finset.sum_le_sum fun s _ => le_tsub_add
                _ = ∑ s, (ps s ^ 2 - ps s / h) + ∑ s, ps s / h :=
                    Finset.sum_add_distrib

/-- Packaged replay forking theorem. -/
theorem le_probEvent_isSome_forkReplay [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (hreach : CfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr[ fun r : Option (α × α) => r.isSome | forkReplay main qb i cf] := by
  rw [probEvent_isSome_eq_one_sub_probOutput_none (mx := forkReplay main qb i cf)]
  have hpre_le_one :=
    forkReplay_precondition_le_one (main := main) (qb := qb) (i := i) (cf := cf)
  have hpre_ne_top :
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹)) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top hpre_le_one
  have hnone_ne_top : Pr[= none | forkReplay main qb i cf] ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top probOutput_le_one
  have hfork :
      Pr[= none | forkReplay main qb i cf] +
          (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
           let h : ℝ≥0∞ := Fintype.card (spec.Range i)
           let q := qb i + 1
           acc * (acc / q - h⁻¹)) ≤ 1 :=
    (ENNReal.le_sub_iff_add_le_right hpre_ne_top hpre_le_one).1
      (probOutput_none_forkReplay_le (main := main) (qb := qb) (i := i) (cf := cf) hreach)
  exact (ENNReal.le_sub_iff_add_le_right hnone_ne_top probOutput_le_one).2
    (by simpa [add_comm] using hfork)

omit [unifSpec ˡ⊂ₒ spec] in
/-- Structural success facts for `forkReplay`. -/
theorem forkReplay_success_log_props [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (forkReplay main qb i cf)) :
    ∃ (log₁ log₂ : QueryLog spec) (s : Fin (qb i + 1)),
      (x₁, log₁) ∈ support (replayFirstRun main) ∧
      (x₂, log₂) ∈ support (replayFirstRun main) ∧
      cf x₁ = some s ∧
      cf x₂ = some s ∧
      QueryLog.getQueryValue? log₁ i ↑s ≠ QueryLog.getQueryValue? log₂ i ↑s ∧
      ∃ (replacement : spec.Range i) (st : ReplayForkState spec i),
        (x₂, st) ∈ support (replayRunWithTraceValue main i log₁ ↑s replacement) ∧
        st.observed = log₂ ∧
        st.mismatch = false ∧
        st.forkConsumed = true ∧
        (∀ n, n < st.cursor →
          QueryLog.inputAt? log₂ n = QueryLog.inputAt? log₁ n) := by
  simp only [forkReplay] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨first, hfirst, h⟩ := h
  rcases hcf : cf first.1 with _ | s
  · simp_all
  · simp only [hcf] at h
    rw [mem_support_bind_iff] at h
    obtain ⟨u, -, h⟩ := h
    simp only [forkReplayWithTraceValue, hcf] at h
    rcases hq : QueryLog.getQueryValue? first.2 i ↑s with _ | logged
    · simp_all
    · simp only [hq] at h
      split_ifs at h with heq
      · simp_all
      · rw [mem_support_bind_iff] at h
        obtain ⟨z, hz, h⟩ := h
        split_ifs at h with hbad hcf₂
        · simp_all
        · rw [mem_support_pure_iff] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hbad' : (z.2.mismatch || !z.2.forkConsumed) = false :=
            Bool.not_eq_true _ |>.mp hbad
          have hmismatch_false : z.2.mismatch = false :=
            (Bool.or_eq_false_iff.mp hbad').1
          have hforkConsumed : z.2.forkConsumed = true := by
            simpa using (Bool.or_eq_false_iff.mp hbad').2
          have htrace : z.2.trace = first.2 :=
            replayRunWithTraceValue_trace_eq (main := main) (i := i) (trace := first.2)
              (forkQuery := ↑s) (replacement := u) hz
          refine ⟨first.2, z.2.observed, s, ?_, ?_, hcf, hcf₂, ?_,
            u, z.2, ?_, rfl, hmismatch_false, hforkConsumed, ?_⟩
          · simpa using hfirst
          · exact replayRunWithTraceValue_mem_support_replayFirstRun
              (main := main) (i := i) (trace := first.2) (forkQuery := ↑s)
              (replacement := u) hz
          · have hrhs := replayRunWithTraceValue_getQueryValue?_observed_eq_replacement
              (main := main) (i := i) (trace := first.2) (forkQuery := ↑s)
              (replacement := u) hz hforkConsumed
            rw [hq, hrhs]
            intro habs
            exact heq (Option.some.inj habs)
          · exact hz
          · intro n hn
            have := replayRunWithTraceValue_prefix_input_eq
              (main := main) (i := i) (trace := first.2) (forkQuery := ↑s)
              (replacement := u) hz hn
            rw [htrace] at this
            exact this
        · simp at h

omit [unifSpec ˡ⊂ₒ spec] in
/-- Transfer logged-run postconditions through a successful replay fork. -/
theorem forkReplay_propertyTransfer [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (P_out : α → QueryLog spec → Prop)
    (hP : ∀ {x log}, (x, log) ∈ support (replayFirstRun main) → P_out x log)
    {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (forkReplay main qb i cf)) :
    ∃ (log₁ log₂ : QueryLog spec) (s : Fin (qb i + 1)),
      cf x₁ = some s ∧
      cf x₂ = some s ∧
      P_out x₁ log₁ ∧
      P_out x₂ log₂ ∧
      QueryLog.getQueryValue? log₁ i ↑s ≠ QueryLog.getQueryValue? log₂ i ↑s := by
  rcases forkReplay_success_log_props
      (main := main) (qb := qb) (i := i) (cf := cf) h with
    ⟨log₁, log₂, s, hx₁, hx₂, hcf₁, hcf₂, hneq, replacement, st, hz, hlog₂, hmismatch,
      hfork, hprefix⟩
  exact ⟨log₁, log₂, s, hcf₁, hcf₂, hP hx₁, hP (by simpa [hlog₂] using hx₂), hneq⟩

end quantitative

end OracleComp
