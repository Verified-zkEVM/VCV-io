/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SeededFork
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

namespace QueryLog

variable {ι : Type} {spec : OracleSpec ι}

/-- The query input at position `n` in the full interleaved log, if it exists. -/
def inputAt? (log : QueryLog spec) (n : Nat) : Option ι :=
  (fun x => x.1) <$> log[n]?

/-- The `n`-th answer in the log for queries to oracle `t`, if it exists. -/
def getQueryValue? [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat) :
    Option (spec.Range t) := by
  match (log.getQ (· = t))[n]? with
  | none => exact none
  | some ⟨t', u⟩ =>
      if h : t' = t then
        exact some (by cases h; exact u)
      else
        exact none

@[simp]
lemma inputAt?_logQuery_of_lt (log : QueryLog spec) (t : ι) (u : spec.Range t) {n : Nat}
    (hn : n < log.length) :
    inputAt? (log.logQuery t u) n = inputAt? log n := by
  unfold inputAt? QueryLog.logQuery QueryLog.singleton
  rw [List.getElem?_append_left hn]

@[simp]
lemma inputAt?_logQuery_self (log : QueryLog spec) (t : ι) (u : spec.Range t) :
    inputAt? (log.logQuery t u) log.length = some t := by
  unfold inputAt? QueryLog.logQuery QueryLog.singleton
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

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
  unfold getQueryValue? at h
  generalize hlk : (log.getQ (· = t))[n]? = opt at h
  match opt, hlk, h with
  | none, _, h => simp at h
  | some ⟨t', u'⟩, _, h =>
      by_cases ht : t' = t
      · subst ht
        simp only [↓reduceDIte, Option.some.injEq] at h
        subst h
        rfl
      · simp [ht] at h

/-- Converse: if the `n`-th `t`-filtered entry is `⟨t, u⟩`, then
`getQueryValue? log t n = some u`. -/
lemma getQueryValue?_eq_some_of_getQ_getElem? [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : (log.getQ (· = t))[n]? = some ⟨t, u⟩) :
    getQueryValue? log t n = some u := by
  unfold getQueryValue?
  rw [h]
  simp

/-- Every entry of `log.getQ (· = t)` has its first component equal to `t`. -/
lemma getQ_eq_mem [spec.DecidableEq] (log : QueryLog spec) (t : ι)
    {entry : (t' : ι) × spec.Range t'} (h : entry ∈ log.getQ (· = t)) :
    entry.1 = t := by
  induction log with
  | nil => simp [QueryLog.getQ] at h
  | cons hd tl ih =>
      simp only [QueryLog.getQ_cons] at h
      by_cases hh : hd.1 = t
      · simp only [hh, ↓reduceIte, List.mem_cons] at h
        rcases h with rfl | h
        · exact hh
        · exact ih h
      · simp only [hh, ↓reduceIte] at h
        exact ih h

/-- If the `t`-filtered log has at least `n + 1` entries, then `getQueryValue? log t n`
is `some _`. -/
lemma getQueryValue?_isSome_of_lt [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat)
    (h : n < (log.getQ (· = t)).length) :
    (getQueryValue? log t n).isSome := by
  unfold getQueryValue?
  have hopt : (log.getQ (· = t))[n]? = some ((log.getQ (· = t))[n]'h) :=
    List.getElem?_eq_getElem h
  have hentry := List.getElem_mem h (l := log.getQ (· = t))
  have ht' : ((log.getQ (· = t))[n]'h).1 = t := getQ_eq_mem log t hentry
  rw [hopt]
  set entry := (log.getQ (· = t))[n]'h
  obtain ⟨t', u'⟩ := entry
  simp only at ht'
  subst ht'
  simp

/-- Prepending an entry whose oracle index does not match `t` leaves the `t`-indexed
view of the log unchanged. -/
lemma getQueryValue?_cons_of_ne [spec.DecidableEq]
    (entry : (t' : ι) × spec.Range t') (log : QueryLog spec) (t : ι) (n : Nat)
    (h : entry.1 ≠ t) :
    getQueryValue? (entry :: log) t n = getQueryValue? log t n := by
  unfold getQueryValue?
  rw [QueryLog.getQ_cons]
  simp [h]

/-- The first entry of `getQueryValue? (⟨t, u⟩ :: log) t 0` is the prepended value. -/
lemma getQueryValue?_cons_self_zero [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) :
    getQueryValue? (⟨t, u⟩ :: log) t 0 = some u := by
  apply getQueryValue?_eq_some_of_getQ_getElem?
  rw [QueryLog.getQ_cons]
  simp

/-- Prepending a matching `⟨t, _⟩` entry shifts later `t`-indexed lookups by one. -/
lemma getQueryValue?_cons_self_succ [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) (n : Nat) :
    getQueryValue? (⟨t, u⟩ :: log) t (n + 1) = getQueryValue? log t n := by
  unfold getQueryValue?
  rw [QueryLog.getQ_cons]
  simp

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
  cases s with
  | zero => simp [takeBeforeForkAt, h]
  | succ s => simp [takeBeforeForkAt, h]

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
        | zero => rw [takeBeforeForkAt_cons_self_zero]; simp [QueryLog.countQ]
        | succ s =>
            rw [takeBeforeForkAt_cons_self_succ]
            simp only [QueryLog.countQ, QueryLog.getQ_cons, ↓reduceIte, List.length_cons]
            have := ih s
            simp only [QueryLog.countQ] at this
            omega
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ h]
        simp only [QueryLog.countQ, QueryLog.getQ_cons]
        rw [if_neg h]
        simpa [QueryLog.countQ] using ih s

/-- If `log` contains at least `s + 1` queries to `i`, then `takeBeforeForkAt log i s` has
exactly `s` queries to `i`. -/
lemma countQ_takeBeforeForkAt_eq [spec.DecidableEq]
    (log : QueryLog spec) (i : ι) (s : ℕ)
    (h : s < (log.getQ (· = i)).length) :
    (takeBeforeForkAt log i s).countQ (· = i) = s := by
  induction log generalizing s with
  | nil => simp [QueryLog.getQ] at h
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      by_cases ht : t = i
      · subst ht
        cases s with
        | zero => rw [takeBeforeForkAt_cons_self_zero]; simp [QueryLog.countQ, QueryLog.getQ]
        | succ s =>
            rw [takeBeforeForkAt_cons_self_succ]
            simp only [QueryLog.countQ, QueryLog.getQ_cons, ↓reduceIte, List.length_cons]
            have h' : s < (QueryLog.getQ tl (· = t)).length := by
              simp only [QueryLog.getQ_cons, ↓reduceIte, List.length_cons] at h
              omega
            have := ih s h'
            simp only [QueryLog.countQ] at this
            omega
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ ht]
        simp only [QueryLog.countQ, QueryLog.getQ_cons]
        rw [if_neg ht]
        simp only [QueryLog.getQ_cons] at h
        rw [if_neg ht] at h
        simpa [QueryLog.countQ] using ih s h

/-- `takeBeforeForkAt log i s` is a prefix of `log`. -/
lemma takeBeforeForkAt_prefix [spec.DecidableEq]
    (log : QueryLog spec) (i : ι) (s : ℕ) :
    (takeBeforeForkAt log i s) <+: log := by
  induction log generalizing s with
  | nil => simp
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      by_cases h : t = i
      · subst h
        cases s with
        | zero =>
            rw [takeBeforeForkAt_cons_self_zero]
            exact List.nil_prefix
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
  have h := countQ_takeBeforeForkAt_le log i s
  simp only [QueryLog.countQ] at h
  have hnone : ((takeBeforeForkAt log i s).getQ (· = i))[s]? = none := by
    rw [List.getElem?_eq_none_iff]
    exact h
  rw [hnone]

/-- If `log` has at most `s` entries of type `i`, then truncating `log` at position `s`
leaves it unchanged: there is no `s`-th `i`-entry to truncate before. -/
lemma takeBeforeForkAt_of_getQ_length_le [spec.DecidableEq]
    (log : QueryLog spec) (i : ι) (s : ℕ)
    (h : (log.getQ (· = i)).length ≤ s) :
    takeBeforeForkAt log i s = log := by
  induction log generalizing s with
  | nil => simp
  | cons entry tl ih =>
      obtain ⟨t, u⟩ := entry
      by_cases ht : t = i
      · subst ht
        cases s with
        | zero =>
            simp only [QueryLog.getQ_cons, ↓reduceIte, List.length_cons, Nat.le_zero] at h
            omega
        | succ s =>
            rw [takeBeforeForkAt_cons_self_succ]
            have h' : (QueryLog.getQ tl (· = t)).length ≤ s := by
              simp only [QueryLog.getQ_cons, ↓reduceIte, List.length_cons] at h
              omega
            rw [ih s h']
      · rw [takeBeforeForkAt_cons_of_ne _ _ _ _ _ ht]
        have h' : (QueryLog.getQ tl (· = i)).length ≤ s := by
          simp only [QueryLog.getQ_cons] at h
          rw [if_neg ht] at h
          exact h
        rw [ih s h']

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
  (simulateQ (loggingOracle (spec := spec)) main).run

@[simp]
lemma fst_map_replayFirstRun (main : OracleComp spec α) :
    Prod.fst <$> replayFirstRun main = main := by
  simpa [replayFirstRun, OracleComp.withQueryLog, loggingOracle] using
    (loggingOracle.fst_map_run_simulateQ (spec := spec) main)

@[simp]
lemma probEvent_fst_replayFirstRun [spec.Fintype] [spec.Inhabited]
    (main : OracleComp spec α) (p : α → Prop) :
    Pr[ fun z => p z.1 | replayFirstRun main] = Pr[ p | main] := by
  simp [replayFirstRun]

@[simp]
lemma probOutput_fst_map_replayFirstRun [spec.Fintype] [spec.Inhabited]
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
    ∀ (st : ReplayForkState spec i),
      (st.forkConsumed = true ∨ st.mismatch = true) →
      (Prod.fst <$> (simulateQ (replayOracle i) main).run st :
        OracleComp spec α) = main := by
  induction main using OracleComp.inductionOn with
  | pure x => intro st _; simp
  | query_bind t oa ih =>
    intro st hst
    have hlive : (st.forkConsumed || st.mismatch) = true := by
      rcases hst with h | h <;> simp [h]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    -- Unfold the oracle at `t` using the live branch.
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
    -- `Prod.fst <$> (do u ← query t; let st' := noteObserved; (simulateQ ...).run st')`
    --   = `do u ← query t; Prod.fst <$> (simulateQ ...).run (noteObserved st u)`
    -- By IH applied to `noteObserved st u` (still in live mode), the inner
    -- `Prod.fst <$> ...` equals `oa u`.
    have hst' : ∀ u : spec.Range t,
        (st.noteObserved t u).forkConsumed = true ∨
          (st.noteObserved t u).mismatch = true := by
      intro u
      rcases hst with h | h
      · left; simpa [ReplayForkState.noteObserved] using h
      · right; simpa [ReplayForkState.noteObserved] using h
    calc (Prod.fst <$> (do
            let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
            (simulateQ (replayOracle i) (oa u)).run (st.noteObserved t u))
            : OracleComp spec α)
        = (do
            let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
            Prod.fst <$> (simulateQ (replayOracle i) (oa u)).run
              (st.noteObserved t u)) := by
          simp [map_bind]
      _ = (do
            let u : spec.Range t ← monadLift (query t : OracleComp spec (spec.Range t))
            oa u) := by
          refine bind_congr fun u => ?_
          exact ih u (st.noteObserved t u) (hst' u)
      _ = (liftM (query t) >>= fun u => oa u : OracleComp spec α) := rfl

/-- α-marginal form of `fst_map_simulateQ_replayOracle_of_live`, specialized to the
`evalDist` level. Once in live mode, the α-output distribution of the replay run is
`evalDist main`. -/
lemma evalDist_fst_map_simulateQ_replayOracle_of_live [spec.DecidableEq]
    [spec.Fintype] [spec.Inhabited]
    (i : ι) (main : OracleComp spec α) (st : ReplayForkState spec i)
    (hst : st.forkConsumed = true ∨ st.mismatch = true) :
    evalDist (Prod.fst <$> (simulateQ (replayOracle i) main).run st :
      OracleComp spec α) = evalDist main := by
  rw [fst_map_simulateQ_replayOracle_of_live i main st hst]

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
      exfalso
      have hfc' : st.forkConsumed = false := by
        simpa [ReplayForkState.noteObserved] using hfc
      have hm' : st.mismatch = false := by
        simpa [ReplayForkState.noteObserved] using hm
      simp [hfc', hm'] at hlive
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
      exfalso
      have hfc' : st.forkConsumed = false := by
        simpa [ReplayForkState.noteObserved] using hfc
      have hm' : st.mismatch = false := by
        simpa [ReplayForkState.noteObserved] using hm
      simp [hfc', hm'] at hlive
    · intro hfc
      have hfc' : st.forkConsumed = true := by
        simpa [ReplayForkState.noteObserved] using hfc
      -- new observed = st.observed ++ [⟨t, u⟩], cursor unchanged.
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
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcursorTrace
        · simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch,
            QueryLog.logQuery, QueryLog.singleton] using
            (Nat.le_trans hcursorObs (Nat.le_succ (List.length st.observed)))
        · intro n hn
          have hnobs : n < st.observed.length := lt_of_lt_of_le hn hcursorObs
          calc
            QueryLog.inputAt? (st.markMismatch.noteObserved t u).observed n
              = QueryLog.inputAt? st.observed n := by
                  simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using
                    (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := t) (u := u)
                      (n := n) hnobs)
            _ = QueryLog.inputAt? st.trace n := hprefix n hn
        · intro hfc hm
          exfalso
          simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch] at hm
        · intro hfc
          exfalso
          have hfc' : st.forkConsumed = true := by
            simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using hfc
          simp [hflags.1] at hfc'
        · intro n hn
          have hn' : n < st.cursor := by
            simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch, hflags.1]
              using hn
          have hnobs : n < st.observed.length := Nat.lt_of_lt_of_le hn' hcursorObs
          change (st.observed.logQuery t u)[n]? = st.trace[n]?
          rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
          have : n < (if st.forkConsumed then st.cursor - 1 else st.cursor) := by
            rw [hflags.1]; simpa using hn'
          exact hvalues n this
        · intro hfc hm
          exfalso
          simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch] at hm
        · intro hfc
          exfalso
          have hfc' : st.forkConsumed = true := by
            simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using hfc
          simp [hflags.1] at hfc'
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
                have : n < (if st.forkConsumed then st.cursor - 1 else st.cursor) := by
                  rw [hflags.1]; simpa using hn'
                exact hvalues n this
              · intro hfc hm
                simp at hfc
              · intro _
                have hdc_old : st.distinguishedCount =
                    (st.observed.getQ (· = i)).length := hdcount hflags.1 hflags.2
                have hdc_fq : st.distinguishedCount = st.forkQuery := hfork
                change (QueryLog.getQ ((st.observed.logQuery i st.replacement).take
                    (st.cursor + 1 - 1)) (· = i)).length = st.forkQuery
                simp only [Nat.add_sub_cancel]
                rw [QueryLog.logQuery, QueryLog.singleton]
                rw [show st.cursor = st.observed.length from hObsEq.symm, List.take_left]
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
                  have : n < (if st.forkConsumed then st.cursor - 1 else st.cursor) := by
                    rw [hflags.1]; simpa using hn''
                  exact hvalues n this
              · intro _ _
                -- non-fork i-query: dc +=1, observed ++=[⟨i, u'⟩], getQ-length gains 1.
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
                have : n < (if st.forkConsumed then st.cursor - 1 else st.cursor) := by
                  rw [hflags.1]; simpa using hn''
                exact hvalues n this
            · intro _ _
              -- non-i, non-fork query: dc unchanged, observed gains a non-i entry.
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
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact hcursorTrace
          · simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch,
              QueryLog.logQuery, QueryLog.singleton] using
                (Nat.le_trans hcursorObs (Nat.le_succ (List.length st.observed)))
          · intro n hn
            have hnobs : n < st.observed.length := lt_of_lt_of_le hn hcursorObs
            calc
              QueryLog.inputAt? (st.markMismatch.noteObserved t u).observed n
                = QueryLog.inputAt? st.observed n := by
                    simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using
                      (QueryLog.inputAt?_logQuery_of_lt (log := st.observed) (t := t) (u := u)
                        (n := n) hnobs)
              _ = QueryLog.inputAt? st.trace n := hprefix n hn
          · intro hfc hm
            exfalso
            simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch] at hm
          · intro hfc
            exfalso
            have hfc' : st.forkConsumed = true := by
              simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using hfc
            simp [hflags.1] at hfc'
          · intro n hn
            have hn' : n < st.cursor := by
              simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch, hflags.1]
                using hn
            have hnobs : n < st.observed.length := Nat.lt_of_lt_of_le hn' hcursorObs
            change (st.observed.logQuery t u)[n]? = st.trace[n]?
            rw [QueryLog.logQuery, QueryLog.singleton, List.getElem?_append_left hnobs]
            have : n < (if st.forkConsumed then st.cursor - 1 else st.cursor) := by
              rw [hflags.1]; simpa using hn'
            exact hvalues n this
          · intro hfc hm
            exfalso
            simp [ReplayForkState.noteObserved, ReplayForkState.markMismatch] at hm
          · intro hfc
            exfalso
            have hfc' : st.forkConsumed = true := by
              simpa [ReplayForkState.noteObserved, ReplayForkState.markMismatch] using hfc
            simp [hflags.1] at hfc'

private theorem replayRun_preservesPrefixInvariant [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) {st₀ : ReplayForkState spec i}
    (hInv : ReplayPrefixInvariant i st₀)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (((simulateQ (replayOracle i) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec i))) :
    ReplayPrefixInvariant i z.2 := by
  induction main using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
      exact hInv
  | query_bind t oa ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hz⟩ := hz
      have husInv :=
        OracleComp.replayOracle_preservesPrefixInvariant (i := i) (t := t) hInv hus
      exact ih (u := us.1) husInv hz

/-- Every reachable replay state preserves the logged query-input prefix up to `cursor`. -/
theorem replayRunWithTraceValue_preservesPrefixInvariant [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    ReplayPrefixInvariant i z.2 := by
  unfold replayRunWithTraceValue at hz
  exact replayRun_preservesPrefixInvariant
    (main := main) (i := i)
    (hInv := ReplayPrefixInvariant.init (i := i) trace forkQuery replacement) hz

/-- Support-level replay-prefix lemma: before `cursor`, the second run queries the same oracle
inputs as the logged first-run transcript. -/
lemma replayRunWithTraceValue_prefix_input_eq [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    {n : Nat} (hn : n < z.2.cursor) :
    QueryLog.inputAt? z.2.observed n = QueryLog.inputAt? z.2.trace n := by
  exact (replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz).2.2.1 n hn

/-- Support-level value-agreement lemma: before the effective fork position (i.e., before
`cursor - 1` once the fork has fired, or before `cursor` while it has not), the second-run
`observed` log agrees with the first-run `trace` log on both the query input and the stored
response. This strengthens `replayRunWithTraceValue_prefix_input_eq` and is the key lemma
for arguing that the adversary's query transcript prior to the fork is identical across
the two runs. -/
lemma replayRunWithTraceValue_prefix_getElem?_eq [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    {n : Nat}
    (hn : n < (if z.2.forkConsumed then z.2.cursor - 1 else z.2.cursor)) :
    z.2.observed[n]? = z.2.trace[n]? :=
  (replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz).2.2.2.2.2.1 n hn

/-- Extract the "fork-position count" invariant: once the fork has fired, the prefix of `observed`
up to the fork position contains exactly `st.forkQuery` entries of type `i`. This pins down where
the replacement entry sits in the filtered `i`-log. -/
lemma replayRunWithTraceValue_forkConsumed_imp_prefix_count [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    (hfork : z.2.forkConsumed = true) :
    (QueryLog.getQ (z.2.observed.take (z.2.cursor - 1)) (· = i)).length = z.2.forkQuery :=
  (replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz).2.2.2.2.2.2.2 hfork

/-- If replay has consumed the fork point, the last consumed log entry is the distinguished query
input `i`. This is the pathwise "same target" fact used downstream. -/
lemma replayRunWithTraceValue_forkConsumed_imp_last_input [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    (hfork : z.2.forkConsumed = true) :
    0 < z.2.cursor ∧
      QueryLog.inputAt? z.2.trace (z.2.cursor - 1) = some i ∧
      QueryLog.inputAt? z.2.observed (z.2.cursor - 1) = some i := by
  have hInv := replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz
  rcases hInv.2.2.2.2.1 hfork with ⟨hpos, htrace⟩
  refine ⟨hpos, htrace, ?_⟩
  exact (replayRunWithTraceValue_prefix_input_eq
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz (n := z.2.cursor - 1) (by omega)).trans htrace

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
            by_cases hfork : st.distinguishedCount = st.forkQuery
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                  map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              exact ⟨rfl, rfl, rfl⟩
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

private theorem replayRun_immutable_params [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) {st₀ : ReplayForkState spec i}
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (((simulateQ (replayOracle i) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec i))) :
    z.2.forkQuery = st₀.forkQuery ∧ z.2.replacement = st₀.replacement ∧
      z.2.trace = st₀.trace := by
  induction main using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
      exact ⟨rfl, rfl, rfl⟩
  | query_bind t oa ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hz⟩ := hz
      have h₁ := OracleComp.replayOracle_immutable_params (i := i) (t := t) hus
      have h₂ := ih (u := us.1) (st₀ := us.2) (z := z) hz
      exact ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

lemma replayRunWithTraceValue_forkQuery_eq [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.forkQuery = forkQuery := by
  unfold replayRunWithTraceValue at hz
  simpa [ReplayForkState.init] using
    (replayRun_immutable_params (main := main) (i := i)
      (st₀ := ReplayForkState.init trace forkQuery replacement) hz).1

lemma replayRunWithTraceValue_replacement_eq [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.replacement = replacement := by
  unfold replayRunWithTraceValue at hz
  simpa [ReplayForkState.init] using
    (replayRun_immutable_params (main := main) (i := i)
      (st₀ := ReplayForkState.init trace forkQuery replacement) hz).2.1

lemma replayRunWithTraceValue_trace_eq [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    z.2.trace = trace := by
  unfold replayRunWithTraceValue at hz
  simpa [ReplayForkState.init] using
    (replayRun_immutable_params (main := main) (i := i)
      (st₀ := ReplayForkState.init trace forkQuery replacement) hz).2.2

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

/-- Per-query preservation of the replay replacement invariant.

Made `protected` (formerly `private`) so the `Std.Do.Triple` bridge in
`VCVio/CryptoFoundations/ReplayForkStdDo.lean` can lift this to a per-query
spec consumable by `mvcgen`. -/
protected lemma replayOracle_preservesReplacementInvariant [spec.DecidableEq]
    (i : ι) (t : ι) {st : ReplayForkState spec i}
    (hInv : ReplayReplacementInvariant i st)
    {z : spec.Range t × ReplayForkState spec i}
    (hz : z ∈ support (((replayOracle i) t).run st :
      OracleComp spec (spec.Range t × ReplayForkState spec i))) :
    ReplayReplacementInvariant i z.2 := by
  obtain ⟨hPre, hPost⟩ := hInv
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hlive : st.forkConsumed || st.mismatch
  · -- Live / post-fork-or-post-mismatch branch: append a fresh sample to observed.
    simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
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
      have hfcPre : st.forkConsumed = true := hfc
      have hPostApp := hPost hfcPre
      -- `observed` grows by appending; the fork-query position is preserved.
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
    have hflags : st.forkConsumed = false ∧ st.mismatch = false := by
      rcases Bool.or_eq_false_iff.mp (by simpa using hlive) with ⟨hfc, hm⟩
      exact ⟨hfc, hm⟩
    cases hnext : st.nextEntry? with
    | none =>
        simp only [hnext, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
            bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
            Set.range_id, Set.image_univ, Set.mem_range] at hz
        rcases hz with ⟨u, _, rfl⟩
        dsimp only
        refine ⟨?_, ?_⟩
        · intro _ hm
          exfalso
          simp [ReplayForkState.markMismatch, ReplayForkState.noteObserved] at hm
        · intro hfc
          exfalso
          simp [ReplayForkState.markMismatch, ReplayForkState.noteObserved, hflags.1] at hfc
    | some entry =>
        rcases entry with ⟨t', u'⟩
        by_cases hsame : t = t'
        · cases hsame
          by_cases hti : t = i
          · cases hti
            by_cases hfork : st.distinguishedCount = st.forkQuery
            · -- Fork fires: append `replacement`, set forkConsumed := true.
              simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
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
            · -- Matching i-query before the fork fires: append logged value,
              -- increment distinguishedCount.
              simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
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
          · -- Matching non-i query.
            simp only [hnext, ↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure,
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
          dsimp only
          refine ⟨?_, ?_⟩
          · intro _ hm
            exfalso
            simp [ReplayForkState.markMismatch, ReplayForkState.noteObserved] at hm
          · intro hfc
            exfalso
            simp [ReplayForkState.markMismatch, ReplayForkState.noteObserved, hflags.1] at hfc

private theorem replayRun_preservesReplacementInvariant [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) {st₀ : ReplayForkState spec i}
    (hInv : ReplayReplacementInvariant i st₀)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (((simulateQ (replayOracle i) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec i))) :
    ReplayReplacementInvariant i z.2 := by
  induction main using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
      exact hInv
  | query_bind t oa ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hz⟩ := hz
      have husInv :=
        OracleComp.replayOracle_preservesReplacementInvariant (i := i) (t := t) hInv hus
      exact ih (u := us.1) husInv hz

/-- Every reachable replay state preserves the replacement invariant. -/
theorem replayRunWithTraceValue_preservesReplacementInvariant [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    ReplayReplacementInvariant i z.2 := by
  unfold replayRunWithTraceValue at hz
  exact replayRun_preservesReplacementInvariant
    (main := main) (i := i)
    (hInv := ReplayReplacementInvariant.init (i := i) trace forkQuery replacement) hz

/-- If the replay has consumed the fork and the fork point is `forkQuery`, then the
`forkQuery`-th distinguished-oracle entry in the observed log is exactly the replacement. -/
lemma replayRunWithTraceValue_getQueryValue?_observed_eq_replacement [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement))
    (hfork : z.2.forkConsumed = true) :
    QueryLog.getQueryValue? z.2.observed i forkQuery = some replacement := by
  have hInv := replayRunWithTraceValue_preservesReplacementInvariant
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz
  -- `forkQuery` stays equal to `z.2.forkQuery` — the replay oracle never mutates it.
  -- We can read this from `ReplayForkState.init`, but easier: prove a preservation lemma
  -- or note that the replayOracle never writes `forkQuery`.
  have hfq : z.2.forkQuery = forkQuery := by
    exact replayRunWithTraceValue_forkQuery_eq
      (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
      (replacement := replacement) hz
  have hrep : z.2.replacement = replacement := by
    exact replayRunWithTraceValue_replacement_eq
      (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
      (replacement := replacement) hz
  have hPostApp := hInv.2 hfork
  rw [hfq] at hPostApp
  rw [hrep] at hPostApp
  exact QueryLog.getQueryValue?_eq_some_of_getQ_getElem? _ _ _ _ hPostApp

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
            by_cases hfork : st.distinguishedCount = st.forkQuery
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              rfl
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
    ∃ log,
      (z.1, log) ∈ support (replayFirstRun main) ∧
      z.2.observed = st₀.observed ++ log := by
  induction main using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
      refine ⟨[], ?_, by simp⟩
      simp [replayFirstRun]
  | query_bind t oa ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hzcont⟩ := hz
      have hus' : us ∈ support (((replayOracle i) t).run st₀ :
          OracleComp spec (spec.Range t × ReplayForkState spec i)) := by
        simpa [simulateQ_query, OracleQuery.query_def] using hus
      rcases ih (u := us.1) (st₀ := us.2) (z := z) hzcont with ⟨log, hlog, hobs⟩
      refine ⟨⟨t, us.1⟩ :: log, ?_, ?_⟩
      · rw [replayFirstRun, OracleComp.run_simulateQ_loggingOracle_query_bind]
        rw [support_bind]
        simp only [Set.mem_iUnion]
        refine ⟨us.1, mem_support_query t us.1, ?_⟩
        rw [support_map]
        exact ⟨(z.1, log), hlog, by simp⟩
      · calc
          z.2.observed = us.2.observed ++ log := hobs
          _ = st₀.observed.logQuery t us.1 ++ log := by
              rw [replayOracle_observed_eq_logQuery (i := i) (t := t) hus']
          _ = st₀.observed ++ (⟨t, us.1⟩ :: log) := by
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
  have hzobs : z.2.observed = log := by
    simpa [ReplayForkState.init] using hobs
  simpa [hzobs] using hlog

end support

section quantitative

variable [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]
variable [∀ i, SampleableType (spec.Range i)] [unifSpec ⊂ₒ spec]
variable [OracleSpec.LawfulSubSpec unifSpec spec]

omit [spec.Fintype] [spec.Inhabited] [∀ i, SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Each step of `replayOracle` makes at most one oracle query. Either the oracle returns
pure (matched-consumption or fork substitution), or it invokes `liftM (query t)` exactly
once (live post-fork, mismatch, missing-entry, or mismatched-type fallback). -/
private lemma replayOracle_step_isTotalQueryBound
    (i : ι) (t : ι) (st : ReplayForkState spec i) :
    IsTotalQueryBound (((replayOracle (spec := spec) i) t).run st) 1 := by
  classical
  -- 1-query block: `liftM (query t) >>= (fun u => pure (u, upd u))`.
  have hquery : ∀ (upd : spec.Range t → ReplayForkState spec i),
      IsTotalQueryBound (liftM (query (spec := spec) t) >>= fun u =>
        (pure (u, upd u) : OracleComp spec (spec.Range t × ReplayForkState spec i))) 1 := by
    intro upd
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  unfold replayOracle
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hlive : st.forkConsumed || st.mismatch
  · -- Live branch: 1 query.
    simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
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
            by_cases hfork : st.distinguishedCount = st.forkQuery
            · -- Fork substitution: 0 queries.
              simp only [↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure]
              exact trivial
            · simp only [↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure]
              exact trivial
          · simp only [↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure]
            exact trivial
        · -- Mismatched type: 1 query.
          simp only [↓reduceDIte, hsame, StateT.run_bind, StateT.run_monadLift,
            monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
            Functor.map_map]
          exact hquery (fun u => (st.markMismatch).noteObserved t u)

omit [spec.Fintype] [spec.Inhabited] [∀ i, SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Replay does not increase the total number of oracle queries. If `main` makes at most
`n` queries, then `replayRunWithTraceValue main i trace forkQuery replacement` also makes
at most `n` queries.

Reduces to `IsTotalQueryBound.simulateQ_run_of_step` with
`replayOracle_step_isTotalQueryBound` supplying the per-step bound of `1`. -/
theorem isTotalQueryBound_replayRunWithTraceValue
    (main : OracleComp spec α) (n : ℕ)
    (hmain : IsTotalQueryBound main n)
    (i : ι) (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    IsTotalQueryBound (replayRunWithTraceValue main i trace forkQuery replacement) n := by
  unfold replayRunWithTraceValue
  exact IsTotalQueryBound.simulateQ_run_of_step (impl := replayOracle i) hmain
    (fun t s => replayOracle_step_isTotalQueryBound i t s) _

omit [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- If `forkReplay` succeeds, both runs agree on the selected fork index. -/
theorem cf_eq_of_mem_support_forkReplay
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (x₁ x₂ : α)
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
        split_ifs at h with hbad hcf₂
        · simp_all
        · rw [mem_support_pure_iff] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨s, hcf, hcf₂⟩
        · simp at h

omit [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- On `forkReplay` support, first-projection success equals the pair-style success event.
This mirrors `probEvent_seededFork_fst_eq_probEvent_pair` for the replay fork. -/
theorem probEvent_forkReplay_fst_eq_probEvent_pair
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) | forkReplay main qb i cf] =
      Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) |
        forkReplay main qb i cf] := by
  refine probEvent_ext ?_
  intro r hr
  rcases r with _ | ⟨x₁, x₂⟩
  · simp
  · have hmem : some (x₁, x₂) ∈ support (forkReplay main qb i cf) := by
      simpa using hr
    rcases cf_eq_of_mem_support_forkReplay
      (main := main) (qb := qb) (i := i) (cf := cf) x₁ x₂ hmem with ⟨t, h₁, h₂⟩
    simp [h₁, h₂]

/-! ### Helper lemmas for `le_probOutput_forkReplay`

The pointwise replay bound is proved by the same three-step decomposition used for
`le_probOutput_seededFork`:

1. `probOutput_collisionReplay_le_main_div` (replay analogue of
   `probOutput_collision_le_main_div`): bounds the probability that the uniformly
   sampled replacement `u` collides with the logged answer at the `s`-th `i`-query of
   the first run. The bound is `Pr[cf <$> main = some s] / h` where
   `h = |spec.Range i|`. Proof is purely about the `replayFirstRun` marginal: for any
   fixed `v`, `Pr[u = v | u ← uniform] = 1/h`.

2. `noGuardReplayComp_le_forkReplay_add_collisionReplay` (replay analogue of
   `hNoGuardLeAdd`): a structural inequality saying that the unrestricted "no-guard"
   composition (which always runs the second pass and inspects both projections of
   `cf`) is dominated by the genuine `forkReplay` success event plus the collision
   event. Proof is pointwise on `(x₁, log)`-pairs from `replayFirstRun`.

3. `sq_probOutput_main_le_noGuardReplayComp` (replay analogue of
   `sq_probOutput_main_le_noGuardComp`): the Jensen / Cauchy-Schwarz step. Squares
   the probability that the first run satisfies `cf x₁ = some s` and bounds it by the
   no-guard joint success probability. This is the deepest piece: it requires a
   replay-side analogue of `seededOracle.tsum_probOutput_generateSeed_weight_takeAtIndex`,
   stating that averaging over the full first-run log is equal to averaging over the
   "log truncated at the `s`-th `i`-query, then completed with a fresh uniform answer
   plus live tail samples". -/

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

/-! ### Replay state-correctness invariant

The next group of lemmas establishes that when `main` is replayed against a log it
itself produced and the fork index is reachable in that log, the second run reaches
the fork query without mismatching the prefix. The proof has three parts:

1. `replayOracle_preservesConsumed` (per-step) and `replayRun_preservesConsumed`
   (full simulation): once `forkConsumed = true ∧ mismatch = false` holds at some
   point, both flags stay set for the remainder of the run.
2. `replayRun_state_correct_aux`: a coupled inductive invariant over `main` showing
   that, starting from a state coupled to a partial first run with enough remaining
   `i`-queries to hit the fork, the simulation reaches `forkConsumed = true` with
   `mismatch = false`.
3. `replayRunWithTraceValue_state_correct`: the user-facing corollary obtained by
   instantiating the auxiliary invariant at the initial replay state. -/

omit [spec.Fintype] [spec.Inhabited]
  [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [OracleSpec.LawfulSubSpec unifSpec spec] in
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
  refine ⟨?_, ?_⟩
  · simpa [ReplayForkState.noteObserved] using h_consumed
  · simpa [ReplayForkState.noteObserved] using h_mismatch

omit [spec.Fintype] [spec.Inhabited]
  [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [OracleSpec.LawfulSubSpec unifSpec spec] in
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
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hzcont⟩ := hz
      have hus' : us ∈ support (((replayOracle idx) t).run st₀ :
          OracleComp spec (spec.Range t × ReplayForkState spec idx)) := by
        simpa [simulateQ_query, OracleQuery.query_def] using hus
      have ⟨h_consumed', h_mismatch'⟩ :=
        replayOracle_preservesConsumed (i := idx) (t := t) h_consumed h_mismatch hus'
      exact ih (u := us.1) (st₀ := us.2) h_consumed' h_mismatch' hzcont

omit [spec.Fintype] [spec.Inhabited]
  [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Coupled invariant for the replay simulation: starting from a state whose remaining
trace coincides with a continuation produced by some first run of `main`, and which
still has enough `idx`-queries left to reach the fork query, every reachable end state
of the second run satisfies `mismatch = false ∧ forkConsumed = true`.

This is the workhorse inductive lemma behind `replayRunWithTraceValue_state_correct`.
The induction is on `main`; the pure case is impossible (no remaining queries to
reach the fork) and the query/bind case dispatches on whether the fork is consumed
in this step (delegating to `replayRun_preservesConsumed`) or postponed (recursing
via the inductive hypothesis with an updated coupled state). -/
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
      omega
  | query_bind t oa ih =>
      -- Decompose the first-run support to expose `log_cont = ⟨t, u_first⟩ :: log_cont'`.
      rw [replayFirstRun, OracleComp.run_simulateQ_loggingOracle_query_bind,
        support_bind] at h_first
      simp only [Set.mem_iUnion, support_map, exists_prop] at h_first
      obtain ⟨u_first, _, p_first, hp_first, hp_eq⟩ := h_first
      obtain ⟨hx_eq, hlog_eq⟩ := Prod.mk.inj hp_eq
      set log_cont' := p_first.2 with hlog_cont'_def
      have hlog_cont_eq : log_cont = ⟨t, u_first⟩ :: log_cont' := hlog_eq.symm
      have hp_first' : (p_first.1, log_cont') ∈ support (replayFirstRun (oa u_first)) := by
        change p_first ∈ support (replayFirstRun (oa u_first))
        exact hp_first
      -- The trace exposes the same head `⟨t, u_first⟩` at position `cursor`.
      have h_trace_drop' : st₀.trace.drop st₀.cursor = ⟨t, u_first⟩ :: log_cont' := by
        rw [h_trace_drop, hlog_cont_eq]
      have hcursor_lt : st₀.cursor < st₀.trace.length := by
        have hlen : (st₀.trace.drop st₀.cursor).length =
            st₀.trace.length - st₀.cursor := List.length_drop
        rw [h_trace_drop'] at hlen
        simp at hlen
        omega
      have h_next_entry : st₀.trace[st₀.cursor]? = some ⟨t, u_first⟩ := by
        have h0 : (st₀.trace.drop st₀.cursor)[0]? = some ⟨t, u_first⟩ := by
          rw [h_trace_drop']; rfl
        rwa [List.getElem?_drop, Nat.add_zero] at h0
      have h_nextEntry_eq : st₀.nextEntry? = some ⟨t, u_first⟩ := by
        unfold ReplayForkState.nextEntry?; exact h_next_entry
      -- Helper: dropping one more step trims the head.
      have hdrop_succ : st₀.trace.drop (st₀.cursor + 1) = log_cont' := by
        have hd : st₀.trace.drop (st₀.cursor + 1) =
            (st₀.trace.drop st₀.cursor).drop 1 := by
          rw [List.drop_drop, Nat.add_comm]
        rw [hd, h_trace_drop']
        rfl
      -- Decompose the second-run support: (us : range × state) is the next step.
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hzcont⟩ := hz
      have hus' : us ∈ support (((replayOracle idx) t).run st₀ :
          OracleComp spec (spec.Range t × ReplayForkState spec idx)) := by
        simpa [simulateQ_query, OracleQuery.query_def] using hus
      -- Analyze the per-step semantics of `replayOracle` at this state.
      unfold replayOracle at hus'
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus'
      have hlive_false : (st₀.forkConsumed || st₀.mismatch) = false := by
        simp [h_forkConsumed, h_mismatch]
      simp only [hlive_false, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        dite_eq_ite, h_nextEntry_eq, ↓reduceDIte] at hus'
      -- Subcase split: t = idx with distinguishedCount = forkQuery vs. otherwise.
      by_cases hti : t = idx
      · subst hti
        by_cases hfork : st₀.distinguishedCount = st₀.forkQuery
        · -- Subcase A: fork query consumed in this step.
          set st₁ : ReplayForkState spec t :=
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
        · -- Subcase B: idx-query but not the fork.
          set st₁ : ReplayForkState spec t :=
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
          have h_st₁_dlt : st₁.distinguishedCount ≤ st₁.forkQuery := by
            simp only [st₁]; omega
          have hcount_cons :
              QueryLog.countQ (⟨t, u_first⟩ :: log_cont') (· = t) =
                log_cont'.countQ (· = t) + 1 := by
            unfold QueryLog.countQ
            rw [QueryLog.getQ_cons]
            simp
          have h_can_reach' : st₁.forkQuery + 1 - st₁.distinguishedCount
              ≤ log_cont'.countQ (· = t) := by
            rw [hlog_cont_eq, hcount_cons] at h_can_reach
            simp only [st₁]; omega
          have hzcont' : z ∈ support (((simulateQ (replayOracle t) (oa u_first)).run st₁) :
              OracleComp spec (α × ReplayForkState spec t)) := by simpa using hzcont
          exact ih u_first hp_first' h_st₁_mismatch h_st₁_obs_len
            h_st₁_trace_drop h_st₁_forkConsumed h_st₁_dlt h_can_reach' hzcont'
      · -- Subcase C: non-idx query.
        set st₁ : ReplayForkState spec idx :=
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
          unfold QueryLog.countQ
          rw [QueryLog.getQ_cons]
          simp [hti]
        have h_can_reach' : st₁.forkQuery + 1 - st₁.distinguishedCount
            ≤ log_cont'.countQ (· = idx) := by
          rw [hlog_cont_eq, hcount_cons] at h_can_reach
          exact h_can_reach
        have hzcont' : z ∈ support (((simulateQ (replayOracle idx) (oa u_first)).run st₁) :
            OracleComp spec (α × ReplayForkState spec idx)) := by simpa using hzcont
        exact ih u_first hp_first' h_st₁_mismatch h_st₁_obs_len
          h_st₁_trace_drop h_st₁_forkConsumed h_st₁_dlt h_can_reach' hzcont'

omit [spec.Fintype] [spec.Inhabited]
  [∀ j, SampleableType (spec.Range j)] [unifSpec ⊂ₒ spec]
  [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Replay correctness invariant: starting from a logged first run of `main` whose
log already records an `i`-query at position `↑s`, replaying `main` against that log
with substitution at the fork query always reaches the fork (so `forkConsumed = true`
and `mismatch = false` on every output state).

This is the user-facing corollary of `replayRun_state_correct_aux`, instantiated at
the initial replay state produced by `ReplayForkState.init`. The invariant is used in
the replay forking lemma to argue that the no-guard composition cannot succeed via a
state-failure path that `forkReplay` would reject. -/
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
  -- Build the coupling hypotheses for `init log s u`.
  set st₀ := ReplayForkState.init log (forkQuery := ↑s) (replacement := u) with hst₀_def
  have h_mismatch : st₀.mismatch = false := by simp [st₀, ReplayForkState.init]
  have h_obs_len : st₀.observed.length = st₀.cursor := by
    simp [st₀, ReplayForkState.init]
  have h_trace_drop : st₀.trace.drop st₀.cursor = log := by
    simp [st₀, ReplayForkState.init]
  have h_forkConsumed : st₀.forkConsumed = false := by
    simp [st₀, ReplayForkState.init]
  have h_dlt : st₀.distinguishedCount ≤ st₀.forkQuery := by
    simp [st₀, ReplayForkState.init]
  -- Reachability gives us the i-query count bound.
  have hreach' := hreach hlog s hcf
  obtain ⟨logged, hlogged⟩ := Option.isSome_iff_exists.mp hreach'
  have h_count : (s : ℕ) + 1 ≤ log.countQ (· = i) := by
    have hgetQ : (log.getQ (· = i))[(s : ℕ)]? = some ⟨i, logged⟩ :=
      QueryLog.getQ_getElem?_eq_of_getQueryValue?_eq_some _ _ _ _ hlogged
    have hlt : (s : ℕ) < (log.getQ (· = i)).length :=
      (List.getElem?_eq_some_iff.1 hgetQ).1
    simpa [QueryLog.countQ] using Nat.succ_le_of_lt hlt
  have h_can_reach : st₀.forkQuery + 1 - st₀.distinguishedCount
      ≤ log.countQ (· = i) := by
    simp only [st₀, ReplayForkState.init, Nat.sub_zero]
    exact h_count
  -- Apply the auxiliary invariant.
  have hq' : q ∈ support (((simulateQ (replayOracle i) main).run st₀) :
      OracleComp spec (α × ReplayForkState spec i)) := by
    simpa [replayRunWithTraceValue, st₀] using hq
  exact replayRun_state_correct_aux (idx := i) (st₀ := st₀) (x_first := x₁)
    (log_cont := log) main hlog h_mismatch h_obs_len h_trace_drop
    h_forkConsumed h_dlt h_can_reach hq'

/-- The "no-guard" replay composition: run `main` with logging, sample `u`, then run
`main` a second time with the replay oracle (replaying log up to the `s`-th `i`-query
and substituting `u` there). Always returns the pair of `cf`-projections, with no
guards. This is the replay analogue of the `noGuardComp` used in
`sq_probOutput_main_le_noGuardComp` for the seeded fork. -/
noncomputable def noGuardReplayComp
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) := do
  let p ← replayFirstRun main
  let u ← liftComp ($ᵗ spec.Range i) spec
  let q ← replayRunWithTraceValue main i p.2 ↑s u
  return some (cf p.1, cf q.1)

/-- The "collision" replay composition: run `main` with logging, sample `u`, and
return `cf x₁` only when `u` coincides with the logged answer at the `s`-th `i`-query.
This is the replay analogue of `collisionComp` used in the seeded forking proof. -/
noncomputable def collisionReplayComp
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) := do
  let p ← replayFirstRun main
  let u ← liftComp ($ᵗ spec.Range i) spec
  if QueryLog.getQueryValue? p.2 i ↑s = some u then return cf p.1 else return none

/-- Replay-side collision bound: the probability that the second-run replacement `u`
coincides with the logged answer at the `s`-th `i`-query of the first run, restricted
to the event `cf x₁ = some s`, is at most `Pr[cf <$> main = some s] / |spec.Range i|`.
This is the replay analogue of `probOutput_collision_le_main_div`.

Proof idea: for any fixed `v`, `Pr[u = v | u ← uniform] = 1/h`, so the conditional
`Pr[ getQueryValue? log i s = some u | u uniform ]` is at most `1/h` regardless of
the log. Averaging over `(x₁, log)` and using `probOutput_fst_map_replayFirstRun`
to drop the log marginal yields the bound. -/
private lemma probOutput_collisionReplay_le_main_div
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
        ↑(Fintype.card (spec.Range i)) := by
  classical
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hcard_pos : (0 : ℝ≥0∞) < (↑(Fintype.card (spec.Range i)) : ℝ≥0∞) := by
    exact_mod_cast (Fintype.card_pos (α := spec.Range i))
  have hcard_ne_zero : (↑(Fintype.card (spec.Range i)) : ℝ≥0∞) ≠ 0 := hcard_pos.ne'
  have hcard_ne_top : (↑(Fintype.card (spec.Range i)) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  -- Bound the inner conditional `Pr[u : getQ log i s = some u]` by `1/h`.
  -- Generalize the lookup so that subsequent `cases` does not substitute back into the goal.
  have h_inner :
      ∀ (x₁ : α) (log : QueryLog spec),
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let u ← liftComp ($ᵗ spec.Range i) spec
          if QueryLog.getQueryValue? log i ↑s = some u then
            return cf x₁ else (return none : OracleComp spec _)] ≤
        (if cf x₁ = some s then (1 : ℝ≥0∞) else 0) * h⁻¹ := by
    intro x₁ log
    -- Generalize the lookup once, then prove the abstracted bound.
    have h_pointwise :
        ∀ (lookup : Option (spec.Range i)),
          Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if lookup = some u then
              return cf x₁ else (return none : OracleComp spec _)] ≤
          (if cf x₁ = some s then (1 : ℝ≥0∞) else 0) * h⁻¹ := by
      intro lookup
      by_cases hcfs : cf x₁ = some s
      · rcases lookup with _ | v
        · have hzero :
              Pr[= (some s : Option (Fin (qb i + 1))) | do
                let u ← liftComp ($ᵗ spec.Range i) spec
                if (none : Option (spec.Range i)) = some u then
                  return cf x₁ else (return none : OracleComp spec _)] = 0 := by
            rw [probOutput_bind_eq_tsum]
            refine ENNReal.tsum_eq_zero.mpr fun u => ?_
            simp
          rw [hzero]; simp [hcfs]
        · -- `lookup = some v`. Only `u = v` triggers the success branch.
          have hcomp :
              Pr[= (some s : Option (Fin (qb i + 1))) | do
                let u ← liftComp ($ᵗ spec.Range i) spec
                if (some v : Option (spec.Range i)) = some u then
                  return cf x₁ else (return none : OracleComp spec _)]
              = Pr[= v | liftComp ($ᵗ spec.Range i) spec] := by
            rw [probOutput_bind_eq_tsum]
            calc
              ∑' u, Pr[= u | liftComp ($ᵗ spec.Range i) spec] *
                  Pr[= (some s : Option (Fin (qb i + 1))) |
                    if (some v : Option (spec.Range i)) = some u then
                      return cf x₁ else (return none : OracleComp spec _)]
                  = ∑' u, if u = v then Pr[= u | liftComp ($ᵗ spec.Range i) spec] else 0 := by
                    refine tsum_congr fun u => ?_
                    by_cases hu : u = v
                    · subst hu; simp [hcfs]
                    · have hne : (some v : Option (spec.Range i)) ≠ some u := by
                        intro habs; exact hu (Option.some.inj habs).symm
                      simp [hne, hu]
              _ = Pr[= v | liftComp ($ᵗ spec.Range i) spec] := by
                    rw [tsum_eq_single v]
                    · simp
                    · intro b hb
                      have : ¬ (b = v) := hb
                      rw [if_neg this]
          rw [hcomp, probOutput_liftComp, probOutput_uniformSample]
          simp [hcfs, h]
      · -- `cf x₁ ≠ some s`: the success branch never produces `some s`.
        have hzero :
            Pr[= (some s : Option (Fin (qb i + 1))) | do
              let u ← liftComp ($ᵗ spec.Range i) spec
              if lookup = some u then
                return cf x₁ else (return none : OracleComp spec _)] = 0 := by
          rw [probOutput_bind_eq_tsum]
          refine ENNReal.tsum_eq_zero.mpr fun u => ?_
          rw [mul_eq_zero]; right
          by_cases hu : lookup = some u
          · rw [if_pos hu]
            simp only [probOutput_pure_eq_indicator, Set.indicator_apply,
              Set.mem_singleton_iff, Function.const_apply]
            split_ifs with hcf
            · exact (hcfs hcf.symm).elim
            · rfl
          · rw [if_neg hu]; simp
        rw [hzero]; simp [hcfs]
    exact h_pointwise (QueryLog.getQueryValue? log i ↑s)
  -- Average the pointwise bound over `(x₁, log) ~ replayFirstRun`.
  have hexpand :
      Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s] =
      ∑' (p : α × QueryLog spec),
        Pr[= p | replayFirstRun main] *
          Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if QueryLog.getQueryValue? p.2 i ↑s = some u then
              return cf p.1 else (return none : OracleComp spec _)] := by
    simp only [collisionReplayComp]
    rw [probOutput_bind_eq_tsum]
  rw [hexpand]
  calc
    ∑' (p : α × QueryLog spec),
        Pr[= p | replayFirstRun main] *
          Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if QueryLog.getQueryValue? p.2 i ↑s = some u then
              return cf p.1 else (return none : OracleComp spec _)]
      ≤ ∑' (p : α × QueryLog spec),
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

/-- **Replay-side prefix-faithfulness (key distributional claim for B1).**

Averaging the uniform substitution `u`, the second run's output distribution depends on
the trace `log` only through its prefix `QueryLog.takeBeforeForkAt log i s`.

Operationally: the replay oracle consumes `log` entry by entry until the fork fires at
the `s`-th `i`-query (substituting `u`), after which it goes live. If we truncate `log`
to `QueryLog.takeBeforeForkAt log i s` (which has at most `s` `i`-entries), the replay
instead hits `nextEntry? = none` at the fork position and falls through to a live
sample, which is uniform, just like averaging over `u`.

This lemma encodes that operational equivalence as a distributional equality. It is
the replay analogue of `evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue`.

Proof structure:
- **Trivial case** (`(log.getQ (· = i)).length ≤ s`): the fork never fires on either side
  because `log` has fewer than `s + 1` `i`-entries, so `takeBeforeForkAt log i s = log`
  (`takeBeforeForkAt_of_getQ_length_le`) and the equality is immediate.
- **Nontrivial case** (`s < (log.getQ (· = i)).length`): fork fires on the left at the
  `s`-th `i`-entry (substituting `u`), and on the right the prefix is exhausted right
  before that entry, so `nextEntry? = none` triggers `markMismatch` and a live sample.
  Both sides trace identical pre-fork behaviour, produce a uniform sample at the fork
  position, and then continue in live (mismatch) mode. Proved by induction on `main`
  tracking the replay-oracle state. -/
private lemma evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
    [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]
    (main : OracleComp spec α) (i : ι) (log : QueryLog spec) (s : ℕ) :
    evalDist (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      Prod.fst <$> replayRunWithTraceValue main i log s u : OracleComp spec α) =
    evalDist (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      Prod.fst <$> replayRunWithTraceValue main i (QueryLog.takeBeforeForkAt log i s) s u) := by
  classical
  by_cases hlen : (log.getQ (· = i)).length ≤ s
  · rw [QueryLog.takeBeforeForkAt_of_getQ_length_le log i s hlen]
  · -- Nontrivial case: `s < (log.getQ (· = i)).length`. Proof deferred to induction on `main`.
    push Not at hlen
    sorry

/-- Probability form of the prefix-faithfulness claim: averaging over `u`, the probability
that the second run produces any fixed output `x` depends on the trace only through its
prefix `QueryLog.takeBeforeForkAt log i s`.

This is the direct consequence of
`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt`, restated at the
`probOutput` level for convenient use in tsum manipulations. -/
private lemma probOutput_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
    (main : OracleComp spec α) (i : ι) (log : QueryLog spec) (s : ℕ) (x : α) :
    Pr[= x | Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i log s u : OracleComp spec (α × _))] =
    Pr[= x | Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i (QueryLog.takeBeforeForkAt log i s) s u)] := by
  have h := evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
    main i log s
  have hcomm₁ : (Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i log s u) : OracleComp spec α) =
      (do let u ← liftComp ($ᵗ spec.Range i) spec
          Prod.fst <$> replayRunWithTraceValue main i log s u) := by
    simp only [map_bind]
  have hcomm₂ : (Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i (QueryLog.takeBeforeForkAt log i s) s u) :
        OracleComp spec α) =
      (do let u ← liftComp ($ᵗ spec.Range i) spec
          Prod.fst <$> replayRunWithTraceValue main i
            (QueryLog.takeBeforeForkAt log i s) s u) := by
    simp only [map_bind]
  rw [hcomm₁, hcomm₂]
  exact congrFun (congrArg DFunLike.coe h) x

/-- **Weighted replay prefix-faithfulness (second key distributional claim for B1).**

Averaging the first-run output `p = (x₁, log)` with any `h`-weight depending only on
the truncated log `QueryLog.takeBeforeForkAt log i s`, the indicator that the
first-run output satisfies `f x₁ = y` may be replaced with the replay-marginal
probability that the *second run* satisfies `f x₂ = y`, without changing the total.

This is the replay analogue of `tsum_probOutput_generateSeed_weight_takeAtIndex`:
a joint-distribution identity stating that, conditional on the truncated log, the
first- and second-run outputs are exchangeable with identical marginals given by the
replay computation `replayRunWithTraceValue main i (takeBeforeForkAt ..) s u` on a
fresh uniform `u`.

Proof plan:
1. Rewrite both sides as tsums over the truncated log `τ` by pushing the
   `trunc p.2`-dependence through with `tsum_congr` and the `takeBeforeForkAt`
   "equal or short" characterisation of the fibres of
   `p ↦ takeBeforeForkAt p.2 i s`.
2. For each fixed `τ`, the two inner tsums over `p` with `takeBeforeForkAt p.2 i s = τ`
   have a joint-marginal interpretation: they average `[cf p.1 = y]` vs. the replay
   marginal over the remaining (post-`τ`) randomness of `main`.
3. Proceed by induction on `main`, mirroring the seeded analogue structurally.
   The logging-oracle on the LHS extends the log with whatever `main` produces;
   the replay-oracle on the RHS starts from the truncated prefix.  Pre-fork, both
   sides consume matching entries; at the truncation boundary both go live with a
   fresh uniform (this is what `B1a`, encoded as
   `probOutput_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt`,
   captures); post-fork, both sides are in live mode and the two marginal distributions
   coincide.

Deferred as a large structural induction (cf. the ~150-line seeded
`tsum_probOutput_generateSeed_weight_takeAtIndex`). -/
private lemma tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt
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
  sorry

/-- Replay-side Jensen / Cauchy-Schwarz step. Squaring the probability that the first
run satisfies `cf x₁ = some s` is bounded by the joint probability that *both* the
first run and the second (substituted) run satisfy `cf · = some s`.

This is the replay analogue of `sq_probOutput_main_le_noGuardComp`. The proof has the
same structure as the seeded version, relying on two replay-specific distributional
identities:

* **Pointwise prefix-faithfulness**
  (`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt`): the
  second-run output distribution, averaged over `u`, depends on the log only through
  its prefix `takeBeforeForkAt log i s`.
* **Weighted prefix-faithfulness**
  (`tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt`): averaging the
  first-run output `p` with an `h`-weight depending on the truncated log, the
  indicator `[cf x₁ = y]` may be replaced by the replay marginal with the same
  truncated log.

With these, the Cauchy-Schwarz chain runs exactly as in the seeded case. -/
private lemma sq_probOutput_main_le_noGuardReplayComp
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= s | cf <$> main] ^ 2 ≤
      Pr[= (some (some s, some s) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          noGuardReplayComp main qb i cf s] := by
  classical
  set y : Option (Fin (qb i + 1)) := some s with hy_def
  set z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (y, y) with hz_def
  -- Shorthand for the replay-marginal probability as a function of a log prefix.
  let Q : QueryLog spec → ℝ≥0∞ := fun τ =>
    Pr[= y | cf <$> Prod.fst <$> (do
      let u ← liftComp ($ᵗ spec.Range i) spec
      replayRunWithTraceValue main i τ ↑s u : OracleComp spec (α × _))]
  -- Shorthand for the indicator-as-probOutput and the first-run marginal.
  let I : α → ℝ≥0∞ := fun x =>
    Pr[= y | (cf <$> (pure x : OracleComp spec α) :
      OracleComp spec (Option (Fin (qb i + 1))))]
  let w : α × QueryLog spec → ℝ≥0∞ := fun p => Pr[= p | replayFirstRun main]
  have hw_le_one : ∑' p, w p ≤ 1 := tsum_probOutput_le_one
  -- `hMain`: expand `Pr[= y | cf <$> main]` as an expectation over `p`.
  have hMain : (Pr[= y | cf <$> main] : ℝ≥0∞) = ∑' p, w p * I p.1 := by
    have h1 : (cf <$> main : OracleComp spec (Option (Fin (qb i + 1)))) =
        (fun p : α × QueryLog spec => cf p.1) <$> replayFirstRun main := by
      conv_lhs => rw [show main = Prod.fst <$> replayFirstRun main from
        (fst_map_replayFirstRun main).symm]
      simp only [Functor.map_map]
    rw [h1, probOutput_map_eq_tsum]
    refine tsum_congr fun p => ?_
    simp only [w, I, map_pure]
  -- `hMainTake`: the same expectation with `Q(trunc_p)` instead of the indicator.
  have hMainTake : (Pr[= y | cf <$> main] : ℝ≥0∞) =
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) := by
    have hB1h := tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt
      (main := main) (i := i) (s := (↑s : ℕ)) (f := cf) (y := y) (h := fun _ => (1 : ℝ≥0∞))
    simp only [one_mul] at hB1h
    calc (Pr[= y | cf <$> main] : ℝ≥0∞)
        = ∑' p, w p * I p.1 := hMain
      _ = ∑' p, Pr[= p | replayFirstRun main] *
            Pr[= y | (cf <$> (pure p.1 : OracleComp spec α) :
              OracleComp spec (Option (Fin (qb i + 1))))] := by
              refine tsum_congr fun p => ?_; rfl
      _ = ∑' p, Pr[= p | replayFirstRun main] *
            Pr[= y | cf <$> Prod.fst <$> (do
              let u ← liftComp ($ᵗ spec.Range i) spec
              replayRunWithTraceValue main i
                (QueryLog.takeBeforeForkAt p.2 i ↑s) ↑s u :
                  OracleComp spec (α × _))] := hB1h
      _ = ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) := by
              refine tsum_congr fun p => ?_; rfl
  -- `hEq`: the two expansions of `Pr[= y | cf <$> main]` coincide.
  have hEq : ∑' p, w p * I p.1 =
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) := hMain.symm.trans hMainTake
  -- `hJensen`: Cauchy-Schwarz with weights `w`.
  have hJensen :
      (∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) ^ 2 ≤
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w (fun p => Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) hw_le_one
  -- `hEq2`: `E[Q²] = E[Q * I]` via weighted faithfulness with `h = Q`.
  have hEq2 :
      ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 =
      ∑' p, w p * (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) * I p.1) := by
    have hB1h := tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt
      (main := main) (i := i) (s := (↑s : ℕ)) (f := cf) (y := y) (h := Q)
    -- `hB1h`: ∑ w p * (Q(trunc) * I p.1) = ∑ w p * (Q(trunc) * Q(trunc))
    -- So `hB1h.symm`: ∑ w p * (Q(trunc) * Q(trunc)) = ∑ w p * (Q(trunc) * I p.1).
    -- Rewrite `Q(trunc)^2 = Q(trunc) * Q(trunc)` to match, then apply hB1h.symm.
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
    calc ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2
        = ∑' p, Pr[= p | replayFirstRun main] *
            (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) *
              Pr[= y | cf <$> Prod.fst <$> (do
                let u ← liftComp ($ᵗ spec.Range i) spec
                replayRunWithTraceValue main i
                  (QueryLog.takeBeforeForkAt p.2 i ↑s) ↑s u :
                    OracleComp spec (α × _))]) := by
            refine tsum_congr fun p => ?_; exact hsq_eq p
      _ = ∑' p, Pr[= p | replayFirstRun main] *
            (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) *
              Pr[= y | (cf <$> (pure p.1 : OracleComp spec α) :
                OracleComp spec (Option (Fin (qb i + 1))))]) := hB1h.symm
      _ = ∑' p, w p * (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) * I p.1) := by
            refine tsum_congr fun p => ?_; rfl
  -- `hFactor`: expand `Pr[= z | noGuardReplayComp]` as `E[I p.1 * Q(p.2)]`.
  have hFactor : Pr[= z | noGuardReplayComp main qb i cf s] =
      ∑' p, w p * (I p.1 * Q p.2) := by
    simp only [noGuardReplayComp, z, hz_def, y]
    rw [probOutput_bind_eq_tsum]
    refine tsum_congr fun p => ?_
    -- Show: Pr[= some (some s, some s) | (do u; q; return some (cf p.1, cf q.1))]
    --       = I p.1 * Q p.2
    congr 1
    -- Rewrite the inner computation.
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
      simp [map_eq_bind_pure_comp, Function.comp]
    rw [hinner, probOutput_some_map_some, probOutput_prod_mk_snd_map]
    -- Goal: (if (some s, some s).1 = cf p.1 then Pr[= (some s, some s).2 | ...] else 0)
    --       = I p.1 * Q p.2
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
  -- `hFactorTrunc`: use B1a to replace `Q p.2` by `Q (trunc p.2)`.
  have hFactorTrunc : Pr[= z | noGuardReplayComp main qb i cf s] =
      ∑' p, w p * (I p.1 * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) := by
    rw [hFactor]
    refine tsum_congr fun p => ?_
    congr 1
    congr 1
    -- `Q p.2 = Q (trunc p.2)` by B1a (probOutput form, composed with cf).
    simp only [Q]
    have hB1a := probOutput_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt
      (main := main) (i := i) (log := p.2) (s := (↑s : ℕ))
    rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
    refine tsum_congr fun a => ?_
    rw [hB1a]
  -- Chain the inequalities.
  have hfinal : (Pr[= y | cf <$> main] : ℝ≥0∞) ^ 2 ≤
      Pr[= z | noGuardReplayComp main qb i cf s] := by
    calc (Pr[= y | cf <$> main] : ℝ≥0∞) ^ 2
        = (∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) ^ 2 := by rw [hMainTake]
      _ ≤ ∑' p, w p * Q (QueryLog.takeBeforeForkAt p.2 i ↑s) ^ 2 := hJensen
      _ = ∑' p, w p * (Q (QueryLog.takeBeforeForkAt p.2 i ↑s) * I p.1) := hEq2
      _ = ∑' p, w p * (I p.1 * Q (QueryLog.takeBeforeForkAt p.2 i ↑s)) := by
            refine tsum_congr fun p => ?_
            ring
      _ = Pr[= z | noGuardReplayComp main qb i cf s] := hFactorTrunc.symm
  change (Pr[= s | cf <$> main] : ℝ≥0∞) ^ 2 ≤ Pr[= z | noGuardReplayComp main qb i cf s]
  have : (Pr[= s | cf <$> main] : ℝ≥0∞) = Pr[= y | cf <$> main] := by
    simp [y]
  rw [this]
  exact hfinal

omit [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Structural replay inequality: the no-guard composition's joint success event is
dominated by the genuine `forkReplay` success event plus the collision event. This is
the replay analogue of the structural inequality `hNoGuardLeAdd` used in
`le_probOutput_seededFork`.

The proof mirrors the seeded version: bind on `replayFirstRun main`, case-split on
`cf x₁`, and reduce the `some s` branch to a per-`u` comparison of the three
computations. Two additional ingredients enter the replay version:

* **`hreach : CfReachable main qb i cf`** ensures the fork query is reachable from
  the first run: whenever `cf x₁ = some s`, the recorded log has an `i`-query at
  position `↑s`. Without this assumption, `forkReplay` returns `pure none`
  unconditionally on the substantive branch and the inequality fails.
* **`replayRunWithTraceValue_state_correct`** ensures the second run always reaches
  the fork without mismatching the prefix, so the state-flag check in
  `forkReplayWithTraceValue` is vacuous on the relevant support. -/
private lemma noGuardReplayComp_le_forkReplay_add_collisionReplay
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
  -- All three computations start with `replayFirstRun main`. Apply the bind
  -- congruence and reduce to a per-`(x₁, log₁)` inequality.
  show Pr[= z | noGuardReplayComp main qb i cf s] ≤
    Pr[= z | f <$> forkReplay main qb i cf] +
      Pr[= (some s : Option (Fin (qb i + 1))) | collisionReplayComp main qb i cf s]
  simp only [noGuardReplayComp, collisionReplayComp, forkReplay, map_bind]
  refine (probOutput_bind_congr_le_add
    (mx := (replayFirstRun main : OracleComp spec (α × QueryLog spec)))
    (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
  intro p hp
  -- Single case-split on whether `cf p.1 = some s`. The non-substantive branch
  -- collapses to `LHS = 0`.
  by_cases hcf_s : cf p.1 = some s
  · -- Substantive case: `cf p.1 = some s`.
    -- Reachability gives a logged value at the fork query.
    have hreach' := hreach hp s hcf_s
    obtain ⟨logged, hlogged⟩ := Option.isSome_iff_exists.mp hreach'
    -- Reduce both sides to per-`u` quantities by binding on `u`.
    simp only [hcf_s, map_bind]
    refine (probOutput_bind_congr_le_add
      (mx := (liftComp ($ᵗ spec.Range i) spec : OracleComp spec (spec.Range i)))
      (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
    intro u _hu
    -- Helper: rewrite `forkReplayWithTraceValue main qb i cf p u`-mapped using `hcf_s`,`hlogged`.
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
          rw [hlogged]; intro habs; exact hcoll (Option.some_inj.mp habs)
        simp [hne, hcoll]
    rw [hforkUnfold, hcollUnfold]
    by_cases hcoll : logged = u
    · -- Collision case: bound by 1 ≤ 0 + 1.
      rw [if_pos hcoll, if_pos hcoll]
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
    · -- No-collision case: use replay correctness.
      rw [if_neg hcoll, if_neg hcoll]
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
        by_cases hq : cf q.1 = some s
        · simp [hq]
        · have hq_symm : ¬ some s = cf q.1 := fun h => hq h.symm
          simp [hq, hq_symm]
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
          by_cases hq : cf q.1 = some s
          · simp [hq, z]
          · simp [hq, z]
        · have hzero : Pr[= q | replayRunWithTraceValue main i p.2 ↑s u] = 0 :=
            probOutput_eq_zero_of_not_mem_support hqmem
          rw [hzero]
          split_ifs <;> simp
      rw [hL_eq, hR_eq]
      exact le_add_of_nonneg_right (zero_le _)
  · -- Non-substantive case: `cf p.1 ≠ some s`.
    -- LHS noGuard returns `some (cf p.1, _)` ≠ `some (some s, some s)` since
    -- `cf p.1 ≠ some s`. So Pr[LHS = z] = 0.
    have hL :
        Pr[= z | do
          let _u ← liftComp ($ᵗ spec.Range i) spec
          let q ← replayRunWithTraceValue main i p.2 ↑s _u
          (pure (some (cf p.1, cf q.1)) : OracleComp spec _)] = 0 := by
      rw [probOutput_eq_zero_iff]
      intro hmem
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        z] at hmem
      obtain ⟨_, _, _, _, hh⟩ := hmem
      have h1 := (Prod.mk.inj (Option.some.inj hh)).1
      exact hcf_s h1.symm
    rw [hL]
    exact zero_le _

/-- Key pointwise replay lower bound. This is the replay analogue of
`le_probOutput_seededFork`.

The summed (aggregated) version is the replay analogue of Firsov-Janku's `pr_fork_success`
in [fsec/proof/Forking.ec:1175](../../../fsec/proof/Forking.ec). The quantitative argument
decomposes into:

1. `pr_split` [Forking.ec:410]: factor out the `acc · h⁻¹` collision term.
2. `pr_succ_resp_eq` [Forking.ec:480]: exchange symmetry of the two replay answers.
3. `pr_fork_specific` [Forking.ec:1115]: pointwise `Pr[success at s]² ≤ Pr[fork at s]`.
4. `square_sum` [Forking.ec:1148]: Jensen / Cauchy-Schwarz `Σ aⱼ² ≥ (Σ aⱼ)² / Q`.

In Lean the analogous pointwise bound corresponds to step (3) combined with (1) and is
structurally similar to the seed-based `le_probOutput_seededFork` proof in
`VCVio/CryptoFoundations/SeededFork.lean`, with `replayFirstRun`/`replayRunWithTraceValue` playing
the role of `generateSeed`/`seededOracle` and `QueryLog.takeBeforeFork`-style slicing replacing
`QuerySeed.takeAtIndex`.

The proof reduces to three helper lemmas:
`probOutput_collisionReplay_le_main_div`,
`sq_probOutput_main_le_noGuardReplayComp`, and
`noGuardReplayComp_le_forkReplay_add_collisionReplay`.

The `hreach` hypothesis (`CfReachable`) is needed because, unlike the seed-based version
(where `cf x = some s` always implies the `s`-th query value is well-defined in the seed),
in the replay setting, `cf` is computed from `x` independently from the actual queries
made by the run that produced it. The hypothesis captures the natural condition that the
fork point `s` chosen by `cf` always corresponds to a query that was actually issued.

**Currently conditional on the two prefix-faithfulness `sorry`s** feeding
`sq_probOutput_main_le_noGuardReplayComp`:
`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt` (induction on `main`)
and `tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt` (weighted-averaging induction).
Downstream consumers (`probOutput_none_forkReplay_le`, `le_probEvent_isSome_forkReplay`,
`Fork.replayForkingBound`, `euf_nma_bound`, `euf_cma_bound`) inherit this conditionality
until both faithfulness lemmas are discharged. -/
theorem le_probOutput_forkReplay
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : CfReachable main qb i cf) (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h
      ≤ Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) |
          forkReplay main qb i cf] := by
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  -- Rewrite the RHS as a `probOutput` over the pair-style success event after `cf` mapping.
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
  -- noGuard bound from Cauchy-Schwarz, plus the structural inequality.
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
/-- The replay-fork precondition is itself bounded by `1`. This mirrors
`seededFork_precondition_le_one`; the statement is independent of the fork mechanism. -/
theorem forkReplay_precondition_le_one
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤ 1 :=
  seededFork_precondition_le_one (main := main) (qb := qb) (i := i) (cf := cf)

omit [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Sum of disjoint replay-fork success events is at most the total `some` probability.
This mirrors `sum_probEvent_fork_le_tsum_some` in `Fork.lean`; the proof is purely
algebraic on the underlying distribution and does not depend on the fork mechanism. -/
private lemma sum_probEvent_forkReplay_le_tsum_some
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
    have h := tsum_option (fun r : Option (α × α) =>
      if r.map (cf ∘ Prod.fst) = some (some s) then
        Pr[= r | forkReplay main qb i cf] else 0) ENNReal.summable
    simp only [Option.map, comp_apply, reduceCtorEq, ite_false, zero_add,
      Option.some.injEq] at h
    exact h
  simp_rw [hsplit]
  rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [tsum_fintype (L := .unconditional _)]
  rcases hcf : cf p.1 with _ | s₀
  · simp
  · rw [Finset.sum_eq_single s₀ (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
    simp

/-- Replay fork failure probability bound. This mirrors `probOutput_none_seededFork_le`;
the proof structure is identical, substituting the pointwise replay lower bound
`le_probOutput_forkReplay` for its seed-based analogue. The `hreach` hypothesis is
threaded through from `le_probOutput_forkReplay`.

**Currently conditional on the two B1 prefix-faithfulness `sorry`s** (transitively via
`le_probOutput_forkReplay` → `sq_probOutput_main_le_noGuardReplayComp`). -/
theorem probOutput_none_forkReplay_le
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
  rw [HasEvalPMF.probFailure_eq_zero, tsub_zero] at htotal
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
              gcongr; rw [div_eq_mul_inv]
              have hn : ((qb i + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
              calc acc ^ 2 * (↑(qb i + 1))⁻¹
                  _ ≤ (↑(qb i + 1) * ∑ s, ps s ^ 2) * (↑(qb i + 1))⁻¹ := by gcongr
                  _ = ∑ s, ps s ^ 2 := by
                      rw [mul_assoc, mul_comm (∑ s, ps s ^ 2) _, ← mul_assoc,
                        ENNReal.mul_inv_cancel hn (by simp), one_mul]
          _ ≤ (∑ s, ps s ^ 2) - ∑ s, ps s / h := by
              gcongr; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
          _ ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
              rw [tsub_le_iff_right]
              calc ∑ s, ps s ^ 2
                ≤ ∑ s, ((ps s ^ 2 - ps s / h) + ps s / h) :=
                    Finset.sum_le_sum fun s _ => le_tsub_add
                _ = ∑ s, (ps s ^ 2 - ps s / h) + ∑ s, ps s / h :=
                    Finset.sum_add_distrib

/-- Packaged replay forking theorem. This is the replay analogue of
`le_probEvent_isSome_seededFork`, derived from `probOutput_none_forkReplay_le` and
`forkReplay_precondition_le_one` by the same `1 - ·` conversion used in
`le_probEvent_isSome_seededFork`. The `hreach` hypothesis is threaded through.

**Currently conditional on the two B1 prefix-faithfulness `sorry`s** (transitively via
`probOutput_none_forkReplay_le` → `le_probOutput_forkReplay`
→ `sq_probOutput_main_le_noGuardReplayComp`). -/
theorem le_probEvent_isSome_forkReplay
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

omit [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Structural success facts for `forkReplay`: both outputs come from logged runs of `main`,
share the same selected fork index, differ at the selected distinguished-oracle answer, and the
second run is witnessed by a replay state whose observed log agrees with the first-run log on the
replayed prefix.

This mirrors Firsov-Janku's `success_log_props` at
[fsec/proof/Forking.ec:1373](../../../fsec/proof/Forking.ec). The Lean proof is library-native:
it unfolds `forkReplay` with `mem_support_bind_iff`, then consumes the already-proved
support-level lemmas `replayRunWithTraceValue_mem_support_replayFirstRun`,
`replayRunWithTraceValue_prefix_input_eq`, and
`replayRunWithTraceValue_getQueryValue?_observed_eq_replacement`. No procedural while-loop
invariant is needed; the replacement invariant `ReplayReplacementInvariant` is established
pointwise by induction on the replay oracle. -/
theorem forkReplay_success_log_props
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
          -- `hbad : ¬(z.2.mismatch || !z.2.forkConsumed) = true`, so both components fail.
          have hbad' : (z.2.mismatch || !z.2.forkConsumed) = false :=
            Bool.not_eq_true _ |>.mp hbad
          have hmismatch_false : z.2.mismatch = false :=
            (Bool.or_eq_false_iff.mp hbad').1
          have hforkConsumed : z.2.forkConsumed = true := by
            have := (Bool.or_eq_false_iff.mp hbad').2
            rcases hfc : z.2.forkConsumed with _ | _
            · simp [hfc] at this
            · rfl
          have htrace : z.2.trace = first.2 :=
            replayRunWithTraceValue_trace_eq (main := main) (i := i) (trace := first.2)
              (forkQuery := ↑s) (replacement := u) hz
          refine ⟨first.2, z.2.observed, s, ?_, ?_, hcf, hcf₂, ?_,
            u, z.2, ?_, rfl, hmismatch_false, hforkConsumed, ?_⟩
          · -- `(x₁, first.2) ∈ support (replayFirstRun main)`
            simpa using hfirst
          · -- `(x₂, z.2.observed) ∈ support (replayFirstRun main)`
            exact replayRunWithTraceValue_mem_support_replayFirstRun
              (main := main) (i := i) (trace := first.2) (forkQuery := ↑s)
              (replacement := u) hz
          · -- `getQueryValue? first.2 i s ≠ getQueryValue? z.2.observed i s`
            have hrhs := replayRunWithTraceValue_getQueryValue?_observed_eq_replacement
              (main := main) (i := i) (trace := first.2) (forkQuery := ↑s)
              (replacement := u) hz hforkConsumed
            rw [hq, hrhs]
            intro habs
            exact heq (Option.some.inj habs)
          · -- `(x₂, z.2) ∈ support (replayRunWithTraceValue main i first.2 ↑s u)`
            exact hz
          · -- Prefix agreement on `[0, z.2.cursor)`
            intro n hn
            have := replayRunWithTraceValue_prefix_input_eq
              (main := main) (i := i) (trace := first.2) (forkQuery := ↑s)
              (replacement := u) hz hn
            rw [htrace] at this
            exact this
        · simp at h

omit [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Replay property transfer: any postcondition that holds for every logged run of `main`
holds for both outputs of a successful replay fork, together with the common selected fork index
and the fact that the distinguished answers differ at that index.

This mirrors Firsov-Janku's `property_transfer` at
[fsec/proof/Forking.ec:1351](../../../fsec/proof/Forking.ec), combining `fst_run_prop` with
the shared-prefix facts established by `success_log_props`. -/
theorem forkReplay_propertyTransfer
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
