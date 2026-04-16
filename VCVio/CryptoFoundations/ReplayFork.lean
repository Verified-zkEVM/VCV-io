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

This mirrors `forkWithSeedValue`: the first-run result and replacement answer are
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

section support

/-- Prefix-style replay invariant: the consumed prefix of `observed` matches the consumed prefix of
`trace` at the level of query inputs, and if the fork has not fired yet then `observed` has no
extra suffix beyond that prefix. -/
def ReplayPrefixInvariant (i : ι) (st : ReplayForkState spec i) : Prop :=
  st.cursor ≤ st.trace.length ∧
  st.cursor ≤ st.observed.length ∧
  (∀ n, n < st.cursor →
    QueryLog.inputAt? st.observed n = QueryLog.inputAt? st.trace n) ∧
  (st.forkConsumed = false → st.mismatch = false → st.observed.length = st.cursor) ∧
  (st.forkConsumed = true →
    0 < st.cursor ∧ QueryLog.inputAt? st.trace (st.cursor - 1) = some i)

namespace ReplayPrefixInvariant

variable {i : ι}

lemma init (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    ReplayPrefixInvariant i (ReplayForkState.init trace forkQuery replacement) := by
  refine ⟨by simp [ReplayForkState.init], by simp [ReplayForkState.init], ?_, ?_, ?_⟩
  · intro n hn
    exact (Nat.not_lt_zero n hn).elim
  · intro hfork hmismatch
    simp [ReplayForkState.init]
  · intro hfork
    simp [ReplayForkState.init] at hfork

end ReplayPrefixInvariant

private lemma replayOracle_preservesPrefixInvariant [spec.DecidableEq]
    (i t : ι) {st : ReplayForkState spec i}
    {z : spec.Range t × ReplayForkState spec i}
    (hInv : ReplayPrefixInvariant i st)
    (hz : z ∈ support ((replayOracle i t).run st)) :
    ReplayPrefixInvariant i z.2 := by
  rcases hInv with ⟨hcursorTrace, hcursorObs, hprefix, hlen, hforked⟩
  unfold replayOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hlive : st.forkConsumed || st.mismatch
  · simp only [hlive, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_monadLift,
      monadLift_eq_self, StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
      support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
      Set.image_univ, Set.mem_range] at hz
    rcases hz with ⟨u, hu, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · simp only [hlive, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, dite_eq_ite] at hz
    cases hnext : st.nextEntry? with
    | none =>
        simp only [hnext, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
            bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
            Set.range_id, Set.image_univ, Set.mem_range] at hz
        rcases hz with ⟨u, hu, rfl⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
          have hflags : st.forkConsumed = false ∧ st.mismatch = false := by
            cases hfc0 : st.forkConsumed <;> cases hm0 : st.mismatch
            · constructor <;> simp
            · simp [hfc0, hm0] at hlive
            · simp [hfc0, hm0] at hlive
            · simp [hfc0, hm0] at hlive
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
              refine ⟨Nat.succ_le_of_lt hlt, ?_, ?_, ?_, ?_⟩
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
            · simp only [hnext, ↓reduceDIte, hfork, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with rfl
              have hlt : st.cursor < st.trace.length := by
                have hsome : st.trace[st.cursor]? = some ⟨i, u'⟩ := by
                  simpa [ReplayForkState.nextEntry?] using hnext
                exact (List.getElem?_eq_some_iff).1 hsome |>.1
              refine ⟨Nat.succ_le_of_lt hlt, ?_, ?_, ?_, ?_⟩
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
          · simp only [hnext, ↓reduceDIte, hti, StateT.run_map, StateT.run_set, map_pure,
              support_pure, Set.mem_singleton_iff] at hz
            rcases hz with rfl
            have hlt : st.cursor < st.trace.length := by
              have hsome : st.trace[st.cursor]? = some ⟨t, u'⟩ := by
                simpa [ReplayForkState.nextEntry?] using hnext
              exact (List.getElem?_eq_some_iff).1 hsome |>.1
            refine ⟨Nat.succ_le_of_lt hlt, ?_, ?_, ?_, ?_⟩
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
        · simp only [hnext, hsame, ↓reduceDIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
            Functor.map_map, support_map, support_liftM, OracleQuery.input_query,
            OracleQuery.cont_query, Set.range_id, Set.image_univ, Set.mem_range] at hz
          rcases hz with ⟨u, hu, rfl⟩
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      have husInv := replayOracle_preservesPrefixInvariant (i := i) (t := t) hInv hus
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
  rcases hInv.2.2.2.2 hfork with ⟨hpos, htrace⟩
  refine ⟨hpos, htrace, ?_⟩
  exact (replayRunWithTraceValue_prefix_input_eq
    (main := main) (i := i) (trace := trace) (forkQuery := forkQuery)
    (replacement := replacement) hz (n := z.2.cursor - 1) (by omega)).trans htrace

private lemma replayOracle_observed_eq_logQuery [spec.DecidableEq]
    [spec.Fintype] [spec.Inhabited]
    (i : ι) (t : ι) {st : ReplayForkState spec i}
    {z : spec.Range t × ReplayForkState spec i}
    (hz : z ∈ support (((replayOracle i) t).run st :
      OracleComp spec (spec.Range t × ReplayForkState spec i))) :
    z.2.observed = st.observed.logQuery t z.1 := by
  sorry

private theorem replayRun_mem_support_replayFirstRun_append [spec.DecidableEq]
    [spec.Fintype] [spec.Inhabited]
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
    [spec.Fintype] [spec.Inhabited]
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

/-- Replay does not increase the total number of oracle queries. This is the runtime-control
placeholder needed before the full quantitative replay forking argument. -/
theorem isTotalQueryBound_replayRunWithTraceValue
    (main : OracleComp spec α) (n : ℕ)
    (hmain : IsTotalQueryBound main n)
    (i : ι) (trace : QueryLog spec) (forkQuery : Nat) (replacement : spec.Range i) :
    IsTotalQueryBound (replayRunWithTraceValue main i trace forkQuery replacement) n := by
  sorry

omit [spec.Fintype] [spec.Inhabited] in
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

/-- On `forkReplay` support, first-projection success equals the pair-style success event.
This mirrors `probEvent_fork_fst_eq_probEvent_pair` for the replay fork. -/
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

/-- Key pointwise replay lower bound. This is the replay analogue of
`le_probOutput_fork`. -/
theorem le_probOutput_forkReplay
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h
      ≤ Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) |
          forkReplay main qb i cf] := by
  sorry

/-- The replay-fork precondition is itself bounded by `1`. This mirrors
`fork_precondition_le_one`. -/
theorem forkReplay_precondition_le_one
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤ 1 := by
  sorry

/-- Replay fork failure probability bound. This mirrors `probOutput_none_fork_le`. -/
theorem probOutput_none_forkReplay_le
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.Range i)
    let q := qb i + 1
    Pr[= none | forkReplay main qb i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  sorry

/-- Packaged replay forking theorem. This is the replay analogue of
`le_probEvent_isSome_fork`, and it is the main quantitative theorem still needed by
`FiatShamir.euf_nma_bound`. -/
theorem le_probEvent_isSome_forkReplay
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr[ fun r : Option (α × α) => r.isSome | forkReplay main qb i cf] := by
  sorry

/-- Structural success facts for `forkReplay`: both outputs come from logged runs of `main`,
share the same selected fork index, differ at the selected distinguished-oracle answer, and the
second run is witnessed by a replay state whose observed log agrees with the first-run log on the
replayed prefix. This mirrors EasyCrypt's `success_log_props` layer. -/
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
  sorry

/-- Replay property transfer: any postcondition that holds for every logged run of `main`
holds for both outputs of a successful replay fork, together with the common selected fork index
and the fact that the distinguished answers differ at that index. This mirrors EasyCrypt's
`property_transfer` convenience layer. -/
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
