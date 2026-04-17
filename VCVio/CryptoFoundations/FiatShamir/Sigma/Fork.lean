/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.SeededFork
import VCVio.CryptoFoundations.ReplayFork

/-!
# Fiat-Shamir forking infrastructure

Wraps a managed-RO NMA adversary against `FiatShamir` into a single-oracle
`OracleComp (unifSpec + (Unit →ₒ Chal))` computation that `ReplayFork` can
fork. Collects the forgery, the adversary's cache, the live query log, and a
`verified` flag, and exposes a `forkPoint` that picks the index at which to
rewind.

The main export is `Fork.replayForkingBound`: the Fiat-Shamir-specific
analogue of Firsov-Janku's `forking_lemma_ro`, stated at the `OracleComp`
level. Callers in `FiatShamir.Sigma.Security` compose it with
`ReplayFork.forkReplay_propertyTransfer` to drive the NMA-to-extraction step
of `euf_nma_bound`.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

namespace Fork

/-- Trace used by the Fiat-Shamir forking reduction for managed-RO NMA adversaries.

Fields:

* `forgery`: the final `(message, (commitment, response))` triple produced by the adversary.
* `advCache`: snapshot of the adversary's locally programmed random oracle. Only the
  reduction side reads from it: `runTrace.verified` and the forking bound treat it purely
  as bookkeeping. In the managed-RO model every adversary challenge query is routed through
  the live oracle, so programmed entries that ever actually influence a verified forgery
  also appear in `roCache`; this is the invariant that `euf_cma_to_nma` is responsible for
  establishing when it bridges `advCache`-only entries back to the live log.
* `roCache`: the live random-oracle cache populated by managed-RO queries during the run.
* `queryLog`: the list of `(message, commitment)` hash points actually queried (live). The
  forking lemma rewinds at a position of this list.
* `verified`: whether the forgery successfully verifies against a cached challenge for its
  target. `runTrace` consults only `roCache` for this flag (see its docstring). -/
structure Trace where
  forgery : M × (Commit × Resp)
  advCache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache
  roCache : (M × Commit →ₒ Chal).QueryCache
  queryLog : List (M × Commit)
  verified : Bool

/-- The hash point corresponding to the final forgery recorded in a fork trace. -/
def Trace.target
    (trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    M × Commit :=
  (trace.forgery.1, trace.forgery.2.1)

/-- Rewinding point extracted from a managed-RO fork trace. The fork is usable exactly when
the final forgery verifies and its hash point appears in the live query log. -/
def forkPoint
    [DecidableEq M] [DecidableEq Commit]
    (qH : ℕ)
    (trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    Option (Fin (qH + 1)) := by
  if hverified : trace.verified then
    let target := trace.target
    if hmem : target ∈ trace.queryLog then
      let idx := trace.queryLog.findIdx (· == target)
      if hidx : idx < qH + 1 then
        exact some ⟨idx, hidx⟩
      else
        exact none
    else
      exact none
  else
    exact none

lemma forkPoint_some_imp_verified
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.verified = true := by
  unfold forkPoint at hs
  by_cases hverified : trace.verified
  · exact hverified
  · simp [hverified] at hs

lemma forkPoint_some_imp_mem
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.target ∈ trace.queryLog := by
  unfold forkPoint at hs
  by_cases hverified : trace.verified
  · have hs' :
        trace.target ∈ trace.queryLog ∧
          ∃ h : trace.queryLog.findIdx (· == trace.target) ≤ qH,
            (⟨trace.queryLog.findIdx (· == trace.target), Nat.lt_succ_of_le h⟩ :
              Fin (qH + 1)) = s := by
        simpa [hverified, Trace.target] using hs
    exact hs'.1
  · simp [hverified] at hs

lemma forkPoint_getElem?_eq_some_target
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.queryLog[↑s]? = some trace.target := by
  unfold forkPoint at hs
  by_cases hverified : trace.verified
  · have hs' :
        trace.target ∈ trace.queryLog ∧
          ∃ h : trace.queryLog.findIdx (· == trace.target) ≤ qH,
            (⟨trace.queryLog.findIdx (· == trace.target), Nat.lt_succ_of_le h⟩ :
              Fin (qH + 1)) = s := by
        simpa [hverified, Trace.target] using hs
    rcases hs' with ⟨hmem, ⟨hidx, hs'⟩⟩
    have hlt : trace.queryLog.findIdx (· == trace.target) < trace.queryLog.length := by
      exact List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩
    subst s
    exact (List.getElem_eq_iff
      (l := trace.queryLog)
      (i := trace.queryLog.findIdx (· == trace.target))
      (x := trace.target)
      hlt).mp <|
      by
        simpa [Trace.target] using
          (List.findIdx_getElem (xs := trace.queryLog) (p := fun x => x == trace.target)
            (w := hlt))
  · simp [hverified] at hs

/-- Wrapped oracle spec used by `runTrace`: uniform sampling plus a single counted challenge
oracle exposing the random-oracle entropy. -/
abbrev wrappedSpec (Chal : Type) : OracleSpec (ℕ ⊕ Unit) :=
  unifSpec + (Unit →ₒ Chal)

/-- Internal simulator state of `runTrace`: the cached random-oracle answers paired with
the chronological list of cache-miss inputs (the trace's `queryLog`). -/
abbrev simSt (M Commit Chal : Type) [DecidableEq M] [DecidableEq Commit] : Type :=
  (M × Commit →ₒ Chal).QueryCache × List (M × Commit)

/-- Forwards a uniform-spec query through to the wrapped spec's `Sum.inl` summand without
touching the simulator state. -/
noncomputable def unifFwd (M Commit Chal : Type) [DecidableEq M] [DecidableEq Commit] :
    QueryImpl unifSpec (StateT (simSt M Commit Chal) (OracleComp (wrappedSpec Chal))) :=
  fun n => monadLift
    (liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) :
      OracleComp (wrappedSpec Chal) _)

/-- Caching random-oracle implementation: on a cache hit the recorded answer is returned,
on a cache miss a fresh `Sum.inr ()` query is issued, the answer is cached, and the
miss input `(msg, c)` is appended to the trace's internal `queryLog`. -/
noncomputable def roImpl (M Commit Chal : Type) [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (M × Commit →ₒ Chal)
      (StateT (simSt M Commit Chal) (OracleComp (wrappedSpec Chal))) :=
  fun mc => do
    let (cache, log) ← get
    match cache mc with
    | some v => pure v
    | none =>
        let v : Chal ← monadLift
          (liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) :
            OracleComp (wrappedSpec Chal) Chal)
        set ((cache.cacheQuery mc v : (M × Commit →ₒ Chal).QueryCache),
          log ++ [mc])
        pure v

/-- Replay a managed-RO NMA adversary against a single counted challenge oracle, keeping both
the adversary-returned cache and the live query log that the forking lemma can rewind.

The `verified` flag is computed strictly from the live `roCache` so that a successful
`forkPoint` extraction always pins the verifying challenge to the live random-oracle
answer at the corresponding outer-log position. Forgeries whose verification depends only
on programmed entries the adversary supplies in `advCache` are not counted: this is a
strict strengthening over an `advCache`-fallback variant and strictly shrinks
`Fork.advantage`. The residual obligation, "every `advCache`-only forgery that would have
verified also has a corresponding live RO query", is a caller-side invariant that must be
discharged by the managed-RO CMA→NMA reduction. Downstream, this is the role of
`euf_cma_to_nma` in `FiatShamir/Sigma/Security.lean`, whose sigma→NMA simulation ensures
that every `advCache` programming step is mirrored by a live query into `roCache`. -/
noncomputable def runTrace
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (wrappedSpec Chal)
      (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := do
  let ((forgery, advCache), st) ←
    StateT.run (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) (nmaAdv.main pk))
      (∅, [])
  let verified :=
    match forgery with
    | (msg, (c, s)) =>
        match st.1 (msg, c) with
        | some ω => σ.verify pk c ω s
        | none => false
  let (roCache, queryLog) := st
  pure {
    forgery := forgery
    advCache := advCache
    roCache := roCache
    queryLog := queryLog
    verified := verified
  }

/-- Forkable managed-RO NMA experiment. Success means the final forged transcript verifies and
the corresponding hash point appears in the live query log, so the forking lemma can rewind it. -/
noncomputable def exp
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ProbComp Bool :=
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := chalSpec))) (do
      let (pk, _) ←
        OracleComp.liftComp hr.gen (unifSpec + chalSpec)
      let trace ← runTrace σ hr M nmaAdv pk
      pure (forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
        qH trace).isSome)

/-- The forkable success probability of a managed-RO NMA adversary. -/
noncomputable def advantage
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ENNReal :=
  Pr[= true | exp σ hr M nmaAdv qH]

section Coupling

variable [DecidableEq M] [DecidableEq Commit]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Coupling invariant for `runTrace`'s inner simulation: the trace's internal `queryLog`
grows by exactly the number of `Sum.inr ()` queries issued to the outer wrapped spec.
Each cache miss in `roImpl` simultaneously appends to the outer log and to the trace's
`queryLog`, while cache hits and `unifFwd`-forwarded `Sum.inl _` queries do not touch the
trace `queryLog`. -/
private theorem queryLog_length_eq_outer_inr_count
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z : γ × simSt M Commit Chal}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (hz : (z, outerLog) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run)) :
    z.2.2.length = l₀.length + outerLog.countQ (· = Sum.inr ()) := by
  classical
  induction Y using OracleComp.inductionOn generalizing c₀ l₀ z outerLog with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
      obtain ⟨hz_eq, hlog_eq⟩ := hz
      subst hz_eq
      subst hlog_eq
      simp [QueryLog.countQ]
  | query_bind t oa ih =>
      have hY :
          (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
            ((liftM (query t) : OracleComp _ _) >>= oa)).run (c₀, l₀) =
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀)) >>= fun us =>
              (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) (oa us.1)).run us.2 := by
        simp [simulateQ_bind, simulateQ_query, StateT.run_bind,
          map_eq_bind_pure_comp, OracleQuery.cont_query, OracleQuery.input_query]
      rw [hY, simulateQ_bind, WriterT.run_bind', support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := hz
      have hpw_split : (pw.1, pw.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w.1.1)).run us_w.1.2)).run) := by
        change pw ∈ support _
        exact hpw
      have hih :
          pw.1.2.2.length = us_w.1.2.2.length + pw.2.countQ (· = Sum.inr ()) :=
        ih (u := us_w.1.1) (c₀ := us_w.1.2.1) (l₀ := us_w.1.2.2)
          (z := pw.1) (outerLog := pw.2) hpw_split
      have hz_eq' : (pw.1, us_w.2 ++ pw.2) = (z, outerLog) := by
        rw [show ((pw.1, us_w.2 ++ pw.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w.2 ++ x) pw from rfl]
        exact hz_eq
      obtain ⟨hz_eq1, hz_eq2⟩ := Prod.mk.inj hz_eq'
      rw [← hz_eq1, ← hz_eq2]
      have houter : us_w ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w
      -- We will show: ∃ u, us_w = ((u, st'), w₁) where w₁ is determined by the case,
      -- and st' is determined by the case.
      cases t with
      | inl n =>
          have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run (c₀, l₀) =
              (liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifFwd]
          rw [hrun] at houter
          change us_w ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec Chal) (Sum.inl n) (fun u => pure (u, (c₀, l₀)))] at houter
          rw [support_bind] at houter
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at houter
          obtain ⟨_, ⟨u, hu_eq⟩, hus_w_in_u⟩ := houter
          subst hu_eq
          rw [Set.mem_singleton_iff] at hus_w_in_u
          rw [hih, hus_w_in_u]
          simp [QueryLog.countQ, QueryLog.getQ]
      | inr mc =>
          by_cases hcache : c₀ mc = none
          · have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) =
                (liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at houter
            change us_w ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec Chal) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])))] at houter
            rw [support_bind] at houter
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at houter
            obtain ⟨_, ⟨v, hv_eq⟩, hus_w_in_u⟩ := houter
            subst hv_eq
            rw [Set.mem_singleton_iff] at hus_w_in_u
            rw [hih]
            subst hus_w_in_u
            simp [QueryLog.countQ, QueryLog.getQ]
            omega
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at houter
            change us_w ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at houter
            subst houter
            exact hih

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Lockstep value invariant for `runTrace`'s inner simulation. Three coupled invariants
travel together along the simulation:

* **(prefix)** the trace's internal `queryLog` only ever extends `l₀`;
* **(monotonicity)** any pre-existing entry in `c₀` is preserved in the final `roCache`;
* **(lockstep)** every cache-miss entry in the trace's `queryLog` is paired in lockstep with
  the corresponding `Sum.inr ()` answer in the outer log. Specifically, for every position
  `i ∈ [l₀.length, z.queryLog.length)`, the trace's cache stores some value `ω` for the
  query `z.queryLog[i]`, and the outer log's `(i - l₀.length)`-th `Sum.inr ()` response is
  the same `ω`.

This is the value-level strengthening of `queryLog_length_eq_outer_inr_count`: the latter
only counts entries, while this lemma threads the recorded values through the cache and the
outer log together. -/
private theorem queryLog_cache_outer_lockstep
    [DecidableEq Chal]
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z : γ × simSt M Commit Chal}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (hz : (z, outerLog) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run)) :
    (∃ l_new, z.2.2 = l₀ ++ l_new) ∧
    (∀ mc ω, c₀ mc = some ω → z.2.1 mc = some ω) ∧
    (∀ i, l₀.length ≤ i → ∀ (h_hi : i < z.2.2.length),
      ∃ ω, z.2.1 (z.2.2[i]'h_hi) = some ω ∧
        QueryLog.getQueryValue? outerLog (Sum.inr ()) (i - l₀.length) = some ω) := by
  classical
  induction Y using OracleComp.inductionOn generalizing c₀ l₀ z outerLog with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
      obtain ⟨hz_eq, hlog_eq⟩ := hz
      subst hz_eq
      subst hlog_eq
      refine ⟨⟨[], by simp⟩, ?_, ?_⟩
      · intro mc ω h; exact h
      · intro i h_lo h_hi
        change i < l₀.length at h_hi
        omega
  | query_bind t oa ih =>
      have hY :
          (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
            ((liftM (query t) : OracleComp _ _) >>= oa)).run (c₀, l₀) =
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀)) >>= fun us =>
              (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) (oa us.1)).run us.2 := by
        simp [simulateQ_bind, simulateQ_query, StateT.run_bind,
          map_eq_bind_pure_comp, OracleQuery.cont_query, OracleQuery.input_query]
      rw [hY, simulateQ_bind, WriterT.run_bind', support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := hz
      have hpw_split : (pw.1, pw.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w.1.1)).run us_w.1.2)).run) := by
        change pw ∈ support _
        exact hpw
      have hih := ih (u := us_w.1.1) (c₀ := us_w.1.2.1) (l₀ := us_w.1.2.2)
        (z := pw.1) (outerLog := pw.2) hpw_split
      have hz_eq' : (pw.1, us_w.2 ++ pw.2) = (z, outerLog) := by
        rw [show ((pw.1, us_w.2 ++ pw.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w.2 ++ x) pw from rfl]
        exact hz_eq
      obtain ⟨hz_eq1, hz_eq2⟩ := Prod.mk.inj hz_eq'
      have hzeq : z = pw.1 := hz_eq1.symm
      have houter_eq : outerLog = us_w.2 ++ pw.2 := hz_eq2.symm
      subst hzeq
      subst houter_eq
      have houter : us_w ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w
      cases t with
      | inl n =>
          have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run (c₀, l₀) =
              (liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifFwd]
          rw [hrun] at houter
          change us_w ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec Chal) (Sum.inl n) (fun u => pure (u, (c₀, l₀)))] at houter
          rw [support_bind] at houter
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at houter
          obtain ⟨_, ⟨u, hu_eq⟩, hus_w_in_u⟩ := houter
          subst hu_eq
          rw [Set.mem_singleton_iff] at hus_w_in_u
          subst hus_w_in_u
          obtain ⟨⟨l_new, hpref⟩, hmono, hlock⟩ := hih
          refine ⟨⟨l_new, hpref⟩, hmono, ?_⟩
          intro i h_lo h_hi
          obtain ⟨ω, hcache, hlog⟩ := hlock i h_lo h_hi
          refine ⟨ω, hcache, ?_⟩
          change QueryLog.getQueryValue?
            ((⟨Sum.inl n, u⟩ : (j : ℕ ⊕ Unit) × (wrappedSpec Chal).Range j)
              :: pw.2) (Sum.inr ()) (i - l₀.length) = some ω
          rw [QueryLog.getQueryValue?_cons_of_ne]
          · exact hlog
          · exact Sum.inl_ne_inr
      | inr mc =>
          by_cases hcache : c₀ mc = none
          · have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) =
                (liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at houter
            change us_w ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec Chal) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])))] at houter
            rw [support_bind] at houter
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at houter
            obtain ⟨_, ⟨v, hv_eq⟩, hus_w_in_u⟩ := houter
            subst hv_eq
            rw [Set.mem_singleton_iff] at hus_w_in_u
            subst hus_w_in_u
            obtain ⟨⟨l_new', hpref'⟩, hmono', hlock'⟩ := hih
            dsimp only at hpref' hmono' hlock'
            have hpref_z : pw.1.2.2 = l₀ ++ ([mc] ++ l_new') := by
              rw [hpref']
              simp [List.append_assoc]
            refine ⟨⟨[mc] ++ l_new', hpref_z⟩, ?_, ?_⟩
            · intro mc' ω hmc'
              apply hmono'
              by_cases heq : mc' = mc
              · subst heq; rw [hcache] at hmc'; exact (Option.some_ne_none ω hmc'.symm).elim
              · rw [QueryCache.cacheQuery_of_ne _ _ heq]; exact hmc'
            · intro i h_lo h_hi
              by_cases hi_eq : i = l₀.length
              · subst hi_eq
                have hidx : pw.1.2.2[l₀.length]'h_hi = mc := by
                  have h_hi'' : l₀.length < (l₀ ++ ([mc] ++ l_new')).length := by
                    rw [← List.append_assoc, ← hpref']; exact h_hi
                  have hcongr : pw.1.2.2[l₀.length]'h_hi =
                      (l₀ ++ ([mc] ++ l_new'))[l₀.length]'h_hi'' :=
                    List.getElem_of_eq hpref_z _
                  rw [hcongr]
                  rw [List.getElem_append_right (Nat.le_refl _)]
                  simp
                refine ⟨v, ?_, ?_⟩
                · rw [hidx]
                  exact hmono' mc v (QueryCache.cacheQuery_self c₀ mc v)
                · change QueryLog.getQueryValue?
                    ((⟨Sum.inr (), v⟩ : (j : ℕ ⊕ Unit) × (wrappedSpec Chal).Range j)
                      :: pw.2) (Sum.inr ()) (l₀.length - l₀.length) = some v
                  rw [Nat.sub_self]
                  exact QueryLog.getQueryValue?_cons_self_zero (Sum.inr ()) v pw.2
              · have h_lo' : (l₀ ++ [mc]).length ≤ i := by
                  simp [List.length_append]; omega
                obtain ⟨ω, hcacheω, hlogω⟩ := hlock' i h_lo' h_hi
                refine ⟨ω, hcacheω, ?_⟩
                obtain ⟨k, hk⟩ : ∃ k, i - l₀.length = k + 1 := ⟨i - l₀.length - 1, by omega⟩
                have hk_eq : k = i - (l₀ ++ [mc]).length := by
                  simp [List.length_append] at hk ⊢; omega
                change QueryLog.getQueryValue?
                  ((⟨Sum.inr (), v⟩ : (j : ℕ ⊕ Unit) × (wrappedSpec Chal).Range j)
                    :: pw.2) (Sum.inr ()) (i - l₀.length) = some ω
                rw [hk]
                rw [QueryLog.getQueryValue?_cons_self_succ]
                rw [hk_eq]
                exact hlogω
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at houter
            change us_w ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at houter
            subst houter
            obtain ⟨⟨l_new, hpref⟩, hmono, hlock⟩ := hih
            refine ⟨⟨l_new, hpref⟩, hmono, ?_⟩
            intro i h_lo h_hi
            obtain ⟨ω, hcacheω, hlogω⟩ := hlock i h_lo h_hi
            refine ⟨ω, hcacheω, ?_⟩
            change QueryLog.getQueryValue? ([] ++ pw.2)
              (Sum.inr ()) (i - l₀.length) = some ω
            rw [List.nil_append]
            exact hlogω

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Prefix monotonicity: running `(simulateQ (unifFwd + roImpl) Y).run (c₀, l₀)` produces a
final simulator state whose `queryLog` component extends `l₀`. The resulting list always
starts with the initial `l₀`: cache misses only append entries, and cache hits plus
`unifFwd`-forwarded queries never touch `l₀`. Used by `inner_prefix_det` to fix the first
`l₀.length` positions of the final `queryLog`. -/
private theorem queryLog_extends_l₀
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z : γ × simSt M Commit Chal}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (h : (z, outerLog) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run)) :
    z.2.2.take l₀.length = l₀ := by
  classical
  induction Y using OracleComp.inductionOn generalizing c₀ l₀ z outerLog with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨hz_eq, _⟩ := h
      rw [hz_eq]
      exact List.take_length
  | query_bind t oa ih =>
      have hY :
          (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
            ((liftM (query t) : OracleComp _ _) >>= oa)).run (c₀, l₀) =
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀)) >>= fun us =>
              (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) (oa us.1)).run us.2 := by
        simp [simulateQ_bind, simulateQ_query, StateT.run_bind,
          map_eq_bind_pure_comp, OracleQuery.cont_query, OracleQuery.input_query]
      rw [hY, simulateQ_bind, WriterT.run_bind', support_bind] at h
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := h
      have hpw_split : (pw.1, pw.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w.1.1)).run us_w.1.2)).run) := by
        change pw ∈ support _
        exact hpw
      have hz_eq' : (pw.1, us_w.2 ++ pw.2) = (z, outerLog) := by
        rw [show ((pw.1, us_w.2 ++ pw.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w.2 ++ x) pw from rfl]
        exact hz_eq
      obtain ⟨hz_eq1, _⟩ := Prod.mk.inj hz_eq'
      have hzeq : z = pw.1 := hz_eq1.symm
      subst hzeq
      have houter : us_w ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w
      cases t with
      | inl n =>
          have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run
              (c₀, l₀) =
              (liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifFwd]
          rw [hrun] at houter
          change us_w ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec Chal) (Sum.inl n) (fun u => pure (u, (c₀, l₀)))] at houter
          rw [support_bind] at houter
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at houter
          obtain ⟨_, ⟨u, hu_eq⟩, hus_w_in⟩ := houter
          subst hu_eq
          rw [Set.mem_singleton_iff] at hus_w_in
          subst hus_w_in
          exact ih u c₀ l₀ hpw_split
      | inr mc =>
          by_cases hcache : c₀ mc = none
          · have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) =
                (liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at houter
            change us_w ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec Chal) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])))] at houter
            rw [support_bind] at houter
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at houter
            obtain ⟨_, ⟨v, hv_eq⟩, hus_w_in⟩ := houter
            subst hv_eq
            rw [Set.mem_singleton_iff] at hus_w_in
            subst hus_w_in
            have hih := ih v (c₀.cacheQuery mc v) (l₀ ++ [mc]) hpw_split
            have hlen_le : l₀.length ≤ (l₀ ++ [mc]).length := by
              simp [List.length_append]
            calc pw.1.2.2.take l₀.length
                = (pw.1.2.2.take (l₀ ++ [mc]).length).take l₀.length := by
                    rw [List.take_take, min_eq_left hlen_le]
              _ = (l₀ ++ [mc]).take l₀.length := by rw [hih]
              _ = l₀ := List.take_left
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at houter
            change us_w ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at houter
            subst houter
            exact ih v c₀ l₀ hpw_split

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Outer-log **prefix**-determinism for `runTrace`'s inner simulation. If the two outer
logs share a common prefix `p` (with `#{Sum.inr ()} = j` in `p`), then the first
`l₀.length + j` positions of the final internal `queryLog`s coincide. This is the
bisimulation up to the fork query that powers `target_eq_of_mem_forkReplay`: a common outer
prefix fixes the adversary's state (and hence the next cache-miss input) up through the
fork. -/
private theorem inner_prefix_det
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z₁ z₂ : γ × simSt M Commit Chal}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec Chal)}
    (h₁ : (z₁, outerLog₁) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run))
    (h₂ : (z₂, outerLog₂) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run))
    (p suffix₁ suffix₂ : QueryLog (wrappedSpec Chal))
    (hlog₁ : outerLog₁ = p ++ suffix₁)
    (hlog₂ : outerLog₂ = p ++ suffix₂) :
    z₁.2.2.take (l₀.length + p.countQ (· = Sum.inr ())) =
      z₂.2.2.take (l₀.length + p.countQ (· = Sum.inr ())) := by
  classical
  induction Y using OracleComp.inductionOn generalizing
      c₀ l₀ z₁ z₂ outerLog₁ outerLog₂ p suffix₁ suffix₂ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
      obtain ⟨hz₁_eq, houter₁'⟩ := h₁
      obtain ⟨hz₂_eq, _⟩ := h₂
      rw [houter₁'] at hlog₁
      have hp_empty : p = [] := by
        cases p with
        | nil => rfl
        | cons _ _ => simp at hlog₁
      subst hp_empty
      simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
      rw [hz₁_eq, hz₂_eq]
  | query_bind t oa ih =>
      have hY :
          (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
            ((liftM (query t) : OracleComp _ _) >>= oa)).run (c₀, l₀) =
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀)) >>= fun us =>
              (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) (oa us.1)).run us.2 := by
        simp [simulateQ_bind, simulateQ_query, StateT.run_bind,
          map_eq_bind_pure_comp, OracleQuery.cont_query, OracleQuery.input_query]
      rw [hY, simulateQ_bind, WriterT.run_bind', support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      have hpw₁_split : (pw₁.1, pw₁.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w₁.1.1)).run us_w₁.1.2)).run) := by
        change pw₁ ∈ support _
        exact hpw₁
      have hpw₂_split : (pw₂.1, pw₂.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w₂.1.1)).run us_w₂.1.2)).run) := by
        change pw₂ ∈ support _
        exact hpw₂
      have hz_eq'₁ : (pw₁.1, us_w₁.2 ++ pw₁.2) = (z₁, outerLog₁) := by
        rw [show ((pw₁.1, us_w₁.2 ++ pw₁.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w₁.2 ++ x) pw₁ from rfl]
        exact hz_eq₁
      have hz_eq'₂ : (pw₂.1, us_w₂.2 ++ pw₂.2) = (z₂, outerLog₂) := by
        rw [show ((pw₂.1, us_w₂.2 ++ pw₂.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w₂.2 ++ x) pw₂ from rfl]
        exact hz_eq₂
      obtain ⟨hz_eq1₁, hz_eq2₁⟩ := Prod.mk.inj hz_eq'₁
      obtain ⟨hz_eq1₂, hz_eq2₂⟩ := Prod.mk.inj hz_eq'₂
      have hzeq₁ : z₁ = pw₁.1 := hz_eq1₁.symm
      have hzeq₂ : z₂ = pw₂.1 := hz_eq1₂.symm
      subst hzeq₁
      subst hzeq₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ suffix₁ := hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ suffix₂ := hz_eq2₂.trans hlog₂
      have houter₁ : us_w₁ ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w₁
      have houter₂ : us_w₂ ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w₂
      cases t with
      | inl n =>
          have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run
              (c₀, l₀) =
              (liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifFwd]
          rw [hrun] at houter₁ houter₂
          change us_w₁ ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter₁
          change us_w₂ ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter₂
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec Chal) (Sum.inl n) (fun u => pure (u, (c₀, l₀)))] at houter₁ houter₂
          rw [support_bind] at houter₁ houter₂
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at houter₁ houter₂
          obtain ⟨_, ⟨u₁, hu₁_eq⟩, hus_w₁_in⟩ := houter₁
          obtain ⟨_, ⟨u₂, hu₂_eq⟩, hus_w₂_in⟩ := houter₂
          subst hu₁_eq
          subst hu₂_eq
          rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
          subst hus_w₁_in
          subst hus_w₂_in
          cases p with
          | nil =>
              simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
              have h₁' : pw₁.1.2.2.take l₀.length = l₀ :=
                queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                  (oa u₁) c₀ l₀ hpw₁_split
              have h₂' : pw₂.1.2.2.take l₀.length = l₀ :=
                queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                  (oa u₂) c₀ l₀ hpw₂_split
              rw [h₁', h₂']
          | cons p_head p_tail =>
              simp only [List.cons_append, List.cons.injEq]
                at houter₁_eq houter₂_eq
              obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
              obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
              have hu_eq : u₁ = u₂ := by
                have := hhead₁.trans hhead₂.symm
                obtain ⟨_, hheq⟩ := Sigma.mk.inj this
                exact eq_of_heq hheq
              subst hu_eq
              have hpH_fst : p_head.1 ≠ Sum.inr () := by
                rw [← hhead₁]; intro h; cases h
              have hp_count :
                  QueryLog.countQ (spec := wrappedSpec Chal) (p_head :: p_tail)
                      (· = Sum.inr ()) =
                    QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) := by
                simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
              rw [hp_count]
              exact ih u₁ c₀ l₀ hpw₁_split hpw₂_split p_tail suffix₁ suffix₂ htail₁ htail₂
      | inr mc =>
          by_cases hcache : c₀ mc = none
          · have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) =
                (liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at houter₁ houter₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter₂
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec Chal) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])))] at houter₁ houter₂
            rw [support_bind] at houter₁ houter₂
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at houter₁ houter₂
            obtain ⟨_, ⟨v₁, hv₁_eq⟩, hus_w₁_in⟩ := houter₁
            obtain ⟨_, ⟨v₂, hv₂_eq⟩, hus_w₂_in⟩ := houter₂
            subst hv₁_eq
            subst hv₂_eq
            rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
            subst hus_w₁_in
            subst hus_w₂_in
            cases p with
            | nil =>
                simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                have h₁' : pw₁.1.2.2.take l₀.length = l₀ := by
                  have h1 := queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                    (oa v₁) (c₀.cacheQuery mc v₁) (l₀ ++ [mc]) hpw₁_split
                  have hlen_le : l₀.length ≤ (l₀ ++ [mc]).length := by
                    simp [List.length_append]
                  calc pw₁.1.2.2.take l₀.length
                      = (pw₁.1.2.2.take (l₀ ++ [mc]).length).take l₀.length := by
                          rw [List.take_take, min_eq_left hlen_le]
                    _ = (l₀ ++ [mc]).take l₀.length := by rw [h1]
                    _ = l₀ := List.take_left
                have h₂' : pw₂.1.2.2.take l₀.length = l₀ := by
                  have h2 := queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                    (oa v₂) (c₀.cacheQuery mc v₂) (l₀ ++ [mc]) hpw₂_split
                  have hlen_le : l₀.length ≤ (l₀ ++ [mc]).length := by
                    simp [List.length_append]
                  calc pw₂.1.2.2.take l₀.length
                      = (pw₂.1.2.2.take (l₀ ++ [mc]).length).take l₀.length := by
                          rw [List.take_take, min_eq_left hlen_le]
                    _ = (l₀ ++ [mc]).take l₀.length := by rw [h2]
                    _ = l₀ := List.take_left
                rw [h₁', h₂']
            | cons p_head p_tail =>
                simp only [List.cons_append, List.cons.injEq]
                  at houter₁_eq houter₂_eq
                obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
                obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
                have hv_eq : v₁ = v₂ := by
                  have := hhead₁.trans hhead₂.symm
                  obtain ⟨_, hheq⟩ := Sigma.mk.inj this
                  exact eq_of_heq hheq
                subst hv_eq
                have hpH_fst : p_head.1 = Sum.inr () := by rw [← hhead₁]
                have hp_count :
                    QueryLog.countQ (spec := wrappedSpec Chal) (p_head :: p_tail)
                        (· = Sum.inr ()) =
                      QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) + 1 := by
                  simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
                rw [hp_count]
                have hlen_eq : l₀.length +
                      (QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) + 1) =
                    (l₀ ++ [mc]).length +
                      QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) := by
                  have : (l₀ ++ [mc]).length = l₀.length + 1 := by
                    simp [List.length_append]
                  omega
                rw [hlen_eq]
                exact ih v₁ (c₀.cacheQuery mc v₁) (l₀ ++ [mc])
                  hpw₁_split hpw₂_split p_tail suffix₁ suffix₂ htail₁ htail₂
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at houter₁ houter₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter₂
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at houter₁ houter₂
            subst houter₁
            subst houter₂
            exact ih v c₀ l₀ hpw₁_split hpw₂_split p suffix₁ suffix₂ houter₁_eq houter₂_eq

omit [SampleableType Stmt] [SampleableType Wit] in
/-- One-more-step extension of `inner_prefix_det`: if the outer logs of two runs share the
prefix `p ++ [⟨Sum.inr (), v_i⟩]` (allowing the values `v₁, v₂` at position `|p|` to differ),
then the internal `queryLog`s coincide for one more entry than `inner_prefix_det` guarantees,
namely up to position `l₀.length + p.countQ(· = Sum.inr ()) + 1`. The extra entry is the
input `mc` of the next cache-miss query issued by the adversary: its value is determined by
the adversary's state after consuming the shared prefix `p`, which is common to both runs. -/
private theorem inner_prefix_det_one_more_inr
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z₁ z₂ : γ × simSt M Commit Chal}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec Chal)}
    (h₁ : (z₁, outerLog₁) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run))
    (h₂ : (z₂, outerLog₂) ∈ support
      ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
        ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run))
    (p : QueryLog (wrappedSpec Chal))
    {v₁ v₂ : Chal} {rest₁ rest₂ : QueryLog (wrappedSpec Chal)}
    (hlog₁ : outerLog₁ = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁))
    (hlog₂ : outerLog₂ = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂)) :
    z₁.2.2.take (l₀.length + p.countQ (· = Sum.inr ()) + 1) =
      z₂.2.2.take (l₀.length + p.countQ (· = Sum.inr ()) + 1) := by
  classical
  induction Y using OracleComp.inductionOn generalizing
      c₀ l₀ z₁ z₂ outerLog₁ outerLog₂ p v₁ v₂ rest₁ rest₂ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₁
      obtain ⟨_, houter₁'⟩ := h₁
      rw [houter₁'] at hlog₁
      simp at hlog₁
  | query_bind t oa ih =>
      have hY :
          (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
            ((liftM (query t) : OracleComp _ _) >>= oa)).run (c₀, l₀) =
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀)) >>= fun us =>
              (simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal) (oa us.1)).run us.2 := by
        simp [simulateQ_bind, simulateQ_query, StateT.run_bind,
          map_eq_bind_pure_comp, OracleQuery.cont_query, OracleQuery.input_query]
      rw [hY, simulateQ_bind, WriterT.run_bind', support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      have hpw₁_split : (pw₁.1, pw₁.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w₁.1.1)).run us_w₁.1.2)).run) := by
        change pw₁ ∈ support _
        exact hpw₁
      have hpw₂_split : (pw₂.1, pw₂.2) ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            ((simulateQ (unifFwd M Commit Chal + roImpl M Commit Chal)
              (oa us_w₂.1.1)).run us_w₂.1.2)).run) := by
        change pw₂ ∈ support _
        exact hpw₂
      have hz_eq'₁ : (pw₁.1, us_w₁.2 ++ pw₁.2) = (z₁, outerLog₁) := by
        rw [show ((pw₁.1, us_w₁.2 ++ pw₁.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w₁.2 ++ x) pw₁ from rfl]
        exact hz_eq₁
      have hz_eq'₂ : (pw₂.1, us_w₂.2 ++ pw₂.2) = (z₂, outerLog₂) := by
        rw [show ((pw₂.1, us_w₂.2 ++ pw₂.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w₂.2 ++ x) pw₂ from rfl]
        exact hz_eq₂
      obtain ⟨hz_eq1₁, hz_eq2₁⟩ := Prod.mk.inj hz_eq'₁
      obtain ⟨hz_eq1₂, hz_eq2₂⟩ := Prod.mk.inj hz_eq'₂
      have hzeq₁ : z₁ = pw₁.1 := hz_eq1₁.symm
      have hzeq₂ : z₂ = pw₂.1 := hz_eq1₂.symm
      subst hzeq₁
      subst hzeq₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁) :=
        hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂) :=
        hz_eq2₂.trans hlog₂
      have houter₁ : us_w₁ ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w₁
      have houter₂ : us_w₂ ∈ support
          ((simulateQ (loggingOracle (spec := wrappedSpec Chal))
            (((unifFwd M Commit Chal + roImpl M Commit Chal) t).run (c₀, l₀))).run) := hus_w₂
      cases t with
      | inl n =>
          have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run
              (c₀, l₀) =
              (liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifFwd]
          rw [hrun] at houter₁ houter₂
          change us_w₁ ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter₁
          change us_w₂ ∈ support (simulateQ loggingOracle
              ((liftM (query (spec := wrappedSpec Chal) (Sum.inl n)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at houter₂
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec Chal) (Sum.inl n)
            (fun u => pure (u, (c₀, l₀)))] at houter₁ houter₂
          rw [support_bind] at houter₁ houter₂
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at houter₁ houter₂
          obtain ⟨_, ⟨u₁, hu₁_eq⟩, hus_w₁_in⟩ := houter₁
          obtain ⟨_, ⟨u₂, hu₂_eq⟩, hus_w₂_in⟩ := houter₂
          subst hu₁_eq
          subst hu₂_eq
          rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
          subst hus_w₁_in
          subst hus_w₂_in
          cases p with
          | nil =>
              simp at houter₁_eq
          | cons p_head p_tail =>
              simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
              obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
              obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
              have hu_eq : u₁ = u₂ := by
                have := hhead₁.trans hhead₂.symm
                obtain ⟨_, hheq⟩ := Sigma.mk.inj this
                exact eq_of_heq hheq
              subst hu_eq
              have hpH_fst : p_head.1 ≠ Sum.inr () := by
                rw [← hhead₁]; intro h; cases h
              have hp_count :
                  QueryLog.countQ (spec := wrappedSpec Chal) (p_head :: p_tail)
                      (· = Sum.inr ()) =
                    QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) := by
                simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
              rw [hp_count]
              exact ih u₁ c₀ l₀ hpw₁_split hpw₂_split p_tail htail₁ htail₂
      | inr mc =>
          by_cases hcache : c₀ mc = none
          · have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) =
                (liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at houter₁ houter₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((liftM (query (spec := wrappedSpec Chal) (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
                    OracleComp _ _))).run at houter₂
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec Chal) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])))] at houter₁ houter₂
            rw [support_bind] at houter₁ houter₂
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at houter₁ houter₂
            obtain ⟨_, ⟨w₁, hw₁_eq⟩, hus_w₁_in⟩ := houter₁
            obtain ⟨_, ⟨w₂, hw₂_eq⟩, hus_w₂_in⟩ := houter₂
            subst hw₁_eq
            subst hw₂_eq
            rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
            subst hus_w₁_in
            subst hus_w₂_in
            cases p with
            | nil =>
                simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                have h₁' : pw₁.1.2.2.take (l₀ ++ [mc]).length = l₀ ++ [mc] :=
                  queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                    (oa w₁) (c₀.cacheQuery mc w₁) (l₀ ++ [mc]) hpw₁_split
                have h₂' : pw₂.1.2.2.take (l₀ ++ [mc]).length = l₀ ++ [mc] :=
                  queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                    (oa w₂) (c₀.cacheQuery mc w₂) (l₀ ++ [mc]) hpw₂_split
                have hlen : (l₀ ++ [mc]).length = l₀.length + 1 := by
                  simp [List.length_append]
                rw [← hlen, h₁', h₂']
            | cons p_head p_tail =>
                simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
                obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
                obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
                have hw_eq : w₁ = w₂ := by
                  have := hhead₁.trans hhead₂.symm
                  obtain ⟨_, hheq⟩ := Sigma.mk.inj this
                  exact eq_of_heq hheq
                subst hw_eq
                have hpH_fst : p_head.1 = Sum.inr () := by rw [← hhead₁]
                have hp_count :
                    QueryLog.countQ (spec := wrappedSpec Chal) (p_head :: p_tail)
                        (· = Sum.inr ()) =
                      QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ())
                        + 1 := by
                  simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
                rw [hp_count]
                have hlen_eq : l₀.length +
                      (QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ())
                        + 1) + 1 =
                    (l₀ ++ [mc]).length +
                      QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ())
                        + 1 := by
                  have : (l₀ ++ [mc]).length = l₀.length + 1 := by
                    simp [List.length_append]
                  omega
                rw [hlen_eq]
                exact ih w₁ (c₀.cacheQuery mc w₁) (l₀ ++ [mc])
                  hpw₁_split hpw₂_split p_tail htail₁ htail₂
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifFwd M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at houter₁ houter₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at houter₂
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at houter₁ houter₂
            subst houter₁
            subst houter₂
            exact ih v c₀ l₀ hpw₁_split hpw₂_split p houter₁_eq houter₂_eq

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Specialization of `queryLog_length_eq_outer_inr_count` to `runTrace`'s initial state
`(∅, [])`: the trace's `queryLog` has the same length as the count of `Sum.inr ()` outer
queries in the recorded log. -/
lemma runTrace_queryLog_length_eq
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt)
    {x : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk))) :
    x.queryLog.length = outerLog.countQ (· = Sum.inr ()) := by
  classical
  unfold replayFirstRun runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hxqueryLog : x.queryLog = a.1.2.2 := by
    have := congrArg Prod.fst ha_eq
    have h2 := congrArg Trace.queryLog this
    simpa [Prod.map_apply, Trace.queryLog] using h2.symm
  have hlog_eq : a.2 = outerLog := by
    have := congrArg Prod.snd ha_eq
    simpa [Prod.map_apply] using this
  rw [hxqueryLog, ← hlog_eq]
  have h := queryLog_length_eq_outer_inr_count (M := M) (Commit := Commit) (Chal := Chal)
    (γ := (M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache)
    (nmaAdv.main pk) ∅ [] (z := a.1) (outerLog := a.2) ha_mem
  simpa using h

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Specialization of `queryLog_cache_outer_lockstep` to `runTrace`'s initial state
`(∅, [])`: the trace's `queryLog[i]` is cached in `x.roCache`, and the cached value matches
the outer log's `i`-th `Sum.inr ()` response. -/
lemma runTrace_cache_outer_lockstep
    [SampleableType Chal] [DecidableEq Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt)
    {x : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk))) :
    ∀ i, ∀ (h_hi : i < x.queryLog.length),
      ∃ ω, x.roCache (x.queryLog[i]'h_hi) = some ω ∧
        QueryLog.getQueryValue? outerLog (Sum.inr ()) i = some ω := by
  classical
  unfold replayFirstRun runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hxqueryLog : x.queryLog = a.1.2.2 := by
    have := congrArg Prod.fst ha_eq
    have h2 := congrArg Trace.queryLog this
    simpa [Prod.map_apply, Trace.queryLog] using h2.symm
  have hxroCache : x.roCache = a.1.2.1 := by
    have := congrArg Prod.fst ha_eq
    have h2 := congrArg Trace.roCache this
    simpa [Prod.map_apply, Trace.roCache] using h2.symm
  have hlog_eq : a.2 = outerLog := by
    have := congrArg Prod.snd ha_eq
    simpa [Prod.map_apply] using this
  intro i h_hi
  have h_hi' : i < a.1.2.2.length := by rw [← hxqueryLog]; exact h_hi
  obtain ⟨_, _, hlock⟩ :=
    queryLog_cache_outer_lockstep (M := M) (Commit := Commit) (Chal := Chal)
      (γ := (M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache)
      (nmaAdv.main pk) ∅ [] (z := a.1) (outerLog := a.2) ha_mem
  obtain ⟨ω, hcache, hlog⟩ := hlock i (Nat.zero_le _) h_hi'
  refine ⟨ω, ?_, ?_⟩
  · rw [hxroCache]
    have hcongr : x.queryLog[i]'h_hi = a.1.2.2[i]'h_hi' :=
      List.getElem_of_eq hxqueryLog _
    rw [hcongr]
    exact hcache
  · rw [← hlog_eq]
    simpa using hlog

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Decoding the `verified` flag of a trace produced by `runTrace`. If the trace's
`verified` field is `true`, then there is a cached challenge `ω` for `x.target` and the
corresponding `σ.verify` succeeds. Used by `forkSupportInvariant_of_mem_replayFirstRun`. -/
lemma runTrace_verified_imp_verify
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt)
    {x : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk)))
    (hv : x.verified = true) :
    ∃ ω, x.roCache x.target = some ω ∧
      σ.verify pk x.target.2 ω x.forgery.2.2 = true := by
  classical
  unfold replayFirstRun runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, _, ha_eq⟩ := hx
  obtain ⟨⟨⟨forgery, advCache⟩, ⟨roCache, queryLog⟩⟩, log_a⟩ := a
  obtain ⟨msg, c, s⟩ := forgery
  have hxeq : x =
      ({ forgery := (msg, c, s),
         advCache := advCache,
         roCache := roCache,
         queryLog := queryLog,
         verified :=
           match roCache (msg, c) with
           | some ω => σ.verify pk c ω s
           | none => false } :
        Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := by
    have := congrArg Prod.fst ha_eq
    simpa using this.symm
  rw [hxeq]
  rw [hxeq] at hv
  simp only [Trace.target] at *
  match hcase : roCache (msg, c), hv with
  | none, hv => simp at hv
  | some ω, hv =>
      refine ⟨ω, rfl, ?_⟩
      simpa using hv

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The `forkPoint`-based reachability invariant for `runTrace`: whenever
`forkPoint qH x = some s`, the outer `QueryLog` of `replayFirstRun (runTrace ...)` has a
`Sum.inr ()` query at position `↑s`. This holds because each cache miss in `runTrace`'s
`roImpl` issues exactly one `Sum.inr ()` query and appends one entry to the trace's
internal `queryLog`, so the trace's logical fork index `s` (an offset into
`trace.queryLog`) always corresponds to a real outer-log query at the same position. -/
theorem runTrace_forkPoint_CfReachable
    [DecidableEq Chal] [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt) :
    CfReachable (runTrace σ hr M nmaAdv pk)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => qH) (Sum.inr ())
      (forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH) := by
  intro x log hx s hs
  have hlen : x.queryLog.length = log.countQ (· = Sum.inr ()) :=
    runTrace_queryLog_length_eq σ hr M nmaAdv pk hx
  have htarget : x.queryLog[(↑s : ℕ)]? = some x.target :=
    forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hslt : (↑s : ℕ) < x.queryLog.length := by
    by_contra hge
    push Not at hge
    have hnone : x.queryLog[(↑s : ℕ)]? = none := List.getElem?_eq_none hge
    rw [hnone] at htarget
    exact (Option.some_ne_none x.target htarget.symm).elim
  have hslt' : (↑s : ℕ) < (log.getQ (· = Sum.inr ())).length := by
    change (↑s : ℕ) < log.countQ (· = Sum.inr ())
    rw [← hlen]
    exact hslt
  exact QueryLog.getQueryValue?_isSome_of_lt log (Sum.inr ()) ↑s hslt'

omit [SampleableType Stmt] [SampleableType Wit] in
/-- **Determinism of `runTrace`'s inner `queryLog` from the outer-log prefix.** If the outer
logs of two runs of `runTrace` share a prefix `p` followed by a `Sum.inr ()` query (whose
response may differ across runs), then the traces' internal `queryLog`s coincide on the first
`p.countQ (· = Sum.inr ()) + 1` entries. This is the `runTrace` specialization of
`inner_prefix_det_one_more_inr`, rephrased at the `replayFirstRun`-visible level. -/
lemma runTrace_queryLog_take_eq
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt)
    {x₁ x₂ : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec Chal)}
    (h₁ : (x₁, outerLog₁) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk)))
    (h₂ : (x₂, outerLog₂) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk)))
    (p : QueryLog (wrappedSpec Chal))
    {v₁ v₂ : Chal} {rest₁ rest₂ : QueryLog (wrappedSpec Chal)}
    (hlog₁ : outerLog₁ = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁))
    (hlog₂ : outerLog₂ = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂)) :
    x₁.queryLog.take (p.countQ (· = Sum.inr ()) + 1) =
      x₂.queryLog.take (p.countQ (· = Sum.inr ()) + 1) := by
  classical
  unfold replayFirstRun runTrace at h₁ h₂
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at h₁ h₂
  obtain ⟨a₁, ha_mem₁, ha_eq₁⟩ := h₁
  obtain ⟨a₂, ha_mem₂, ha_eq₂⟩ := h₂
  have hxqL₁ : x₁.queryLog = a₁.1.2.2 := by
    have := congrArg Prod.fst ha_eq₁
    have h3 := congrArg Trace.queryLog this
    simpa [Prod.map_apply, Trace.queryLog] using h3.symm
  have hxqL₂ : x₂.queryLog = a₂.1.2.2 := by
    have := congrArg Prod.fst ha_eq₂
    have h3 := congrArg Trace.queryLog this
    simpa [Prod.map_apply, Trace.queryLog] using h3.symm
  have hlog_eq₁ : a₁.2 = outerLog₁ := by
    have := congrArg Prod.snd ha_eq₁
    simpa [Prod.map_apply] using this
  have hlog_eq₂ : a₂.2 = outerLog₂ := by
    have := congrArg Prod.snd ha_eq₂
    simpa [Prod.map_apply] using this
  rw [hxqL₁, hxqL₂]
  have hdet := inner_prefix_det_one_more_inr (M := M) (Commit := Commit) (Chal := Chal)
    (γ := (M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache)
    (nmaAdv.main pk) ∅ []
    (z₁ := a₁.1) (z₂ := a₂.1)
    (outerLog₁ := a₁.2) (outerLog₂ := a₂.2)
    ha_mem₁ ha_mem₂ p (v₁ := v₁) (v₂ := v₂)
    (rest₁ := rest₁) (rest₂ := rest₂)
    (hlog_eq₁.trans hlog₁) (hlog_eq₂.trans hlog₂)
  simpa using hdet

end Coupling

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Managed-RO replay-fork convenience theorem at a fixed public key, stated at the
`OracleComp (unifSpec + (Unit →ₒ Chal))` level.

This is the Fiat-Shamir-specific analogue of Firsov-Janku's `forking_lemma_ro` at
[fsec/proof/ForkingRO.ec:443](../../../fsec/proof/ForkingRO.ec). It packages the replay
quantitative bound with the distinct-answer and postcondition-transfer facts for the wrapped
managed random-oracle trace experiment, composing `le_probEvent_isSome_forkReplay`
(quantitative bound) and `forkReplay_propertyTransfer` (postcondition transfer).

**On the level of the statement.** We state the bound at the `OracleComp` level rather than
lifting through `simulateQ` to `ProbComp`. Each caller (e.g. `euf_nma_bound`) can bridge to
`ProbComp` in one line using `uniformSampleImpl.probEvent_simulateQ` when needed, keeping this
lemma focused on the forking-lemma content.

**On the target-equality conjunct.** A maximally-informative version would also conclude
`x₁.target = x₂.target` (i.e. message-commit pair coincidence at the fork point), matching
Firsov-Janku's `forking_lemma_ro`. In the Lean formalization this conjunct is consumed by the
downstream reduction `euf_nma_bound` to align the cached challenges `ω_i = x_i.roCache target`.
Since it relies on a value-level log-prefix invariant across `replayRunWithTraceValue` plus a
correspondence between the adversary's internal `queryLog` and the outer `QueryLog`, it is
extracted through the caller-provided `P_out` transfer predicate: the caller may choose `P_out`
so that `P_out x log` pins `x.target` to a deterministic function of `(log, cf x)`, and then
derive target-equality from the distinct-answer disagreement on the outer log.

**On the `hreach` hypothesis.** `CfReachable` ensures that whenever `forkPoint` selects an
index `s` for a trace `x`, the outer `QueryLog` actually has an `i = Sum.inr ()` query at
position `↑s`. For the FiatShamir setting this follows from the correspondence between the
trace's internal `queryLog : List (M × Commit)` and the outer `QueryLog` of `Sum.inr ()`
queries: each cache miss in `roImpl` appends to both simultaneously, so a logical index `s`
into the trace's list corresponds to the same physical position in the outer log. Callers
discharge `hreach` by establishing this correspondence at the level of `runTrace`.

**On typeclass requirements.** The `wrappedSpec Chal` oracle space is
`unifSpec + (Unit →ₒ Chal)`, and the quantitative section of `ReplayFork.lean` requires the
typeclass `[OracleSpec.LawfulSubSpec unifSpec spec]` (to factor `probOutput_uniformSample`
through `liftComp` on the `forkReplay` side). This instance is discharged by Mathlib
automation at this call site.

**Currently conditional on the two B1 prefix-faithfulness `sorry`s** (transitively via
`le_probEvent_isSome_forkReplay` → `sq_probOutput_main_le_noGuardReplayComp`
→ `evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt`
and `tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt`). -/
theorem replayForkingBound
    [DecidableEq M] [DecidableEq Commit]
    [DecidableEq Chal] [SampleableType Chal] [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    (P_out : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      QueryLog (unifSpec + (Unit →ₒ Chal)) → Prop)
    (hP : ∀ {x log},
      (x, log) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk)) →
      P_out x log)
    (hreach : CfReachable (runTrace σ hr M nmaAdv pk)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => qH) (Sum.inr ())
      (forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)) :
    let wrappedMain := runTrace σ hr M nmaAdv pk
    let cf := forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
    let qb : ℕ ⊕ Unit → ℕ := fun j => match j with | .inl _ => 0 | .inr () => qH
    let acc := Pr[ fun x => (cf x).isSome | wrappedMain]
    acc * (acc / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr[
        fun r : Option
            (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
          ∃ (x₁ x₂ :
              Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
            (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
            r = some (x₁, x₂) ∧
            cf x₁ = some s ∧
            cf x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
              QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
            P_out x₁ log₁ ∧
            P_out x₂ log₂
        | forkReplay wrappedMain qb (Sum.inr ()) cf] := by
  intro wrappedMain cf qb acc
  -- Step 1: Rewrite `acc` as `∑ s, Pr[= some s | cf <$> wrappedMain]`, matching the LHS of
  -- `le_probEvent_isSome_forkReplay`.
  classical
  have hAcc_sum :
      acc = ∑ s, Pr[= some s | cf <$> wrappedMain] := by
    simp only [acc]
    rw [show (fun x => (cf x).isSome = true) =
        (fun x : _ => (Option.isSome x = true)) ∘ cf from rfl,
      ← probEvent_map (q := fun r => Option.isSome r = true)]
    rw [probEvent_eq_tsum_ite]
    rw [tsum_option _ ENNReal.summable]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
      ↓reduceIte, zero_add]
    rw [tsum_fintype]
  rw [hAcc_sum]
  -- Step 2: Apply the forking lemma lower bound `le_probEvent_isSome_forkReplay`,
  -- then upgrade the RHS event from `isSome` to the structural postcondition using
  -- `forkReplay_propertyTransfer` through `probEvent_mono`.
  have hH_inv : (Fintype.card ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr ())) : ENNReal)⁻¹ =
      challengeSpaceInv Chal := rfl
  have hqb_eq : qb (Sum.inr ()) = qH := rfl
  calc (∑ s, Pr[= some s | cf <$> wrappedMain]) *
        ((∑ s, Pr[= some s | cf <$> wrappedMain]) / (↑qH + 1) - challengeSpaceInv Chal)
      = (∑ s, Pr[= some s | cf <$> wrappedMain]) *
        ((∑ s, Pr[= some s | cf <$> wrappedMain]) / ↑(qb (Sum.inr ()) + 1)
          - challengeSpaceInv Chal) := by rw [hqb_eq]; push_cast; ring_nf
    _ ≤ Pr[ fun r : Option
            (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
              r.isSome | forkReplay wrappedMain qb (Sum.inr ()) cf] := by
        have hbound := le_probEvent_isSome_forkReplay
          (main := wrappedMain) (qb := qb) (i := Sum.inr ()) (cf := cf) hreach
        simp only at hbound
        rw [hH_inv] at hbound
        exact hbound
    _ ≤ _ := by
        apply probEvent_mono
        intro r hr hisSome
        rcases r with _ | ⟨x₁, x₂⟩
        · simp at hisSome
        obtain ⟨log₁, log₂, s, hcf₁, hcf₂, hP₁, hP₂, hneq⟩ :=
          forkReplay_propertyTransfer
            (main := wrappedMain) (qb := qb) (i := Sum.inr ()) (cf := cf)
            (P_out := P_out) (hP := hP) hr
        exact ⟨x₁, x₂, s, log₁, log₂, rfl, hcf₁, hcf₂, hneq, hP₁, hP₂⟩

end Fork

end FiatShamir
