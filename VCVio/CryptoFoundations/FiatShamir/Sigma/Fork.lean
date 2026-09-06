/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.QueryBounds
public import VCVio.CryptoFoundations.FiatShamir.Sigma
public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.CryptoFoundations.SeededFork

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
`ReplayFork.contextFork_propertyTransfer` to drive the NMA-to-extraction step
of `euf_nma_bound`.

## Main definitions

* `Trace`: the forgery, adversary cache, random-oracle cache, live query log, and `verified`
  flag of one run.
* `forkPoint`: the query-log index at which to rewind the adversary.
* `wrappedSpec`: the single-oracle signature `unifSpec + (Unit →ₒ Chal)` that the fork runs in.
* `runTrace`: the wrapped NMA adversary, packaged as a forkable `OracleComp`.
* `exp` and `advantage`: the resulting security experiment and its advantage.

## Main results

* `queryLog_length_le_of_nmaHashQueryBound`: the query log respects the adversary's hash bound.
* `runTrace_forkPoint_CfReachable`: the fork point is reachable, discharging `ReplayFork`'s
  reachability side condition.
* `runTrace_target_eq_of_mem_contextFork`: both fork branches agree on the forgery target.
* `replayForkingBound`: the Fiat-Shamir replay forking bound.
-/

@[expose] public section

universe u v

open OracleComp OracleSpec

open scoped OracleSpec.PrimitiveQuery

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type}
     {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

namespace Fork

/- The fork proof repeatedly compares source and wrapped sum-spec response families. -/
attribute [local implicit_reducible] PFunctor.Obj

/-- Trace used by the Fiat-Shamir forking reduction for managed-RO NMA adversaries. Records
one run's forgery, the adversary's programmed cache, the live random-oracle cache, the live
query log, and whether the forgery verifies. -/
structure Trace where
  /-- The final `(message, (commitment, response))` triple produced by the adversary. -/
  forgery : M × (Commit × Resp)
  /-- Snapshot of the adversary's locally programmed random oracle. Only the reduction side
  reads from it: `runTrace.verified` and the forking bound treat it purely as bookkeeping. In
  the managed-RO model every adversary challenge query is routed through the live oracle, so
  programmed entries that ever actually influence a verified forgery also appear in `roCache`;
  this is the invariant that `euf_cma_to_nma` is responsible for establishing when it bridges
  `advCache`-only entries back to the live log. -/
  advCache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache
  /-- The live random-oracle cache populated by managed-RO queries during the run. -/
  roCache : (M × Commit →ₒ Chal).QueryCache
  /-- The list of `(message, commitment)` hash points actually queried (live). The forking
  lemma rewinds at a position of this list. -/
  queryLog : List (M × Commit)
  /-- Whether the forgery successfully verifies against a cached challenge for its target.
  `runTrace` consults only `roCache` for this flag (see its docstring). -/
  verified : Bool

/-- The hash point corresponding to the final forgery recorded in a fork trace. -/
def Trace.target (trace : @Trace Commit Chal Resp M) : M × Commit :=
  (trace.forgery.1, trace.forgery.2.1)

/-- Rewinding point extracted from a managed-RO fork trace. The fork is usable exactly when
the final forgery verifies and its hash point appears in the live query log. -/
def forkPoint [DecidableEq M] [DecidableEq Commit] (qH : ℕ)
    (trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    Option (Fin (qH + 1)) :=
  if trace.verified then
    if trace.target ∈ trace.queryLog then
      let idx := trace.queryLog.findIdx (· == trace.target)
      if hidx : idx < qH + 1 then some ⟨idx, hidx⟩ else none
    else none
  else none

/-- If `forkPoint` selects a rewinding index, the recorded forgery verifies. -/
lemma verified_of_forkPoint_eq_some [DecidableEq M] [DecidableEq Commit] {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)} {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH trace = some s) :
    trace.verified = true := by
  simp_all [forkPoint]

/-- If `forkPoint` selects a rewinding index, the recorded forgery's hash point appears in
the live query log. -/
lemma target_mem_queryLog_of_forkPoint_eq_some [DecidableEq M] [DecidableEq Commit] {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)} {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH trace = some s) :
    trace.target ∈ trace.queryLog := by
  simp_all [forkPoint]

/-- The index selected by `forkPoint` looks up the forgery's hash point in the live query
log: `trace.queryLog[s]?` equals `some trace.target`. -/
lemma forkPoint_getElem?_eq_some_target [DecidableEq M] [DecidableEq Commit] {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)} {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH trace = some s) :
    trace.queryLog[↑s]? = some trace.target := by
  grind [forkPoint]

/-- Wrapped oracle spec used by `runTrace`: uniform sampling plus a single counted challenge
oracle exposing the random-oracle entropy. -/
abbrev wrappedSpec (Chal : Type) : OracleSpec (ℕ ⊕ Unit) := unifSpec + (Unit →ₒ Chal)

/-- Internal simulator state of `runTrace`: the cached random-oracle answers paired with
the chronological list of cache-miss inputs (the trace's `queryLog`). -/
abbrev SimState (M Commit Chal : Type) : Type := (M × Commit →ₒ Chal).QueryCache × List (M × Commit)

/-- A uniform query in the wrapped target, with its component response family explicit. -/
def wrappedUniformQuery (Chal : Type) (n : unifSpec.Domain) :
    OracleComp (wrappedSpec Chal) (unifSpec.Range n) :=
  liftM ((wrappedSpec Chal).query (Sum.inl n))

/-- The challenge query in the wrapped target, with response type `Chal` explicit. -/
def wrappedChallengeQuery (Chal : Type) : OracleComp (wrappedSpec Chal) Chal :=
  liftM ((wrappedSpec Chal).query (Sum.inr ()))

/-- A uniform-response entry in the wrapped query log. -/
def wrappedUniformEntry (Chal : Type) (n : unifSpec.Domain) (u : unifSpec.Range n) :
    (j : (wrappedSpec Chal).Domain) × (wrappedSpec Chal).Range j :=
  ⟨Sum.inl n, u⟩

/-- A challenge-response entry in the wrapped query log. -/
def wrappedChallengeEntry (Chal : Type) (v : Chal) :
    (j : (wrappedSpec Chal).Domain) × (wrappedSpec Chal).Range j :=
  ⟨Sum.inr (), v⟩

@[simp] lemma wrappedUniformEntry_fst (Chal : Type) (n : unifSpec.Domain)
    (u : unifSpec.Range n) : (wrappedUniformEntry Chal n u).1 = Sum.inl n := rfl

@[simp] lemma wrappedChallengeEntry_fst (Chal : Type) (v : Chal) :
    (wrappedChallengeEntry Chal v).1 = Sum.inr () := rfl

@[simp]
lemma getQueryValue?_wrappedUniformEntry [DecidableEq Chal]
    (n : unifSpec.Domain) (u : unifSpec.Range n) (log : QueryLog (wrappedSpec Chal)) (k : ℕ) :
    QueryLog.getQueryValue? (wrappedUniformEntry Chal n u :: log) (Sum.inr ()) k =
      QueryLog.getQueryValue? log (Sum.inr ()) k := by
  apply QueryLog.getQueryValue?_cons_of_ne
  exact Sum.inl_ne_inr

@[simp]
lemma getQueryValue?_wrappedChallengeEntry_zero [DecidableEq Chal]
    (v : Chal) (log : QueryLog (wrappedSpec Chal)) :
    QueryLog.getQueryValue? (wrappedChallengeEntry Chal v :: log) (Sum.inr ()) 0 = some v := by
  simp [wrappedChallengeEntry]

@[simp]
lemma getQueryValue?_wrappedChallengeEntry_succ [DecidableEq Chal]
    (v : Chal) (log : QueryLog (wrappedSpec Chal)) (k : ℕ) :
    QueryLog.getQueryValue? (wrappedChallengeEntry Chal v :: log) (Sum.inr ()) (k + 1) =
      QueryLog.getQueryValue? log (Sum.inr ()) k := by
  simp [wrappedChallengeEntry]

/-- Forwards a uniform-spec query through to the wrapped spec's `Sum.inl` summand without
touching the simulator state. -/
def unifForward (M Commit Chal : Type) :
    QueryImpl unifSpec (StateT (SimState M Commit Chal) (OracleComp (wrappedSpec Chal))) :=
  fun n ↦ StateT.lift (wrappedUniformQuery Chal n)

/-- Caching random-oracle implementation: on a cache hit the recorded answer is returned,
on a cache miss a fresh `Sum.inr ()` query is issued, the answer is cached, and the
miss input `(msg, c)` is appended to the trace's internal `queryLog`. -/
def roImpl (M Commit Chal : Type) [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (M × Commit →ₒ Chal)
      (StateT (SimState M Commit Chal) (OracleComp (wrappedSpec Chal))) :=
  fun mc => do
    let (cache, log) ← get
    match cache mc with
    | some v => pure v
    | none =>
        let v ← StateT.lift (wrappedChallengeQuery Chal)
        set (cache.cacheQuery mc v, log ++ [mc])
        pure v

@[simp]
lemma unifForward_run (n : unifSpec.Domain) (st : SimState M Commit Chal) :
    (unifForward M Commit Chal n).run st =
      (do
        let u ← wrappedUniformQuery Chal n
        pure (u, st)) := by
  simp [unifForward]

@[simp]
private lemma support_wrapped_query_inl (n : unifSpec.Domain) :
    support (wrappedUniformQuery Chal n) = Set.univ :=
  support_query (spec := wrappedSpec Chal) (Sum.inl n)

@[simp]
private lemma support_wrapped_query_inr :
    support (wrappedChallengeQuery Chal) = Set.univ :=
  support_query (spec := wrappedSpec Chal) (Sum.inr ())

@[simp]
lemma roImpl_run_some [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache)
    (log : List (M × Commit)) (v : Chal) (hcache : cache mc = some v) :
    (roImpl M Commit Chal mc).run (cache, log) = pure (v, (cache, log)) := by
  simp [roImpl, StateT.run_bind, StateT.run_get, hcache]

@[simp]
lemma roImpl_run_none [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache)
    (log : List (M × Commit)) (hcache : cache mc = none) :
    (roImpl M Commit Chal mc).run (cache, log) =
      wrappedChallengeQuery Chal >>=
        fun v ↦ pure (v, (cache.cacheQuery mc v, log ++ [mc])) := by
  simp [roImpl, StateT.run_bind, StateT.run_get, StateT.run_set, hcache]

/-- A forwarded uniform query preserves the simulator state throughout its support. -/
@[simp]
lemma mem_support_unifForward_run_iff
    (n : unifSpec.Domain) (st : SimState M Commit Chal)
    (z : unifSpec.Range n × SimState M Commit Chal) :
    z ∈ support ((unifForward M Commit Chal n).run st) ↔ z.2 = st := by
  rw [unifForward_run, support_bind]
  simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, _, hz⟩
    exact congrArg Prod.snd hz
  · intro hz
    refine ⟨z.1, support_wrapped_query_inl n ▸ Set.mem_univ z.1, ?_⟩
    exact Prod.ext (Eq.refl _) hz

/-- A forwarded uniform query runs in the wrapped target without changing simulator state. -/
@[simp]
lemma simulateQ_unifForward_add_roImpl_query_inl_run
    [DecidableEq M] [DecidableEq Commit]
    (n : unifSpec.Domain) (st : SimState M Commit Chal) :
    (simulateQ (unifForward M Commit Chal + roImpl M Commit Chal)
      (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inl n)))).run st =
      wrappedUniformQuery Chal n >>= fun u => pure (u, st) := by
  rw [simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (unifForward M Commit Chal n).run st = _
  exact unifForward_run (M := M) (Commit := Commit) (Chal := Chal) n st

/-- A cached random-oracle query returns its stored answer without changing simulator state. -/
@[simp]
lemma simulateQ_unifForward_add_roImpl_query_inr_run_some
    [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache)
    (log : List (M × Commit)) (v : Chal) (hcache : cache mc = some v) :
    (simulateQ (unifForward M Commit Chal + roImpl M Commit Chal)
      (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)))).run (cache, log) =
      pure (v, (cache, log)) := by
  rw [simulateQ_spec_query, QueryImpl.add_apply_inr]
  change (roImpl M Commit Chal mc).run (cache, log) = _
  exact roImpl_run_some (M := M) (Commit := Commit) (Chal := Chal) mc cache log v hcache

/-- An uncached random-oracle query samples a wrapped challenge, caches it, and records its
input in the simulator log. -/
@[simp]
lemma simulateQ_unifForward_add_roImpl_query_inr_run_none
    [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache)
    (log : List (M × Commit)) (hcache : cache mc = none) :
    (simulateQ (unifForward M Commit Chal + roImpl M Commit Chal)
      (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)))).run (cache, log) =
      wrappedChallengeQuery Chal >>=
        fun v => pure (v, (cache.cacheQuery mc v, log ++ [mc])) := by
  rw [simulateQ_spec_query, QueryImpl.add_apply_inr]
  change (roImpl M Commit Chal mc).run (cache, log) = _
  exact roImpl_run_none (M := M) (Commit := Commit) (Chal := Chal) mc cache log hcache

/-- A routed cached random-oracle query has the unique cached outcome in its support. -/
@[simp]
lemma mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_some_iff
    [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache)
    (log : List (M × Commit)) (v : Chal) (hcache : cache mc = some v)
    (z : Chal × SimState M Commit Chal) :
    z ∈ support ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal)
      (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)))).run
      (cache, log)) ↔ z = (v, (cache, log)) := by
  rw [simulateQ_unifForward_add_roImpl_query_inr_run_some
    (M := M) (Commit := Commit) (Chal := Chal) mc cache log v hcache]
  change z ∈ support
    (pure (v, (cache, log)) : OracleComp (wrappedSpec Chal)
      (Chal × SimState M Commit Chal)) ↔ z = (v, (cache, log))
  rw [support_pure, Set.mem_singleton_iff]

/-- A routed uncached random-oracle query has exactly the freshly sampled cache-and-log
updates in its support. -/
@[simp]
lemma mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_none_iff
    [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache)
    (log : List (M × Commit)) (hcache : cache mc = none)
    (z : Chal × SimState M Commit Chal) :
    z ∈ support ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal)
      (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)))).run
        (cache, log)) ↔
      ∃ v : Chal, z = (v, (cache.cacheQuery mc v, log ++ [mc])) := by
  rw [simulateQ_unifForward_add_roImpl_query_inr_run_none
    (M := M) (Commit := Commit) (Chal := Chal) mc cache log hcache]
  change z ∈ support
    ((Fork.wrappedChallengeQuery Chal >>= fun v =>
      pure (v, (cache.cacheQuery mc v, log ++ [mc]))) :
      OracleComp (wrappedSpec Chal) (Chal × SimState M Commit Chal)) ↔
    ∃ v : Chal, z = (v, (cache.cacheQuery mc v, log ++ [mc]))
  rw [support_bind]
  simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, _, hz⟩
    exact ⟨v, hz⟩
  · rintro ⟨v, hz⟩
    exact ⟨v, support_wrapped_query_inr ▸ Set.mem_univ v, hz⟩

/-- Running the inner `unifForward + roImpl` simulator against a source computation with
an `nmaHashQueryBound Q` can grow the internal `queryLog` by at most `Q`.

Each source `Sum.inr` step consumes one unit of the `nmaHashQueryBound` budget, while
`roImpl` appends to `queryLog` only on a cache miss, hence at most once per such step. -/
theorem queryLog_length_le_of_nmaHashQueryBound
    [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] {α : Type}
    {oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α} {Q : ℕ}
    (hQ : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q)
    (st : SimState M Commit Chal) {z : α × SimState M Commit Chal}
    (hz : z ∈ support ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) oa).run st)) :
    z.2.2.length ≤ st.2.length + Q := by
  induction oa using OracleComp.inductionOn generalizing Q st z with
  | pure x =>
      obtain rfl : z = (x, st) := by
        simpa [simulateQ_pure, StateT.run_pure, support_pure] using hz
      simp
  | query_bind t mx ih =>
      rw [nmaHashQueryBound_query_bind_iff (M := M) (Commit := Commit) (Chal := Chal)] at hQ
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hz'⟩ := hz
      cases t with
      | inl n =>
          change unifSpec.Range n × SimState M Commit Chal at us
          rcases st with ⟨cache, log⟩
          rcases us with ⟨u, usState⟩
          have hstate := (mem_support_unifForward_run_iff
            (M := M) (Commit := Commit) (Chal := Chal)
            n (cache, log) (u, usState)).mp hus
          change usState = (cache, log) at hstate
          subst usState
          simpa using ih u (hQ.2 u) (cache, log) hz'
      | inr mc =>
          change Chal × SimState M Commit Chal at us
          rcases st with ⟨cache, log⟩
          cases hcache : cache mc with
          | some v =>
              have hus' : us ∈ ({(v, cache, log)} : Set _) := by
                change us ∈ support ((roImpl M Commit Chal mc).run (cache, log)) at hus
                rw [roImpl_run_some (M := M) (Commit := Commit) (Chal := Chal)
                  mc cache log v hcache] at hus
                simpa only [support_pure] using hus
              obtain rfl := Set.mem_singleton_iff.mp hus'
              have hrec : z.2.2.length ≤ log.length + (Q - 1) := by
                simpa using ih v (hQ.2 v) (cache, log) hz'
              exact le_trans hrec (Nat.add_le_add_left (Nat.sub_le _ _) _)
          | none =>
              obtain ⟨u, rfl⟩ : us ∈ Set.range (fun u : Chal =>
                  (u, cache.cacheQuery mc u, log ++ [mc])) := by
                change us ∈ support ((roImpl M Commit Chal mc).run (cache, log)) at hus
                rw [roImpl_run_none (M := M) (Commit := Commit) (Chal := Chal)
                  mc cache log hcache, support_bind, support_wrapped_query_inr] at hus
                simpa [support_bind] using hus
              have hrec : z.2.2.length ≤ (log ++ [mc]).length + (Q - 1) := by
                simpa using
                  ih u (hQ.2 u)
                    ((cache.cacheQuery mc u : (M × Commit →ₒ Chal).QueryCache), log ++ [mc]) hz'
              have hQpos : 0 < Q := hQ.1
              simp only [List.length_append, List.length_singleton] at hrec ⊢
              lia

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
def runTrace [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (wrappedSpec Chal)
      (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := do
  let ((forgery, advCache), st) ←
    StateT.run (simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) (nmaAdv.main pk))
      (∅, [])
  let verified :=
    match forgery with
    | (msg, (c, s)) =>
        match st.1 (msg, c) with
        | some ω => σ.verify pk c ω s
        | none => false
  let (roCache, queryLog) := st
  pure { forgery, advCache, roCache, queryLog, verified }

/-- Forkable managed-RO NMA experiment. Success means the final forged transcript verifies and
the corresponding hash point appears in the live query log, so the forking lemma can rewind it. -/
def exp [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ProbComp Bool :=
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := chalSpec)) do
    let (pk, _) ← liftComp hr.gen (unifSpec + chalSpec)
    let trace ← runTrace σ hr M nmaAdv pk
    pure (forkPoint M qH trace).isSome

/-- The forkable success probability of a managed-RO NMA adversary. -/
noncomputable def advantage [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ENNReal :=
  Pr[= true | exp σ hr M nmaAdv qH]

section Coupling

variable [DecidableEq M] [DecidableEq Commit]

/-! ### Per-step support characterizations

Two thin lemmas that describe the support of a single step of the layered simulation
`(simulateQ loggingOracle (((unifForward + roImpl) t).run (c₀, l₀))).run`. Used by the
1-state and 2-state preservation helpers below to do *all* per-step case analysis in
one place. The `Sum.inl` step always issues a forwarded uniform query and logs it; the
`Sum.inr` step branches on whether the cache already contains the asked hash point. -/

private lemma support_step_inl
    (n : ℕ) (s : SimState M Commit Chal)
    (z : ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inl n) × SimState M Commit Chal) ×
      QueryLog (wrappedSpec Chal)) :
    z ∈ support ((simulateQ (wrappedSpec Chal).loggingOracle
      (((unifForward M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run s)).run) ↔
    ∃ u : (unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inl n),
      z = ((u, s), [wrappedUniformEntry Chal n u]) := by
  obtain ⟨c₀, l₀⟩ := s
  have hrun : ((unifForward M Commit Chal + roImpl M Commit Chal) (Sum.inl n)).run (c₀, l₀) =
      (liftM ((wrappedSpec Chal).query (Sum.inl n)) : OracleComp _ _) >>=
        fun u => pure (u, (c₀, l₀)) := by
    simp [QueryImpl.add_apply_inl, unifForward, wrappedUniformQuery]
  rw [hrun]
  change z ∈ support (simulateQ loggingOracle
      ((liftM ((wrappedSpec Chal).query (Sum.inl n)) : OracleComp _ _) >>=
        fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run ↔ _
  rw [OracleComp.run_simulateQ_loggingOracle_query_bind
    (spec := wrappedSpec Chal) (Sum.inl n) (fun u => pure (u, (c₀, l₀)))]
  simp only [support_bind, support_map, support_query, Set.mem_univ, simulateQ_pure,
    WriterT.run_pure', support_pure, Set.image_singleton, Set.iUnion_const]
  exact Set.mem_iUnion.trans (exists_congr fun _ => Set.mem_singleton_iff)

private lemma support_step_inr
    (mc : M × Commit) (s : SimState M Commit Chal)
    (z : ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr mc) × SimState M Commit Chal) ×
      QueryLog (wrappedSpec Chal)) :
    z ∈ support ((simulateQ (wrappedSpec Chal).loggingOracle
      (((unifForward M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run s)).run) ↔
    (∃ v, s.1 mc = some v ∧ z = ((v, s), [])) ∨
    (s.1 mc = none ∧ ∃ v,
      z = ((v, (s.1.cacheQuery mc v, s.2 ++ [mc])), [wrappedChallengeEntry Chal v])) := by
  obtain ⟨c₀, l₀⟩ := s
  by_cases hcache : c₀ mc = none
  · have hrun : ((unifForward M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run (c₀, l₀) =
        (liftM ((wrappedSpec Chal).query (Sum.inr ())) : OracleComp _ _) >>=
          fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) := by
      simp [QueryImpl.add_apply_inr, roImpl, wrappedChallengeQuery,
        StateT.run_bind, StateT.run_get, StateT.run_set, hcache]
    rw [hrun]
    change z ∈ support (simulateQ loggingOracle
        ((liftM ((wrappedSpec Chal).query (Sum.inr ())) : OracleComp _ _) >>=
          fun v => (pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])) :
            OracleComp _ _))).run ↔ _
    rw [OracleComp.run_simulateQ_loggingOracle_query_bind
      (spec := wrappedSpec Chal) (Sum.inr ())
      (fun v => pure (v, (c₀.cacheQuery mc v, l₀ ++ [mc])))]
    simp only [support_bind, support_map, support_query, Set.mem_univ,
      simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
      Set.iUnion_const]
    refine ⟨fun ⟨_, ⟨v, rfl⟩, hzeq⟩ => Or.inr ⟨hcache, v, hzeq⟩, ?_⟩
    rintro (⟨v, hv, _⟩ | ⟨_, v, hzeq⟩)
    · exact absurd hv.symm (hcache ▸ Option.some_ne_none v)
    · exact ⟨_, ⟨v, rfl⟩, hzeq⟩
  · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
    have hrun : ((unifForward M Commit Chal + roImpl M Commit Chal) (Sum.inr mc)).run (c₀, l₀) =
        pure (v, (c₀, l₀)) := by
      simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
    rw [hrun]
    change z ∈ support (simulateQ loggingOracle
        (pure (v, (c₀, l₀)) : OracleComp _ _)).run ↔ _
    simp only [simulateQ_pure, WriterT.run_pure', support_pure]
    refine ⟨fun h => Or.inl ⟨v, hv.symm, h⟩, ?_⟩
    rintro (⟨v', hv', hzeq⟩ | ⟨h0, _⟩)
    · obtain rfl : v = v' := Option.some_inj.mp (hv.trans hv')
      exact hzeq
    · exact absurd h0 (Option.ne_none_iff_exists.mpr ⟨v, hv⟩)

/-! ### Layered preservation helpers

Two skeletons that capture the entire structural induction `OracleComp.inductionOn`
on `Y` for the layered simulation. All five Coupling lemmas below boil down to writing
the per-step preservation in *three* concrete cases (Sum.inl, Sum.inr cache hit, Sum.inr
cache miss) using the support characterizations above; the inductive bookkeeping is
factored out once. -/

private theorem preservesInv_layered {γ : Type}
    (Inv : SimState M Commit Chal → QueryLog (wrappedSpec Chal) → Prop)
    (hstep : ∀ t (s : SimState M Commit Chal) (w : QueryLog (wrappedSpec Chal)),
      Inv s w →
      ∀ z ∈ support ((simulateQ (wrappedSpec Chal).loggingOracle
        (((unifForward M Commit Chal + roImpl M Commit Chal) t).run s)).run),
      Inv z.1.2 (w ++ z.2))
    (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (s₀ : SimState M Commit Chal) (w₀ : QueryLog (wrappedSpec Chal))
    (hinit : Inv s₀ w₀)
    {z : (γ × SimState M Commit Chal) × QueryLog (wrappedSpec Chal)}
    (hz : z ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run s₀)).run)) :
    Inv z.1.2 (w₀ ++ z.2) := by
  classical
  induction Y using OracleComp.inductionOn generalizing s₀ w₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinit
  | query_bind t oa ih =>
      rw [run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind', support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, rfl⟩ := hz
      simp only [Prod.map_fst, Prod.map_snd, id_eq, ← List.append_assoc]
      exact ih us_w.1.1 (s₀ := us_w.1.2) (w₀ := w₀ ++ us_w.2)
        (hstep t s₀ w₀ hinit us_w hus_w) hpw

private theorem queryLog_length_eq_outer_inr_count
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit)) {z : γ × SimState M Commit Chal}
    {outerLog : QueryLog (wrappedSpec Chal)} (hz : (z, outerLog) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run)) :
    z.2.2.length = l₀.length + outerLog.countQ (· = Sum.inr ()) := by
  have h := preservesInv_layered (M := M) (Commit := Commit) (Chal := Chal)
    (Inv := fun s w => s.2.length = l₀.length + w.countQ (· = Sum.inr ()))
    (hstep := ?_) Y (c₀, l₀) [] (by simp [QueryLog.countQ]) hz
  · simpa [List.nil_append] using h
  · intro t s w hI z hz
    cases t with
    | inl n =>
        rw [support_step_inl] at hz
        obtain ⟨u, rfl⟩ := hz
        change unifSpec.Range n at u
        simpa [QueryLog.countQ, QueryLog.getQ, QueryLog.countQ_append] using hI
    | inr mc =>
        rw [support_step_inr] at hz
        rcases hz with ⟨v, _, rfl⟩ | ⟨_, v, rfl⟩
        · simpa using hI
        · change Chal at v
          have h1 : QueryLog.countQ (spec := wrappedSpec Chal)
              [wrappedChallengeEntry Chal v] (· = Sum.inr ()) = 1 := by
            simp [QueryLog.countQ, QueryLog.getQ]
          simp only [List.length_append, List.length_singleton, QueryLog.countQ_append, h1, hI]
          lia

/- Lockstep value invariant for `runTrace`'s inner simulation. Three coupled invariants
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
private theorem queryLog_cache_outer_lockstep [DecidableEq Chal] {γ : Type}
    (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ) (c₀ : (M × Commit →ₒ Chal).QueryCache)
    (l₀ : List (M × Commit)) {z : γ × SimState M Commit Chal}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (hz : (z, outerLog) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
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
      refine ⟨⟨[], by simp⟩, fun _ _ h => h, ?_⟩
      intro i h_lo h_hi
      change i < l₀.length at h_hi
      lia
  | query_bind t oa ih =>
      rw [run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind', support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := hz
      have hih := ih (u := us_w.1.1) (c₀ := us_w.1.2.1) (l₀ := us_w.1.2.2)
        (z := pw.1) (outerLog := pw.2) hpw
      have hz_eq' : (pw.1, us_w.2 ++ pw.2) = (z, outerLog) := by
        rw [show ((pw.1, us_w.2 ++ pw.2) : _ × QueryLog (wrappedSpec Chal)) =
              Prod.map id (fun x => us_w.2 ++ x) pw from rfl]
        exact hz_eq
      obtain ⟨hz_eq1, hz_eq2⟩ := Prod.mk.inj hz_eq'
      subst hz_eq1
      subst hz_eq2
      cases t with
      | inl n =>
          rw [support_step_inl] at hus_w
          obtain ⟨u, rfl⟩ := hus_w
          change unifSpec.Range n at u
          obtain ⟨⟨l_new, hpref⟩, hmono, hlock⟩ := hih
          refine ⟨⟨l_new, hpref⟩, hmono, ?_⟩
          intro i h_lo h_hi
          obtain ⟨ω, hcache, hlog⟩ := hlock i h_lo h_hi
          refine ⟨ω, hcache, ?_⟩
          change QueryLog.getQueryValue?
            (wrappedUniformEntry Chal n u :: pw.2)
              (Sum.inr ()) (i - l₀.length) = some ω
          rw [getQueryValue?_wrappedUniformEntry]
          exact hlog
      | inr mc =>
          rw [support_step_inr] at hus_w
          rcases hus_w with ⟨v, _hcache, rfl⟩ | ⟨hcache, v, rfl⟩
          · change Chal at v
            obtain ⟨⟨l_new, hpref⟩, hmono, hlock⟩ := hih
            refine ⟨⟨l_new, hpref⟩, hmono, ?_⟩
            intro i h_lo h_hi
            obtain ⟨ω, hcacheω, hlogω⟩ := hlock i h_lo h_hi
            refine ⟨ω, hcacheω, ?_⟩
            change QueryLog.getQueryValue? ([] ++ pw.2)
              (Sum.inr ()) (i - l₀.length) = some ω
            rw [List.nil_append]
            exact hlogω
          · change Chal at v
            dsimp only at hcache
            obtain ⟨⟨l_new', hpref'⟩, hmono', hlock'⟩ := hih
            dsimp only at hpref' hmono' hlock'
            have hpref_z : pw.1.2.2 = l₀ ++ ([mc] ++ l_new') := by
              rw [hpref']
              simp [List.append_assoc]
            refine ⟨⟨[mc] ++ l_new', hpref_z⟩, ?_, ?_⟩
            · intro mc' ω hmc'
              apply hmono'
              by_cases heq : mc' = mc
              · subst heq
                rw [hcache] at hmc'
                exact (Option.some_ne_none ω hmc'.symm).elim
              · rwa [QueryCache.cacheQuery_of_ne _ _ heq]
            · intro i h_lo h_hi
              by_cases hi_eq : i = l₀.length
              · subst hi_eq
                have hidx : pw.1.2.2[l₀.length]'h_hi = mc := by
                  have h_hi'' : l₀.length < (l₀ ++ ([mc] ++ l_new')).length := by
                    rwa [← List.append_assoc, ← hpref']
                  have hcongr : pw.1.2.2[l₀.length]'h_hi =
                      (l₀ ++ ([mc] ++ l_new'))[l₀.length]'h_hi'' :=
                    List.getElem_of_eq hpref_z _
                  rw [hcongr, List.getElem_append_right (Nat.le_refl _)]
                  simp
                refine ⟨v, ?_, ?_⟩
                · rw [hidx]
                  exact hmono' mc v (QueryCache.cacheQuery_self c₀ mc v)
                · change QueryLog.getQueryValue?
                    (wrappedChallengeEntry Chal v :: pw.2)
                      (Sum.inr ()) (l₀.length - l₀.length) = some v
                  rw [Nat.sub_self]
                  exact getQueryValue?_wrappedChallengeEntry_zero v pw.2
              · have h_lo' : (l₀ ++ [mc]).length ≤ i := by
                  simp only [List.length_append, List.length_singleton]
                  lia
                obtain ⟨ω, hcacheω, hlogω⟩ := hlock' i h_lo' h_hi
                refine ⟨ω, hcacheω, ?_⟩
                obtain ⟨k, hk⟩ : ∃ k, i - l₀.length = k + 1 := ⟨i - l₀.length - 1, by lia⟩
                have hk_eq : k = i - (l₀ ++ [mc]).length := by
                  simp only [List.length_append, List.length_singleton] at hk ⊢
                  lia
                change QueryLog.getQueryValue?
                  (wrappedChallengeEntry Chal v :: pw.2)
                    (Sum.inr ()) (i - l₀.length) = some ω
                rw [hk, getQueryValue?_wrappedChallengeEntry_succ, hk_eq]
                exact hlogω

/- Prefix monotonicity: running `(simulateQ (unifForward + roImpl) Y).run (c₀, l₀)` produces a
final simulator state whose `queryLog` component extends `l₀`. The resulting list always
starts with the initial `l₀`: cache misses only append entries, and cache hits plus
`unifForward`-forwarded queries never touch `l₀`. Used by `inner_prefix_det` to fix the first
`l₀.length` positions of the final `queryLog`. -/
private theorem queryLog_extends_l₀
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z : γ × SimState M Commit Chal}
    {outerLog : QueryLog (wrappedSpec Chal)}
    (h : (z, outerLog) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run)) :
    z.2.2.take l₀.length = l₀ := by
  classical
  induction Y using OracleComp.inductionOn generalizing c₀ l₀ z outerLog with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨hz_eq, _⟩ := h
      rw [hz_eq]
      exact List.take_length
  | query_bind t oa ih =>
      rw [run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind', support_bind] at h
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := h
      obtain ⟨hzeq, _⟩ := Prod.mk.inj hz_eq
      subst hzeq
      cases t with
      | inl n =>
          rw [support_step_inl] at hus_w
          obtain ⟨u, rfl⟩ := hus_w
          exact ih u c₀ l₀ hpw
      | inr mc =>
          rw [support_step_inr] at hus_w
          rcases hus_w with ⟨v, _, rfl⟩ | ⟨_, v, rfl⟩
          · exact ih v c₀ l₀ hpw
          · calc pw.1.2.2.take l₀.length
                = (pw.1.2.2.take (l₀ ++ [mc]).length).take l₀.length := by
                    rw [List.take_take, min_eq_left (by simp [List.length_append])]
              _ = (l₀ ++ [mc]).take l₀.length := by
                    rw [ih v (c₀.cacheQuery mc v) (l₀ ++ [mc]) hpw]
              _ = l₀ := List.take_left

/- Outer-log prefix-determinism for `runTrace`'s inner simulation. If the two outer
logs share a common prefix `p` (with `#{Sum.inr ()} = j` in `p`), then the first
`l₀.length + j` positions of the final internal `queryLog`s coincide. This is the
bisimulation up to the focused query used by
`runTrace_target_eq_of_mem_contextFork`: a common outer prefix fixes the
adversary's state (and hence the next cache-miss input) through that query. -/
private theorem inner_prefix_det
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z₁ z₂ : γ × SimState M Commit Chal}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec Chal)}
    (h₁ : (z₁, outerLog₁) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run))
    (h₂ : (z₂, outerLog₂) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
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
      rw [run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind',
        support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      have hz_eq'₁ : (pw₁.1, us_w₁.2 ++ pw₁.2) = (z₁, outerLog₁) := hz_eq₁
      have hz_eq'₂ : (pw₂.1, us_w₂.2 ++ pw₂.2) = (z₂, outerLog₂) := hz_eq₂
      obtain ⟨rfl, hz_eq2₁⟩ := Prod.mk.inj hz_eq'₁
      obtain ⟨rfl, hz_eq2₂⟩ := Prod.mk.inj hz_eq'₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ suffix₁ := hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ suffix₂ := hz_eq2₂.trans hlog₂
      cases t with
      | inl n =>
          rw [support_step_inl] at hus_w₁ hus_w₂
          obtain ⟨u₁, rfl⟩ := hus_w₁
          obtain ⟨u₂, rfl⟩ := hus_w₂
          cases p with
          | nil =>
              simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
              have h₁' : pw₁.1.2.2.take l₀.length = l₀ :=
                queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                  (oa u₁) c₀ l₀ hpw₁
              have h₂' : pw₂.1.2.2.take l₀.length = l₀ :=
                queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                  (oa u₂) c₀ l₀ hpw₂
              rw [h₁', h₂']
          | cons p_head p_tail =>
              simp only [List.cons_append, List.cons.injEq]
                at houter₁_eq houter₂_eq
              obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
              obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
              have hu_eq : u₁ = u₂ := by
                obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                exact eq_of_heq hheq
              subst hu_eq
              have hpH_fst : p_head.1 ≠ Sum.inr () := by
                rw [← hhead₁]
                intro h
                cases h
              have hp_count :
                  QueryLog.countQ (spec := wrappedSpec Chal) (p_head :: p_tail)
                      (· = Sum.inr ()) =
                    QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) := by
                simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
              rw [hp_count]
              exact ih u₁ c₀ l₀ hpw₁ hpw₂ p_tail suffix₁ suffix₂ htail₁ htail₂
      | inr mc =>
          rw [support_step_inr] at hus_w₁ hus_w₂
          rcases hus_w₁ with ⟨v₁, hsome₁, rfl⟩ | ⟨hnone₁, v₁, rfl⟩
          · rcases hus_w₂ with ⟨v₂, hsome₂, rfl⟩ | ⟨hnone₂, v₂, rfl⟩
            · dsimp only at hsome₁ hsome₂
              rw [hsome₁] at hsome₂
              obtain rfl := Option.some.inj hsome₂
              exact ih v₁ c₀ l₀ hpw₁ hpw₂ p suffix₁ suffix₂ houter₁_eq houter₂_eq
            · dsimp only at hsome₁ hnone₂
              rw [hsome₁] at hnone₂
              contradiction
          · rcases hus_w₂ with ⟨v₂, hsome₂, rfl⟩ | ⟨hnone₂, v₂, rfl⟩
            · dsimp only at hnone₁ hsome₂
              rw [hnone₁] at hsome₂
              contradiction
            · change Chal at v₁ v₂
              cases p with
              | nil =>
                  simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                  have take_eq : ∀ (v : Chal)
                      (pw : (γ × SimState M Commit Chal) × QueryLog (wrappedSpec Chal)),
                      pw ∈ support ((simulateQ (wrappedSpec Chal).loggingOracle
                        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal)
                          (oa v)).run (c₀.cacheQuery mc v, l₀ ++ [mc]))).run) →
                      pw.1.2.2.take l₀.length = l₀ := fun v pw h => by
                    have hext := queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                      (oa v) (c₀.cacheQuery mc v) (l₀ ++ [mc]) h
                    calc pw.1.2.2.take l₀.length
                        = (pw.1.2.2.take (l₀ ++ [mc]).length).take l₀.length := by
                            rw [List.take_take, min_eq_left (by simp [List.length_append])]
                      _ = (l₀ ++ [mc]).take l₀.length := by rw [hext]
                      _ = l₀ := List.take_left
                  rw [take_eq v₁ pw₁ hpw₁, take_eq v₂ pw₂ hpw₂]
              | cons p_head p_tail =>
                  simp only [List.cons_append, List.cons.injEq]
                    at houter₁_eq houter₂_eq
                  obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
                  obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
                  have hv_eq : v₁ = v₂ := by
                    obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                    exact eq_of_heq hheq
                  subst hv_eq
                  have hpH_fst : p_head.1 = Sum.inr () := by
                    simpa using congrArg Sigma.fst hhead₁.symm
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
                    lia
                  rw [hlen_eq]
                  exact ih v₁ (c₀.cacheQuery mc v₁) (l₀ ++ [mc])
                    hpw₁ hpw₂ p_tail suffix₁ suffix₂ htail₁ htail₂

/- One-more-step extension of `inner_prefix_det`: if the outer logs of two runs share the
prefix `p ++ [⟨Sum.inr (), v_i⟩]` (allowing the values `v₁, v₂` at position `|p|` to differ),
then the internal `queryLog`s coincide for one more entry than `inner_prefix_det` guarantees,
namely up to position `l₀.length + p.countQ(· = Sum.inr ()) + 1`. The extra entry is the
input `mc` of the next cache-miss query issued by the adversary: its value is determined by
the adversary's state after consuming the shared prefix `p`, which is common to both runs. -/
private theorem inner_prefix_det_one_more_inr
    {γ : Type} (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (c₀ : (M × Commit →ₒ Chal).QueryCache) (l₀ : List (M × Commit))
    {z₁ z₂ : γ × SimState M Commit Chal}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec Chal)}
    (h₁ : (z₁, outerLog₁) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
          (c₀, l₀))).run))
    (h₂ : (z₂, outerLog₂) ∈ support
      ((simulateQ (wrappedSpec Chal).loggingOracle
        ((simulateQ (unifForward M Commit Chal + roImpl M Commit Chal) Y).run
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
      rw [run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind',
        support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      have hz_eq'₁ : (pw₁.1, us_w₁.2 ++ pw₁.2) = (z₁, outerLog₁) := hz_eq₁
      have hz_eq'₂ : (pw₂.1, us_w₂.2 ++ pw₂.2) = (z₂, outerLog₂) := hz_eq₂
      obtain ⟨rfl, hz_eq2₁⟩ := Prod.mk.inj hz_eq'₁
      obtain ⟨rfl, hz_eq2₂⟩ := Prod.mk.inj hz_eq'₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁) :=
        hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂) :=
        hz_eq2₂.trans hlog₂
      cases t with
      | inl n =>
          rw [support_step_inl] at hus_w₁ hus_w₂
          obtain ⟨u₁, rfl⟩ := hus_w₁
          obtain ⟨u₂, rfl⟩ := hus_w₂
          cases p with
          | nil =>
              simp only [List.nil_append, List.cons_append, List.cons.injEq] at houter₁_eq
              have hfalse := congrArg Sigma.fst houter₁_eq.1
              have : Sum.inl n = Sum.inr () :=
                (wrappedUniformEntry_fst Chal n u₁).symm.trans hfalse
              cases this
          | cons p_head p_tail =>
              simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
              obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
              obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
              have hu_eq : u₁ = u₂ := by
                obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                exact eq_of_heq hheq
              subst hu_eq
              have hpH_fst : p_head.1 ≠ Sum.inr () := by
                rw [← hhead₁]
                intro h
                cases h
              have hp_count :
                  QueryLog.countQ (spec := wrappedSpec Chal) (p_head :: p_tail)
                      (· = Sum.inr ()) =
                    QueryLog.countQ (spec := wrappedSpec Chal) p_tail (· = Sum.inr ()) := by
                simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
              rw [hp_count]
              exact ih u₁ c₀ l₀ hpw₁ hpw₂ p_tail htail₁ htail₂
      | inr mc =>
          rw [support_step_inr] at hus_w₁ hus_w₂
          rcases hus_w₁ with ⟨w₁, hsome₁, rfl⟩ | ⟨hnone₁, w₁, rfl⟩
          · rcases hus_w₂ with ⟨w₂, hsome₂, rfl⟩ | ⟨hnone₂, w₂, rfl⟩
            · dsimp only at hsome₁ hsome₂
              rw [hsome₁] at hsome₂
              obtain rfl := Option.some.inj hsome₂
              exact ih w₁ c₀ l₀ hpw₁ hpw₂ p houter₁_eq houter₂_eq
            · dsimp only at hsome₁ hnone₂
              rw [hsome₁] at hnone₂
              contradiction
          · rcases hus_w₂ with ⟨w₂, hsome₂, rfl⟩ | ⟨hnone₂, w₂, rfl⟩
            · dsimp only at hnone₁ hsome₂
              rw [hnone₁] at hsome₂
              contradiction
            · change Chal at w₁ w₂
              cases p with
              | nil =>
                  simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                  have h₁' : pw₁.1.2.2.take (l₀ ++ [mc]).length = l₀ ++ [mc] :=
                    queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                      (oa w₁) (c₀.cacheQuery mc w₁) (l₀ ++ [mc]) hpw₁
                  have h₂' : pw₂.1.2.2.take (l₀ ++ [mc]).length = l₀ ++ [mc] :=
                    queryLog_extends_l₀ (M := M) (Commit := Commit) (Chal := Chal)
                      (oa w₂) (c₀.cacheQuery mc w₂) (l₀ ++ [mc]) hpw₂
                  have hlen : (l₀ ++ [mc]).length = l₀.length + 1 := by
                    simp [List.length_append]
                  rw [← hlen, h₁', h₂']
              | cons p_head p_tail =>
                  simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
                  obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
                  obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
                  have hw_eq : w₁ = w₂ := by
                    obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                    exact eq_of_heq hheq
                  subst hw_eq
                  have hpH_fst : p_head.1 = Sum.inr () := by
                    simpa using congrArg Sigma.fst hhead₁.symm
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
                    lia
                  rw [hlen_eq]
                  exact ih w₁ (c₀.cacheQuery mc w₁) (l₀ ++ [mc])
                    hpw₁ hpw₂ p_tail htail₁ htail₂

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
  unfold replayFirstRun withQueryLog runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hxqueryLog : x.queryLog = a.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq)).symm
  have hlog_eq : a.2 = outerLog := by simpa [Prod.map_apply] using congrArg Prod.snd ha_eq
  rw [hxqueryLog, ← hlog_eq]
  simpa using queryLog_length_eq_outer_inr_count (M := M) (Commit := Commit) (Chal := Chal)
    (γ := (M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache)
    (nmaAdv.main pk) ∅ [] (z := a.1) (outerLog := a.2) ha_mem

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
  unfold replayFirstRun withQueryLog runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hxqueryLog : x.queryLog = a.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq)).symm
  have hxroCache : x.roCache = a.1.2.1 := by
    simpa [Prod.map_apply, Trace.roCache] using
      (congrArg Trace.roCache (congrArg Prod.fst ha_eq)).symm
  have hlog_eq : a.2 = outerLog := by simpa [Prod.map_apply] using congrArg Prod.snd ha_eq
  intro i h_hi
  obtain ⟨_, _, hlock⟩ :=
    queryLog_cache_outer_lockstep (M := M) (Commit := Commit) (Chal := Chal)
      (γ := (M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache)
      (nmaAdv.main pk) ∅ [] (z := a.1) (outerLog := a.2) ha_mem
  obtain ⟨ω, hcache, hlog⟩ := hlock i (Nat.zero_le _) (hxqueryLog ▸ h_hi)
  refine ⟨ω, ?_, ?_⟩
  · rwa [hxroCache, List.getElem_of_eq hxqueryLog]
  · simpa [← hlog_eq] using hlog

/-- Decoding the `verified` flag of a trace produced by `runTrace`. If the trace's
`verified` field is `true`, then there is a cached challenge `ω` for `x.target` and the
corresponding `σ.verify` succeeds. Used by `forkSupportInvariant_of_mem_replayFirstRun`. -/
lemma exists_cached_verify_of_runTrace_verified
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
  unfold replayFirstRun withQueryLog runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨⟨⟨⟨⟨msg, c, s⟩, advCache⟩, roCache, queryLog⟩, log_a⟩, _, ha_eq⟩ := hx
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
    simpa using (congrArg Prod.fst ha_eq).symm
  subst hxeq
  simp only [Trace.target] at hv ⊢
  split at hv <;> simp_all

/-- The `forkPoint`-based reachability invariant for `runTrace`: whenever
`forkPoint qH x = some s`, the outer `QueryLog` of `replayFirstRun (runTrace ...)` has a
`Sum.inr ()` query at position `↑s`. This discharges `ReplayFork`'s `CfReachable` side
condition. -/
theorem runTrace_forkPoint_CfReachable
    [DecidableEq Chal] [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt) :
    CfReachable (runTrace σ hr M nmaAdv pk)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => qH) (Sum.inr ())
      (forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH) := by
  intro x log hx s hs
  have hslt : (↑s : ℕ) < log.countQ (· = Sum.inr ()) :=
    runTrace_queryLog_length_eq σ hr M nmaAdv pk hx ▸
      (List.getElem?_eq_some_iff.mp (forkPoint_getElem?_eq_some_target
        (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) hs)).1
  exact QueryLog.getQueryValue?_isSome_of_lt log (Sum.inr ()) ↑s hslt

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
  unfold replayFirstRun withQueryLog runTrace at h₁ h₂
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at h₁ h₂
  obtain ⟨a₁, ha_mem₁, ha_eq₁⟩ := h₁
  obtain ⟨a₂, ha_mem₂, ha_eq₂⟩ := h₂
  have hxqL₁ : x₁.queryLog = a₁.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq₁)).symm
  have hxqL₂ : x₂.queryLog = a₂.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq₂)).symm
  have hlog_eq₁ : a₁.2 = outerLog₁ := by
    simpa [Prod.map_apply] using congrArg Prod.snd ha_eq₁
  have hlog_eq₂ : a₂.2 = outerLog₂ := by
    simpa [Prod.map_apply] using congrArg Prod.snd ha_eq₂
  have hdet := inner_prefix_det_one_more_inr (M := M) (Commit := Commit) (Chal := Chal)
    (γ := (M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache)
    (nmaAdv.main pk) ∅ []
    (z₁ := a₁.1) (z₂ := a₂.1)
    (outerLog₁ := a₁.2) (outerLog₂ := a₂.2)
    ha_mem₁ ha_mem₂ p (v₁ := v₁) (v₂ := v₂)
    (rest₁ := rest₁) (rest₂ := rest₂)
    (hlog_eq₁.trans hlog₁) (hlog_eq₂.trans hlog₂)
  simpa [hxqL₁, hxqL₂] using hdet

end Coupling

/-- If two successful contextual forks select the same fork index, their
forgery targets agree. -/
lemma runTrace_target_eq_of_mem_contextFork
    [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal] [SampleableType Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    (x₁ x₂ : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (s : Fin (qH + 1))
    (hsup : some (x₁, x₂) ∈ support (contextFork (runTrace σ hr M nmaAdv pk)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => qH) (Sum.inr ())
      (forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)))
    (h₁ : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH x₁ = some s)
    (h₂ : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH x₂ = some s) :
    x₁.target = x₂.target := by
  let : Fintype Chal := Fintype.ofFinite Chal
  let : IsUniformSpec ((Unit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  let qb : ℕ ⊕ Unit → ℕ := fun j => match j with | .inl _ => 0 | .inr () => qH
  let cf := forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  let main := runTrace σ hr M nmaAdv pk
  obtain ⟨path, s', located, second, hpath, hcf₁, _hsecond,
      _hne, _hcf₂, hx₁, hx₂⟩ :=
    contextFork_success main qb (Sum.inr ()) cf hsup
  have hs' : s' = s := by
    apply Option.some.inj
    calc
      some s' = cf (PFunctor.FreeM.output main path) := hcf₁.symm
      _ = cf x₁ := by rw [hx₁]
      _ = some s := h₁
  subst s'
  let commonLog : QueryLog (wrappedSpec Chal) := located.occurrence.before
  have hfirst := replayPathResult_mem_support_replayFirstRun main path hpath
  have hsecond := replayPathResult_mem_support_replayFirstRun main second.path
    (mem_support_replayFirstPath main second.path)
  have hxlog₁ : (x₁, (replayPathResult main path).2) ∈
      support (replayFirstRun main) := by
    simpa [replayPathResult, pathLogResult, hx₁] using hfirst
  have hxlog₂ : (x₂, (replayPathResult main second.path).2) ∈
      support (replayFirstRun main) := by
    simpa [replayPathResult, pathLogResult, hx₂] using hsecond
  have hlog₁ : (replayPathResult main path).2 =
      commonLog ++
        (⟨Sum.inr (), located.completion.answer⟩ ::
          (replayPathResult (located.occurrence.resume
            located.completion.answer) located.completion.suffix).2) := by
    have htrace := congrArg
      (fun p : PFunctor.FreeM.Path main =>
        (show QueryLog (wrappedSpec Chal) from
          PFunctor.FreeM.Path.trace main p)) located.path_eq
    calc
      (replayPathResult main path).2
          = (replayPathResult main located.completion.path).2 := htrace.symm
      _ = _ := by
        change PFunctor.FreeM.Path.trace main located.completion.path =
          List.append
            (show PFunctor.TraceList (wrappedSpec Chal).toPFunctor from
              commonLog)
            (⟨Sum.inr (), located.completion.answer⟩ ::
              PFunctor.FreeM.Path.trace
                (located.occurrence.resume located.completion.answer)
                located.completion.suffix)
        unfold commonLog
        exact PFunctor.FreeM.Cursor.Occurrence.trace_plug
          located.occurrence located.completion.answer
            located.completion.suffix
  have hlog₂ : (replayPathResult main second.path).2 =
      commonLog ++
        (⟨Sum.inr (), second.answer⟩ ::
          (replayPathResult (located.occurrence.resume second.answer)
            second.suffix).2) := by
    change PFunctor.FreeM.Path.trace main second.path =
      List.append
        (show PFunctor.TraceList (wrappedSpec Chal).toPFunctor from
          commonLog)
        (⟨Sum.inr (), second.answer⟩ ::
          PFunctor.FreeM.Path.trace
            (located.occurrence.resume second.answer) second.suffix)
    unfold commonLog
    exact PFunctor.FreeM.Cursor.Occurrence.trace_plug
      located.occurrence second.answer second.suffix
  have htakeEq := runTrace_queryLog_take_eq σ hr M (Resp := Resp) nmaAdv pk
    (x₁ := x₁) (x₂ := x₂)
    (outerLog₁ := (replayPathResult main path).2)
    (outerLog₂ := (replayPathResult main second.path).2)
    hxlog₁ hxlog₂
    (p := commonLog)
    (v₁ := located.completion.answer) (v₂ := second.answer)
    (rest₁ := (replayPathResult (located.occurrence.resume
      located.completion.answer) located.completion.suffix).2)
    (rest₂ := (replayPathResult (located.occurrence.resume second.answer)
      second.suffix).2) hlog₁ hlog₂
  have hprefixCount : commonLog.countQ
      (fun x => x = Sum.inr ()) = (↑s : ℕ) := by
    calc
      commonLog.countQ (fun x => x = Sum.inr ()) =
          PFunctor.TraceList.occurrences (P := (wrappedSpec Chal).toPFunctor)
            (Sum.inr ())
            (show PFunctor.TraceList (wrappedSpec Chal).toPFunctor from
              commonLog) := QueryLog.countQ_eq_occurrences commonLog (Sum.inr ())
      _ = (↑s : ℕ) := by
        simp [commonLog]
  rw [hprefixCount] at htakeEq
  have htgt₁ : x₁.queryLog[(↑s : ℕ)]? = some x₁.target :=
    forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) h₁
  have htgt₂ : x₂.queryLog[(↑s : ℕ)]? = some x₂.target :=
    forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) h₂
  have hgetElemTake (l : List (M × Commit)) :
      (l.take ((↑s : ℕ) + 1))[(↑s : ℕ)]? = l[(↑s : ℕ)]? :=
    List.getElem?_take_of_lt (Nat.lt_succ_self _)
  apply Option.some.inj
  rw [← htgt₁, ← htgt₂, ← hgetElemTake x₁.queryLog,
    ← hgetElemTake x₂.queryLog, htakeEq]

/-- Managed-RO replay-fork convenience theorem at a fixed public key, stated at the
`OracleComp (unifSpec + (Unit →ₒ Chal))` level.

Packages the replay-forking quantitative bound with the distinct-answer and
postcondition-transfer facts for the wrapped managed random-oracle trace experiment.

**On the level of the statement.** We state the bound at the `OracleComp` level rather than
lifting through `simulateQ` to `ProbComp`. Each caller (e.g. `euf_nma_bound`) can bridge to
`ProbComp` in one line using `uniformSampleImpl.probEvent_simulateQ` when needed, keeping this
lemma focused on the forking-lemma content.

**On the target-equality conjunct.** A maximally-informative version would also conclude
`x₁.target = x₂.target` (i.e. message-commit pair coincidence at the fork point), matching
Firsov-Janku's `forking_lemma_ro`. In the Lean formalization this conjunct is consumed by the
downstream reduction `euf_nma_bound` to align the cached challenges `ω_i = x_i.roCache target`.
It follows from the occurrence's intrinsic common-prefix decomposition plus a correspondence
between the adversary's internal `queryLog` and the outer `QueryLog`. It is extracted through
the caller-provided `P_out` transfer predicate: the caller may choose `P_out`
so that `P_out x log` pins `x.target` to a deterministic function of `(log, cf x)`, and then
derive target-equality from the distinct-answer disagreement on the outer log.

**On the `hreach` hypothesis.** `CfReachable` ensures that whenever `forkPoint` selects an
index `s` for a trace `x`, the outer `QueryLog` actually has an `i = Sum.inr ()` query at
position `↑s`. For the FiatShamir setting this follows from the correspondence between the
trace's internal `queryLog : List (M × Commit)` and the outer `QueryLog` of `Sum.inr ()`
queries: each cache miss in `roImpl` appends to both simultaneously, so a logical index `s`
into the trace's list corresponds to the same physical position in the outer log. Callers
discharge `hreach` by establishing this correspondence at the level of `runTrace`. -/
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
    letI : IsUniformSpec ((Unit →ₒ Chal) : OracleSpec _) :=
      IsUniformSpec.ofFintypeInhabited _
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
        | contextFork wrappedMain qb (Sum.inr ()) cf] := by
  let : IsUniformSpec ((Unit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  intro wrappedMain cf qb acc
  classical
  have hAcc_sum : acc = ∑ s, Pr[= some s | cf <$> wrappedMain] := by
    simp only [acc]
    rw [show (fun x => (cf x).isSome = true) =
        (fun x : _ => (Option.isSome x = true)) ∘ cf from rfl,
      ← probEvent_map (q := fun r => Option.isSome r = true),
      probEvent_isSome_eq_tsum_probOutput_some, tsum_fintype]
  rw [hAcc_sum]
  have hH_inv : (Fintype.card ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr ())) : ENNReal)⁻¹ =
      challengeSpaceInv Chal := rfl
  refine (?_ : _ ≤ Pr[ fun r => r.isSome | contextFork wrappedMain qb (Sum.inr ()) cf]).trans
    (probEvent_mono fun r hr hisSome => ?_)
  · simpa only [show qb (Sum.inr ()) = qH from rfl, hH_inv, Nat.cast_add, Nat.cast_one] using
      le_probEvent_isSome_contextFork (main := wrappedMain) (qb := qb) (i := Sum.inr ())
        (cf := cf) hreach.toPathCfReachable
  · rcases r with _ | ⟨x₁, x₂⟩
    · simp at hisSome
    obtain ⟨log₁, log₂, s, hcf₁, hcf₂, hP₁, hP₂, hneq⟩ :=
      contextFork_propertyTransfer (main := wrappedMain) (qb := qb) (i := Sum.inr ())
        (cf := cf) (P_out := P_out) (hP := hP) hr
    exact ⟨x₁, x₂, s, log₁, log₂, rfl, hcf₁, hcf₂, hneq, hP₁, hP₂⟩

end Fork

end FiatShamir
