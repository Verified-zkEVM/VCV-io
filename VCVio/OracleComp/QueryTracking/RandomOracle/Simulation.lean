/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Random-Oracle Simulation Helpers

Generic lemmas for simulating `OracleComp (unifSpec + hashSpec)` computations via
`unifFwdImpl + ro` in `StateT hashSpec.QueryCache ProbComp`, where `unifFwdImpl` forwards
uniform-randomness queries and `ro` handles the hash oracle (typically `randomOracle`).

These lemmas factor out boilerplate shared by `FiatShamir.perfectlyCorrect`,
`FiatShamirWithAbort.correct`, and other random-oracle-model proofs.

The typical usage pattern is:

```
let ro : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp) := randomOracle
let impl := unifFwdImpl hashSpec + ro
```

Then the `roSim` namespace lemmas apply to `simulateQ impl`.

## Main definitions

* `unifFwdImpl`: the identity forwarding implementation for `unifSpec`, lifted to `StateT`
* `OracleComp.unifFwdAnswerImpl`: forwards uniform queries while using a fixed deterministic
  answer table for the other summand
* `OracleComp.probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff`: reduces a
  probability-one claim for the combined lazy random oracle to all agreeing fixed answer tables
-/

@[expose] public section

open OracleComp OracleSpec

variable {ι : Type} {hashSpec : OracleSpec ι}

/-- The identity forwarding implementation for `unifSpec` queries, lifted to
`StateT hashSpec.QueryCache ProbComp`. Each uniform query passes through to the underlying
`ProbComp` without touching the cache state. -/
def unifFwdImpl (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (StateT hashSpec.QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT hashSpec.QueryCache ProbComp)

namespace unifFwdImpl

/-- Simulating a plain `ProbComp` through `unifFwdImpl` and running it on cache `s` leaves
the cache untouched, pairing each sampled output with the unchanged `s`. -/
lemma simulateQ_run {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec) oa).run s = (fun x => (x, s)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [unifFwdImpl, ← ih]

end unifFwdImpl

namespace roSim

variable (ro : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))

/-- Simulating a `liftComp`-embedded `ProbComp` through `unifFwdImpl + ro` discards the hash
oracle, reducing to simulation through `unifFwdImpl` alone. -/
lemma simulateQ_liftComp {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (OracleComp.liftComp oa (unifSpec + hashSpec)) =
    simulateQ (unifFwdImpl hashSpec) oa :=
  QueryImpl.simulateQ_add_liftComp_left
    (m' := StateT hashSpec.QueryCache ProbComp) (unifFwdImpl hashSpec) ro oa

/-- Running the `unifFwdImpl + ro` simulation of a lifted `ProbComp` on cache `s` leaves the
cache untouched, pairing each sampled output with `s`. -/
lemma run_liftM {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s =
      (fun x => (x, s)) <$> oa := by
  rw [show simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) =
      simulateQ (unifFwdImpl hashSpec) oa from simulateQ_liftComp ro oa]
  exact unifFwdImpl.simulateQ_run oa s

/-- The support of the `unifFwdImpl + ro` simulation of a lifted `ProbComp` run on cache `s`
is the image of `support oa` under pairing each output with `s`. -/
lemma run_liftM_support {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    support ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s) =
      (fun x => (x, s)) '' support oa := by
  rw [run_liftM, support_map]

/-- Running the `unifFwdImpl + ro` simulation of a lifted `ProbComp` bound to a continuation,
projected to its value via `run'`, samples `oa` and then runs each continuation on cache `s`. -/
lemma run'_liftM_bind {α β : Type} (oa : ProbComp α)
    (rest : α → StateT hashSpec.QueryCache ProbComp β) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run' s =
      oa >>= fun x => (rest x).run' s := by
  change Prod.fst <$>
    ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run s) =
    oa >>= fun x => Prod.fst <$> (rest x).run s
  rw [StateT.run_bind, run_liftM]
  simp [map_bind]

/-- Simulating a `hashSpec` query through `unifFwdImpl + ro` dispatches it to the hash-oracle
handler `ro`, since uniform forwarding leaves hash queries to `ro`. -/
@[simp]
lemma simulateQ_liftM_spec_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro) (hashSpec.query q) = ro q := by
  change simulateQ (unifFwdImpl hashSpec + ro)
    (liftM (liftM (hashSpec.query q) :
      OracleQuery (unifSpec + hashSpec) _)) = _
  exact QueryImpl.simulateQ_add_liftM_query_right (unifFwdImpl hashSpec) ro q

/-- Simulating a `HasQuery.query` hash query through `unifFwdImpl + ro` dispatches it to the
hash-oracle handler `ro`, matching `simulateQ_liftM_spec_query` through the monad-lift form. -/
lemma simulateQ_HasQuery_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (HasQuery.query (spec := hashSpec)
        (m := OracleComp (unifSpec + hashSpec)) q) =
      ro q := by
  simp

end roSim

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Interpret uniform queries probabilistically while answering every `spec` query with the
deterministic table `f`. This is the fixed-table counterpart of
`unifFwdImpl spec + randomOracle`. -/
def unifFwdAnswerImpl (f : QueryImpl spec Id) :
    QueryImpl (unifSpec + spec) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) + f.liftTarget ProbComp

/-- The random-oracle simulation of a plain `OracleComp` never fails on any starting cache. -/
theorem neverFail_simulateQ_randomOracle_run
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    NeverFail ((simulateQ randomOracle oa).run cache) := by
  let : spec.Inhabited :=
    { inhabitedB := fun t =>
        Classical.inhabited_of_nonempty (α := spec.Range t) inferInstance }
  infer_instance

/-- Running the lazy random oracle on an uncached query `t` and binding the result samples the
fresh answer uniformly, so the support of the bound computation is the union over all answers of
the support obtained after caching that answer. -/
private lemma support_randomOracle_run_bind_of_uncached [DecidableEq ι]
    [(t : spec.Domain) → SampleableType (spec.Range t)] {β : Type} (t : spec.Domain)
    {cache : spec.QueryCache} (hcache : cache t = none)
    (g : spec.Range t × spec.QueryCache → ProbComp β) :
    support ((randomOracle (spec := spec) t).run cache >>= g) =
      ⋃ u, support (g (u, cache.cacheQuery t u)) := by
  rw [QueryImpl.withCaching_run_none _ hcache, support_bind, support_map,
    show support (uniformSampleImpl t) = Set.univ from support_uniformSample _]
  simp

/-- Support characterization for a computation with both fresh uniform queries and a lazy
random oracle.

An output `a` is reachable from `cache` under `unifFwdImpl spec + randomOracle` iff it is
reachable while keeping the uniform queries probabilistic and replacing the hash oracle by some
total deterministic answer table that agrees with `cache`. The final lazy-oracle cache is
existentially quantified away. -/
theorem exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (unifSpec + spec) α) (cache : spec.QueryCache) (a : α) :
    (∃ f : QueryImpl spec Id, cache.AgreesWithFn f ∧
      a ∈ support (simulateQ (unifFwdAnswerImpl f) oa))
    ↔
    (∃ cache' : spec.QueryCache,
      (a, cache') ∈ support
        ((simulateQ (unifFwdImpl spec +
          (spec.randomOracle : QueryImpl spec (StateT spec.QueryCache ProbComp))) oa).run
            cache)) := by
  classical
  let : spec.Inhabited :=
    { inhabitedB := fun t =>
        Classical.inhabited_of_nonempty (α := spec.Range t) inferInstance }
  induction oa using OracleComp.inductionOn generalizing cache a with
  | pure x =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff,
      StateT.run_pure, Prod.mk.injEq]
    refine ⟨fun ⟨_, _, h⟩ => ⟨cache, h, rfl⟩, fun ⟨_, ha, _⟩ => ?_⟩
    obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := spec) cache
    exact ⟨f, hf, ha⟩
  | query_bind t k ih =>
    cases t with
    | inl t =>
      simp only [simulateQ_bind, simulateQ_spec_query, unifFwdAnswerImpl,
        QueryImpl.add_apply_inl, HasQuery.toQueryImpl_apply, unifFwdImpl,
        QueryImpl.liftTarget_apply, StateT.run_bind, StateT.run_liftM,
        support_bind, Set.mem_iUnion]
      constructor
      · rintro ⟨f, hf, u, hu, ha⟩
        obtain ⟨cache', hcache'⟩ := (ih u cache a).mp
          ⟨f, hf, by simpa [unifFwdAnswerImpl] using ha⟩
        exact ⟨cache', (u, cache), ⟨u, hu, by simp⟩, hcache'⟩
      · rintro ⟨cache', ⟨u, cache₀⟩, ⟨u', hu', hpair⟩, ha⟩
        have hpair' : (u, cache₀) = (u', cache) := by simpa using hpair
        have hu : u = u' := congrArg Prod.fst hpair'
        have hc : cache₀ = cache := congrArg Prod.snd hpair'
        subst u'
        subst cache₀
        obtain ⟨f, hf, hs⟩ := (ih u cache a).mpr ⟨cache', ha⟩
        exact ⟨f, hf, u, hu', by simpa [unifFwdAnswerImpl] using hs⟩
    | inr t =>
      have h_eval : ∀ f : QueryImpl spec Id,
          simulateQ (unifFwdAnswerImpl f)
              (liftM ((unifSpec + spec).query (Sum.inr t)) >>= k) =
            simulateQ (unifFwdAnswerImpl f) (k (f t)) := by
        intro f
        rw [simulateQ_bind, simulateQ_spec_query]
        change (pure (f t) : ProbComp _) >>= (fun u =>
          simulateQ (unifFwdAnswerImpl f) (k u)) = _
        rw [pure_bind]
      simp_rw [h_eval]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.add_apply_inr]
      rcases hcache : cache t with _ | u
      · simp only [support_randomOracle_run_bind_of_uncached t hcache, Set.mem_iUnion]
        constructor
        · rintro ⟨f, hf, ha⟩
          obtain ⟨cache', hcache'⟩ := (ih (f t) (cache.cacheQuery t (f t)) a).mp
            ⟨f, (QueryCache.agreesWithFn_cacheQuery_iff cache t (f t) f hcache).mpr
              ⟨hf, rfl⟩, ha⟩
          exact ⟨cache', f t, hcache'⟩
        · rintro ⟨cache', u, hcache'⟩
          obtain ⟨f, hagree, ha⟩ := (ih u (cache.cacheQuery t u) a).mpr
            ⟨cache', hcache'⟩
          obtain ⟨hf, hfu⟩ :=
            (QueryCache.agreesWithFn_cacheQuery_iff cache t u f hcache).mp hagree
          exact ⟨f, hf, hfu ▸ ha⟩
      · rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]
        constructor
        · rintro ⟨f, hf, ha⟩
          exact (ih u cache a).mp ⟨f, hf, hf hcache ▸ ha⟩
        · intro hsupp
          obtain ⟨f, hf, ha⟩ := (ih u cache a).mpr hsupp
          exact ⟨f, hf, hf hcache ▸ ha⟩

/-- Probability-one form of the combined uniform-query/random-oracle support characterization.

The combined lazy-oracle simulation satisfies `p` almost surely from `preexisting_cache` iff,
for every deterministic hash-answer table extending that cache, the computation that keeps fresh
uniform queries probabilistic and uses that fixed table satisfies `p` almost surely. No separate
`NeverFail` premise is needed: both interpretations are `ProbComp` computations and hence total. -/
theorem probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff
    [DecidableEq ι] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (unifSpec + spec) α) (preexisting_cache : spec.QueryCache) (p : α → Prop) :
    Pr[fun v => p v.1 |
      (simulateQ (unifFwdImpl spec +
        (spec.randomOracle : QueryImpl spec (StateT spec.QueryCache ProbComp))) oa).run
          preexisting_cache] = 1
    ↔
    ∀ f : QueryImpl spec Id, preexisting_cache.AgreesWithFn f →
      Pr[p | simulateQ (unifFwdAnswerImpl f) oa] = 1 := by
  classical
  rw [probEvent_eq_one_iff]
  constructor
  · rintro ⟨_, hsupp⟩ f hf
    rw [probEvent_eq_one_iff]
    refine ⟨probFailure_eq_zero' (by infer_instance), ?_⟩
    intro a ha
    obtain ⟨cache', hcache'⟩ :=
      (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
        oa preexisting_cache a).mp ⟨f, hf, ha⟩
    exact hsupp (a, cache') hcache'
  · intro h
    refine ⟨probFailure_eq_zero' (by infer_instance), ?_⟩
    rintro ⟨a, cache'⟩ ha
    obtain ⟨f, hf, has⟩ :=
      (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
        oa preexisting_cache a).mpr ⟨cache', ha⟩
    exact ((probEvent_eq_one_iff.mp (h f hf)).2 a has)

/-- Support characterization for lazy random-oracle simulation.

A value `a` can appear as the output of the random-oracle simulation from `cache` iff some total
answer function agreeing with `cache` evaluates the computation to `a`. The final cache produced
by the simulation is existentially quantified away. -/
theorem exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) (a : α) :
    (∃ f : QueryImpl spec Id, cache.AgreesWithFn f ∧ evalWithAnswerFn f oa = a)
    ↔
    (∃ cache' : spec.QueryCache,
      (a, cache') ∈ support ((simulateQ randomOracle oa).run cache)) := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq]
    refine ⟨fun ⟨_, _, h⟩ => ⟨cache, h.symm, rfl⟩, fun ⟨_, ha, _⟩ => ?_⟩
    obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := spec) cache
    exact ⟨f, hf, ha.symm⟩
  | query_bind t k ih =>
    have h_eval : ∀ f : QueryImpl spec Id, evalWithAnswerFn f (liftM (spec.query t) >>= k)
        = evalWithAnswerFn f (k (f t)) := fun f => by
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (spec.query t)) = f t from simulateQ_spec_query f t]
    simp_rw [h_eval]
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases hcache : cache t with _ | u
    · simp only [support_randomOracle_run_bind_of_uncached t hcache, Set.mem_iUnion]
      refine ⟨fun ⟨f, hf, ha⟩ => ?_, fun ⟨cache', u, hcache'⟩ => ?_⟩
      · obtain ⟨cache', hcache'⟩ := (ih (f t) (cache.cacheQuery t (f t)) a).mp
          ⟨f, (QueryCache.agreesWithFn_cacheQuery_iff cache t (f t) f hcache).mpr ⟨hf, rfl⟩, ha⟩
        exact ⟨cache', f t, hcache'⟩
      · obtain ⟨f, hagree, ha⟩ := (ih u (cache.cacheQuery t u) a).mpr ⟨cache', hcache'⟩
        obtain ⟨hf, hfu⟩ := (QueryCache.agreesWithFn_cacheQuery_iff cache t u f hcache).mp hagree
        exact ⟨f, hf, hfu ▸ ha⟩
    · rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]
      refine ⟨fun ⟨f, hf, ha⟩ => (ih u cache a).mp ⟨f, hf, hf hcache ▸ ha⟩, fun hsupp => ?_⟩
      obtain ⟨f, hf, ha⟩ := (ih u cache a).mpr hsupp
      exact ⟨f, hf, hf hcache ▸ ha⟩

/-- Probability-one form of the random-oracle support characterization.

A predicate on the result value holds with probability one under lazy random-oracle simulation
from `preexisting_cache` iff it holds for every total answer function agreeing with that cache. -/
theorem probEvent_eq_one_simulateQ_randomOracle_run_iff
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (preexisting_cache : spec.QueryCache) (p : α → Prop) :
    Pr[fun v => p v.1 | (simulateQ randomOracle oa).run preexisting_cache] = 1
    ↔
    ∀ f : QueryImpl spec Id, preexisting_cache.AgreesWithFn f → p (evalWithAnswerFn f oa) := by
  classical
  rw [probEvent_eq_one_iff]
  refine ⟨fun ⟨_, hsupp⟩ f hf => ?_, fun h => ⟨?_, ?_⟩⟩
  · obtain ⟨cache', hcache'⟩ :=
      (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support oa preexisting_cache
        (evalWithAnswerFn f oa)).mp ⟨f, hf, rfl⟩
    exact hsupp _ hcache'
  · exact probFailure_eq_zero' (neverFail_simulateQ_randomOracle_run oa preexisting_cache)
  · rintro ⟨a, cache'⟩ hac
    obtain ⟨f, hf, ha⟩ :=
      (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support oa preexisting_cache a).mpr
        ⟨cache', hac⟩
    exact ha ▸ h f hf

end OracleComp

/-- Simulating the random oracle leaves a mapped uniform `Fin` sample unchanged: the query is
intercepted, but from the empty cache it misses and resamples uniformly, and the updated cache is
then discarded by `run'`, so the distribution over results is identical to the original sample. -/
lemma simulateQ_randomOracle_map_uniformFin {α : Type} (n : ℕ) (f : Fin (n + 1) → α) :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (f <$> uniformSample (Fin (n + 1)) : ProbComp α) :
        StateT unifSpec.QueryCache ProbComp α).run' ∅) =
      (f <$> uniformSample (Fin (n + 1))) := by
  rw [simulateQ_map, StateT.run'_map']
  congr 1
