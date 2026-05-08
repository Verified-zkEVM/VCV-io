/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.Structures

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
-/

open OracleComp OracleSpec

variable {ι : Type} {hashSpec : OracleSpec ι}

/-- The identity forwarding implementation for `unifSpec` queries, lifted to
`StateT hashSpec.QueryCache ProbComp`. Each uniform query passes through to the underlying
`ProbComp` without touching the cache state. -/
noncomputable def unifFwdImpl (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (StateT hashSpec.QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT hashSpec.QueryCache ProbComp)

namespace unifFwdImpl

lemma simulateQ_run {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec) oa).run s = (fun x => (x, s)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [unifFwdImpl, ← ih]

end unifFwdImpl

namespace roSim

variable (ro : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))

lemma simulateQ_liftComp {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (OracleComp.liftComp oa (unifSpec + hashSpec)) =
    simulateQ (unifFwdImpl hashSpec) oa :=
  QueryImpl.simulateQ_add_liftComp_left
    (m' := StateT hashSpec.QueryCache ProbComp)
    (unifFwdImpl hashSpec) ro oa

lemma run_liftM {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s =
      (fun x => (x, s)) <$> oa := by
  rw [show simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) =
      simulateQ (unifFwdImpl hashSpec) oa from simulateQ_liftComp ro oa]
  exact unifFwdImpl.simulateQ_run oa s

lemma run_liftM_support {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    support ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s) =
      (fun x => (x, s)) '' support oa := by
  rw [run_liftM, support_map]

lemma run'_liftM_bind {α β : Type} (oa : ProbComp α)
    (rest : α → StateT hashSpec.QueryCache ProbComp β)
    (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run' s =
      oa >>= fun x => (rest x).run' s := by
  change Prod.fst <$>
    ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run s) =
    oa >>= fun x => Prod.fst <$> (rest x).run s
  rw [StateT.run_bind, run_liftM]
  simp [map_bind]

@[simp]
lemma simulateQ_liftM_spec_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro) (hashSpec.query q) = ro q := by
  change simulateQ (unifFwdImpl hashSpec + ro)
    (liftM (liftM (hashSpec.query q) :
      OracleQuery (unifSpec + hashSpec) _)) = _
  simp [simulateQ_query]

lemma simulateQ_HasQuery_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (HasQuery.query (spec := hashSpec)
        (m := OracleComp (unifSpec + hashSpec)) q) =
      ro q := by
  rw [HasQuery.instOfMonadLift_query]
  exact simulateQ_liftM_spec_query ro q

end roSim

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The random-oracle simulation of a plain `OracleComp` never fails on any starting cache. -/
theorem neverFail_simulateQ_randomOracle_run
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    NeverFail ((simulateQ randomOracle oa).run cache) := by
  grind only [= HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

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
    have hpure : (simulateQ randomOracle (pure x : OracleComp spec α)).run cache
        = (pure (x, cache) : ProbComp _) := by simp [simulateQ_pure, StateT.run_pure]
    rw [hpure]
    refine ⟨fun ⟨_, _, h⟩ => ?_, fun ⟨cache', hcache'⟩ => ?_⟩
    · refine ⟨cache, ?_⟩
      rw [evalWithAnswerFn_pure] at h
      rw [support_pure, Set.mem_singleton_iff, ← h]
    · obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := spec) cache
      refine ⟨f, hf, ?_⟩
      rw [evalWithAnswerFn_pure]
      rw [support_pure, Set.mem_singleton_iff] at hcache'
      exact (Prod.mk.inj hcache').1.symm
  | query_bind t k ih =>
    have h_eval : ∀ f : QueryImpl spec Id,
        evalWithAnswerFn f (liftM (spec.query t) >>= k) = evalWithAnswerFn f (k (f t)) := by
      intro f
      rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn f (k (simulateQ f (liftM (spec.query t))))
        = evalWithAnswerFn f (k (f t))
      rw [simulateQ_spec_query]
    simp_rw [h_eval]
    have h_reduce :
        (simulateQ randomOracle (liftM (spec.query t) >>= k)).run cache
          = ((randomOracle (spec := spec) t).run cache) >>=
            fun p : (spec.Range t) × spec.QueryCache =>
              (simulateQ randomOracle (k p.1)).run p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      exact StateT.run_bind _ _ _
    rw [h_reduce]
    rcases hcache : cache t with _ | u
    · rw [show ((randomOracle (spec := spec) t).run cache) =
            (fun u => (u, cache.cacheQuery t u)) <$> ($ᵗ spec.Range t) from
            QueryImpl.withCaching_run_none _ hcache]
      rw [show (((fun u => (u, cache.cacheQuery t u)) <$> ($ᵗ spec.Range t)) >>=
              fun p : (spec.Range t) × spec.QueryCache =>
                (simulateQ randomOracle (k p.1)).run p.2)
            = (($ᵗ spec.Range t) >>= fun u =>
                (simulateQ randomOracle (k u)).run (cache.cacheQuery t u)) from by
        rw [map_eq_bind_pure_comp]
        simp [bind_assoc]]
      rw [support_bind]
      simp only [support_uniformSample, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      refine ⟨fun ⟨f, hf, ha⟩ => ?_, fun ⟨cache', u, hcache'⟩ => ?_⟩
      · have hagree : (cache.cacheQuery t (f t)).AgreesWithFn f :=
          (QueryCache.agreesWithFn_cacheQuery_iff cache t (f t) f hcache).mpr ⟨hf, rfl⟩
        obtain ⟨cache', hcache'⟩ :=
          (ih (f t) (cache.cacheQuery t (f t)) a).mp ⟨f, hagree, ha⟩
        exact ⟨cache', f t, hcache'⟩
      · obtain ⟨f, hagree, ha⟩ :=
          (ih u (cache.cacheQuery t u) a).mpr ⟨cache', hcache'⟩
        have ⟨hf, hfu⟩ :=
          (QueryCache.agreesWithFn_cacheQuery_iff cache t u f hcache).mp hagree
        exact ⟨f, hf, hfu ▸ ha⟩
    · rw [show ((randomOracle (spec := spec) t).run cache) = (pure (u, cache) : ProbComp _) from
            QueryImpl.withCaching_run_some _ hcache]
      rw [pure_bind]
      refine ⟨fun ⟨f, hf, ha⟩ => ?_, fun hsupp => ?_⟩
      · have hft : f t = u := hf hcache
        rw [hft] at ha
        exact (ih u cache a).mp ⟨f, hf, ha⟩
      · obtain ⟨f, hf, ha⟩ := (ih u cache a).mpr hsupp
        have hft : f t = u := hf hcache
        exact ⟨f, hf, hft ▸ ha⟩

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
  · haveI := neverFail_simulateQ_randomOracle_run oa preexisting_cache
    exact probFailure_eq_zero
  · rintro ⟨a, cache'⟩ hac
    obtain ⟨f, hf, ha⟩ :=
      (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support oa preexisting_cache a).mpr
        ⟨cache', hac⟩
    exact ha ▸ h f hf

end OracleComp
