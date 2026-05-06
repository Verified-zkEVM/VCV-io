/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Running an Oracle Computation with a Deterministic Function

This file ports `runWithOracle` and the bridge lemma
`randomOracle_neverFails_iff_runWithOracle_neverFails` from ArkLib's pre-removal
`ToVCVio/Oracle.lean` (commit 9a06cc55) into VCVio.

`runWithOracle f oa` runs `oa : OracleComp spec α` deterministically against an answer-function
`f : spec.FunctionType`, returning the resulting `α`. In current VCVio, plain `OracleComp` has
no built-in failure case, so the result is unwrapped (no `Option`).

The bridge lemmas connect probabilistic `NeverFail` claims about `simulateQ randomOracle` to
deterministic claims about `runWithOracle`. The original ArkLib proofs were left as `sorry` and
remain so here, awaiting completion.
-/

namespace OracleSpec

variable {ι : Type}

/-- A deterministic function answering oracle queries: maps each query input `t : spec.Domain`
to a value in the corresponding range `spec.Range t`. -/
def FunctionType (spec : OracleSpec ι) : Type _ := (t : spec.Domain) → spec.Range t

end OracleSpec

namespace OracleComp

open OracleSpec

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Run an oracle computation `oa : OracleComp spec α` deterministically against an oracle
function `f : spec.FunctionType`, producing the resulting value of type `α`.

Implemented as `simulateQ` through the `Id` monad. -/
def runWithOracle (f : spec.FunctionType) (oa : OracleComp spec α) : α :=
  simulateQ (QueryImpl.ofFn f) oa

@[simp]
theorem runWithOracle_pure (f : spec.FunctionType) (a : α) :
    runWithOracle f (pure a : OracleComp spec α) = a := rfl

@[simp]
theorem runWithOracle_bind (f : spec.FunctionType)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    runWithOracle f (oa >>= ob) = runWithOracle f (ob (runWithOracle f oa)) := by
  change simulateQ (QueryImpl.ofFn f) (oa >>= ob)
    = simulateQ (QueryImpl.ofFn f) (ob (simulateQ (QueryImpl.ofFn f) oa))
  rw [simulateQ_bind]; rfl

@[simp]
theorem runWithOracle_query (f : spec.FunctionType) (t : spec.Domain) :
    runWithOracle f (query t : OracleComp spec _) = f t := by
  change simulateQ (QueryImpl.ofFn f) (liftM (spec.query t)) = f t
  rw [simulateQ_spec_query]; rfl

@[simp]
theorem runWithOracle_map (f : spec.FunctionType)
    (g : α → β) (oa : OracleComp spec α) :
    runWithOracle f (g <$> oa) = g (runWithOracle f oa) := by
  change simulateQ (QueryImpl.ofFn f) (g <$> oa) = g (simulateQ (QueryImpl.ofFn f) oa)
  rw [simulateQ_map]; rfl

end OracleComp

namespace OracleSpec.QueryCache

variable {ι : Type} {spec : OracleSpec ι}

/-- A random-oracle cache `cache : spec.QueryCache` is *contained* in a deterministic answer
function `f : spec.FunctionType` if every cached entry agrees with `f`. -/
def containedIn (cache : spec.QueryCache) (f : spec.FunctionType) : Prop :=
  ∀ (t : spec.Domain) (r : spec.Range t), cache t = some r → f t = r

/-- For any cache there is some deterministic function containing it. -/
lemma exists_containedIn [spec.Inhabited] (cache : spec.QueryCache) :
    ∃ f : spec.FunctionType, cache.containedIn f := by
  refine ⟨fun t => (cache t).getD default, ?_⟩
  intro t r h
  simp [h]

variable [DecidableEq ι] [spec.DecidableEq]

omit [spec.DecidableEq] in
/-- An answer-function `f` extends `cache.cacheQuery t u` iff it extends `cache` (away from `t`)
and pins `f t = u`. When the original cache has no entry at `t`, this is just
`cache.containedIn f ∧ f t = u`. -/
lemma containedIn_cacheQuery_iff (cache : spec.QueryCache) (t : spec.Domain)
    (u : spec.Range t) (f : spec.FunctionType) (hcache : cache t = none) :
    (cache.cacheQuery t u).containedIn f ↔ cache.containedIn f ∧ f t = u := by
  classical
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · -- f extends cache because cache.cacheQuery agrees with cache off `t`
    intro t' r' hr'
    by_cases htt : t' = t
    · -- the case `t' = t` is impossible since cache t = none
      subst htt; rw [hcache] at hr'; exact absurd hr' (by simp)
    · exact h t' r' (by rw [cacheQuery_of_ne _ _ htt]; exact hr')
  · -- f t = u follows from inspecting the override entry
    exact h t u (by simp)
  · -- forward direction at `cache.cacheQuery t u`
    intro t' r' hr'
    by_cases htt : t' = t
    · -- `subst` here keeps `t'` and discards `t`, so we work in terms of `t'`
      subst htt
      have hrun : (cache.cacheQuery t' u) t' = some u := by simp
      rw [hrun] at hr'; cases hr'; exact h2
    · exact h1 t' r' (by rw [cacheQuery_of_ne _ _ htt] at hr'; exact hr')

end OracleSpec.QueryCache

namespace OracleComp

open OracleSpec

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The random-oracle simulation of a (failure-free) `OracleComp` never fails on any starting
cache. Internally `simulateQ randomOracle oa : StateT spec.QueryCache ProbComp α`, and `ProbComp`
itself is failure-free for plain `OracleComp` computations whose only oracle effects are uniform
samples through `randomOracle`. -/
theorem neverFail_simulateQ_randomOracle_run
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    NeverFail ((simulateQ randomOracle oa).run cache) := by
  grind only [= HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

/-- Support characterization: a value-cache pair `(a, c')` is reachable in the random-oracle
simulation starting from `cache` iff there is a deterministic answer-function `f` extending
`cache` such that `runWithOracle f oa = a`. (We only retain the value side here; the resulting
cache `c'` is not constrained.)

This is the structural lemma underlying `probEvent_eq_one_simulateQ_randomOracle_run_iff`. -/
theorem exists_containedIn_runWithOracle_eq_iff_mem_support
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (cache : spec.QueryCache) (a : α) :
    (∃ f : spec.FunctionType, cache.containedIn f ∧ runWithOracle f oa = a)
    ↔
    (∃ c' : spec.QueryCache, (a, c') ∈ support ((simulateQ randomOracle oa).run cache)) := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a with
  | pure x =>
    -- Both sides reduce to `a = x`.
    have hpure : (simulateQ randomOracle (pure x : OracleComp spec α)).run cache
        = (pure (x, cache) : ProbComp _) := by simp [simulateQ_pure, StateT.run_pure]
    rw [hpure]
    refine ⟨fun ⟨_, _, h⟩ => ?_, fun ⟨c', hc'⟩ => ?_⟩
    · refine ⟨cache, ?_⟩
      rw [runWithOracle_pure] at h
      rw [support_pure, Set.mem_singleton_iff, ← h]
    · obtain ⟨f, hf⟩ := QueryCache.exists_containedIn (spec := spec) cache
      refine ⟨f, hf, ?_⟩
      rw [runWithOracle_pure]
      rw [support_pure, Set.mem_singleton_iff] at hc'
      exact (Prod.mk.inj hc').1.symm
  | query_bind t k ih =>
    -- Pre-rewrite the LHS so `runWithOracle f (query t >>= k) = runWithOracle f (k (f t))`.
    have hLHS_runWithOracle : ∀ f : spec.FunctionType,
        runWithOracle f (liftM (spec.query t) >>= k) = runWithOracle f (k (f t)) := by
      intro f
      rw [runWithOracle_bind]
      change runWithOracle f (k (simulateQ (QueryImpl.ofFn f) (liftM (spec.query t))))
        = runWithOracle f (k (f t))
      rw [simulateQ_spec_query]; rfl
    simp_rw [hLHS_runWithOracle]
    -- Reduce simulateQ on the LHS to the same bind structure.
    have hLHS_reduce :
        (simulateQ randomOracle (liftM (spec.query t) >>= k)).run cache
          = ((randomOracle (spec := spec) t).run cache) >>=
            fun p : (spec.Range t) × spec.QueryCache =>
              (simulateQ randomOracle (k p.1)).run p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]; exact StateT.run_bind _ _ _
    rw [hLHS_reduce]
    -- Case split on `cache t`.
    rcases hcache : cache t with _ | u
    · -- Cache miss: the bind reduces to a uniform sample over `Range t`, then a recursive call.
      rw [show ((randomOracle (spec := spec) t).run cache) =
            (fun u => (u, cache.cacheQuery t u)) <$> ($ᵗ spec.Range t) from
            QueryImpl.withCaching_run_none _ hcache]
      rw [show (((fun u => (u, cache.cacheQuery t u)) <$> ($ᵗ spec.Range t)) >>=
              fun p : (spec.Range t) × spec.QueryCache =>
                (simulateQ randomOracle (k p.1)).run p.2)
            = (($ᵗ spec.Range t) >>= fun u =>
                (simulateQ randomOracle (k u)).run (cache.cacheQuery t u)) from by
        rw [map_eq_bind_pure_comp]; simp [bind_assoc]]
      rw [support_bind]
      simp only [support_uniformSample, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      -- LHS ↔ ∃ f extending cache, runWithOracle f (k (f t)) = a
      -- RHS ↔ ∃ u, ∃ c', (a, c') ∈ support ((simulateQ randomOracle (k u)).run (cacheQuery t u))
      --     ↔ (by ih) ∃ u, ∃ f extending (cacheQuery t u), runWithOracle f (k u) = a
      --     ↔ (containedIn_cacheQuery_iff) ∃ u, ∃ f extending cache with f t = u,
      --         runWithOracle f (k u) = a
      --     ↔ ∃ f extending cache, runWithOracle f (k (f t)) = a
      refine ⟨fun ⟨f, hf, ha⟩ => ?_, fun ⟨c', u, hc'⟩ => ?_⟩
      · -- Forward: have `f` extending cache; produce `(c', u)` with u = f t.
        have hcontain : (cache.cacheQuery t (f t)).containedIn f :=
          (QueryCache.containedIn_cacheQuery_iff cache t (f t) f hcache).mpr ⟨hf, rfl⟩
        obtain ⟨c', hc'⟩ := (ih (f t) (cache.cacheQuery t (f t)) a).mp ⟨f, hcontain, ha⟩
        exact ⟨c', f t, hc'⟩
      · -- Backward: extract `f` from IH at u, lift to extending cache.
        obtain ⟨f, hcontain, ha⟩ :=
          (ih u (cache.cacheQuery t u) a).mpr ⟨c', hc'⟩
        have ⟨hf, hfu⟩ :=
          (QueryCache.containedIn_cacheQuery_iff cache t u f hcache).mp hcontain
        exact ⟨f, hf, hfu ▸ ha⟩
    · -- Cache hit: bind collapses since `(randomOracle t).run = pure (u, cache)`.
      rw [show ((randomOracle (spec := spec) t).run cache) = (pure (u, cache) : ProbComp _) from
            QueryImpl.withCaching_run_some _ hcache]
      rw [pure_bind]
      -- LHS ↔ ∃ f extending cache, runWithOracle f (k (f t)) = a;
      -- but f t = u, so = runWithOracle f (k u) = a
      -- RHS ↔ ∃ c', (a, c') ∈ support ((simulateQ randomOracle (k u)).run cache)
      --     ↔ (by ih) ∃ f extending cache, runWithOracle f (k u) = a ✓
      refine ⟨fun ⟨f, hf, ha⟩ => ?_, fun hsupp => ?_⟩
      · have hft : f t = u := hf t u hcache
        rw [hft] at ha
        exact (ih u cache a).mp ⟨f, hf, ha⟩
      · obtain ⟨f, hf, ha⟩ := (ih u cache a).mpr hsupp
        have hft : f t = u := hf t u hcache
        exact ⟨f, hf, hft ▸ ha⟩

/-- For a particular preexisting cache, the random-oracle simulation never fails on that cache
iff `runWithOracle` succeeds for every deterministic answer-function compatible with the cache.

In current VCVio, plain `OracleComp` has no failure case, so `runWithOracle f oa` always
produces a value. The lemma is preserved for parity with the ArkLib API; its left-hand side is
the content carried by `NeverFail`-shaped Merkle-tree completeness statements. -/
theorem randomOracle_cache_neverFails_iff_runWithOracle_neverFails
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (preexisting_cache : spec.QueryCache) :
    NeverFail ((simulateQ randomOracle oa).run preexisting_cache)
    ↔
    ∀ f : spec.FunctionType, preexisting_cache.containedIn f →
      ∃ _a : α, runWithOracle f oa = _a :=
  ⟨fun _ _ _ => ⟨_, rfl⟩, fun _ => neverFail_simulateQ_randomOracle_run oa preexisting_cache⟩

/-- The random-oracle simulation never fails on any starting cache iff `runWithOracle` succeeds
for every deterministic answer-function. -/
theorem randomOracle_neverFails_iff_runWithOracle_neverFails
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) :
    (∀ preexisting_cache : spec.QueryCache,
        NeverFail ((simulateQ randomOracle oa).run preexisting_cache))
    ↔
    ∀ f : spec.FunctionType, ∃ _a : α, runWithOracle f oa = _a :=
  ⟨fun _ _ => ⟨_, rfl⟩, fun _ c => neverFail_simulateQ_randomOracle_run oa c⟩

/-- Probability-one form: a predicate on the *result value* (ignoring the final cache) holds with
probability 1 under the random-oracle simulation iff `runWithOracle` makes the predicate hold for
every deterministic answer-function extending the preexisting cache.

This is the lemma needed to prove `Pr[verify = true | ...] = 1` style completeness claims
using deterministic-oracle reasoning. It follows directly from the support characterization
`exists_containedIn_runWithOracle_eq_iff_mem_support` together with
`neverFail_simulateQ_randomOracle_run`. -/
theorem probEvent_eq_one_simulateQ_randomOracle_run_iff
    [DecidableEq ι] [spec.Inhabited] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp spec α) (preexisting_cache : spec.QueryCache) (p : α → Prop) :
    Pr[fun v => p v.1 | (simulateQ randomOracle oa).run preexisting_cache] = 1
    ↔
    ∀ f : spec.FunctionType, preexisting_cache.containedIn f → p (runWithOracle f oa) := by
  classical
  rw [probEvent_eq_one_iff]
  refine ⟨fun ⟨_, hsupp⟩ f hf => ?_, fun h => ⟨?_, ?_⟩⟩
  · -- Forward: pick any `f` extending cache, get a witness `(runWithOracle f oa, c') ∈ support`.
    obtain ⟨c', hc'⟩ :=
      (exists_containedIn_runWithOracle_eq_iff_mem_support oa preexisting_cache
        (runWithOracle f oa)).mp ⟨f, hf, rfl⟩
    exact hsupp _ hc'
  · -- Never-fail half is automatic.
    haveI := neverFail_simulateQ_randomOracle_run oa preexisting_cache
    exact probFailure_eq_zero
  · -- Support half: every `(a, c')` in support corresponds to some compatible `f` with
    -- `runWithOracle f oa = a`.
    rintro ⟨a, c'⟩ hac
    obtain ⟨f, hf, ha⟩ :=
      (exists_containedIn_runWithOracle_eq_iff_mem_support oa preexisting_cache a).mpr
        ⟨c', hac⟩
    exact ha ▸ h f hf

end OracleComp
