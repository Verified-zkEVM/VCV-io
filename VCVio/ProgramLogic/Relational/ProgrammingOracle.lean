/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.ProgrammingOracle
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# TV-distance bound for `withProgramming` vs `withCaching`

The user-facing theorem `tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad` bounds
the total variation distance between the output distribution of `withCaching` and the output
distribution of `withProgramming policy` by the probability that the bad flag of
`withProgramming policy` ever fires (i.e., the adversary queries a point on which `policy` is
defined).

The proof factors through the auxiliary `withCachingTrackingPolicy` (defined alongside
`withProgramming` in `OracleComp/QueryTracking/ProgrammingOracle.lean`):

* On every step from non-bad input `(cache, false)`, the head distributions of
  `withProgramming policy` and `withCachingTrackingPolicy policy` agree on **non-bad** outputs.
  On policy-firing steps, both implementations produce only bad outputs (with possibly
  different `(value, cache)` components). This is the exact shape consumed by
  `OracleComp.ProgramLogic.Relational.identical_until_bad_with_flag`.
* `withCachingTrackingPolicy_run'_eq` projects `withCachingTrackingPolicy` to `withCaching`
  on the output marginal, eliminating the auxiliary impl from the user-facing statement.

The bound applies to any underlying `so : QueryImpl spec (OracleComp spec)`, with the policy
acting on inputs of `spec`.
-/

open ENNReal OracleSpec OracleComp QueryImpl

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α : Type}

/-! ## Per-step distributional agreement on non-bad outputs -/

private lemma probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (cache : spec.QueryCache)
    (u : spec.Range t) (cache' : spec.QueryCache) :
    Pr[= (u, (cache', false)) | (so.withProgramming policy t).run (cache, false)] =
      Pr[= (u, (cache', false)) | (so.withCachingTrackingPolicy policy t).run (cache, false)] := by
  classical
  cases hcache : cache t with
  | some v =>
    have hL : (so.withProgramming policy t).run (cache, false) =
        (pure (v, (cache, false)) :
          OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
      change (do let s ← (get : StateT _ (OracleComp spec) _); _).run (cache, false) = _
      simp [hcache]
    have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
        (pure (v, (cache, false)) :
          OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
      change (do let s ← (get : StateT _ (OracleComp spec) _); _).run (cache, false) = _
      simp [hcache]
    rw [hL, hR]
  | none =>
    cases hpol : policy t with
    | none =>
      have hL : (so.withProgramming policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', false)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        change (do let s ← (get : StateT _ (OracleComp spec) _); _).run (cache, false) = _
        simp [hcache, hpol, StateT.run_bind]
      have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', false)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        change (do let s ← (get : StateT _ (OracleComp spec) _); _).run (cache, false) = _
        simp [hcache, hpol, StateT.run_bind]
      rw [hL, hR]
    | some v =>
      have hne : ∀ (w : spec.Range t) (c : spec.QueryCache),
          ((u, (cache', false)) : spec.Range t × spec.QueryCache × Bool) ≠ (w, (c, true)) := by
        intro w c hcontr
        injection hcontr with _ h2
        injection h2 with _ h3
        cases h3
      have hL_run : (so.withProgramming policy t).run (cache, false) =
          (pure (v, (cache.cacheQuery t v, true)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        change (do let s ← (get : StateT _ (OracleComp spec) _); _).run (cache, false) = _
        simp [hcache, hpol]
      have hR_run : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', true)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        change (do let s ← (get : StateT _ (OracleComp spec) _); _).run (cache, false) = _
        simp [hcache, hpol, StateT.run_bind]
      rw [hL_run, hR_run]
      rw [probOutput_pure, if_neg (hne v _)]
      rw [probOutput_bind_eq_tsum]
      symm
      refine ENNReal.tsum_eq_zero.mpr (fun u' => ?_)
      rw [probOutput_pure, if_neg (hne u' _), mul_zero]

/-! ## Bad-input monotonicity wrappers (`σ × Bool` shape) -/

omit [spec.Fintype] [spec.Inhabited] in
private lemma withProgramming_mono_pair
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (p : spec.QueryCache × Bool) (hp : p.2 = true)
    (z) (hz : z ∈ support ((so.withProgramming policy t).run p)) : z.2.2 = true := by
  rcases p with ⟨cache, b⟩
  cases (show b = true from hp)
  exact QueryImpl.withProgramming_bad_monotone (so := so) (policy := policy) t cache z hz

omit [spec.Fintype] [spec.Inhabited] in
private lemma withCachingTrackingPolicy_mono_pair
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (p : spec.QueryCache × Bool) (hp : p.2 = true)
    (z) (hz : z ∈ support ((so.withCachingTrackingPolicy policy t).run p)) :
    z.2.2 = true := by
  rcases p with ⟨cache, b⟩
  cases (show b = true from hp)
  exact QueryImpl.withCachingTrackingPolicy_bad_monotone (so := so) (policy := policy) t cache z hz

/-! ## TV-distance bound -/

/-- TV-distance between the output marginal of `withProgramming policy` and the output marginal
of `withCachingTrackingPolicy policy` is bounded by the probability that the bad flag of
`withProgramming policy` fires during the run. -/
private theorem tvDist_withProgramming_withCachingTrackingPolicy_le_probEvent_bad
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ (so.withProgramming policy) oa).run' (cache, false))
        ((simulateQ (so.withCachingTrackingPolicy policy) oa).run' (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (so.withProgramming policy) oa).run (cache, false)].toReal := by
  refine identical_until_bad_with_flag
    (impl₁ := so.withProgramming policy)
    (impl₂ := so.withCachingTrackingPolicy policy)
    (oa := oa) (s₀ := cache)
    ?_ ?_ ?_
  · intro t s u s'
    exact probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output
      so policy t s u s'
  · intro t p hp z hz
    exact withProgramming_mono_pair so policy t p hp z hz
  · intro t p hp z hz
    exact withCachingTrackingPolicy_mono_pair so policy t p hp z hz

/-- TV-distance between the output marginal of `so.withCaching` and the output marginal of
`so.withProgramming policy` is bounded by the probability that the bad flag of
`withProgramming policy` fires (i.e., the adversary queries a programmed point) during the run.

This is the user-facing "identical until bad" bound: programming a random oracle is
indistinguishable from the unprogrammed oracle until the adversary queries a programmed point.
The bound is one-sided in the natural way for "ratchet" arguments: it controls the answer
distribution under the unprogrammed oracle by the bad-event probability under the programmed
oracle. -/
theorem tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ so.withCaching oa).run' cache)
        ((simulateQ (so.withProgramming policy) oa).run' (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (so.withProgramming policy) oa).run (cache, false)].toReal := by
  have h_proj :
      (simulateQ so.withCaching oa).run' cache =
        (simulateQ (so.withCachingTrackingPolicy policy) oa).run' (cache, false) :=
    (withCachingTrackingPolicy_run'_eq' so policy oa cache false).symm
  have h_tv :=
    tvDist_withProgramming_withCachingTrackingPolicy_le_probEvent_bad so policy oa cache
  rw [h_proj, tvDist_comm]
  exact h_tv

end OracleComp.ProgramLogic.Relational
