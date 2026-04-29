/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.OracleComp.QueryTracking.ProgrammingOracle
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# TV-distance bound for `withProgramming` vs `withCaching`

The headline theorem `tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad` bounds
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

## Programming collision bound

Built directly on top of the headline TV-distance bound, `programming_collision_bound` is the
"collision-event" repackaging used by Fiat-Shamir-style identical-until-bad reductions: given
any upper bound `B` on `probEventBadOfWithProgramming so policy oa`, the TV-distance between
the unprogrammed and programmed runs is at most `B.toReal`. The convenience wrapper
`programming_collision_bound_qP_qH_β` specializes `B` to the textbook `qP * qH * β` shape so
callers only need to discharge a union-bound hypothesis. Both live in this `Relational`
namespace because they are TV-distance statements; the underlying `withProgramming` /
`withCaching` definitions and the `HasUnpredictableSample` typeclass remain in
`QueryTracking/`.
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
      simp [QueryImpl.withProgramming_apply, hcache]
    have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
        (pure (v, (cache, false)) :
          OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
      simp [QueryImpl.withCachingTrackingPolicy_apply, hcache]
    rw [hL, hR]
  | none =>
    cases hpol : policy t with
    | none =>
      have hL : (so.withProgramming policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', false)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withProgramming_apply, hcache, hpol, Functor.map_map]
      have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', false)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withCachingTrackingPolicy_apply, hcache, hpol, Functor.map_map]
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
        simp [QueryImpl.withProgramming_apply, hcache, hpol]
      have hR_run : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', true)) :
            OracleComp spec (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withCachingTrackingPolicy_apply, hcache, hpol, Functor.map_map]
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

/-! ## Programming collision bound -/

/-- The bad-event probability of `withProgramming policy` on input `oa`, started from an empty
cache and `bad := false`. The bad flag flips on the first cache-miss whose query input lies in
the policy's support; this abbreviation isolates that probability so downstream union-bound
arguments can name it. -/
noncomputable abbrev probEventBadOfWithProgramming
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec) (oa : OracleComp spec α) : ℝ≥0∞ :=
  Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
      (simulateQ (so.withProgramming policy) oa).run (∅, false)]

/-- **Programming collision bound.**

The TV-distance between running `oa` under pure caching and under a `policy`-programming
oracle is bounded by any upper bound `B` on the bad-event probability of
`withProgramming policy` (provided `B < ∞`).

This is the user-facing wrapper around
`tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad`: the heavy lifting (the
identical-until-bad bridge between `withCaching` and `withProgramming`) is the headline
theorem of this file; here we just expose it under the canonical "collision" name and combine
it with a user-supplied bad-event bound `hBad`.

The canonical `qP * qH * β` Fiat-Shamir slack is recovered by instantiating
`B := (qP : ℝ≥0∞) * qH * β` (see `programming_collision_bound_qP_qH_β`) and discharging `hBad`
via a union bound over the at most `qP` programmed points (each contributing at most `qH * β`
by per-step unpredictability of the queried inputs). For Schnorr with `spec.Domain = M × Commit`,
`β = 1/|G|`, `qP = qS`, and effective `qH = qS + qH`, this matches `collisionSlack qS qH G`.

The per-point union bound itself depends on the structure of `oa`'s queries (specifically, an
unpredictability hypothesis on each query's input distribution); it is discharged in the
caller's setting. See `Examples/CommitmentScheme/` and `CryptoFoundations/FiatShamir/Sigma/`
for FS-flavored applications. -/
theorem programming_collision_bound
    (oa : OracleComp spec α)
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec)
    {B : ℝ≥0∞} (hB_lt_top : B < ∞)
    (hBad : probEventBadOfWithProgramming so policy oa ≤ B) :
    tvDist
        ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false))
      ≤ B.toReal :=
  (tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad so policy oa ∅).trans
    (ENNReal.toReal_mono hB_lt_top.ne hBad)

/-- Convenience repackaging of `programming_collision_bound`: when the user has a bad-event
bound of the canonical `qP * qH * β` shape, we get the canonical FS slack as the TV-distance
bound. The caller need only discharge `hBad` (typically by a union bound over at most `qP`
programmed points, each hit with probability `≤ qH * β`). -/
theorem programming_collision_bound_qP_qH_β
    (oa : OracleComp spec α) (qH qP : ℕ) (β : ℝ≥0∞) (hβ_lt_top : β < ∞)
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec)
    (hBad : probEventBadOfWithProgramming so policy oa ≤ (qP : ℝ≥0∞) * qH * β) :
    tvDist
        ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false))
      ≤ ((qP : ℝ≥0∞) * qH * β).toReal := by
  have hBound_lt_top : (qP : ℝ≥0∞) * qH * β < ∞ := by
    have hqPqH : (qP : ℝ≥0∞) * qH < ∞ :=
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.natCast_lt_top _)
    exact ENNReal.mul_lt_top hqPqH hβ_lt_top
  exact programming_collision_bound oa so policy hBound_lt_top hBad

end OracleComp.ProgramLogic.Relational
