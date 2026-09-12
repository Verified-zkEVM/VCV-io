/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.TapeFactorization

/-! # GPV Hash-and-Sign: Flag-Instrumented Inline-Salt Handlers

The flag-instrumented original (inline-salt) handlers and the
freshness-tracking vehicle carrying the signed-set product factor.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! ### Flag-instrumented original (inline-salt) handlers

The front-tape route front-loads every signing salt into an upfront `drawList ($ᵗ Salt) qSign`
block, which forces the cardinality telescope to *re-interleave* the upfront tape back to the
per-signing-step draws before the `saltSeq` telescope applies — a deferred-sampling fold
commutation.

The handlers below avoid that re-interleaving by flag-instrumenting the *original*
inline-salt handlers `gpvRealImpl` / `progGameRunImplNoRec`, where each signing query
draws its fresh salt `r ← $ᵗ Salt` *at* its signing step. The collision flag fires when the
inline-drawn salt `r` is already a key of the running random-oracle cache (`saltKeyed`). Because the
salt is drawn at the step (not upfront), the run-level flag probability telescopes *directly* to the
`saltSeq` form (each salt is fresh uniform against the cache slice it is checked against) — no
re-interleaving is needed. The identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` applied to these flag handlers bounds the
total-variation distance of the two original game runs by the run-level flag probability. -/

open Classical in
/-- **Flag-instrumented original real handler.** `gpvRealImpl` threaded with a collision flag: the
state is `((Salt × M →ₒ Range).QueryCache × Bool)`. Uniform and random-oracle-read queries leave the
flag untouched; a signing query draws its fresh inline salt `r ← $ᵗ Salt`, sets the flag if `r` is
already a key of the cache (`saltKeyed`), monotonically OR-ing into the prior flag, then runs the
underlying `gpvRealImpl` signing body on it. Its `run'`-projection (dropping the flag) is the
original `gpvRealImpl`.

Unlike the tape handler `gpvRealImplTapeFlag`, the salt is drawn *inline at the signing step*, so
the collision decision is made against the cache the body actually queries, and there is no
empty-tape fallback branch: the off-bad per-query agreement is genuinely universal (no spurious bad
state). -/
@[expose] noncomputable def gpvRealImplFlag (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, s.2 || saltKeyed M Salt s.1 r))

open Classical in
/-- **Flag-instrumented original programmed handler.** The programmed dual of `gpvRealImplFlag`:
`progGameRunImplNoRec` threaded with the same collision flag (set on a signing step when the
inline-drawn salt `r` is already a key of the cache). Its `run'`-projection is the original
`progGameRunImplNoRec`. -/
@[expose]
noncomputable def progGameRunImplNoRecFlag (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$>
          (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn), (s.1.cacheQuery (r, msg) (psf.eval pk sgn), s.2 || saltKeyed M Salt s.1 r))

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlag` on a non-signing query.** The flag is untouched; the
underlying `gpvRealImpl` runs on the cache component. -/
lemma gpvRealImplFlag_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (gpvRealImplFlag psf hr M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1 := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlag` on a non-signing query.** -/
lemma progGameRunImplNoRecFlag_run_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (progGameRunImplNoRecFlag psf M Salt domainSample pk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1 := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlag` on a signing query.** The fresh inline salt `r` is
drawn, the real signing body runs the lazy random oracle at `(r, msg)` and trapdoor-samples, and the
flag is OR-ed with the collision predicate `saltKeyed` on the inline salt. -/
lemma gpvRealImplFlag_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (gpvRealImplFlag psf hr M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, s.2 || saltKeyed M Salt s.1 r))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlag` on a signing query.** -/
lemma progGameRunImplNoRecFlag_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (progGameRunImplNoRecFlag psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn),
          (s.1.cacheQuery (r, msg) (psf.eval pk sgn), s.2 || saltKeyed M Salt s.1 r))) := rfl

omit [Fintype Salt] in
/-- **Per-query flag-projection of the real flag handler.** Dropping the flag component
(`Prod.map id Prod.fst`) from one `gpvRealImplFlag` query step recovers the corresponding
`gpvRealImpl` step on the flagless cache state. The flag is a passive auxiliary: it is written by
the signing step but never affects the output or the cache, so projecting it away yields the
original handler. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplFlag_proj_fst (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (gpvRealImplFlag psf hr M Salt pk sk t).run s =
      (gpvRealImpl psf hr M Salt pk sk t).run s.1 := by
  cases t with
  | inl q => rw [gpvRealImplFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      rw [gpvRealImplFlag_run_inr, gpvRealImpl_run_sign]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query flag-projection of the programmed flag handler.** The programmed dual of
`gpvRealImplFlag_proj_fst`: dropping the flag recovers `progGameRunImplNoRec`. -/
lemma progGameRunImplNoRecFlag_proj_fst (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (progGameRunImplNoRecFlag psf M Salt domainSample pk t).run s =
      (progGameRunImplNoRec psf M Salt domainSample pk t).run s.1 := by
  cases t with
  | inl q => rw [progGameRunImplNoRecFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      rw [progGameRunImplNoRecFlag_run_inr, progGameRunImplNoRec_run_sign]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **Run-level flag-projection of the real flag handler.** Dropping the flag from the full
simulated run of `gpvRealImplFlag` over `adv.main pk` recovers the flagless run of `gpvRealImpl`.
This transports the per-query projection `gpvRealImplFlag_proj_fst` through the whole adversary via
`map_run_simulateQ_eq_of_query_map_eq`, witnessing that the collision flag is a passive instrument:
its addition does not change the output-and-cache distribution. -/
lemma map_run_gpvRealImplFlag_eq (pk : PK) (sk : SK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImpl psf hr M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (gpvRealImplFlag_proj_fst psf hr M Salt pk sk) oa s

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Run-level flag-projection of the programmed flag handler.** The programmed dual of
`map_run_gpvRealImplFlag_eq`. -/
lemma map_run_progGameRunImplNoRecFlag_eq (domainSample : PK → ProbComp Domain) (pk : PK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk) oa).run s =
      (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (progGameRunImplNoRecFlag_proj_fst psf M Salt domainSample pk) oa s

omit [Fintype Salt] in
/-- **Bad-monotonicity of the real flag handler.** Once the collision flag is set on the input state
(`p.2 = true`), every output of one `gpvRealImplFlag` query step also carries the flag set: the
non-signing branch preserves `s.2`, and the signing branch only OR-s a new collision indicator into
it. This is the `h_mono` hypothesis the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` consumes: the bad event is absorbing. -/
lemma gpvRealImplFlag_bad_mono (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : (Salt × M →ₒ Range).QueryCache × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((gpvRealImplFlag psf hr M Salt pk sk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [gpvRealImplFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [gpvRealImplFlag_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, c, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Bad-monotonicity of the programmed flag handler.** The programmed dual of
`gpvRealImplFlag_bad_mono`. -/
lemma progGameRunImplNoRecFlag_bad_mono (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : (Salt × M →ₒ Range).QueryCache × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((progGameRunImplNoRecFlag psf M Salt domainSample pk t).run p),
      z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [progGameRunImplNoRecFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [progGameRunImplNoRecFlag_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Salt] in
/-- **Off-bad joint agreement of the two original-run flag signing steps on a fresh inline salt (the
`hreg` substitution bridge, inline-salt signing case).** With the inline salt `r` *fixed* and *not
yet keyed* in the cache (`cache (r, msg) = none`, so the collision flag stays `false`), the full
signing-step body output distributions of `gpvRealImplFlag` and `progGameRunImplNoRecFlag` — the
returned signature `(r, sgn)`, the updated cache, and the (still `false`) flag — *coincide*.

The real side runs the lazy random oracle at `(r, msg)` (a miss, so it draws a fresh uniform target
`c ← $ᵗ Range`, records `(r, msg) ↦ c`), draws a trapdoor preimage `sgn ← trapdoorSample pk sk c`,
and tags the flag `false`; the programmed side forward-samples `sgn ← domainSample pk`, records
`(r, msg) ↦ psf.eval pk sgn`, and tags the flag `false`. Both apply the *same* deterministic
post-processing `fun (c, s) => ((r, s), cache.cacheQuery (r, msg) c, false)` to a `(target,
preimage)` pair drawn from two distributions that coincide by PSF regularity `hreg`. This is the
inline-salt analogue of `evalSPMF_gpvImplTape_run_sign_miss_eq`, the signing-query case of the
universal off-bad agreement `gpvImplFlag_h_agree_good`. It is *pinned* to the concrete flag handlers
(no free parameters). -/
theorem evalSPMF_gpvImplFlag_run_sign_offbad_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) (hmiss : cache (r, msg) = none)
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒮[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        let sgn ← psf.trapdoorSample pk sk p.1
        pure (((r, sgn), (p.2, false)) :
          (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))]
      = 𝒮[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn), (cache.cacheQuery (r, msg) (psf.eval pk sgn), false)) :
            (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))] := by
  classical
  set g : Range × Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool) :=
    fun cs => ((r, cs.2), (cache.cacheQuery (r, msg) cs.1, false)) with hg
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        = (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  have hLHS :
      𝒮[(do
          let p ← (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
          let sgn ← psf.trapdoorSample pk sk p.1
          pure (((r, sgn), (p.2, false)) :
            (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))]
        = 𝒮[g <$> (do let c ← ($ᵗ Range); let sgn ← psf.trapdoorSample pk sk c; pure (c, sgn)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  have hRHS :
      𝒮[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn), (cache.cacheQuery (r, msg) (psf.eval pk sgn), false)) :
            (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))]
        = 𝒮[g <$> (do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  exact evalSPMF_map_eq_of_evalSPMF_eq hreg.symm g

omit [Fintype Salt] in
open Classical in
/-- **Off-bad random-oracle-read agreement of the two original handlers.** On a random-oracle read
the underlying `gpvRealImpl` and `progGameRunImplNoRec` agree in distribution: on a cache hit both
return the recorded value with the cache unchanged; on a cache miss the real lazy oracle draws a
fresh uniform answer while the programmed oracle answers `psf.eval pk (domainSample pk)` and records
it, and these two answers are equally distributed by the first marginal of `hreg`. This is the
random-oracle-read case of the universal off-bad agreement `gpvImplFlag_h_agree_good`. -/
theorem evalSPMF_gpvImpl_run_read_eq (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (mc : Salt × M) (cache : (Salt × M →ₒ Range).QueryCache)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒮[(gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache]
      = 𝒮[(progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache] := by
  classical
  rw [gpvRealImpl_run_read, progGameRunImplNoRec_run_read]
  rcases h : cache mc with _ | v
  · -- Cache miss: real draws a fresh uniform answer; prog programs `eval ∘ domainSample`.
    rw [QueryImpl.withCaching_run_none uniformSampleImpl h]
    simp only []
    -- The first marginal of `hreg`: `eval ∘ domainSample ~ $ᵗ Range`.
    have hfst := evalSPMF_eval_domainSample_eq_uniform psf pk sk domainSample hNF hreg
    -- Both sides are `g <$> (·)` for `g w = (w, cache.cacheQuery mc w)` on the equal answers.
    calc 𝒮[(fun u => (u, cache.cacheQuery mc u)) <$>
            (uniformSampleImpl (spec := (Salt × M →ₒ Range)) mc)]
        = 𝒮[(fun w : Range => (w, cache.cacheQuery mc w)) <$> ($ᵗ Range : ProbComp Range)] := rfl
      _ = 𝒮[(fun w : Range => (w, cache.cacheQuery mc w)) <$>
            (do let sd ← domainSample pk; pure (psf.eval pk sd) : ProbComp Range)] :=
          evalSPMF_map_eq_of_evalSPMF_eq hfst.symm _
      _ = 𝒮[(fun sd : Domain => (psf.eval pk sd, cache.cacheQuery mc (psf.eval pk sd))) <$>
            (domainSample pk : ProbComp Domain)] := by
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · -- Cache hit: both return the recorded value, cache unchanged.
    rw [QueryImpl.withCaching_run_some uniformSampleImpl h]

omit [Fintype Salt] in
open Classical in
/-- **Universal off-bad per-query agreement of the two original-run flag handlers (the framework
`h_agree_good`).** For *every* query `t` and *every* off-bad input state `(s, false)`, the two flag
handlers `gpvRealImplFlag` / `progGameRunImplNoRecFlag` assign equal probability to every *off-bad
output* `(u, (s', false))`.

This is the exact `h_agree_good` hypothesis of the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad`. It is genuinely *universal* without any spurious
"empty-tape" bad state: the salt of each signing query is drawn *inline at the step*, so on a
signing query the off-bad output probability splits (over the inline salt `r`) into a sum whose
keyed-`r` summands vanish (the flag fires, so the `false`-flag output has probability `0` on both
sides) and whose unkeyed-`r` summands agree by the inline-salt signing-miss bridge
`evalSPMF_gpvImplFlag_run_sign_offbad_eq`. Non-signing queries reduce to the underlying
`gpvRealImpl` / `progGameRunImplNoRec` agreement (uniform: literally identical; random-oracle read:
cache hit identical, cache miss distributional by `hreg`).

It is *true-as-stated* and *pinned* to the concrete flag handlers (no free parameters). -/
theorem gpvImplFlag_h_agree_good (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache)
    (u : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t)
    (s' : (Salt × M →ₒ Range).QueryCache) :
    Pr[= (u, (s', false)) | (gpvRealImplFlag psf hr M Salt pk sk t).run (s, false)]
      = Pr[= (u, (s', false)) |
          (progGameRunImplNoRecFlag psf M Salt domainSample pk t).run (s, false)] := by
  cases t with
  | inl q =>
      -- Non-signing query: flag is passive (`F = false`), reduce to the underlying agreement.
      rw [gpvRealImplFlag_run_inl, progGameRunImplNoRecFlag_run_inl]
      rw [probOutput_flagTag_false, probOutput_flagTag_false, if_pos rfl, if_pos rfl]
      cases q with
      | inl n =>
          -- Uniform query: the two underlying handlers are literally identical.
          rw [gpvRealImpl_run_unif, progGameRunImplNoRec_run_unif]
      | inr mc =>
          -- Random-oracle read: agree by the underlying read agreement (hit/miss by `hreg`).
          exact probOutput_congr rfl
            (evalSPMF_gpvImpl_run_read_eq psf hr M Salt pk sk domainSample mc s hNF hreg)
  | inr msg =>
      -- Signing query: split over the inline salt `r`.  Keyed `r` ⇒ flag fires ⇒ both `0`;
      -- unkeyed `r` ⇒ flag stays `false` ⇒ bodies agree by the inline-salt signing-miss bridge.
      rw [gpvRealImplFlag_run_inr, progGameRunImplNoRecFlag_run_inr]
      simp only [Bool.false_or]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr (fun r => ?_)
      refine congrArg _ ?_
      rcases hkey : saltKeyed M Salt s r with _ | _
      · -- Unkeyed salt `r`: flag stays `false`; bodies agree.
        have hmiss : s (r, msg) = none := (saltKeyed_eq_false_iff M Salt s r).1 hkey msg
        exact probOutput_congr rfl
          (evalSPMF_gpvImplFlag_run_sign_offbad_eq psf M Salt pk sk domainSample
            msg r s hmiss hreg)
      · -- Keyed salt `r`: the flag fires (`true`); the `false`-flag output has probability `0`.
        rw [probOutput_eq_zero_of_not_mem_support, probOutput_eq_zero_of_not_mem_support]
        · -- Real side support: every output carries flag `true`.
          intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto
        · -- Programmed side support: every output carries flag `true`.
          intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto

omit [Fintype Salt] in
open Classical in
/-- **Original-run framework reduction of Step 1 to the run-level collision flag.** The
total-variation distance between the two *original* GPV game runs `realGameRun` / `progGameRun` is
bounded by the run-level collision-flag probability of the flag-instrumented real run
`gpvRealImplFlag`.

This is the direct application of the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` to the flag-instrumented original handlers
`gpvRealImplFlag` / `progGameRunImplNoRecFlag`, fed the universal off-bad per-query agreement
`gpvImplFlag_h_agree_good` and the bad-monotonicity `gpvRealImplFlag_bad_mono` /
`progGameRunImplNoRecFlag_bad_mono` (the `h_mono` hypotheses).  The run-level flag projection
`map_run_gpvRealImplFlag_eq` / `map_run_progGameRunImplNoRecFlag_eq` identifies the output
projection of the flagless original run with that of the flagged run, and
`realGameRun_eq_run'_implReal` / `progGameRun_eq_run'_implNoRec` pin those flagless output
projections to the actual game runs; the data-processing contraction `tvDist_map_le` then reduces
the framework total-variation bound to the original-run TV distance.

Unlike a reduction over a front-loaded salt tape (`TapeFactorization.lean`), there is **no upfront
salt tape**: each signing salt is drawn inline at its step, so the run-level flag probability
telescopes *directly* to the salt-averaged birthday term (no re-interleaving). -/
theorem gpv_tvDist_orig_run_le_probEvent_flag (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    SPMF.tvDist (realGameRun psf hr M Salt adv pk sk)
        (progGameRun psf hr M Salt adv domainSample pk)
      ≤ Pr[fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), false)].toReal := by
  -- Pin both game runs to the output projections of the flagless original runs.
  rw [realGameRun_eq_run'_implReal, progGameRun_eq_run'_implNoRec, StateT.run', StateT.run']
  -- Move to the `OracleComp.tvDist` form (`SPMF.tvDist 𝒮[·] 𝒮[·] = tvDist · ·`).
  change tvDist (Prod.fst <$> (simulateQ (gpvRealImpl psf hr M Salt pk sk) (adv.main pk)).run
        (∅ : (Salt × M →ₒ Range).QueryCache))
      (Prod.fst <$> (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (adv.main pk)).run
        (∅ : (Salt × M →ₒ Range).QueryCache)) ≤ _
  -- The output projection of each flagless run equals the doubly-projected flagged run.
  have hreal := map_run_gpvRealImplFlag_eq psf hr M Salt pk sk (adv.main pk)
    ((∅ : (Salt × M →ₒ Range).QueryCache), false)
  have hprog := map_run_progGameRunImplNoRecFlag_eq psf M Salt domainSample pk (adv.main pk)
    ((∅ : (Salt × M →ₒ Range).QueryCache), false)
  rw [show (Prod.fst <$> (simulateQ (gpvRealImpl psf hr M Salt pk sk) (adv.main pk)).run
          (∅ : (Salt × M →ₒ Range).QueryCache))
        = (fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.1) <$>
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), false) from by
      rw [← hreal, Functor.map_map]; rfl]
  rw [show (Prod.fst <$> (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk)
          (adv.main pk)).run (∅ : (Salt × M →ₒ Range).QueryCache))
        = (fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.1) <$>
          (simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), false) from by
      rw [← hprog, Functor.map_map]; rfl]
  -- Data-processing contraction then the framework identical-until-bad bound.
  refine le_trans (tvDist_map_le _ _ _) ?_
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (gpvRealImplFlag psf hr M Salt pk sk) (progGameRunImplNoRecFlag psf M Salt domainSample pk)
    (adv.main pk) (∅ : (Salt × M →ₒ Range).QueryCache)
    (gpvImplFlag_h_agree_good psf hr M Salt pk sk domainSample hNF hreg)
    (gpvRealImplFlag_bad_mono psf hr M Salt pk sk)
    (progGameRunImplNoRecFlag_bad_mono psf M Salt domainSample pk)

/-- **Finset of salts already keyed in the random-oracle cache.** The salts `r` for which some
random-oracle key `(r, m)` is already recorded (`saltKeyed`).  Its cardinality is the size of the
cache slice the inline signing salt is charged against in the `(A2)` telescope: a fresh uniform salt
lands in it with probability `card / |Salt|` (`probEvent_mem_uniformSample`). -/
noncomputable def keyedSalts (cache : (Salt × M →ₒ Range).QueryCache) : Finset Salt :=
  Finset.univ.filter (fun r : Salt => saltKeyed M Salt cache r)

omit [DecidableEq Range] [SampleableType Range] [SampleableType Salt] in
/-- **Cache-slice growth on one recorded random-oracle answer.** Recording a single random-oracle
entry `(r, msg) ↦ v` enlarges the keyed-salt slice by at most one element (the salt `r`): every
other salt's keyed status is unchanged, since `cacheQuery` only updates the key `(r, msg)`.  This is
the per-step cache-growth bound that drives the `(A2)` cardinality telescope (`card (cache j) ≤
j + qHash`). -/
lemma keyedSalts_cacheQuery_card_le (cache : (Salt × M →ₒ Range).QueryCache)
    (r : Salt) (msg : M) (v : Range) :
    (keyedSalts M Salt (cache.cacheQuery (r, msg) v)).card
      ≤ (keyedSalts M Salt cache).card + 1 := by
  classical
  refine le_trans (Finset.card_le_card ?_) (le_trans (Finset.card_insert_le r
    (keyedSalts M Salt cache)) (by rw [add_comm]))
  intro s hs
  simp only [keyedSalts, Finset.mem_filter, Finset.mem_univ, true_and, saltKeyed,
    decide_eq_true_eq] at hs
  obtain ⟨m, hm⟩ := hs
  simp only [Finset.mem_insert, keyedSalts, Finset.mem_filter, Finset.mem_univ, true_and,
    saltKeyed, decide_eq_true_eq]
  by_cases hsr : s = r
  · exact Or.inl hsr
  · refine Or.inr ⟨m, ?_⟩
    have hne : (s, m) ≠ (r, msg) := by
      simp only [ne_eq, Prod.mk.injEq, not_and]; intro h; exact absurd h hsr
    rwa [OracleSpec.QueryCache.cacheQuery_of_ne (cache := cache) (u := v) hne] at hm

omit [DecidableEq Range] [SampleableType Salt] in
/-- **Cache-slice growth through one lazy random-oracle read.** Any state `p` reachable from a
single lazy random-oracle step `(randomOracle mc).run cache` enlarges the keyed-salt slice by at
most one element: on a cache hit the cache is unchanged, and on a miss the new entry is recorded via
`cacheQuery`, which adds at most one keyed salt (`keyedSalts_cacheQuery_card_le`). -/
lemma keyedSalts_randomOracle_run_card_le (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache)
    (p : Range × (Salt × M →ₒ Range).QueryCache)
    (hp : p ∈ support ((randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache)) :
    (keyedSalts M Salt p.2).card ≤ (keyedSalts M Salt cache).card + 1 := by
  classical
  rcases hcache : cache mc with _ | u
  · rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache] at hp
    rw [support_map] at hp
    obtain ⟨v, -, rfl⟩ := hp
    exact keyedSalts_cacheQuery_card_le M Salt cache mc.1 mc.2 v
  · rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache] at hp
    rw [support_pure] at hp
    obtain rfl := hp
    exact Nat.le_succ _

open Classical in
/-- **(A2) cardinality-telescope auxiliary (general motive).**

The general-motive inductive core behind `gpv_orig_flag_le_collisionBound`: over an arbitrary
adversary computation `oa`, the run-level collision-flag probability of `gpvRealImplFlag` started
from a state `(cache, false)` is bounded by the running birthday sum `∑_{j < qS} (m + j) / |Salt|`,
provided `oa` makes at most `qS` signing and `qH` hash queries and the keyed-salt slice of the
starting cache satisfies `card (keyedSalts cache) + qH ≤ m`.

Proved by `OracleComp.inductionOn` over `oa`, generalizing the cache, the residual signing/hash
budgets, and the offset `m`.  At a signing step the fresh inline salt `r ← $ᵗ Salt` is drawn
*independently* of the running cache, so it lands in `keyedSalts cache` with probability
`card (keyedSalts cache) / |Salt| ≤ m / |Salt|` (`probEvent_mem_uniformSample`); on the
non-collision branch the cache slice grows by at most one (`keyedSalts_cacheQuery_card_le`), so the
continuation is bounded by the IH at offset `m + 1` and residual budget `qS - 1`, and the per-step
union recombines to the running sum.  Non-signing steps leave the flag untouched; a uniform step
leaves the cache unchanged and a read step grows the slice by at most one (absorbed by `qH`). -/
theorem gpv_orig_flag_le_collisionBound_aux [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (cache : (Salt × M →ₒ Range).QueryCache) (m qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      (keyedSalts M Salt cache).card + qH ≤ m →
      Pr[fun z : β × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, false)]
        ≤ ∑ j ∈ Finset.range qS, ((m + j : ℕ) : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro cache m qS qH _ _ _
      simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
      intro cache m qS qH hQS hQH hcard
      rw [simulateQ_query_bind, StateT.run_bind]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases t with (n | mc) | msg
      · -- uniform query: flag and cache untouched
        simp only [OracleQuery.input_query, monadLift_self,
          gpvRealImplFlag_run_inl, gpvRealImpl_run_unif, map_eq_bind_pure_comp, bind_assoc,
          Function.comp_apply, pure_bind]
        refine probEvent_bind_le_of_forall_le (fun x hx => ?_)
        exact ih _ cache m qS qH (by simpa using hQS2 _) (by simpa using hQH2 _) hcard
      · -- random-oracle read: flag untouched, cache slice grows ≤ 1
        have hqH : 0 < qH := by
          simpa using hQH1
        simp only [OracleQuery.input_query, monadLift_self,
          gpvRealImplFlag_run_inl, gpvRealImpl_run_read]
        rw [map_eq_bind_pure_comp, bind_assoc]
        refine probEvent_bind_le_of_forall_le (fun p hp => ?_)
        simp only [Function.comp_apply, pure_bind]
        have hbS := hQS2 p.1
        have hbH := hQH2 p.1
        simp only [Bool.false_eq_true, if_false, if_true] at hbS hbH
        have hcard' : (keyedSalts M Salt p.2).card + (qH - 1) ≤ m := by
          have hgrow := keyedSalts_randomOracle_run_card_le M Salt mc cache p hp
          omega
        exact ih p.1 p.2 m qS (qH - 1) hbS hbH hcard'
      · -- signing query: the inline salt is charged against the keyed-salt slice
        have hqS : 0 < qS := by simpa using hQS1
        simp only [OracleQuery.input_query, monadLift_self, gpvRealImplFlag_run_inr]
        -- Reassociate the inline salt draw to the front of the whole step + continuation.
        rw [bind_assoc]
        -- Split the running sum into the head charge `(m)/|Salt|` and the IH tail.
        rw [show qS = (qS - 1) + 1 from (Nat.succ_pred_eq_of_pos hqS).symm,
          Finset.sum_range_succ', add_comm]
        -- Phrase the collision event in the `¬ · = false` form expected by `probEvent_bind_le_add`.
        refine le_trans (le_of_eq (probEvent_congr'
          (q := fun z => ¬ z.2.2 = false) (oa' := _)
          (fun z _ => by cases h : z.2.2 <;> simp) rfl)) ?_
        -- Head charge: the fresh inline salt lands in `keyedSalts cache` w.p. `≤ m / |Salt|`.
        have hhead :
            Pr[fun r : Salt => ¬ (fun r : Salt => saltKeyed M Salt cache r = false) r |
                ($ᵗ Salt : ProbComp Salt)]
              ≤ ((m + 0 : ℕ) : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
          have hkey : (fun r : Salt => ¬ saltKeyed M Salt cache r = false)
              = (fun r : Salt => r ∈ keyedSalts M Salt cache) := by
            funext r
            simp only [keyedSalts, Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_false]
          rw [show (fun r : Salt => saltKeyed M Salt cache r = false → False)
              = (fun r : Salt => r ∈ keyedSalts M Salt cache) from hkey,
            probEvent_mem_uniformSample]
          gcongr
          exact_mod_cast hcard.trans' (Nat.le_add_right _ _)
        -- Off-collision tail: the continuation is bounded by the IH at offset `m + 1`.
        have htail : ∀ r ∈ support ($ᵗ Salt : ProbComp Salt),
            (fun r : Salt => saltKeyed M Salt cache r = false) r →
            Pr[fun z : β × ((Salt × M →ₒ Range).QueryCache × Bool) =>
                ¬ z.2.2 = false |
              (do
                let p ← (randomOracle (r, msg)).run cache
                let sgn ← psf.trapdoorSample pk sk p.1
                pure ((r, sgn), p.2, false || saltKeyed M Salt cache r)) >>=
              fun p_1 => (simulateQ (gpvRealImplFlag psf hr M Salt pk sk)
                (mx ((OracleSpec.query (Sum.inr msg)).cont p_1.1))).run p_1.2]
              ≤ ∑ j ∈ Finset.range (qS - 1),
                ((m + (j + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
          intro r _ hr
          -- Convert the event back to `z.2.2 = true` (cleaner for the IH).
          refine le_trans (le_of_eq (probEvent_congr' (q := fun z => z.2.2 = true) (oa' := _)
            (fun z _ => by cases h : z.2.2 <;> simp) rfl)) ?_
          -- Bound the continuation pointwise over the signing-step outputs.
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le (fun p hp => ?_)
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le (fun sgn _ => ?_)
          rw [pure_bind]
          -- On the off-collision branch the flag stays false; the cache `p.2` grew by ≤ 1.
          simp only [hr, Bool.or_false]
          have hbS := hQS2 (r, sgn)
          have hbH := hQH2 (r, sgn)
          simp only [if_true, Bool.false_eq_true, if_false] at hbS hbH
          refine le_trans (ih (r, sgn) p.2 (m + 1) (qS - 1) qH hbS hbH ?_)
            (le_of_eq (Finset.sum_congr rfl fun j _ => by
              rw [show m + 1 + j = m + (j + 1) from by omega]))
          -- Cache-growth invariant: `card (keyedSalts p.2) + qH ≤ m + 1`.
          have hgrow := keyedSalts_randomOracle_run_card_le M Salt (r, msg) cache p hp
          omega
        exact probEvent_bind_le_add hhead htail

open Classical in
/-- **(A2) Original-run cardinality telescope: the run-level collision flag of the inline-salt real
handler is bounded by `collisionBound`.**

The run-level collision-flag probability of the flag-instrumented *original* real run of
`adv.main pk` (started from the empty cache and an unset flag) is bounded by
`(collisionBound Salt qSign qHash).toReal`.

The flag fires when an inline-drawn signing salt `r ← $ᵗ Salt` lands on a key already recorded in
the running random-oracle cache.  Because the salt is drawn *at* its signing step (not pre-drawn
into an upfront tape), an `OracleComp.inductionOn` over `adv.main pk` threads the partial flag
probability `Pr[flag fired in the first j queries]` across the adaptive adversary; at the `j`-th
signing step the inline salt `r` is a fresh uniform `$ᵗ Salt` *independent of the running cache*
(it has not yet been
revealed at that point), so it lands on the cache slice with probability `card (cache j) / |Salt|`
(`probEvent_mem_uniformSample`), where `card (cache j) ≤ j + qHash` by the cache-growth invariant
(`hQ` bounds the adversary to `≤ qSign` signing salts and `≤ qHash` hash-query cache entries).
Summing
`∑_{j < qSign} (j + qHash) / |Salt| = (qSign + qHash)² / (2 |Salt|) = collisionBound`
(`sum_range_div_card_le_collisionBound`) gives the bound, mapping onto the
`probEvent_saltSeq_le_collisionBound` telescope — *without* the front-tape re-interleaving the
upfront-tape route required.

It is *true-as-stated* (counterexample-checked at `qSign = 0`: `hQ` permits no signing query, so the
flag — which only fires on a signing step — is never set, the flag probability is `0`, and
`0 ≤ (collisionBound …).toReal`) and *pinned* to the concrete flag handler `gpvRealImplFlag` and the
actual game-run vehicle `adv.main pk` (NOT free parameters).  It carries the run-level coupling
content; the off-collision per-query agreement it pairs with is `gpvImplFlag_h_agree_good`
(universal), and the reduction of Step 1's TV to this flag probability is
`gpv_tvDist_orig_run_le_probEvent_flag`. -/
theorem gpv_orig_flag_le_collisionBound [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false)].toReal
      ≤ (collisionBound Salt qSign qHash).toReal := by
  -- Instantiate the general-motive auxiliary at the empty cache, with `m := qHash`, charging each
  -- fresh inline signing salt against the running cache slice; then finish with the Gauss-sum
  -- estimate `sum_range_div_card_le_collisionBound`.
  obtain ⟨hQS, hQH⟩ := hQ
  have hempty : (keyedSalts M Salt (∅ : (Salt × M →ₒ Range).QueryCache)).card = 0 := by
    rw [Finset.card_eq_zero]
    refine Finset.filter_eq_empty_iff.2 (fun r _ => ?_)
    simp [saltKeyed]
  have haux := gpv_orig_flag_le_collisionBound_aux psf hr M Salt pk sk (adv.main pk)
    (∅ : (Salt × M →ₒ Range).QueryCache) qHash qSign qHash hQS hQH (by omega)
  have hbound : (probEvent ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
      ((∅ : (Salt × M →ₒ Range).QueryCache), false)) fun z => z.2.2 = true)
      ≤ collisionBound Salt qSign qHash := by
    refine haux.trans (le_trans (Finset.sum_le_sum fun j _ => ?_)
      (sum_range_div_card_le_collisionBound Salt qSign qHash))
    rw [Nat.add_comm qHash j]
  refine ENNReal.toReal_mono ?_ hbound
  unfold collisionBound
  exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])

omit [Fintype Salt] in
/-- **Flag-neutrality of a signing-free continuation (real flag handler).**
The collision flag of `gpvRealImplFlag` is set *only* on a signing step. Hence a computation `ob`
that issues **no** signing query (`ob.IsQueryBoundP (· matches .inr _) 0`) cannot move the flag: run
from `(cache, b)`, every output state still carries flag `b`.

Proved by `OracleComp.inductionOn` over `ob`: the `pure` case is immediate; a `.inl` (uniform /
random-oracle) step leaves the flag at `s.2 = b` (`gpvRealImplFlag_run_inl`) and the IH applies; a
`.inr` (signing) step is excluded because the query bound forbids it (`0 < 0` is false).

This is the key fact that keeps the verify-Bool lift on the *same* `collisionBound`: appending the
verification read (a signing-free `.inl` continuation) after `adv.main pk` adds no flag mass, so no
extra `qHash` budget is charged. -/
theorem gpvRealImplFlag_run_no_sign_flag_eq [Inhabited Range] (pk : PK) (sk : SK) :
    ∀ {γ : Type}
      (ob : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
      (cache : (Salt × M →ₒ Range).QueryCache) (b : Bool),
      ob.IsQueryBoundP (· matches .inr _) 0 →
      ∀ z ∈ support ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) ob).run (cache, b)),
        z.2.2 = b := by
  intro γ ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro cache b _ z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
  | query_bind t mx ih =>
      intro cache b hQ z hz
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ0, hQrec⟩ := hQ
      simp only [mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      rcases t with q | msg
      · -- non-signing step: the flag stays `s.2 = b`, then apply the IH.
        simp only [OracleQuery.input_query, monadLift_self, gpvRealImplFlag_run_inl] at hw
        simp only [support_map] at hw
        obtain ⟨v, _, hv⟩ := hw
        have hwb : w.2.2 = b := by rw [← hv]
        have hbS := hQrec w.1
        simp only [Bool.false_eq_true, if_false] at hbS
        have := ih w.1 w.2.1 w.2.2 hbS z hz
        rw [this, hwb]
      · -- signing step is excluded: `0 < 0` is false.
        simp only [or_false, lt_self_iff_false] at hQ0
        exact absurd trivial hQ0

omit [Fintype Salt] in
/-- **A signing-free continuation cannot increase the collision flag (real flag handler).**
Appending a signing-free continuation `kont` (each `kont x` makes no signing query, e.g. the GPV
verification read) after `oa` does not increase the run-level collision-flag probability of
`gpvRealImplFlag`: the flag fires only on signing steps, so by `gpvRealImplFlag_run_no_sign_flag_eq`
the final flag of the `kont`-run equals the flag at the end of `oa` on every support point (and the
`kont` run may only lose mass on failure).  This is the run-level statement of the off-by-one
resolution: the verification read carries no flag mass. -/
theorem probEvent_flag_bind_no_sign_le [Inhabited Range] (pk : PK) (sk : SK)
    {β γ : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (kont : β → OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (cache : (Salt × M →ₒ Range).QueryCache) (b : Bool)
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0) :
    Pr[fun z : γ × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (oa >>= kont)).run (cache, b)]
      ≤ Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] := by
  classical
  rw [simulateQ_bind, StateT.run_bind]
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun w => ?_
  -- Inner event probability is `≤ 1{w.2.2 = true}`: on every support point the flag equals `w.2.2`.
  have hinner :
      Pr[fun z : γ × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (kont w.1)).run w.2]
        ≤ (if w.2.2 = true then 1 else 0) := by
    by_cases hw : w.2.2 = true
    · rw [if_pos hw]; exact probEvent_le_one
    · rw [if_neg hw]
      refine le_of_eq (probEvent_eq_zero_iff.2 (fun z hz => ?_))
      obtain ⟨a, c', b'⟩ := w
      have := gpvRealImplFlag_run_no_sign_flag_eq psf hr M Salt pk sk (kont a) c' b'
        (hkont a) z hz
      simp only [this]
      simpa using hw
  calc Pr[= w | (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] *
        Pr[fun z : γ × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
            (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (kont w.1)).run w.2]
      ≤ Pr[= w | (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] *
          (if w.2.2 = true then 1 else 0) := by gcongr
    _ = (if w.2.2 = true then
          Pr[= w | (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)]
          else 0) := by
        by_cases hw : w.2.2 = true <;> simp [hw]

open Classical in
/-- **Verify-Bool coupling (fixed key pair).** Running the adversary `adv.main pk` followed by a
signing-free continuation `kont` (the verification read, kept *inside the shared random-oracle
cache*) on the two flag-instrumented original GPV handlers stays within `collisionBound`.

This is the genuine verify-Bool content of the lift: the framework identical-until-bad reduction
`tvDist_simulateQ_run_le_probEvent_output_bad` applies *verbatim* to the verify-extended computation
`adv.main pk >>= kont` (its conclusion keeps the final state, so the verification reads against the
shared cache), bounding the TV by the run-level collision flag.  Because `kont` issues no signing
query, the flag carries no extra mass (`probEvent_flag_bind_no_sign_le`), so the flag probability is
the *same* `collisionBound Salt qSign qHash` as for `adv.main pk` alone
(`gpv_orig_flag_le_collisionBound`) — no `qHash` off-by-one from the verification read. -/
theorem gpv_tvDist_orig_verify_le_collisionBound [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) {γ : Type}
    (kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    tvDist ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk >>= kont)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false))
        ((simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk)
            (adv.main pk >>= kont)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  -- Framework identical-until-bad on the verify-extended computation: the conclusion keeps the
  -- final cache, so `kont` reads against the shared random oracle.
  refine le_trans
    (OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (gpvRealImplFlag psf hr M Salt pk sk) (progGameRunImplNoRecFlag psf M Salt domainSample pk)
      (adv.main pk >>= kont) (∅ : (Salt × M →ₒ Range).QueryCache)
      (gpvImplFlag_h_agree_good psf hr M Salt pk sk domainSample hNF hreg)
      (gpvRealImplFlag_bad_mono psf hr M Salt pk sk)
      (progGameRunImplNoRecFlag_bad_mono psf M Salt domainSample pk)) ?_
  -- The verify-extended flag probability is ≤ the flag probability of `adv.main pk` alone
  -- (no signing query in `kont`), which the cardinality telescope bounds by `collisionBound`.
  refine ENNReal.toReal_mono ?_ ?_
  · unfold collisionBound
    exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
  · refine le_trans (probEvent_flag_bind_no_sign_le psf hr M Salt pk sk (adv.main pk) kont
      (∅ : (Salt × M →ₒ Range).QueryCache) false hkont) ?_
    have hreal := gpv_orig_flag_le_collisionBound psf hr M Salt pk sk adv qSign qHash hQ
    have hne : (collisionBound Salt qSign qHash) ≠ ⊤ := by
      unfold collisionBound
      exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
    exact (ENNReal.toReal_le_toReal probEvent_ne_top hne).mp hreal

/-! ### Freshness-tracking vehicle (the signed-set product factor)

The verify-Bool coupling `gpv_tvDist_orig_verify_le_collisionBound` runs the verification read
inside the shared random-oracle cache, but its vehicle state `QueryCache × Bool` carries no record
of which messages were sent to the *signing* oracle, so a freshness mask cannot be computed on it.
The EUF-CMA forgery winning condition requires the forged message to be *fresh* (never signed); a
replay of a received signature is not a forgery.

The handlers below carry the verify-Bool coupling over a *freshness-tracking* vehicle
with state `(QueryCache × Finset M) × Bool`: the random-oracle cache, a `Finset M` recording the
signed messages, and the salt-collision flag (the unchanged bad event). The signed-set is a
*passive product factor*: each signing step inserts the message identically on both the real and
the programmed handler, and every non-signing step leaves it untouched, so it agrees off-bad and
the flag/telescope are unaffected. The identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` is generic over the state, so the *same* salt-
collision bad event applies; projecting the signed-set away recovers the original flag run, so the
flag probability — and hence the `collisionBound` — is identical. The verification continuation may
then read the signed-set to apply the freshness mask. -/

omit [DecidableEq Range] [SampleableType Range] [DecidableEq Salt] [SampleableType Salt]
  [Fintype Salt] in
/-- **Flag-and-signed-set tag on a non-signing step output.** Tagging the output of a flagless
underlying step `m : ProbComp (α' × QueryCache)` with a *fixed* signed-set `sgnSet` and a flag `F`
gives the off-bad output probability: `0` if the flag fired, otherwise the signed-set must match
`sgnSet` and the probability reduces to the underlying step. This is the signed-set-carrying
analogue of `probOutput_flagTag_false`, used in the non-signing branch of the fresh
`h_agree_good`. -/
lemma probOutput_flagSignedTag_false {α' : Type}
    (m : ProbComp (α' × (Salt × M →ₒ Range).QueryCache)) (sgnSet sgnSet' : Finset M) (F : Bool)
    (u : α') (c' : (Salt × M →ₒ Range).QueryCache) :
    Pr[= (u, ((c', sgnSet'), false)) |
        ((fun p : α' × (Salt × M →ₒ Range).QueryCache => (p.1, ((p.2, sgnSet), F)))
          <$> m : ProbComp (α' × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
      = if F = false ∧ sgnSet' = sgnSet then Pr[= (u, c') | m] else 0 := by
  classical
  rw [probOutput_map_eq_tsum_ite]
  by_cases hF : F = false ∧ sgnSet' = sgnSet
  · obtain ⟨hF0, hFs⟩ := hF
    subst hF0; subst hFs
    rw [if_pos ⟨rfl, rfl⟩, ← tsum_ite_eq (u, c') (fun x => Pr[= x | m])]
    refine tsum_congr fun x => ?_
    congr 1
    rw [eq_iff_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h1, ⟨h2, _⟩, _⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, ⟨h2.symm, rfl⟩, rfl⟩
  · rw [if_neg hF, ENNReal.tsum_eq_zero]
    intro x
    rw [if_neg]
    rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
    rintro ⟨_, ⟨_, h3⟩, h4⟩
    exact hF ⟨h4.symm, h3⟩

open Classical in
/-- **Flag-instrumented freshness-tracking real handler.** `gpvRealImplFlag` extended with a passive
`Finset M` recording the signed messages. The state is `((QueryCache × Finset M) × Bool)`. Uniform
and random-oracle-read queries leave the signed-set and flag untouched; a signing query draws its
fresh inline salt `r ← $ᵗ Salt`, runs the underlying real signing body on the cache component,
*inserts the message* into the signed-set, and OR-s the collision flag with `saltKeyed`. Projecting
the signed-set away recovers `gpvRealImplFlag`. -/
@[expose] noncomputable def gpvRealImplFlagFresh (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
          (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), ((p.2, insert msg s.1.2), s.2 || saltKeyed M Salt s.1.1 r))

open Classical in
/-- **Flag-instrumented freshness-tracking programmed handler.** The programmed dual of
`gpvRealImplFlagFresh`: `progGameRunImplNoRecFlag` extended with the same passive signed-set,
inserting the message on each signing step. Projecting the signed-set away recovers
`progGameRunImplNoRecFlag`. -/
@[expose]
noncomputable def progGameRunImplNoRecFlagFresh (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
          (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn), ((s.1.1.cacheQuery (r, msg) (psf.eval pk sgn), insert msg s.1.2),
          s.2 || saltKeyed M Salt s.1.1 r))

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlagFresh` on a non-signing query.** -/
lemma gpvRealImplFlagFresh_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (gpvRealImplFlagFresh psf hr M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1.1 := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlagFresh` on a non-signing query.** -/
lemma progGameRunImplNoRecFlagFresh_run_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inl q)).run s =
      (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1.1 := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlagFresh` on a signing query.** -/
lemma gpvRealImplFlagFresh_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (gpvRealImplFlagFresh psf hr M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), ((p.2, insert msg s.1.2), s.2 || saltKeyed M Salt s.1.1 r))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlagFresh` on a signing query.** -/
lemma progGameRunImplNoRecFlagFresh_run_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (msg : M) (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn), ((s.1.1.cacheQuery (r, msg) (psf.eval pk sgn), insert msg s.1.2),
          s.2 || saltKeyed M Salt s.1.1 r))) := rfl

omit [Fintype Salt] in
/-- **Per-query signed-set projection of the real fresh flag handler.** Dropping the signed-set
component (`fun s => (s.1.1, s.2)`, keeping the cache and the flag) from one
`gpvRealImplFlagFresh` query step recovers the corresponding `gpvRealImplFlag` step. The signed-set
is a passive auxiliary: it is written by the signing step but never affects the output, the cache,
or the flag, so projecting it away yields the `gpvRealImplFlag` handler. This is the per-query
hypothesis of the state-projection transport `map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplFlagFresh_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2)) <$>
        (gpvRealImplFlagFresh psf hr M Salt pk sk t).run s =
      (gpvRealImplFlag psf hr M Salt pk sk t).run (s.1.1, s.2) := by
  cases t with
  | inl q =>
      rw [gpvRealImplFlagFresh_run_inl, gpvRealImplFlag_run_inl]
      simp only [Functor.map_map, Prod.map, id_eq]
  | inr msg =>
      rw [gpvRealImplFlagFresh_run_inr, gpvRealImplFlag_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query signed-set projection of the programmed fresh flag handler.** The programmed dual of
`gpvRealImplFlagFresh_proj`: dropping the signed-set recovers `progGameRunImplNoRecFlag`. -/
lemma progGameRunImplNoRecFlagFresh_proj (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2)) <$>
        (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run s =
      (progGameRunImplNoRecFlag psf M Salt domainSample pk t).run (s.1.1, s.2) := by
  cases t with
  | inl q =>
      rw [progGameRunImplNoRecFlagFresh_run_inl, progGameRunImplNoRecFlag_run_inl]
      simp only [Functor.map_map, Prod.map, id_eq]
  | inr msg =>
      rw [progGameRunImplNoRecFlagFresh_run_inr, progGameRunImplNoRecFlag_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **Run-level signed-set projection of the real fresh flag handler.** Dropping the signed-set from
the full simulated run of `gpvRealImplFlagFresh` over `oa` recovers the run of `gpvRealImplFlag`.
This transports the per-query projection `gpvRealImplFlagFresh_proj` through
the whole computation via `map_run_simulateQ_eq_of_query_map_eq`, witnessing that the signed-set is
a passive instrument: its addition changes neither the output, the cache, nor the flag. -/
lemma map_run_gpvRealImplFlagFresh_eq (pk : PK) (sk : SK)
    {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2)) <$>
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (s.1.1, s.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2))
    (gpvRealImplFlagFresh_proj psf hr M Salt pk sk) oa s

omit [Fintype Salt] in
/-- **Bad-monotonicity of the real fresh flag handler.** Once the collision flag is set
(`p.2 = true`), every output of one `gpvRealImplFlagFresh` query step also carries the flag set.
This is the `h_mono` hypothesis of `tvDist_simulateQ_run_le_probEvent_output_bad`. -/
lemma gpvRealImplFlagFresh_bad_mono (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((gpvRealImplFlagFresh psf hr M Salt pk sk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [gpvRealImplFlagFresh_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [gpvRealImplFlagFresh_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, c, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Bad-monotonicity of the programmed fresh flag handler.** -/
lemma progGameRunImplNoRecFlagFresh_bad_mono (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run p),
      z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [progGameRunImplNoRecFlagFresh_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [progGameRunImplNoRecFlagFresh_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Salt] in
/-- **Off-bad joint agreement of the two fresh-vehicle flag signing steps on a fresh inline salt.**
The signed-set-carrying analogue of `evalSPMF_gpvImplFlag_run_sign_offbad_eq`: with the inline salt
`r` fixed and not yet keyed (`cache (r, msg) = none`, so the flag stays `false`), the full
signing-step body outputs — including the *same* inserted signed-set `insert msg sgnSet` — coincide
in distribution. Both handlers apply the same deterministic post-processing inserting `msg` to the
two `(target, preimage)` draws that coincide by PSF regularity `hreg`. -/
theorem evalSPMF_gpvImplFlagFresh_run_sign_offbad_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt) (sgnSet : Finset M)
    (cache : (Salt × M →ₒ Range).QueryCache) (hmiss : cache (r, msg) = none)
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒮[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        let sgn ← psf.trapdoorSample pk sk p.1
        pure (((r, sgn), ((p.2, insert msg sgnSet), false)) :
          (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
      = 𝒮[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn),
            ((cache.cacheQuery (r, msg) (psf.eval pk sgn), insert msg sgnSet), false)) :
            (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))] := by
  classical
  -- Reuse the flagless-signed-set signing-miss bridge by post-composing the signed-set insertion.
  set g : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool) →
      (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :=
    fun z => (z.1, ((z.2.1, insert msg sgnSet), z.2.2)) with hg
  have hbase := evalSPMF_gpvImplFlag_run_sign_offbad_eq psf M Salt pk sk domainSample
    msg r cache hmiss hreg
  have hL :
      𝒮[(do
          let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
          let sgn ← psf.trapdoorSample pk sk p.1
          pure (((r, sgn), ((p.2, insert msg sgnSet), false)) :
            (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
        = 𝒮[g <$> (do
            let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
            let sgn ← psf.trapdoorSample pk sk p.1
            pure (((r, sgn), (p.2, false)) :
              (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))] := by
    simp only [hg, map_bind, map_pure]
  have hR :
      𝒮[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn),
            ((cache.cacheQuery (r, msg) (psf.eval pk sgn), insert msg sgnSet), false)) :
            (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
        = 𝒮[g <$> (do
            let sgn ← (domainSample pk : ProbComp Domain)
            pure (((r, sgn), (cache.cacheQuery (r, msg) (psf.eval pk sgn), false)) :
              (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))] := by
    simp only [hg, map_bind, map_pure]
  rw [hL, hR]
  exact evalSPMF_map_eq_of_evalSPMF_eq hbase g

omit [Fintype Salt] in
open Classical in
/-- **Universal off-bad per-query agreement of the two fresh-vehicle flag handlers (the framework
`h_agree_good`).** For every query `t` and every off-bad input state `(s, false)` (with
`s : QueryCache × Finset M`), the two fresh flag handlers assign equal probability to every off-bad
output `(u, (s', false))`. This is the signed-set-carrying analogue of `gpvImplFlag_h_agree_good`:
the signed-set is inserted identically on both sides at a signing step and untouched elsewhere, so
that agreement carries over verbatim, with the signing-miss bridge supplied by
`evalSPMF_gpvImplFlagFresh_run_sign_offbad_eq`. -/
theorem gpvImplFlagFresh_h_agree_good (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Finset M)
    (u : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t)
    (s' : (Salt × M →ₒ Range).QueryCache × Finset M) :
    Pr[= (u, (s', false)) | (gpvRealImplFlagFresh psf hr M Salt pk sk t).run (s, false)]
      = Pr[= (u, (s', false)) |
          (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run (s, false)] := by
  cases t with
  | inl q =>
      -- Non-signing query: signed-set and flag are passive; reduce to the underlying agreement.
      rw [gpvRealImplFlagFresh_run_inl, progGameRunImplNoRecFlagFresh_run_inl]
      obtain ⟨c', sgnSet'⟩ := s'
      rw [probOutput_flagSignedTag_false, probOutput_flagSignedTag_false]
      by_cases hsig : sgnSet' = s.2
      · simp only [hsig, and_self, if_pos]
        cases q with
        | inl n =>
            -- Uniform query: the two underlying handlers are literally identical.
            rw [gpvRealImpl_run_unif, progGameRunImplNoRec_run_unif]
        | inr mc =>
            -- Random-oracle read: agree by the underlying read agreement.
            exact probOutput_congr rfl
              (evalSPMF_gpvImpl_run_read_eq psf hr M Salt pk sk domainSample mc s.1 hNF hreg)
      · simp only [hsig, and_false, if_false]
  | inr msg =>
      -- Signing query: split over the inline salt `r`; keyed `r` ⇒ flag fires ⇒ both `0`;
      -- unkeyed `r` ⇒ flag stays `false`, signed-set inserts `msg`, bodies agree.
      rw [gpvRealImplFlagFresh_run_inr, progGameRunImplNoRecFlagFresh_run_inr]
      simp only [Bool.false_or]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr (fun r => ?_)
      refine congrArg _ ?_
      rcases hkey : saltKeyed M Salt s.1 r with _ | _
      · -- Unkeyed salt `r`: flag stays `false`; bodies agree (signed-set inserts `msg` on both).
        have hmiss : s.1 (r, msg) = none := (saltKeyed_eq_false_iff M Salt s.1 r).1 hkey msg
        exact probOutput_congr rfl
          (evalSPMF_gpvImplFlagFresh_run_sign_offbad_eq psf M Salt pk sk domainSample
            msg r s.2 s.1 hmiss hreg)
      · -- Keyed salt `r`: the flag fires (`true`); the `false`-flag output has probability `0`.
        rw [probOutput_eq_zero_of_not_mem_support, probOutput_eq_zero_of_not_mem_support]
        · intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto
        · intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto

omit [Fintype Salt] in
/-- **Flag-probability projection of the fresh vehicle.** The run-level collision-flag probability
of the fresh handler `gpvRealImplFlagFresh` equals that of the handler `gpvRealImplFlag`:
the signed-set is passive, so projecting it away (`map_run_gpvRealImplFlagFresh_eq`) preserves the
flag (which lives in the retained `Bool` component). This is the bridge that lets the
cardinality telescope `gpv_orig_flag_le_collisionBound` bound the fresh flag at the *same*
`collisionBound`. -/
lemma probEvent_flag_gpvRealImplFlagFresh_eq (pk : PK) (sk : SK)
    {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (cache : (Salt × M →ₒ Range).QueryCache) (sgnSet : Finset M) (b : Bool) :
    Pr[fun z : β × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run ((cache, sgnSet), b)]
      = Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] := by
  have hmap := map_run_gpvRealImplFlagFresh_eq psf hr M Salt pk sk oa ((cache, sgnSet), b)
  calc Pr[fun z : β × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run ((cache, sgnSet), b)]
      = Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
          (Prod.map id
            (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2))) <$>
            (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run
              ((cache, sgnSet), b)] := by
        rw [probEvent_map]; rfl
    _ = Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] := by
        rw [hmap]

open Classical in
/-- **Verify-Bool coupling on the freshness-tracking vehicle (fixed key pair).** Running the
adversary `adv.main pk` followed by a signing-free continuation `kont` (the verification read, kept
*inside the shared random-oracle cache* and now able to read the signed-set for the freshness mask)
on the two *fresh* flag-instrumented GPV handlers stays within `collisionBound`.

This re-derives `gpv_tvDist_orig_verify_le_collisionBound` over the freshness-tracking vehicle
`gpvRealImplFlagFresh` / `progGameRunImplNoRecFlagFresh` (state `(QueryCache × Finset M) × Bool`):
the framework identical-until-bad reduction `tvDist_simulateQ_run_le_probEvent_output_bad` applies
*verbatim* to the verify-extended computation `adv.main pk >>= kont` (its conclusion keeps the final
state, so the verification reads against the shared cache *and* the shared signed-set), bounding the
TV by the run-level collision flag.  Because `kont` issues no signing query, the flag carries no
extra mass; projecting the passive signed-set away (`probEvent_flag_gpvRealImplFlagFresh_eq`)
reduces the fresh flag probability to the `gpvRealImplFlag` flag probability, bounded by the *same*
`collisionBound Salt qSign qHash` via `probEvent_flag_bind_no_sign_le` and
`gpv_orig_flag_le_collisionBound` — no `qHash` off-by-one from the verification read.

Unlike the frozen `gpv_tvDist_orig_verify_le_collisionBound`, the vehicle now carries the signed-set
factor, so `kont` may compute the EUF-CMA freshness mask (the forged message not being among the
signed messages) while staying within the same collision bound. -/
theorem gpv_tvDist_orig_verify_fresh_le_collisionBound [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) {γ : Type}
    (kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    tvDist ((simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) (adv.main pk >>= kont)).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false))
        ((simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
            (adv.main pk >>= kont)).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  -- Framework identical-until-bad on the verify-extended computation over the fresh vehicle.
  refine le_trans
    (OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (gpvRealImplFlagFresh psf hr M Salt pk sk)
      (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
      (adv.main pk >>= kont) ((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M))
      (gpvImplFlagFresh_h_agree_good psf hr M Salt pk sk domainSample hNF hreg)
      (gpvRealImplFlagFresh_bad_mono psf hr M Salt pk sk)
      (progGameRunImplNoRecFlagFresh_bad_mono psf M Salt domainSample pk)) ?_
  -- Project the passive signed-set away, reducing the fresh flag to the `gpvRealImplFlag` flag,
  -- then bound the verify-extended flag by `collisionBound` (signing-free `kont` adds no flag).
  refine ENNReal.toReal_mono ?_ ?_
  · unfold collisionBound
    exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
  · rw [probEvent_flag_gpvRealImplFlagFresh_eq psf hr M Salt pk sk (adv.main pk >>= kont)
      (∅ : (Salt × M →ₒ Range).QueryCache) (∅ : Finset M) false]
    refine le_trans (probEvent_flag_bind_no_sign_le psf hr M Salt pk sk (adv.main pk) kont
      (∅ : (Salt × M →ₒ Range).QueryCache) false hkont) ?_
    have hreal := gpv_orig_flag_le_collisionBound psf hr M Salt pk sk adv qSign qHash hQ
    have hne : (collisionBound Salt qSign qHash) ≠ ⊤ := by
      unfold collisionBound
      exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
    exact (ENNReal.toReal_le_toReal probEvent_ne_top hne).mp hreal

open Classical in
/-- **Flag-free freshness-tracking real handler.** `gpvRealImplFlagFresh` with the passive
salt-collision `Bool` flag removed, leaving the state `(QueryCache × Finset M)`. The signing step
draws its fresh inline salt, runs the real signing body on the cache, and inserts the message into
the signed-set; non-signing queries leave the signed-set untouched. Projecting the flag away from
`gpvRealImplFlagFresh` recovers this handler.  Because the winning Bool of the freshness verify
games (`decide (msg ∉ signedSet) && verified`) never reads the flag, the flag-free vehicle carries
exactly the information the game observes. -/
@[expose] noncomputable def gpvRealImplFresh (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × Finset M) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$>
          (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, insert msg s.2))

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFresh` on a non-signing query.** -/
lemma gpvRealImplFresh_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Finset M) :
    (gpvRealImplFresh psf hr M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1 := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFresh` on a signing query.** -/
lemma gpvRealImplFresh_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × Finset M) :
    (gpvRealImplFresh psf hr M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, insert msg s.2))) := rfl

omit [Fintype Salt] in
/-- **Per-query flag projection of the fresh flag handler.** Dropping the passive collision flag
(`Prod.map id Prod.fst`, keeping the cache and the signed-set) from one `gpvRealImplFlagFresh` query
step recovers the corresponding `gpvRealImplFresh` step. The flag is written by the signing step but
never affects the output, the cache, or the signed-set, so projecting it away yields the flag-free
fresh handler. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplFlagFresh_proj_flag (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool →
        (Salt × M →ₒ Range).QueryCache × Finset M) <$>
        (gpvRealImplFlagFresh psf hr M Salt pk sk t).run s =
      (gpvRealImplFresh psf hr M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      rw [gpvRealImplFlagFresh_run_inl, gpvRealImplFresh_run_inl]
      simp only [Functor.map_map, Prod.map, id_eq]
  | inr msg =>
      rw [gpvRealImplFlagFresh_run_inr, gpvRealImplFresh_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **Run-level flag projection of the fresh flag handler.** Dropping the collision flag from the
full simulated run of `gpvRealImplFlagFresh` over `oa` recovers the run of the flag-free handler
`gpvRealImplFresh`. Transports the per-query `gpvRealImplFlagFresh_proj_flag` through the whole
computation via `map_run_simulateQ_eq_of_query_map_eq`: the flag is a passive instrument. -/
lemma map_run_gpvRealImplFlagFresh_proj_flag (pk : PK) (sk : SK) {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool →
        (Salt × M →ₒ Range).QueryCache × Finset M) <$>
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImplFresh psf hr M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool →
      (Salt × M →ₒ Range).QueryCache × Finset M)
    (gpvRealImplFlagFresh_proj_flag psf hr M Salt pk sk) oa s

end GPVHashAndSign
