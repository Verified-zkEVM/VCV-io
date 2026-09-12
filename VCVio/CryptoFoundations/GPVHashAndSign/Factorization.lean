/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.CollisionTelescope

/-! # GPV Hash-and-Sign: The Adaptive-to-signRunF Factorization

The factorization of the adaptive game runs through the fixed signing-step
recursion, and the concrete GPV per-step answer handlers witnessing it.
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

/-! ## Adaptive→`signRunF` factorization

The unconditional salt-inclusive U2 `signRunF_tvDist_le_collisionBound` (above) bounds the real and
programmed *salt-inclusive signing runs* — phrased over the fixed `qSign`-step recursion `signRunF`.
To consume it in the four GPV theorems, whose advantage is over the **adaptive** real game run
`simulateQ impl (adv.main pk)` (`SignatureAlg.unforgeableExp`), one must match that adaptive run to
the fixed `signRunF` recursion. That match is the **adaptive→`signRunF` factorization**:
the adversary interleaves its `≤ qSign` signing queries (each drawing one fresh salt `r ← $ᵗ Salt`)
with `≤ qHash` random-oracle queries *adaptively*, while `signRunF` draws its `qSign` salts in a
fixed front sequence. Front-loading the interleaved salt draws past the adaptive adversary fold is a
deferred-sampling joint coupling, structurally identical to the Fiat–Shamir-with-abort
*fold-level tape factorization*
`FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` (each signing body's inline
draws are recast as consumption from a pre-drawn front tape, proved by induction over the
`simulateQ` fold using `OracleComp.DeferredSampling.evalSPMF_step_commute_tape` for the
answer-irrelevant — here, the adversary hash/uniform — steps and a per-body splice for the drawing
steps).

This section establishes the off-collision branch agreement and packages the factorization as a
typed predicate.

* `regularity_signAnswer_agree` discharges the abstract coupling's off-collision branch-agreement
  hypothesis (`h_step`) for the concrete GPV signing answer: under PSF regularity the *real*
  RO-cache-miss answer `(c, s)` (fresh uniform target `c ← $ᵗ Range`, then
  `s ← trapdoorSample pk sk c`) and the *programmed* answer (`s ← domainSample pk`, target
  `eval pk s`) are equal in distribution. This is the regularity equation transposed and is the
  per-step content the off-collision case of `signRunF_tvDist_le_saltSeq_aux` consumes.

* `AdaptiveFactorizesSignRunF` is the typed predicate packaging the factorization — that the
  adaptive real and programmed game runs are distributed as the corresponding `signRunF` runs over a
  common per-query cache sequence `c` with `card (c j) ≤ j + qHash`. It is a `Prop` (a typed
  obligation, in the style of `hcouple`), naming the deferred-sampling content as a single target.
  `factorized_advantage_le_collisionBound` shows that supplying it discharges the salt-inclusive U2
  against the adaptive game run via the unconditional `signRunF_tvDist_le_collisionBound`. -/

omit [DecidableEq Range] in
/-- **Regularity branch-agreement bridge.** Under PSF regularity, the real cache-miss
signing answer and the programmed signing answer agree in distribution.

The real answer at a fresh salt — produced by the lazy random oracle on a cache miss — draws a fresh
uniform target `c ← $ᵗ Range` and then a short preimage `s ← trapdoorSample pk sk c`, returning the
pair `(c, s)`. The programmed answer draws `s ← domainSample pk` and uses the target `eval pk s`,
returning `(eval pk s, s)`. PSF regularity (`psf.Regularity`) states exactly that these two joint
distributions coincide, so this is the regularity equation read right-to-left.

This is the GPV-concrete witness for the off-collision branch-agreement hypothesis `h_step` of
`signRunF_tvDist_le_saltSeq` / `signRunF_tvDist_le_collisionBound`: off the per-step salt collision
`r ∉ c j`, the real and programmed per-signing-step answer handlers agree in distribution. -/
theorem regularity_signAnswer_agree (hreg : psf.Regularity) (pk : PK) (sk : SK) :
    ∃ domainSample : PK → ProbComp Domain,
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
          : ProbComp (Range × Domain))]
        = 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨domainSample, (h pk sk).symm⟩

/-- **Adaptive→`signRunF` factorization predicate.**

`AdaptiveFactorizesSignRunF realRun progRun` asserts the existence of a `signRunF` presentation of
the adaptive real and programmed game runs sharing a common per-signing-query cache sequence: there
exist a handler-state type `St`, real/programmed per-step answer handlers `stepReal`/`stepProg` (the
latter agreeing with the former off the per-step salt collision, `stepReal` never failing), a
per-query recorded-cache sequence `c` bounded by `card (c j) ≤ j + qHash`, and a start state such
that the real and programmed adaptive runs equal (in distribution) the corresponding
`signRunF stepReal c qSign` / `signRunF stepProg c qSign` runs.

This is the content the deferred-sampling fold-level coupling establishes (cf.
`FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`): front-load the
adaptively-interleaved fresh salt draws of `realRun`/`progRun` into the fixed `qSign`-step
`signRunF` sequence. It is a typed predicate naming the factorization as a single target;
`factorized_advantage_le_collisionBound` shows it suffices. -/
def AdaptiveFactorizesSignRunF [Nonempty Salt] {α : Type}
    (realRun progRun : SPMF α) (qSign qHash : ℕ) : Prop :=
  ∃ (St : Type) (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) (st : St) (g : St × Bool → ProbComp α),
    (∀ n s r, NeverFail (stepReal n s r)) ∧
    (∀ n s r, r ∉ c n → 𝒮[stepReal n s r] = 𝒮[stepProg n s r]) ∧
    (∀ j, (c j).card ≤ j + qHash) ∧
    realRun = 𝒮[signRunF (Salt := Salt) stepReal c qSign (st, false) >>= g] ∧
    progRun = 𝒮[signRunF (Salt := Salt) stepProg c qSign (st, false) >>= g]

/-- **The factorization predicate suffices.** Supplying the adaptive→`signRunF` factorization
predicate `AdaptiveFactorizesSignRunF` discharges the salt-inclusive U2 against the adaptive game
runs: the total-variation distance between the real and programmed game runs is bounded by
`collisionBound Salt qSign qHash`.

The proof factors the runs through the predicate's `signRunF` presentation, applies the
data-processing inequality `tvDist_bind_right_le` to drop the shared post-processing `g`, and closes
with the unconditional salt-inclusive U2 `signRunF_tvDist_le_collisionBound`. Once the
deferred-sampling fold-level coupling establishes `AdaptiveFactorizesSignRunF`, the four GPV
theorems' sign-then-hash hop follows with no further probability content. -/
theorem factorized_advantage_le_collisionBound [Finite Salt] [Nonempty Salt] {α : Type}
    (realRun progRun : SPMF α) (qSign qHash : ℕ)
    (hfac : AdaptiveFactorizesSignRunF (Salt := Salt) realRun progRun qSign qHash) :
    SPMF.tvDist realRun progRun ≤ (collisionBound Salt qSign qHash).toReal := by
  obtain ⟨St, stepReal, stepProg, c, st, g, hNF, hstep, hcache, hreal, hprog⟩ := hfac
  subst hreal hprog
  refine le_trans (tvDist_bind_right_le g _ _) ?_
  have : ∀ n s r, NeverFail (stepReal n s r) := hNF
  exact signRunF_tvDist_le_collisionBound (Salt := Salt) (St := St)
    stepReal stepProg c hstep qSign qHash hcache st

/-! ## Concrete GPV `signRunF` handlers

The predicate `AdaptiveFactorizesSignRunF` is an existential over a handler-state type `St`,
real/programmed per-step handlers, a recorded-cache sequence `c`, a start state, and a shared
post-processor `g`. This section pins the GPV-concrete witnesses for the handler-state and step
handlers, and proves the two *structural* conjuncts of the predicate against them — the `NeverFail`
of the real step and the off-collision branch agreement under regularity. The two run-equalities
`realRun = 𝒮[signRunF stepReal c qSign …]` / `progRun = 𝒮[signRunF stepProg c qSign …]` together
with the cache-growth bound on the *adaptive* run's recorded slices would be the front-loading fold
factorization; that factorization is not established here, and the Step-1 bound
`gpv_tvDist_real_programmed_le_collisionBound` is instead proved by the original-run route
(`gpv_tvDist_orig_run_le_probEvent_flag`, `gpv_orig_flag_le_collisionBound`). The per-body
splices below are the signing-step ingredients the fold factorization would consume.

The handler state is the lazy random-oracle cache `(Salt × M →ₒ Range).QueryCache`; both step
handlers update it at the freshly drawn salt `r` and the `n`-th signing message `msgs n`. The
`stepReal` handler mirrors the real signing oracle's *cache-miss* branch: draw a uniform target
`c ← $ᵗ Range`, draw the trapdoor preimage, and cache `c`. The `stepProg` handler mirrors the
sign-then-hash simulator: forward-sample a short preimage `s ← domainSample pk` and program the
cache entry to `psf.eval pk s`. -/

open Classical in
/-- **Real GPV signing step (cache-miss branch).** At signing step `n` with random-oracle cache
`cache` and freshly drawn salt `r`, draw a uniform target `c ← $ᵗ Range`, draw a trapdoor preimage
of `c`, and record `(r, msgs n) ↦ c` in the cache. This is the per-step handler used as `stepReal`
in the GPV `signRunF` presentation of the real game run. -/
noncomputable def gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let c ← ($ᵗ Range)
    let _s ← psf.trapdoorSample pk sk c
    pure (cache.cacheQuery (r, msgs n) c)

open Classical in
/-- **Programmed GPV signing step (sign-then-hash branch).** At signing step `n` with random-oracle
cache `cache` and freshly drawn salt `r`, forward-sample a short preimage `s ← domainSample pk` and
record `(r, msgs n) ↦ psf.eval pk s` in the cache. This is the per-step handler used as `stepProg`
in the GPV `signRunF` presentation of the programmed (simulator) run. -/
@[expose]
noncomputable def gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let s ← domainSample pk
    pure (cache.cacheQuery (r, msgs n) (psf.eval pk s))

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV step never fails.** Given that the trapdoor sampler never fails (a mild
side-condition satisfied by any total preimage sampler — e.g. Falcon's `ffSampling` loop, which
always returns), the real per-step handler `gpvStepReal` never fails: the uniform target draw is
total, the trapdoor draw is total by hypothesis, and the final cache update is a `pure`. This
discharges the `NeverFail (stepReal n s r)` conjunct of the obligation against the concrete
`stepReal := gpvStepReal`. -/
theorem gpvStepReal_neverFail (pk : PK) (sk : SK) (msgs : ℕ → M)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    NeverFail (gpvStepReal psf M Salt pk sk msgs n cache r) := by
  unfold gpvStepReal
  rw [neverFail_bind_iff]
  refine ⟨inferInstance, fun c _ => ?_⟩
  rw [neverFail_bind_iff]
  exact ⟨hNF c, fun _ _ => inferInstance⟩

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real/programmed GPV step distributional agreement.** Under PSF regularity (witnessed by the
forward sampler `domainSample` of `psf.Regularity`), the real and programmed per-step handlers agree
as output distributions at every step `n`, cache, and salt `r`.

Both handlers update the same cache slot `(r, msgs n)` with the first component of a `(target,
preimage)` pair; the real handler draws that pair as `(c, s)` with `c ← $ᵗ Range`, `s ←
trapdoorSample pk sk c`, while the programmed handler draws it as `(eval pk s, s)` with `s ←
domainSample pk`. PSF regularity equates exactly these two joint distributions, so projecting onto
the cache update preserves the equality. This agreement is in fact *unconditional* in `r` (it does
not require `r ∉ c n`), which is stronger than the obligation's off-collision conjunct demands. -/
theorem gpvStep_agree (pk : PK) (sk : SK) (msgs : ℕ → M)
    (domainSample : PK → ProbComp Domain)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    𝒮[gpvStepReal psf M Salt pk sk msgs n cache r]
      = 𝒮[gpvStepProg psf M Salt pk domainSample msgs n cache r] := by
  unfold gpvStepReal gpvStepProg
  set proj : Range × Domain → (Salt × M →ₒ Range).QueryCache :=
    fun cs => cache.cacheQuery (r, msgs n) cs.1 with hproj
  have hR : (($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => (pure (cache.cacheQuery (r, msgs n) c) : ProbComp _))
        = ((($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>= fun s => pure (c, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  have hP : (domainSample pk >>=
              fun s => (pure (cache.cacheQuery (r, msgs n) (psf.eval pk s)) : ProbComp _))
        = ((domainSample pk >>= fun s => pure (psf.eval pk s, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  change 𝒮[(($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => pure (cache.cacheQuery (r, msgs n) c))] = _
  rw [hR, hP]
  simp only [evalSPMF_bind, hreg]

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV signing-body cache splice (cache-miss key).** One real signing-query body, run
through the lazy random oracle at a *missing* cache key `(r, msgs n)`, produces a recorded-cache
transition distributed exactly as the concrete `signRunF` real step `gpvStepReal` at the (already
fixed) salt `r`.

The signing body queries the random oracle at `(r, msgs n)`; on the cache miss `cache (r, msgs n) =
none` the oracle draws a fresh uniform target `u ← $ᵗ Range`, records `(r, msgs n) ↦ u`, and returns
`u`; the body then draws the trapdoor preimage and yields the updated cache. The handler
`gpvStepReal` draws the same uniform target `c ← $ᵗ Range`, the same trapdoor preimage, and records
`(r, msgs n) ↦ c` — so the two recorded-cache distributions coincide. This is the *per-body splice*
of the adaptive→`signRunF` fold factorization (the signing-step case of the real run-equality
`realRun = 𝒮[signRunF gpvStepReal c qSign …]`): it recasts one inline signing-oracle body, on a
fresh-salt cache miss, as the concrete `signRunF` real step, with the fresh salt `r` front-loaded
out of the body. It is *pinned* to the concrete `randomOracle` and `gpvStepReal`, requires only the
cache-miss side condition `hmiss` (guaranteed for a fresh salt), and is unconditional otherwise. -/
theorem evalSPMF_gpvSignBody_run_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt)
    (hmiss : cache (r, msgs n) = none) :
    𝒮[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        let _s ← psf.trapdoorSample pk sk p.1
        pure p.2 : ProbComp ((Salt × M →ₒ Range).QueryCache))]
      = 𝒮[gpvStepReal psf M Salt pk sk msgs n cache r] := by
  unfold gpvStepReal
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        = (fun u => (u, cache.cacheQuery (r, msgs n) u)) <$>
            (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  rw [show (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
        = ($ᵗ Range : ProbComp Range) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Programmed GPV signing-body cache splice (simulator signing query).** One programmed
simulator signing-query body — the `signImpl` handler of `progGameRun`, which draws a fresh salt
`r ← $ᵗ Salt`, forward-samples a short preimage `s ← domainSample pk`, programs the random-oracle
cache entry `(r, msg) ↦ psf.eval pk s`, updates the preimage record, and returns `(r, s)` — has its
recorded random-oracle *cache component* (with the salt draw front-loaded, and the returned
signature and the auxiliary preimage record dropped) distributed exactly as the salt-prefixed
concrete `signRunF` programmed step: draw the same fresh salt `r ← $ᵗ Salt`, then apply
`gpvStepProg` at that `r`.

This is the programmed-side dual of `evalSPMF_gpvSignBody_run_eq_gpvStepReal`, and the signing-step
case of the *programmed* run-equality
`progGameRun … = 𝒮[signRunF gpvStepProg c qSign …]` of the fold
factorization. It is *pinned* to the concrete `progGameRun` signing body
and the concrete `gpvStepProg`: the cache transition
`cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)`
on both sides is the same, the salt draw is the same front-loaded `$ᵗ Salt`, and `domainSample` is
the shared programming randomness. No probability-mass averaging is performed; the equality is the
exact recasting of one inline simulator signing body — with its salt front-loaded — as one
`signRunF` programmed step. The auxiliary preimage record `((Salt × M) → Option Domain)` of
`progGameRun`'s state, which `gpvStepProg` does not carry, is dropped here (it is
collision-extraction bookkeeping, irrelevant to the random-oracle cache distribution that the
sign-then-hash hop compares; it is reattached at the run level, not the per-step level). -/
theorem evalSPMF_gpvSignBody_run_eq_gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain)
    (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (pre : (Salt × M) → Option Domain) :
    𝒮[(do
        -- The actual `progGameRun` simulator signing body (`signImpl`), with the fresh salt draw
        -- front-loaded, run on state `(cache, pre)`; project out the random-oracle cache component
        -- (dropping the returned signature and the auxiliary preimage record).
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← ((do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            let st ← get
            set ((st.1.cacheQuery (r, msgs n) v,
              fun t' => if t' = (r, msgs n) then some s else st.2 t')
                : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
            pure (r, s) :
              StateT ((Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
                ProbComp (Salt × Domain)).run (cache, pre))
        pure p.2.1 : ProbComp ((Salt × M →ₒ Range).QueryCache))]
      = 𝒮[(do
          let r ← ($ᵗ Salt : ProbComp Salt)
          gpvStepProg psf M Salt pk domainSample msgs n cache r
            : ProbComp ((Salt × M →ₒ Range).QueryCache))] := by
  unfold gpvStepProg
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    StateT.run_map, bind_pure_comp, map_pure, Functor.map_map, monadLift_self]

end GPVHashAndSign
