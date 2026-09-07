/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.Factorization

/-! # GPV Hash-and-Sign: Game Runs and Tape Handlers

Front-loading the adaptive salt draws: the pinned GPV game runs, collapsing the
runtime indirection, dropping the preimage-record component, the tape-consuming
implementations, the flag-instrumented tape handlers carrying the
identical-until-bad collision flag, and the per-query tape-to-unified bridges.
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

/-! ## Front-loading the adaptive salt draws into `signRunF`

The remaining content of `AdaptiveFactorizesSignRunF` against the concrete handlers above is the
pair of run-equalities together with the cache-growth bound on the recorded slices. These facts are
*not* structural: they assert that the adaptive real / programmed game runs
`simulateQ impl (adv.main pk)` (where each signing query draws a fresh salt at an
adversary-chosen point and queries the random oracle at it) factor through the *fixed* `qSign`-step
`signRunF` recursion with the concrete `gpvStepReal` / `gpvStepProg` handlers and a common recorded
cache sequence `c` with `card (c j) ≤ j + qHash`.

Establishing this is the deferred-sampling fold-level coupling: every fresh salt draw, currently
issued inside the signing oracle at an adversarially-chosen point in an adaptively-interleaved query
stream, is *commuted to the front* of a clean `qSign`-step draw sequence (the salts are fresh
uniform and independent of the adversary view until revealed; the interleaved hash queries are
answer-irrelevant w.r.t. the salt draws and so commute). This is the GPV instance of the worked
Fiat–Shamir factorization
`FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`: an induction on
`adv.main pk` via `OracleComp.inductionOn`, with the uniform / hash-read steps handled by the
generic `OracleComp.DeferredSampling.evalSPMF_step_commute_tape` answer-irrelevant commute and the
signing step handled by a bespoke per-body salt splice. -/

/-! ### The pinned GPV game runs

The Step-1 coupling `gpv_tvDist_real_programmed_le_collisionBound` is pinned to the *actual* GPV
game runs of the adversary's main computation `adv.main pk`, not to free `SPMF` parameters or to a
hash-only run under a deterministic programming policy. Two named game-run distributions model the
two worlds of the sign-then-hash hop:

- `realGameRun` is the **real EUF-CMA game run**: `adv.main pk` simulated under the real ambient
  oracle forwarding (the lazy random oracle via the `runtime` bundle) and the real GPV signing
  oracle (`SignatureAlg.signingOracle`, which on each signing query draws a fresh salt, queries the
  random oracle, and trapdoor-samples a preimage). This is exactly the inner run of
  `SignatureAlg.unforgeableExpNoFresh` for the GPV scheme, with the forgery `(msg, σ)` extracted.

- `progGameRun` is the **randomized sign-then-hash game run**: `adv.main pk` simulated under the
  *programmed* random oracle and the *simulator* signing oracle of the collision reduction
  (the very handler stack of `reduction`). On each random-oracle miss the programmed oracle
  forward-samples `s ← domainSample pk` and records `psf.eval pk s`; on each signing query the
  simulator draws a fresh salt `r`, forward-samples `s`, programs `(r, msg) := psf.eval pk s`, and
  returns `(r, s)`. The randomness is genuine (it lives in `domainSample`), so this models the
  randomized sign-then-hash game rather than a deterministic point-mass programming policy.

The total-variation distance between these two runs is the sign-then-hash hop bounded by
`collisionBound`; the coupling factors both through the `signRunF` presentation so that
`factorized_advantage_le_collisionBound` delivers the bound. -/

open Classical in
/-- **The real GPV EUF-CMA game run** of `adv.main pk` at key pair `(pk, sk)`.

The adversary's main computation is simulated under the real ambient oracle forwarding (the lazy
random oracle supplied by the `runtime` bundle) together with the real GPV signing oracle
(`SignatureAlg.signingOracle`), and the resulting forgery `(msg, σ)` is extracted. This is exactly
the inner run of `SignatureAlg.unforgeableExpNoFresh` for the GPV scheme: it is the real-world side
of the sign-then-hash hop, the coupling's `realRun`. -/
noncomputable def realGameRun
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    SPMF (M × (Salt × Domain)) :=
  (runtime M Salt).evalSPMF do
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
      (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
        (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).signingOracle pk sk
    let (out, _log) ← (simulateQ impl (adv.main pk)).run
    pure out

open Classical in
/-- **The randomized sign-then-hash game run** of `adv.main pk` at public key `pk`.

The adversary's main computation is simulated under the collision reduction's programmed
random-oracle / simulator-signing handler stack (the handler model of `reduction`): on a
random-oracle miss the oracle forward-samples `s ← domainSample pk` and records `psf.eval pk s`; on
a signing query the simulator draws a fresh salt `r`, forward-samples `s`, programs
`(r, msg) := psf.eval pk s`, and returns `(r, s)`. The forgery `(msg, σ)` is extracted. The
programming is *randomized* (the randomness lives in `domainSample`), so this models the randomized
sign-then-hash game; it is the coupling's `progRun`. -/
noncomputable def progGameRun
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    SPMF (M × (Salt × Domain)) :=
  let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set ((st.1.cacheQuery (r, msg) v,
        fun t' => if t' = (r, msg) then some s else st.2 t') : State)
      pure (r, s)
  let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
  𝒮[Prod.fst <$> (simulateQ impl (adv.main pk)).run (∅, fun _ => none)]

/-! ### Collapsing the runtime indirection of `realGameRun`

The real-side run-equality compares `realGameRun` — defined through the bundled `runtime` `SPMF`
semantics, which is *itself* a `simulateQ` (`withStateOracle`) over a `StateT` random-oracle layer
wrapping the WriterT signing-oracle `simulateQ` — against the single-`simulateQ` `signRunF`
presentation. Before that fold coupling is attempted with the generic handler-congruence /
`inductionOn` machinery, the *outer* runtime indirection of `realGameRun` is peeled back to an
explicit `simulateQ` form. The two lemmas below do exactly that peeling (and nothing more): they are
pure structural unfoldings of the `runtime` bundle, pinned to the concrete `realGameRun`, and do
**not** perform any distributional coupling. -/

/-- **`withStateOracle` `SPMF` semantics as an explicit `simulateQ` run (general).**

The bundled `withStateOracle hashImpl s` `SPMF` semantics of a surface computation `mx` is exactly
the observed `StateT.run'` of the `simulateQ` of the public-randomness lift summed with the stateful
`hashImpl`, started from `s`. This is a definitional unfolding of the bundle (`evalSPMF` is
`denote = observe ∘ interpret`, with `interpret = simulateQ'` and
`observe = liftM ∘ StateT.run' · s`) and carries no probabilistic content; it is the entry point for
reasoning about the runtime layer of
`realGameRun` by an explicit `simulateQ`. -/
theorem withStateOracle_evalSPMF_eq {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α : Type} (mx : OracleComp (unifSpec + hashSpec) α) :
    (SPMFSemantics.withStateOracle hashImpl s).evalSPMF mx
      = (liftM (StateT.run'
          (simulateQ
            ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
            mx) s) : SPMF α) := by
  unfold SPMFSemantics.evalSPMF SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]

/-- **WriterT-log discard across a substituting oracle (general).**

Simulating `oa` under a WriterT-valued query implementation `so` and then projecting away the
written log (`Prod.fst <$> (·).run`) coincides with simulating `oa` under the *unlogged* base-spec
implementation `soNoLog`, provided the two agree per query after the same log discard
(`hso : ∀ t, Prod.fst <$> (so t).run = soNoLog t`).

Unlike `OracleComp.fst_map_writerT_run_simulateQ`, the target base spec `specBase` may differ from
the source spec `spec`: `soNoLog` is allowed to *substitute* each query by an arbitrary base-spec
computation (not merely re-emit it), so this applies to a genuine oracle replacement such as the GPV
signing oracle (which replaces an abstract signing query by its real `sign` computation over the
random-oracle spec). It is proved by induction on `oa`, with the append-accumulated WriterT log on
the binder collapsing under `Prod.fst`. The log carrier uses the append-based `WriterT` monad
(`[EmptyCollection ω] [Append ω] [LawfulAppend ω]`) so that it applies directly to the `QueryLog`
log of the GPV signing oracle, whose `WriterT` monad instance is the append-based one (there is
deliberately no `Monoid (QueryLog spec)` instance). -/
theorem fst_map_writerT_run_simulateQ_noLog
    {ι ιB : Type} {spec : OracleSpec ι} {specBase : OracleSpec ιB}
    {ω : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω] {α : Type}
    (so : QueryImpl spec (WriterT ω (OracleComp specBase)))
    (soNoLog : QueryImpl spec (OracleComp specBase))
    (hso : ∀ (t : spec.Domain),
      (Prod.fst <$> (so t).run : OracleComp specBase _) = soNoLog t)
    (oa : OracleComp spec α) :
    (Prod.fst <$> (simulateQ so oa).run : OracleComp specBase α) = simulateQ soNoLog oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
    rw [simulateQ_bind, simulateQ_query, WriterT.run_bind, map_bind]
    have heq : ((OracleSpec.query t).cont <$> so (OracleSpec.query t).input) = so t := by
      simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [heq]
    rw [show simulateQ soNoLog (liftM (OracleSpec.query t) >>= oa)
          = soNoLog t >>= fun u => simulateQ soNoLog (oa u) by
        rw [simulateQ_bind, simulateQ_query]
        simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]]
    refine (bind_congr fun x => ?_).trans (by rw [← bind_map_left, hso t])
    obtain ⟨a, w₁⟩ := x
    dsimp only []
    rw [← LawfulFunctor.comp_map]
    have : Prod.fst ∘ (fun x : α × ω ↦ (x.1, w₁ ++ x.2)) = Prod.fst :=
      funext fun ⟨_, _⟩ => rfl
    rw [this]
    exact ih a

/-- **The unlogged real GPV handler stack.**

The real-world handler used inside `realGameRun` is the WriterT-valued stack
`(HasQuery.toQueryImpl).liftTarget (WriterT …) + signingOracle pk sk`, which logs each signing
query. `realGameRunImplNoLog` is the same handler with the signing log discarded: the public/random
oracle queries are re-emitted unchanged into the underlying `OracleComp (unifSpec + (Salt × M →ₒ
Range))`, and each signing query is replaced by the real GPV `sign pk sk` computation (draw a fresh
salt, query the random oracle, trapdoor-sample). It targets `OracleComp (unifSpec + (Salt × M →ₒ
Range))` directly, so simulating `adv.main pk` under it produces the same forgery distribution as
the logged stack with its log discarded (`realGameRun_writerLog_discard`). -/
@[expose] noncomputable def realGameRunImplNoLog (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (OracleComp (unifSpec + (Salt × M →ₒ Range))) :=
  (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
      (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
    (fun msg => (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
      psf hr M Salt).sign pk sk msg)

omit [Fintype Salt] in
/-- **Real-side WriterT-log discard (pinned).**

Discarding the signing log from the real GPV WriterT handler stack of `realGameRun` leaves exactly
the unlogged stack `realGameRunImplNoLog`: projecting the first component of the WriterT run of
`simulateQ ((HasQuery.toQueryImpl).liftTarget (WriterT …) + signingOracle pk sk) (adv.main pk)`
equals `simulateQ (realGameRunImplNoLog …) (adv.main pk)`.

It is *pinned* to the concrete real GPV handler stack and is a pure structural rewrite (the general
`fst_map_writerT_run_simulateQ_noLog` discharged by the per-query log-transparency of the two
summands: the lifted public/random-oracle handler re-emits its query, and
`signingOracle = withLogging sign` recovers `sign` after the log discard). No salt front-loading or
distributional coupling is
performed; this is the WriterT-boundary half of the real-side normalization toward the single-impl
`signRunF` shape. -/
theorem realGameRun_writerLog_discard (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (Prod.fst <$> (simulateQ
        (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk))
        (adv.main pk)).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) (M × (Salt × Domain)))
      = simulateQ (realGameRunImplNoLog psf hr M Salt pk sk) (adv.main pk) := by
  refine fst_map_writerT_run_simulateQ_noLog _ _ (fun t => ?_) (adv.main pk)
  rcases t with t | msg
  · change (Prod.fst <$> ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
        (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) t).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) _)
      = realGameRunImplNoLog psf hr M Salt pk sk (Sum.inl t)
    simp only [QueryImpl.liftTarget_apply, WriterT.run_liftM]
    rfl
  · change (Prod.fst <$> ((GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
        psf hr M Salt).signingOracle pk sk msg).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) _)
      = (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).sign pk sk msg
    simp only [SignatureAlg.signingOracle, QueryImpl.withLogging_apply, bind_pure_comp,
      WriterT.run_bind, WriterT.run_liftM, bind_map_left]
    simp only [WriterT.run_map, WriterT.run_tell, map_pure]
    rw [← Functor.map_map]
    simp

open Classical in
omit [Fintype Salt] in
/-- **Real-side normalization (pinned): `realGameRun` as an explicit two-layer
`simulateQ` run.**

This peels the bundled `runtime` indirection off `realGameRun`, exposing the *explicit* nested
`simulateQ` form: the inner WriterT signing-oracle `simulateQ` over `adv.main pk` (its `.run`
discarding the signing log to the `Prod.fst` projection), evaluated under the outer
public-randomness-lift `+ randomOracle` `StateT QueryCache ProbComp` `simulateQ`, observed by
`StateT.run'` from the empty cache.

It is *pinned* to the concrete `realGameRun` (it is an equation about that exact distribution, with
the concrete WriterT handler stack `liftTarget HasQuery.toQueryImpl + signingOracle pk sk` and the
concrete outer lazy random oracle), and it is a pure structural rewrite — the trailing `pure out`
of the `realGameRun` do-block is commuted out by `withStateOracle_evalSPMF_bind_pure`, and the
runtime layer is unfolded by `withStateOracle_evalSPMF_eq`. No salt front-loading and no
distributional coupling is performed; this is the runtime-indirection removal that the deep fold
coupling builds on. -/
theorem realGameRun_eq_simulateQ_run
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      Prod.fst <$> ((SPMFSemantics.withStateOracle
        (randomOracle : QueryImpl (Salt × M →ₒ Range)
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalSPMF
        ((simulateQ
            (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk))
            (adv.main pk)).run)) := by
  unfold realGameRun
  rw [show (do
        let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
          (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
              (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk
        let (out, _log) ← (simulateQ impl (adv.main pk)).run
        pure out) = ((simulateQ
            (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk))
            (adv.main pk)).run >>= fun p => pure p.1) from rfl]
  rw [GPVHashAndSign.runtime]
  change (SPMFSemantics.withStateOracle _ ∅).evalSPMF _ = _
  rw [SPMFSemantics.withStateOracle_evalSPMF_bind_pure]

open Classical in
omit [Fintype Salt] in
/-- **Real-side normalization (pinned, single-impl): `realGameRun` as one bundled
`simulateQ` over the unlogged real handler stack.**

This is the assembled real-side normalization: `realGameRun` equals the bundled `withStateOracle`
random-oracle `SPMF` semantics of `simulateQ (realGameRunImplNoLog …) (adv.main pk)` — a *single*
`OracleComp (unifSpec + (Salt × M →ₒ Range))`-valued `simulateQ` over the unlogged real GPV handler
stack, with no remaining WriterT layer. It chains `realGameRun_eq_simulateQ_run` (peeling the
`runtime` indirection and commuting the trailing `pure out` to `Prod.fst <$>`),
`SPMFSemantics.withStateOracle_evalSPMF_map` (pushing that `Prod.fst <$>` *inside* the outer
bundle, since `<$>` does not thread the random-oracle state), and `realGameRun_writerLog_discard`
(collapsing the inner WriterT signing-log run to `realGameRunImplNoLog`).

It is *pinned* to the concrete `realGameRun` and is purely structural (no salt front-loading, no
distributional coupling). This is the canonical single-`simulateQ` shape that the eventual fold
coupling consumes: `realGameRun`'s adversary computation is now interpreted by one ambient handler
`realGameRunImplNoLog` over `OracleComp (unifSpec + (Salt × M →ₒ Range))`, then observed by the
random-oracle `withStateOracle` bundle — the same surface shape carried by `progGameRun`'s single
`StateT`-state `simulateQ`. -/
theorem realGameRun_eq_withStateOracle_implNoLog
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      (SPMFSemantics.withStateOracle
        (randomOracle : QueryImpl (Salt × M →ₒ Range)
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalSPMF
        (simulateQ (realGameRunImplNoLog psf hr M Salt pk sk) (adv.main pk)) := by
  rw [realGameRun_eq_simulateQ_run, ← SPMFSemantics.withStateOracle_evalSPMF_map,
    realGameRun_writerLog_discard]

/-! ### Dropping the preimage-record component of `progGameRun`

`progGameRun` simulates `adv.main pk` under a handler stack whose state is the product
`QueryCache × ((Salt × M) → Option Domain)`. The second component is the *preimage record*: it
records, for each programmed random-oracle point, the domain element forward-sampled to produce the
answer. That record is bookkeeping for the collision reduction's extraction only — it is written by
every programming step (and read solely to update *itself*), but it never influences the
random-oracle cache, the output, or any other branch. Hence the forgery distribution `progGameRun`
(the `Prod.fst` of the run) is unchanged by dropping the record component, leaving a single
`simulateQ` over the bare
`StateT QueryCache ProbComp` random-oracle surface — the *same* state shape carried by
`realGameRunImplNoLog` under the runtime `withStateOracle` bundle. The lemma below performs exactly
that drop (no distributional coupling). -/

/-- **The record-free `progGameRun` handler stack.**

The same programmed random-oracle / simulator-signing handler stack as `progGameRun`, but with the
preimage-record component removed: its state is just the random-oracle `QueryCache`. The
random-oracle handler programs a miss with `psf.eval pk (domainSample pk)`; the signing handler
draws a fresh salt, forward-samples, programs the cache point, and returns `(r, s)`. This carries
the same
`StateT QueryCache ProbComp` random-oracle surface as `realGameRunImplNoLog` (observed through the
runtime `withStateOracle` bundle), the shared shape required before the fold coupling. -/
@[expose] noncomputable def progGameRunImplNoRec (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  let roImpl : QueryImpl (Salt × M →ₒ Range)
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun t => do
      let st ← get
      match st t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set (st.cacheQuery t v)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set (st.cacheQuery (r, msg) v)
      pure (r, s)
  (unifImpl + roImpl) + signImpl

open Classical in
omit [Fintype Salt] in
/-- **Prog-side normalization (pinned): `progGameRun` with the preimage record dropped.**

`progGameRun … adv domainSample pk` equals the random-oracle `SPMF` semantics of the *single*
`simulateQ (progGameRunImplNoRec …) (adv.main pk)` over the bare `StateT QueryCache ProbComp` state,
observed by `StateT.run'` from the empty cache. The preimage-record component of `progGameRun`'s
state is genuinely passive: it is written by the programming steps but never read by the cache, the
output, or the control flow, so projecting it away (`proj = Prod.fst`) commutes with every oracle
step and hence with the whole simulation (`map_run_simulateQ_eq_of_query_map_eq`).

It is *pinned* to the concrete `progGameRun` and is a pure structural state-projection (no salt
front-loading, no distributional coupling). Together with `realGameRun_eq_withStateOracle_implNoLog`
this puts **both** game runs on the same `StateT QueryCache ProbComp` random-oracle surface — the
prerequisite for the `OracleComp.inductionOn` fold coupling. -/
theorem progGameRun_eq_run'_implNoRec
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    progGameRun psf hr M Salt adv domainSample pk =
      𝒮[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk)
          (adv.main pk)).run' (∅ : (Salt × M →ₒ Range).QueryCache)] := by
  unfold progGameRun
  simp only [evalSPMF]
  refine congrArg _ ?_
  -- LHS is `Prod.fst <$> run = run'`; the record component (initially `fun _ => none`) is the
  -- passive auxiliary, so the state projection `proj = Prod.fst` commutes with every step.
  rw [show ((∅ : (Salt × M →ₒ Range).QueryCache)) = Prod.fst
      (((∅ : (Salt × M →ₒ Range).QueryCache), (fun _ => none : (Salt × M) → Option Domain))) from
        rfl]
  rw [← StateT.run']
  refine run'_simulateQ_eq_of_query_map_eq _
    (progGameRunImplNoRec psf M Salt domainSample pk) Prod.fst ?_ (adv.main pk)
    (∅, fun _ => none)
  -- For each oracle (uniform / random-oracle / signing) the cache update depends only on the
  -- cache component, so projecting away the preimage record commutes with the step.
  rintro ((t | t) | t) ⟨st, rec⟩ <;>
    simp only [HAdd.hAdd, QueryImpl.add, progGameRunImplNoRec]
  · -- uniform-sampling query: state untouched by either handler
    simp [StateT.run_monadLift, Prod.map]
  · -- random-oracle query: the cache hit/miss is determined by the cache component `st t`
    rcases h : st t with _ | v <;>
      simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, Prod.map, h]
  · -- signing query: cache update depends only on the cache component
    simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, Prod.map]

/-- **The composed single-impl real GPV handler stack.**

The two-layer real-side simulation of `realGameRun` — `simulateQ realGameRunImplNoLog (adv.main pk)`
producing an `OracleComp (unifSpec + (Salt × M →ₒ Range))`, then observed by the runtime's
public-randomness-lift `+ randomOracle` `StateT QueryCache ProbComp` simulation — fused into a
*single* `StateT QueryCache ProbComp`-valued handler via `QueryImpl.compose` (`∘ₛ`). This carries
the same bare `StateT QueryCache ProbComp` random-oracle surface as `progGameRunImplNoRec`, the
shared shape the fold coupling consumes. -/
@[expose] noncomputable def gpvRealImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))) ∘ₛ
    realGameRunImplNoLog psf hr M Salt pk sk)

open Classical in
omit [Fintype Salt] in
/-- **Real-side single-impl normalization (pinned): `realGameRun` as one bundled `simulateQ`
over the composed real handler `gpvRealImpl`.**

This collapses the two-layer real-side simulation of `realGameRun` into a single `simulateQ` over
the composed handler `gpvRealImpl` (`= outerLift ∘ₛ realGameRunImplNoLog`), observed by
`StateT.run'` from the empty cache:
`realGameRun … = 𝒮[(simulateQ (gpvRealImpl …) (adv.main pk)).run' ∅]`. It
chains `realGameRun_eq_withStateOracle_implNoLog` (the peeling of the runtime indirection to
a single `simulateQ realGameRunImplNoLog` observed through `withStateOracle`),
`withStateOracle_evalSPMF_eq` (unfolding the `withStateOracle` bundle to an explicit
`StateT.run'`-of-`simulateQ` of the public-randomness lift `+ randomOracle`), and
`QueryImpl.simulateQ_compose` (fusing the two `simulateQ` layers into the single composed handler).

It is *pinned* to the concrete `realGameRun` and is a pure structural normalization — no salt
front-loading, no distributional coupling. Together with `progGameRun_eq_run'_implNoRec` this puts
**both** game runs in the identical `𝒮[(simulateQ · (adv.main pk)).run' ∅]` shape over the *same*
`StateT QueryCache ProbComp` random-oracle surface, the prerequisite for attempting the
`OracleComp.inductionOn` fold coupling on a common vehicle. -/
theorem realGameRun_eq_run'_implReal
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      𝒮[(simulateQ (gpvRealImpl psf hr M Salt pk sk)
          (adv.main pk)).run' (∅ : (Salt × M →ₒ Range).QueryCache)] := by
  rw [realGameRun_eq_withStateOracle_implNoLog, withStateOracle_evalSPMF_eq]
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-! ### GPV tape-consuming impls

The front-tape factorization follows the worked Fiat–Shamir instance
`FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`: an
`OracleComp.inductionOn`
over `adv.main pk` that front-loads every signing query's fresh salt draw into a single front draw
block `OracleComp.drawList ($ᵗ Salt) qSign`, leaving a *tape-consuming* run whose signing steps read
their salt off the pre-drawn tape rather than drawing it inline.

This section builds the GPV tape-consuming handlers — the analogues of Fiat–Shamir's
`tapeDrawReadImpl` — and their per-query `.run` unfolding lemmas (the analogues of
`tapeDrawReadImpl_run_unif` / `_read` / `_sign`). Each handler carries the random-oracle
`QueryCache` *plus a salt tape* `List Salt` in its state: a signing query consumes the head salt of
the tape (running the rest of the inline signing body on it) instead of drawing `r ← $ᵗ Salt`, while
uniform and random-oracle-read queries leave the tape untouched. These are concrete definitions and
their structural per-query unfoldings; the full `inductionOn` factorization (relating
`simulateQ gpvRealImpl` to the front-tape `drawList ($ᵗ Salt) qSign >>= simulateQ gpvRealImplTape`)
and the `drawList`↔`signRunF` bridge are carried out in the front-tape factorization below. -/

/-- **The real GPV tape-consuming handler.**

The salt-tape analogue of `gpvRealImpl`: its state is the random-oracle `QueryCache` paired with a
*salt tape* `List Salt`. A signing query consumes the head salt `r` of the tape (instead of drawing
`r ← $ᵗ Salt` inline), queries the random oracle at `(r, msg)`, trapdoor-samples a preimage, and
returns `(r, s)` while advancing the tape by one; uniform and random-oracle-read queries behave
exactly as the real handler and leave the tape untouched. The tape is over-provisioned (length
`qSign`, one salt per signing query); a missing head (empty tape) defaults to the inline draw so the
handler is total. This is the GPV analogue of Fiat–Shamir's `tapeDrawReadImpl`; its per-query
unfoldings are recorded by `gpvRealImplTape_run_unif` / `_read` / `_sign` below. -/
@[expose] noncomputable def gpvRealImplTape (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, s.2))) <$>
        (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1
  | .inr msg => StateT.mk fun s =>
      match s.2 with
      | [] =>
          (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache =>
              (rsc.1, (rsc.2, ([] : List Salt)))) <$>
            (do
              let r ← ($ᵗ Salt : ProbComp Salt)
              let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
              let sgn ← psf.trapdoorSample pk sk p.1
              pure ((r, sgn), p.2))
      | r :: tl =>
          (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
            (do
              let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
              let sgn ← psf.trapdoorSample pk sk p.1
              pure ((r, sgn), p.2))

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a uniform query.** The tape is untouched. -/
lemma gpvRealImplTape_run_unif (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a random-oracle read query.** The tape is
untouched; the cache component runs the lazy `randomOracle` step. -/
lemma gpvRealImplTape_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s =
      (fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, s.2))) <$>
        (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a signing query with a non-empty tape.** The head
salt `r` is consumed off the tape (the tape advances to its tail `tl`), the random oracle is queried
at `(r, msg)`, a trapdoor preimage is drawn, and `(r, s)` is returned. This is the GPV analogue of
`tapeDrawReadImpl_run_sign`: the inline salt draw `r ← $ᵗ Salt` is *replaced* by consuming the
pre-drawn tape head. -/
lemma gpvRealImplTape_run_sign_cons (pk : PK) (sk : SK) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImplTape psf M Salt pk sk (.inr msg)).run (cache, r :: tl) =
      (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
        (do
          let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
          let sgn ← psf.trapdoorSample pk sk p.1
          pure ((r, sgn), p.2)) := rfl

/-- **The programmed (simulator) GPV tape-consuming handler.**

The salt-tape analogue of `progGameRunImplNoRec`: its state is the random-oracle `QueryCache` paired
with a salt tape `List Salt`. A signing query consumes the head salt `r` of the tape (instead of
drawing `r ← $ᵗ Salt` inline), forward-samples a short preimage `s ← domainSample pk`, programs the
cache point `(r, msg) ↦ psf.eval pk s`, and returns `(r, s)` while advancing the tape; the
random-oracle handler programs a miss with `psf.eval pk (domainSample pk)` and the uniform handler
is the bare sample, both leaving the tape untouched. This is the programmed dual of
`gpvRealImplTape`; its per-query unfoldings are recorded by `progGameRunImplTape_run_unif` /
`_read` / `_sign` below. -/
@[expose] noncomputable def progGameRunImplTape (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1 mc with
      | some v => pure (v, s)
      | none =>
          (fun sd : Domain => (psf.eval pk sd, (s.1.cacheQuery mc (psf.eval pk sd), s.2))) <$>
            (domainSample pk : ProbComp Domain)
  | .inr msg => StateT.mk fun s =>
      match s.2 with
      | [] =>
          (do
            let r ← ($ᵗ Salt : ProbComp Salt)
            let sd ← (domainSample pk : ProbComp Domain)
            pure ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), ([] : List Salt))))
      | r :: tl =>
          (fun sd : Domain => ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
            (domainSample pk : ProbComp Domain)

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a uniform query.** The tape is untouched. -/
lemma progGameRunImplTape_run_unif (domainSample : PK → ProbComp Domain) (pk : PK)
    (n : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a random-oracle read query.** The tape is
untouched; on a cache hit the recorded value is returned, on a miss the answer is programmed to
`psf.eval pk (domainSample pk)`. -/
lemma progGameRunImplTape_run_read (domainSample : PK → ProbComp Domain) (pk : PK) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s =
      (match s.1 mc with
        | some v => pure (v, s)
        | none =>
            (fun sd : Domain => (psf.eval pk sd, (s.1.cacheQuery mc (psf.eval pk sd), s.2))) <$>
              (domainSample pk : ProbComp Domain)) := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a signing query with a non-empty tape.** The
head salt `r` is consumed off the tape (the tape advances to its tail `tl`), a short preimage is
forward-sampled, the cache point `(r, msg) ↦ psf.eval pk s` is programmed, and `(r, s)` is returned.
This is the programmed analogue of `gpvRealImplTape_run_sign_cons`: the inline salt draw is replaced
by consuming the pre-drawn tape head. -/
lemma progGameRunImplTape_run_sign_cons (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (r : Salt) (tl : List Salt) (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run (cache, r :: tl) =
      (fun sd : Domain => ((r, sd), (cache.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
        (domainSample pk : ProbComp Domain) := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **Real tape signing-step cache bridge.** The cache component of one `gpvRealImplTape` signing
step on a consed tape `r :: tl`, at a *missing* cache key `(r, msgs n) = none`, is distributed
exactly as the concrete `signRunF` real step `gpvStepReal` at the consumed head salt `r`.

This is the GPV analogue of Fiat–Shamir's per-body splice (the signing-step case of the fold
factorization): it relates the tape-consuming signing step to the `signRunF` handler of the
sequenced coupling `signRunF_tvDist_le_collisionBound`. It is *pinned* to the concrete
`gpvRealImplTape` and
`gpvStepReal`, and reduces (via `gpvRealImplTape_run_sign_cons`) to the inline splice
`evalSPMF_gpvSignBody_run_eq_gpvStepReal`: with the head salt `r` already supplied (front-loaded out
of the tape), the tape signing step is exactly one real signing body run through the lazy random
oracle, whose recorded cache transition is `gpvStepReal n cache r`. The only side condition is the
fresh-salt cache miss `hmiss`. -/
lemma evalSPMF_gpvRealImplTape_sign_cache_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (r : Salt) (tl : List Salt) (cache : (Salt × M →ₒ Range).QueryCache)
    (hmiss : cache (r, msgs n) = none) :
    𝒮[(fun p : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.2.1) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr (msgs n))).run (cache, r :: tl)]
      = 𝒮[gpvStepReal psf M Salt pk sk msgs n cache r] := by
  rw [gpvRealImplTape_run_sign_cons]
  simp only [Functor.map_map]
  rw [← evalSPMF_gpvSignBody_run_eq_gpvStepReal psf M Salt pk sk msgs n cache r hmiss]
  simp [map_bind]

open Classical in
omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Programmed tape signing-step cache bridge.** The cache component of one
`progGameRunImplTape` signing step on a consed tape `r :: tl` is distributed exactly as the concrete
`signRunF` programmed step `gpvStepProg` at the consumed head salt `r`.

This is the programmed dual of `evalSPMF_gpvRealImplTape_sign_cache_eq_gpvStepReal`, and the
signing-step case of the *programmed* run-equality the coupling factors through. It is *pinned* to
the concrete `progGameRunImplTape` and `gpvStepProg`: both forward-sample `s ← domainSample pk` and
record the cache transition `cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)` at the consumed
head salt `r`, so projecting the random-oracle cache component yields exactly `gpvStepProg`. No
side condition is required (the programmed step caches unconditionally). -/
lemma evalSPMF_progGameRunImplTape_sign_cache_eq_gpvStepProg (domainSample : PK → ProbComp Domain)
    (pk : PK) (msgs : ℕ → M) (n : ℕ) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    𝒮[(fun p : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.2.1) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr (msgs n))).run (cache, r :: tl)]
      = 𝒮[gpvStepProg psf M Salt pk domainSample msgs n cache r] := by
  rw [progGameRunImplTape_run_sign_cons]
  unfold gpvStepProg
  simp [map_eq_bind_pure_comp, Function.comp]

omit [Fintype Salt] [DecidableEq Range] in
/-- **Off-bad joint agreement of the two tape signing steps on a fresh head salt (the `hreg`
substitution bridge, signing case).** On a non-empty tape `r :: tl` whose head salt `r` is *not yet
keyed* in the cache — so the random-oracle read at `(r, msg)` is a miss — the full signing-step
output distributions of `gpvRealImplTape` and `progGameRunImplTape` *coincide*: the returned
signature `(r, sgn)`, the updated cache, and the advanced tape `tl` are jointly distributed the same
on both sides.

The real side draws a fresh uniform target `c ← $ᵗ Range`, a trapdoor preimage `sgn ←
trapdoorSample pk sk c`, records `(r, msg) ↦ c`, and returns `((r, sgn), cache', tl)`; the
programmed side forward-samples `sd ← domainSample pk`, records `(r, msg) ↦ psf.eval pk sd`, and
returns `((r, sd), cache'', tl)`. Both apply the *same* deterministic post-processing
`fun (c, s) => ((r, s), cache.cacheQuery (r, msg) c, tl)` to a `(target, preimage)` pair drawn from
two distributions that coincide by PSF regularity `hreg`. This is the signing-query case of the
per-step no-bad-path agreement underlying the tape-route identical-until-bad coupling, the
full-output generalization of the cache-marginal `gpvStep_agree`. -/
theorem evalSPMF_gpvImplTape_run_sign_miss_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) (hmiss : cache (r, msg) = none)
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒮[(gpvRealImplTape psf M Salt pk sk (.inr msg)).run (cache, r :: tl)]
      = 𝒮[(progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run (cache, r :: tl)] := by
  classical
  rw [gpvRealImplTape_run_sign_cons, progGameRunImplTape_run_sign_cons]
  -- The shared post-processing of a `(target, preimage)` pair.
  set g : Range × Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) :=
    fun cs => ((r, cs.2), (cache.cacheQuery (r, msg) cs.1, tl)) with hg
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        = (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  -- Both sides reduce to `g <$> (·)` applied to the two `hreg`-equal `(target, preimage)` draws.
  have hLHS :
      𝒮[((fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
          (do
            let p ← (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
            let sgn ← psf.trapdoorSample pk sk p.1
            pure ((r, sgn), p.2)))]
        = 𝒮[g <$> (do let c ← ($ᵗ Range); let sgn ← psf.trapdoorSample pk sk c; pure (c, sgn)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  have hRHS :
      𝒮[((fun sd : Domain => ((r, sd), (cache.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
          (domainSample pk : ProbComp Domain))]
        = 𝒮[g <$> (do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  exact evalSPMF_map_eq_of_evalSPMF_eq hreg.symm g

/-! ### Flag-instrumented tape handlers (the identical-until-bad collision flag)

A per-tape identical-until-bad coupling over the front salt tape would be established, in the
Fiat–Shamir template, by instrumenting the two tape handlers with a collision *flag*: a `Bool`
threaded through the state, set the first time a consumed signing tape head salt `r` is already a
key of the running random-oracle cache. Off the flag (no salt has yet collided) the two handlers
agree in distribution by the `hreg` first marginal; once the flag fires it stays set
(bad-monotone). The framework lemma `tvDist_simulateQ_run_le_probEvent_output_bad` would then
bound the per-tape TV by the run-level flag probability, which the cardinality telescope
(`saltSeq` / `tapeCheck`) bounds by `collisionBound`. This section builds the flag-instrumented
tape handlers and their off-flag agreements; the coupling headline over the tape is not
established, and the Step-1 bound `gpv_tvDist_real_programmed_le_collisionBound` is proved by
the inline-salt route of `FlagHandlers.lean` instead.

`saltKeyed cache r` is the per-step bad predicate: the head salt `r` is already a key of the cache
(some `(r, m)` is recorded). It is the collision event the flag accumulates. -/

open Classical in
/-- **Salt-already-keyed predicate.** `saltKeyed cache r` holds when the salt `r` already appears as
the first component of some recorded random-oracle key `(r, m)` in `cache`. It is the per-signing-
step collision event: a consumed signing tape head salt landing on a key the running cache already
holds. The flag-instrumented tape handlers set their collision flag exactly when this fires on the
consumed head salt. -/
@[expose] noncomputable def saltKeyed (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) : Bool :=
  decide (∃ m : M, (cache (r, m)).isSome)

open Classical in
/-- **Flag-instrumented real tape handler.** `gpvRealImplTape` threaded with a collision flag: the
state is `((QueryCache × List Salt) × Bool)`. Uniform and random-oracle queries leave the flag
untouched; a signing query, before consuming its head salt `r`, sets the flag if `r` is already a
key of the cache (`saltKeyed`) on a non-empty tape, or unconditionally when the tape is *empty*
(no head salt to consume), monotonically OR-ing into the prior flag, then runs the underlying
`gpvRealImplTape` signing step. Its `run'`-projection (dropping the flag) is the original
`gpvRealImplTape`.

The empty-tape signing case fires the flag because there the underlying handler falls back to an
*inline* fresh salt draw that the tape-collision flag does not track, so the real and programmed
runs may diverge off-flag there; firing the flag makes the empty-tape signing state lie *inside*
the bad set, which is what makes the off-bad per-query agreement (`h_agree_good`) universal over all
states. In the actual `qSign`-salt run this branch is unreachable (the query bound permits at most
`qSign` signing queries and the tape holds `qSign` salts), so it contributes no probability mass. -/
@[expose] noncomputable def gpvRealImplTapeFlag (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImplTape psf M Salt pk sk (.inl q)).run s.1
    | .inr msg =>
        let flag' : Bool := s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r
                                                      | [] => true)
        (fun p => (p.1, (p.2, flag'))) <$> (gpvRealImplTape psf M Salt pk sk (.inr msg)).run s.1

open Classical in
/-- **Flag-instrumented programmed tape handler.** The programmed dual of `gpvRealImplTapeFlag`:
`progGameRunImplTape` threaded with the same collision flag (set on a signing step when the consumed
head salt `r` is already a key of the cache). Its `run'`-projection is the original
`progGameRunImplTape`. -/
@[expose]
noncomputable def progGameRunImplTapeFlag (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$>
          (progGameRunImplTape psf M Salt domainSample pk (.inl q)).run s.1
    | .inr msg =>
        let flag' : Bool := s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r
                                                      | [] => true)
        (fun p => (p.1, (p.2, flag'))) <$>
          (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s.1

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTapeFlag` on a non-signing query.** The flag is untouched;
the underlying `gpvRealImplTape` runs on the `(cache, tape)` component. -/
lemma gpvRealImplTapeFlag_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (gpvRealImplTapeFlag psf M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImplTape psf M Salt pk sk (.inl q)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTapeFlag` on a non-signing query.** -/
lemma progGameRunImplTapeFlag_run_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (progGameRunImplTapeFlag psf M Salt domainSample pk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inl q)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTapeFlag` on a signing query.** The flag is OR-ed with the
collision predicate on the head salt (`saltKeyed` if the tape is non-empty, `false` otherwise), then
the underlying `gpvRealImplTape` signing step runs on the `(cache, tape)` component. -/
lemma gpvRealImplTapeFlag_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (gpvRealImplTapeFlag psf M Salt pk sk (.inr msg)).run s =
      (fun p => (p.1, (p.2, s.2 || (match s.1.2 with
                                    | r :: _ => saltKeyed M Salt s.1.1 r
                                    | [] => true)))) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr msg)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTapeFlag` on a signing query.** The programmed dual of
`gpvRealImplTapeFlag_run_inr`. -/
lemma progGameRunImplTapeFlag_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (progGameRunImplTapeFlag psf M Salt domainSample pk (.inr msg)).run s =
      (fun p => (p.1, (p.2, s.2 || (match s.1.2 with
                                    | r :: _ => saltKeyed M Salt s.1.1 r
                                    | [] => true)))) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **Per-query flag-projection of the real flag handler.** Dropping the flag component
(`Prod.map id Prod.fst`) from one `gpvRealImplTapeFlag` query step recovers the corresponding
`gpvRealImplTape` step on the flagless `(cache, tape)` state. The flag is a passive auxiliary: it is
written by the signing step but never affects the output, the cache, or the tape, so projecting it
away yields the original handler. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplTapeFlag_proj_fst (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (gpvRealImplTapeFlag psf M Salt pk sk t).run s =
      (gpvRealImplTape psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q => rw [gpvRealImplTapeFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      change Prod.map id Prod.fst <$> ((fun p => (p.1, (p.2,
          s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r | [] => true)))) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr msg)).run s.1) = _
      simp [Functor.map_map, Prod.map]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Per-query flag-projection of the programmed flag handler.** The programmed dual of
`gpvRealImplTapeFlag_proj_fst`: dropping the flag recovers `progGameRunImplTape`. -/
lemma progGameRunImplTapeFlag_proj_fst (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (progGameRunImplTapeFlag psf M Salt domainSample pk t).run s =
      (progGameRunImplTape psf M Salt domainSample pk t).run s.1 := by
  cases t with
  | inl q => rw [progGameRunImplTapeFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      change Prod.map id Prod.fst <$> ((fun p => (p.1, (p.2,
          s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r | [] => true)))) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s.1) = _
      simp [Functor.map_map, Prod.map]

omit [Fintype Salt] [DecidableEq Range] in
/-- **Run-level flag-projection of the real flag handler.** Dropping the flag from the full
simulated run of `gpvRealImplTapeFlag` over `adv.main pk` recovers the flagless run of
`gpvRealImplTape`. This
transports the per-query projection `gpvRealImplTapeFlag_proj_fst` through the whole adversary via
`map_run_simulateQ_eq_of_query_map_eq`, witnessing that the collision flag is a passive instrument:
its addition does not change the output-and-`(cache, tape)` distribution. -/
lemma map_run_gpvRealImplTapeFlag_eq (pk : PK) (sk : SK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (simulateQ (gpvRealImplTapeFlag psf M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImplTape psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (gpvRealImplTapeFlag_proj_fst psf M Salt pk sk) oa s

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Run-level flag-projection of the programmed flag handler.** The programmed dual of
`map_run_gpvRealImplTapeFlag_eq`. -/
lemma map_run_progGameRunImplTapeFlag_eq (domainSample : PK → ProbComp Domain) (pk : PK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (simulateQ (progGameRunImplTapeFlag psf M Salt domainSample pk) oa).run s =
      (simulateQ (progGameRunImplTape psf M Salt domainSample pk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (progGameRunImplTapeFlag_proj_fst psf M Salt domainSample pk) oa s

omit [Fintype Salt] [DecidableEq Range] in
/-- **Bad-monotonicity of the real flag handler.** Once the collision flag is set on the input state
(`p.2 = true`), every output of one `gpvRealImplTapeFlag` query step also carries the flag set: the
non-signing branch preserves `s.2`, and the signing branch only OR-s a new collision indicator into
it. This is the `h_mono` hypothesis the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` consumes: the bad event is absorbing. -/
lemma gpvRealImplTapeFlag_bad_mono (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((gpvRealImplTapeFlag psf M Salt pk sk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [gpvRealImplTapeFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      have : z.2.2 = (p.2 || (match p.1.2 with
          | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)) := by
        change z ∈ support ((fun w => (w.1, (w.2,
            p.2 || (match p.1.2 with | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)))) <$>
          (gpvRealImplTape psf M Salt pk sk (.inr msg)).run p.1) at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, _, hw⟩ := hz
        simp [← hw]
      simp [this, hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Bad-monotonicity of the programmed flag handler.** The programmed dual of
`gpvRealImplTapeFlag_bad_mono`. -/
lemma progGameRunImplTapeFlag_bad_mono (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((progGameRunImplTapeFlag psf M Salt domainSample pk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [progGameRunImplTapeFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      have : z.2.2 = (p.2 || (match p.1.2 with
          | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)) := by
        change z ∈ support ((fun w => (w.1, (w.2,
            p.2 || (match p.1.2 with | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)))) <$>
          (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run p.1) at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, _, hw⟩ := hz
        simp [← hw]
      simp [this, hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] [DecidableEq Salt] [DecidableEq M]
  [SampleableType Salt] in
/-- **Off-collision unfolding of `saltKeyed`.** If the head salt `r` is not yet keyed in the cache
(`saltKeyed cache r = false`), then for every message `m` the random-oracle key `(r, m)` is a cache
miss. This is the side condition the off-bad signing-step agreement consumes: an unkeyed head salt
forces the random-oracle read at `(r, msg)` to be a miss, where the lazy real oracle and the
programmed oracle agree in distribution by `hreg`. -/
lemma saltKeyed_eq_false_iff (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    saltKeyed M Salt cache r = false ↔ ∀ m : M, cache (r, m) = none := by
  classical
  unfold saltKeyed
  rw [decide_eq_false_iff_not, not_exists]
  exact forall_congr' fun m => by rw [Option.not_isSome_iff_eq_none]

omit [Fintype Salt] [DecidableEq Range] in
/-- **(i) Off-bad signing-step agreement of the two flag-instrumented tape handlers.** On a
*non-empty* tape `r :: tl` whose head salt `r` is not yet keyed (`saltKeyed cache r = false`, so the
collision flag stays `false`), the full signing-step output distributions of `gpvRealImplTapeFlag`
and `progGameRunImplTapeFlag`, started from the off-bad state `((cache, r :: tl), false)`, coincide.

This is the framework `h_agree_good` *signing case* of the tape-route identical-until-bad
coupling, lifted from the underlying tape-handler agreement
`evalSPMF_gpvImplTape_run_sign_miss_eq` (the joint `hreg` substitution): off the collision flag both
flag handlers OR the same `false` collision indicator (the head salt is unkeyed) into the prior
`false` flag, and apply the same flag post-processing to the agreeing underlying signing-step
outputs.  It is the full-output, flag-level generalization of the cache-marginal `gpvStep_agree`,
*pinned* to the concrete flag handlers (no free parameters). -/
theorem evalSPMF_gpvImplTapeFlag_run_sign_offbad_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) (hkey : saltKeyed M Salt cache r = false)
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒮[(gpvRealImplTapeFlag psf M Salt pk sk (.inr msg)).run ((cache, r :: tl), false)]
      = 𝒮[(progGameRunImplTapeFlag psf M Salt domainSample pk (.inr msg)).run
          ((cache, r :: tl), false)] := by
  have hmiss : cache (r, msg) = none := (saltKeyed_eq_false_iff M Salt cache r).1 hkey msg
  rw [gpvRealImplTapeFlag_run_inr, progGameRunImplTapeFlag_run_inr]
  -- The flag post-processing is the same `false`-OR on both sides: simplify it away.
  simp only [Bool.false_or, hkey]
  -- Both reduce to the flag-tagging map applied to the agreeing underlying signing steps.
  exact evalSPMF_map_eq_of_evalSPMF_eq
    (evalSPMF_gpvImplTape_run_sign_miss_eq psf M Salt pk sk domainSample msg r tl cache hmiss hreg)
    _

/-- **Constant-flag map projection of a `false`-tagged output probability.** For the flag-tagging
map `fun p => (p.1, (p.2, F))` (the post-processing common to both flag-instrumented tape handlers
on a single query step), the probability of a `false`-flag output `(u, (s', false))` is exactly the
underlying probability of `(u, s')` when the flag value `F` is `false`, and `0` when `F` is `true`.

This is the bookkeeping that turns the per-query agreement of the *underlying* tape handlers into
the flag-level off-bad agreement `h_agree_good`: where the flag stays `false` the two flagged steps
agree because their underlying steps agree, and where the flag fires the `false`-output probability
is `0` on both sides regardless. -/
lemma probOutput_flagTag_false {α' σ' : Type}
    (m : ProbComp (α' × σ')) (F : Bool) (u : α') (s' : σ') :
    Pr[= (u, (s', false)) |
        ((fun p : α' × σ' => (p.1, (p.2, F))) <$> m : ProbComp (α' × σ' × Bool))]
      = if F = false then Pr[= (u, s') | m] else 0 := by
  classical
  rw [probOutput_map_eq_tsum_ite]
  by_cases hF : F = false
  · subst hF
    rw [if_pos rfl, ← tsum_ite_eq (u, s') (fun x => Pr[= x | m])]
    refine tsum_congr fun x => ?_
    congr 1
    rw [eq_iff_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm, rfl⟩
  · rw [if_neg hF, ENNReal.tsum_eq_zero]
    intro x
    rw [if_neg]
    rw [Prod.ext_iff, Prod.ext_iff]
    rintro ⟨_, _, h3⟩
    exact hF h3.symm

/-! ### Per-query tape↔unified-impl bridges

These lemmas relate one query-step of the tape-consuming impls `gpvRealImplTape` /
`progGameRunImplTape` to one query-step of the unified impls `gpvRealImpl` /
`progGameRunImplNoRec`, all on a common per-query `.run`. They are the analogues of
Fiat–Shamir's per-query relating lemmas. The full `inductionOn (adv.main pk)` factorization
(relating `simulateQ gpvRealImpl` to the front-tape
`drawList ($ᵗ Salt) qSign >>= simulateQ gpvRealImplTape`) and the `drawList`↔`signRunF` step bridge
are carried out in the front-tape factorization below.

First the per-query `.run` unfoldings of the *unified* impls on non-signing queries (the unified
analogues of `gpvRealImplTape_run_unif` / `_read`). Unlike the tape lemmas these are not `rfl`: the
unified real handler is the `∘ₛ`-composition `gpvRealImpl = (outerLift + randomOracle) ∘ₛ
realGameRunImplNoLog`, so each non-signing query reduces through `QueryImpl.compose` /
`realGameRunImplNoLog`'s query re-emission. -/

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a uniform query.** The cache is untouched: the unified
real handler re-emits the public-randomness query through `realGameRunImplNoLog` and the outer
public-randomness lift forwards it to the bare `unifSpec.query n`, pairing the cache back unchanged.
-/
lemma gpvRealImpl_run_unif (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run cache =
      (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a random-oracle read query.** The unified real handler
re-emits the random-oracle query through `realGameRunImplNoLog`, and the outer `randomOracle`
summand runs the lazy random-oracle step on the cache component. -/
lemma gpvRealImpl_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache =
      (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache := by
  simp [gpvRealImpl, QueryImpl.compose, realGameRunImplNoLog, HAdd.hAdd, QueryImpl.add]

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a signing query (the `∘ₛ`/`liftM` unfold).** The
unified real handler runs the real GPV signing body of `realGameRunImplNoLog` — `do r ← $ᵗ Salt; c ←
query (r, msg); s ← trapdoorSample c; pure (r, s)` — through the outer public-randomness-lift `+
randomOracle` simulation. The inline salt draw `r ← $ᵗ Salt` and the trapdoor draw pass through the
left (public-randomness) lift unchanged, and the random-oracle query `query (r, msg)` is answered by
the outer lazy `randomOracle` on the cache component, yielding the explicit inline sign body: draw a
fresh salt `r`, run the lazy random-oracle step at `(r, msg)`, draw the trapdoor preimage, and
return `((r, s), cache')`.

This is the GPV analogue of the FS deferred-sign-step body unfolding; it resolves the `∘ₛ`/`liftM`
indirection of `gpvRealImpl = (outerLift + randomOracle) ∘ₛ realGameRunImplNoLog` on the signing
query. It is *pinned* to the concrete `gpvRealImpl` and is a pure structural unfold (no salt
front-loading, no distributional coupling), via the per-action `simulateQ` rungs
(`simulateQ_add_liftM_left` / `simulateQ_liftTarget` / `ofLift_eq_id'` for the lifted draws) and
`gpvRealImpl_run_read` for the random-oracle query. -/
lemma gpvRealImpl_run_sign (pk : PK) (sk : SK) (msg : M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (Sum.inr msg)).run cache =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        let s ← psf.trapdoorSample pk sk p.1
        pure ((r, s), p.2)) := by
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
      ((GPVHashAndSign psf hr M Salt).sign pk sk msg)).run cache = _
  simp only [GPVHashAndSign, simulateQ_bind, StateT.run_bind,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, QueryImpl.ofLift_eq_id',
    simulateQ_id', StateT.run_monadLift, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind]
  refine bind_congr (fun x => ?_)
  congr 1
  exact gpvRealImpl_run_read psf hr M Salt pk sk (x, msg) cache

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a uniform query.** The cache is untouched. -/
lemma progGameRunImplNoRec_run_unif (domainSample : PK → ProbComp Domain) (pk : PK)
    (n : unifSpec.Domain) (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run cache =
      (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _) := rfl

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a random-oracle read query.** On a cache hit
the recorded value is returned; on a miss the answer is programmed to
`psf.eval pk (domainSample pk)` and recorded in the cache. The tape (in the tape impl) is replaced
here by the bare cache. -/
lemma progGameRunImplNoRec_run_read (domainSample : PK → ProbComp Domain) (pk : PK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache =
      (match cache mc with
        | some v => pure (v, cache)
        | none =>
            (fun sd : Domain => (psf.eval pk sd, cache.cacheQuery mc (psf.eval pk sd))) <$>
              (domainSample pk : ProbComp Domain)) := by
  cases h : cache mc <;>
    simp [progGameRunImplNoRec, HAdd.hAdd, QueryImpl.add, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_monadLift, h, map_eq_bind_pure_comp, Function.comp]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a signing query.** The programmed (simulator)
signing handler draws a fresh salt `r ← $ᵗ Salt`, forward-samples a short preimage `s ← domainSample
pk`, programs the random-oracle cache point `(r, msg) ↦ psf.eval pk s`, and returns `(r, s)` (the
preimage record is dropped in the record-free `progGameRunImplNoRec` model). The `.run cache` thus
yields the explicit inline programmed sign body: draw `r`, draw `s`, and pair `(r, s)` with the
programmed cache `cache.cacheQuery (r, msg) (psf.eval pk s)`.

This is the programmed dual of `gpvRealImpl_run_sign`; it is *pinned* to the concrete
`progGameRunImplNoRec` signing handler and is a pure structural unfold. -/
lemma progGameRunImplNoRec_run_sign (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (Sum.inr msg)).run cache =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let s ← (domainSample pk : ProbComp Domain)
        pure ((r, s), cache.cacheQuery (r, msg) (psf.eval pk s))) := by
  simp [progGameRunImplNoRec, HAdd.hAdd, QueryImpl.add, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_monadLift, map_eq_bind_pure_comp, Function.comp, bind_assoc,
    pure_bind]

omit [Fintype Salt] in
/-- **Tier-1 (uniform) tape↔unified bridge — real side.** One uniform query-step of the tape impl
`gpvRealImplTape` equals the corresponding `gpvRealImpl` step with the salt tape carried through
unchanged: both forward the bare `unifSpec.query n` and leave the cache (resp. cache and tape)
untouched. This is the FS template's trivial per-query relating lemma; the tape is a passive
passenger on a uniform query. -/
lemma gpvRealImplTape_run_unif_eq_gpvRealImpl (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run cache := by
  rw [gpvRealImplTape_run_unif, gpvRealImpl_run_unif]; rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Tier-1 (uniform) tape↔unified bridge — programmed side.** One uniform query-step of the
programmed tape impl `progGameRunImplTape` equals the corresponding `progGameRunImplNoRec` step with
the salt tape carried through unchanged. -/
lemma progGameRunImplTape_run_unif_eq_progGameRunImplNoRec (domainSample : PK → ProbComp Domain)
    (pk : PK) (n : unifSpec.Domain) (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run cache := by
  rw [progGameRunImplTape_run_unif, progGameRunImplNoRec_run_unif]; rfl

omit [Fintype Salt] in
/-- **Tier-2 (random-oracle read) tape↔unified bridge — real side.** One random-oracle read
query-step of the tape impl `gpvRealImplTape` equals the corresponding `gpvRealImpl` step with the
salt tape carried through unchanged: both run the *same* lazy `randomOracle` step on the cache
component (`gpvRealImpl` re-emits the read query through `realGameRunImplNoLog` and the outer
`randomOracle` summand answers it), leaving the tape a passive passenger. -/
lemma gpvRealImplTape_run_read_eq_gpvRealImpl (pk : PK) (sk : SK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache := by
  rw [gpvRealImplTape_run_read, gpvRealImpl_run_read]; rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Tier-2 (random-oracle read) tape↔unified bridge — programmed side.** One random-oracle read
query-step of the programmed tape impl `progGameRunImplTape` equals the corresponding
`progGameRunImplNoRec` step with the salt tape carried through unchanged: on a cache hit both return
the recorded value, on a miss both program `psf.eval pk (domainSample pk)` and record it, leaving
the tape untouched. -/
lemma progGameRunImplTape_run_read_eq_progGameRunImplNoRec (domainSample : PK → ProbComp Domain)
    (pk : PK) (mc : Salt × M) (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache := by
  rw [progGameRunImplTape_run_read, progGameRunImplNoRec_run_read]
  cases h : cache mc <;> simp [h, Functor.map_map]

end GPVHashAndSign
