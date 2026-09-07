/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.GameRuns

/-! # GPV Hash-and-Sign: The Front Salt-Tape Factorization

The front salt-tape factorization of the game runs and the direct front-tape
derivation of the Step-1 total-variation bound.
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

/-! ### Front salt-tape factorization

With the per-query tape↔unified bridges in place, the front-tape factorization of each
game run is the `OracleComp.inductionOn (adv.main pk)` mirroring the worked Fiat–Shamir headline
`FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`. Each game run distributes
as a single front draw block `OracleComp.drawList ($ᵗ Salt) qSign` of fresh signing salts followed
by the corresponding *tape-consuming* run (`gpvRealImplTape` / `progGameRunImplTape`) reading each
signing query's salt off the tape head, with the spent tape suffix projected away on output.

Unlike the Fiat–Shamir instance (where each signing query consumes a `maxAttempts`-block), every GPV
signing query consumes *exactly one* salt off the tape head, so the front block has length `qSign`
and the per-signing-query split peels off a single leading salt (`drawList ($ᵗ Salt) 1`). The
non-signing (uniform / random-oracle-read) steps consume *zero* tape and commute trivially past the
front block (the generic answer-irrelevant commute
`OracleComp.DeferredSampling.evalSPMF_step_commute_tape`, fed by the tape↔unified
bridges). -/

omit [Fintype Salt] [DecidableEq Salt] in
/-- **Front salt-tape splits as a leading salt followed by the remaining block.** Drawing a
`drawList ($ᵗ Salt) (n + 1)` front block is the same as drawing one leading salt and then the
remaining `n`-block, consing the leading salt onto the front. This is the GPV (one-salt-per-signing
step) analogue of `FiatShamirWithAbort.drawList_commit_add` at `m = 1`; it peels the head salt that
a single signing query consumes off the over-provisioned front tape. -/
lemma drawList_salt_succ (n : ℕ) :
    OracleComp.drawList ($ᵗ Salt : ProbComp Salt) (n + 1) =
      (do let r ← ($ᵗ Salt : ProbComp Salt)
          let tl ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) n
          pure (r :: tl)) := by
  rfl

omit [Fintype Salt] in
/-- **Real-side signing-step front-tape commute (the crux inductive step).** One real signing
query-step of the unified handler `gpvRealImpl`, composed with the deferred continuation, factors as
a single front draw block `drawList ($ᵗ Salt) (qSrem + 1)` of fresh salts followed by the
tape-consuming `gpvRealImplTape` signing step (reading the head salt) and the tape-threaded
continuation.

The genuine framework content: the leading salt is peeled off the front block by
`drawList_salt_succ` and fed to the tape signing step (consuming the tape head `r :: tl`); the
per-body cache transition of that tape step is exactly the unified `gpvRealImpl` signing step at the
front-loaded salt `r` (the per-body splice `evalSPMF_gpvRealImplTape_sign_cache_eq_gpvStepReal`
reformulated against `gpvRealImpl`); and the continuation's `qSrem`-block (supplied by the inductive
hypothesis `hcont`) commutes past the body via the i.i.d. resampling commute `evalSPMF_bind_comm`.

It is *pinned* to the concrete `gpvRealImpl` / `gpvRealImplTape` handlers and is the signing case of
the real-side front-tape factorization headline
`evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`. -/
theorem evalSPMF_gpvSignStep_commute_real {γ : Type} (pk : PK) (sk : SK) (msg : M)
    (cache : (Salt × M →ₒ Range).QueryCache) (qSrem : ℕ)
    (ob : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (hcont : ∀ (a : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range
          (Sum.inr msg))
        (c' : (Salt × M →ₒ Range).QueryCache),
      𝒮[(simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob a)).run c'] =
        𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
            (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a)).run (c', tape)]) :
    𝒮[(gpvRealImpl psf hr M Salt pk sk (Sum.inr msg)).run cache >>= fun p =>
        (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob p.1)).run p.2] =
      𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) (qSrem + 1) >>= fun tape =>
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
            ((gpvRealImplTape psf M Salt pk sk (Sum.inr msg)).run (cache, tape) >>= fun p =>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2)] := by
  -- Peel the leading salt off both sides: the LHS inline sign body (via `gpvRealImpl_run_sign`)
  -- and the RHS front draw block (via `drawList_salt_succ`) both begin with `r ← $ᵗ Salt`.
  rw [gpvRealImpl_run_sign, drawList_salt_succ]
  simp only [bind_assoc, map_bind, pure_bind]
  refine OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ (fun r => ?_)
  -- Both sides reduce to a common middle form: draw the `qSrem` salt tape, then the random-oracle
  -- answer and the trapdoor preimage `s`, then run the tape continuation `ob (r, s)`.
  -- LHS reaches it by applying `hcont` under the two leading draws and commuting the front block to
  -- the head; RHS by flattening the consumed tape head (`hflat`, no reordering).
  trans 𝒮[do
      let tl ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem
      let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
      let s ← psf.trapdoorSample pk sk p.1
      (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
        (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
  · -- LHS → middle: rewrite the unified continuation by `hcont` under the two leading draws, then
    -- commute the resulting `drawList qSrem` block to the front past the answer-irrelevant draws.
    rw [show 𝒮[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          psf.trapdoorSample pk sk p.1 >>= fun s =>
            (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob (r, s))).run p.2]
        = 𝒮[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          psf.trapdoorSample pk sk p.1 >>= fun s =>
            OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
              (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
      from OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ (fun p =>
        OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ (fun s => hcont (r, s) p.2))]
    -- Commute the innermost `drawList qSrem` past the trapdoor draw (under the random-oracle bind).
    rw [show 𝒮[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          psf.trapdoorSample pk sk p.1 >>= fun s =>
            OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
              (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
        = 𝒮[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
            psf.trapdoorSample pk sk p.1 >>= fun s =>
              (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
      from OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ (fun p =>
        OracleComp.DeferredSampling.evalSPMF_bind_comm
          (psf.trapdoorSample pk sk p.1)
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun s tl =>
            (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)))]
    -- Commute the `drawList qSrem` past the random-oracle draw to the front.
    rw [OracleComp.DeferredSampling.evalSPMF_bind_comm
      ((randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache)
      (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
      (fun p tl => psf.trapdoorSample pk sk p.1 >>= fun s =>
        (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
          (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl))]
  · -- middle → RHS: flatten the consumed tape head `r :: tl` (no reordering needed).
    symm
    have hflat : ∀ (tl : List Salt),
        ((do
            let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
            let s ← psf.trapdoorSample pk sk p.1
            pure (((r, s), p.2, tl) :
              (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt))) >>=
          fun a => (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) =>
              (pp.1, pp.2.1)) <$>
            (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a.1)).run a.2)
          = (do
            let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
            let s ← psf.trapdoorSample pk sk p.1
            (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)) := by
      intro tl; simp only [bind_assoc, pure_bind]
    simp only [gpvRealImplTape_run_sign_cons, map_bind, map_pure]
    exact OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _
      (fun tl => congrArg _ (hflat tl))

omit [Fintype Salt] in
/-- **Real-side front salt-tape factorization (the Fiat–Shamir-template headline, real side).** By
`OracleComp.inductionOn` on the adversary computation `oa`, the unified real run distributes as a
single front draw block `drawList ($ᵗ Salt) qSrem` of fresh signing salts followed by the
tape-consuming real run `gpvRealImplTape`, the spent-tape suffix projected away on output:

`𝒮[(simulateQ gpvRealImpl oa).run cache]`
`  = 𝒮[drawList ($ᵗ Salt) qSrem >>= fun tape => (·.1, ·.2.1) <$> (simulateQ gpvRealImplTape oa).run`
`        (cache, tape)]`,

where `qSrem` bounds the number of signing queries of `oa` (the `(· matches .inr _)` component of
`signHashQueryBound`). At a **pure** step the front block is value-irrelevant and discarded
(never-failing-prefix discard via `OracleComp.probFailure_drawList`); at a **uniform /
random-oracle-read** step the answer is independent of the tape so the front block commutes
trivially past the step (`OracleComp.DeferredSampling.evalSPMF_step_commute_tape`, fed by the
tape↔unified bridges); at a **signing** step the leading salt is peeled off and consumed by
the tape head (`evalSPMF_gpvSignStep_commute_real`).

It is *pinned* to the concrete `gpvRealImpl` / `gpvRealImplTape` handlers; together with the
prog-side dual it puts both game runs in the front-tape form the coupling factors through. -/
theorem evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape {γ : Type} (pk : PK) (sk : SK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (cache : (Salt × M →ₒ Range).QueryCache),
        𝒮[(simulateQ (gpvRealImpl psf hr M Salt pk sk) oa).run cache] =
          𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
              (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) oa).run (cache, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ cache
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
        (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ cache
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: answer independent of the tape; commute the front block past the step.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (gpvRealImpl psf hr M Salt pk sk (Sum.inl (Sum.inl n))).run cache
              = (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)
            from gpvRealImpl_run_unif psf hr M Salt pk sk n cache]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((gpvRealImplTape psf M Salt pk sk (Sum.inl (Sum.inl n))).run (cache, tape)
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : unifSpec.Range n × (Salt × M →ₒ Range).QueryCache =>
                  (p.1, (p.2, tape))) <$>
                  ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)))
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [gpvRealImplTape_run_unif_eq_gpvRealImpl psf hr M Salt pk sk n cache tape,
                gpvRealImpl_run_unif]
              rfl]
        exact OracleComp.DeferredSampling.evalSPMF_step_commute_tape
          ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _))
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob a)).run c')
          (fun a st => (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- READ: answer is the lazy RO step, independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (gpvRealImpl psf hr M Salt pk sk (Sum.inl (Sum.inr mc))).run cache
              = (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache
            from gpvRealImpl_run_read psf hr M Salt pk sk mc cache]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((gpvRealImplTape psf M Salt pk sk (Sum.inl (Sum.inr mc))).run (cache, tape)
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, tape))) <$>
                  (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache)
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [gpvRealImplTape_run_read_eq_gpvRealImpl psf hr M Salt pk sk mc cache tape,
                gpvRealImpl_run_read]
              rfl]
        exact OracleComp.DeferredSampling.evalSPMF_step_commute_tape
          ((randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache)
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob a)).run c')
          (fun a st => (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- SIGN: peel the leading salt; consume the tape head.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalSPMF_gpvSignStep_commute_real psf hr M Salt pk sk msg cache (qSrem - 1) ob
          (fun a c' => ih a (qSrem - 1) (hQ2 a) c')

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Programmed-side signing-step front-tape commute (the crux inductive step, programmed dual).**
One programmed signing query-step of the unified handler `progGameRunImplNoRec`, composed with the
deferred continuation, factors as a single front draw block `drawList ($ᵗ Salt) (qSrem + 1)` of
fresh salts followed by the tape-consuming `progGameRunImplTape` signing step (reading the head
salt) and the tape-threaded continuation.

This is the programmed dual of `evalSPMF_gpvSignStep_commute_real`: the leading salt is peeled off
the front block and fed to the tape signing step (consuming the tape head `r :: tl`); the per-body
cache transition of that tape step is the unified `progGameRunImplNoRec` signing step at the
front-loaded salt `r` (the per-body splice `evalSPMF_progGameRunImplTape_sign_cache_eq_gpvStepProg`
reformulated against `progGameRunImplNoRec`); and the continuation's `qSrem`-block commutes past the
body via the i.i.d. resampling commute `evalSPMF_bind_comm`.

It is *pinned* to the concrete `progGameRunImplNoRec` / `progGameRunImplTape` handlers and is the
signing case of the prog-side headline
`evalSPMF_progGameRunImplNoRec_eq_drawList_progGameRunImplTape`. -/
theorem evalSPMF_gpvSignStep_commute_prog {γ : Type} (domainSample : PK → ProbComp Domain)
    (pk : PK) (msg : M) (cache : (Salt × M →ₒ Range).QueryCache) (qSrem : ℕ)
    (ob : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (hcont : ∀ (a : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range
          (Sum.inr msg))
        (c' : (Salt × M →ₒ Range).QueryCache),
      𝒮[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob a)).run c'] =
        𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
            (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a)).run (c', tape)]) :
    𝒮[(progGameRunImplNoRec psf M Salt domainSample pk (Sum.inr msg)).run cache >>= fun p =>
        (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob p.1)).run p.2] =
      𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) (qSrem + 1) >>= fun tape =>
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
            ((progGameRunImplTape psf M Salt domainSample pk (Sum.inr msg)).run (cache, tape)
              >>= fun p =>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2)] := by
  -- Peel the leading salt off both sides: the LHS inline sign body (via
  -- `progGameRunImplNoRec_run_sign`) and the RHS front draw block (via `drawList_salt_succ`).
  rw [progGameRunImplNoRec_run_sign, drawList_salt_succ]
  simp only [bind_assoc, map_bind, pure_bind]
  refine OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ (fun r => ?_)
  -- Both sides reduce to the drawList-outermost middle form. LHS: apply `hcont` under the
  -- `domainSample` draw, then commute the resulting `drawList qSrem` block to the front. RHS:
  -- flatten the consumed tape head (no reordering).
  trans 𝒮[do
      let tl ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem
      let s ← (domainSample pk : ProbComp Domain)
      (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
        (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob (r, s))).run
          (cache.cacheQuery (r, msg) (psf.eval pk s), tl)]
  · -- LHS → middle: rewrite the unified continuation by `hcont` under the `domainSample` draw,
    -- then commute the `drawList qSrem` block to the front past the `domainSample` draw.
    rw [show 𝒮[(domainSample pk : ProbComp Domain) >>= fun s =>
          (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob (r, s))).run
            (cache.cacheQuery (r, msg) (psf.eval pk s))]
        = 𝒮[(domainSample pk : ProbComp Domain) >>= fun s =>
          OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
            (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob (r, s))).run
                (cache.cacheQuery (r, msg) (psf.eval pk s), tl)]
      from OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _
        (fun s => hcont (r, s) (cache.cacheQuery (r, msg) (psf.eval pk s)))]
    rw [OracleComp.DeferredSampling.evalSPMF_bind_comm
      (domainSample pk : ProbComp Domain)
      (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
      (fun s tl =>
        (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
          (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob (r, s))).run
            (cache.cacheQuery (r, msg) (psf.eval pk s), tl))]
  · -- middle → RHS: flatten the consumed tape head `r :: tl` (no reordering needed).
    symm
    refine OracleComp.DeferredSampling.evalSPMF_bind_congr_left _ _ _ (fun tl => ?_)
    rw [progGameRunImplTape_run_sign_cons]
    exact congrArg _ (bind_map_left
      (fun sd => ((r, sd), cache.cacheQuery (r, msg) (psf.eval pk sd), tl))
      (domainSample pk)
      (fun a => (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
        (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a.1)).run a.2))

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Prog-side front salt-tape factorization (the Fiat–Shamir-template headline, prog side).**
By `OracleComp.inductionOn` on the adversary computation `oa`, the unified programmed run
distributes as a single front draw block `drawList ($ᵗ Salt) qSrem` of fresh signing salts followed
by the tape-consuming programmed run `progGameRunImplTape`, the spent-tape suffix projected away on
output.

This is the programmed dual of `evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`: pure step
discards the value-irrelevant front block; uniform / random-oracle-read steps commute the front
block past the answer-irrelevant step (via the tape↔unified bridges and
`OracleComp.DeferredSampling.evalSPMF_step_commute_tape`); the signing step peels off and consumes
the leading salt (`evalSPMF_gpvSignStep_commute_prog`). It is *pinned* to the concrete
`progGameRunImplNoRec` / `progGameRunImplTape` handlers. -/
theorem evalSPMF_progGameRunImplNoRec_eq_drawList_progGameRunImplTape {γ : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (cache : (Salt × M →ₒ Range).QueryCache),
        𝒮[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) oa).run cache] =
          𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
            (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) oa).run
                (cache, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ cache
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
        (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ cache
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: answer independent of the tape; commute the front block past the step.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (progGameRunImplNoRec psf M Salt domainSample pk (Sum.inl (Sum.inl n))).run cache
              = (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)
            from progGameRunImplNoRec_run_unif psf M Salt domainSample pk n cache]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((progGameRunImplTape psf M Salt domainSample pk (Sum.inl (Sum.inl n))).run
                  (cache, tape) >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : unifSpec.Range n × (Salt × M →ₒ Range).QueryCache =>
                  (p.1, (p.2, tape))) <$>
                  ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)))
                >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [progGameRunImplTape_run_unif_eq_progGameRunImplNoRec psf M Salt domainSample pk n
                  cache tape,
                progGameRunImplNoRec_run_unif]
              rfl]
        exact OracleComp.DeferredSampling.evalSPMF_step_commute_tape
          ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _))
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob a)).run c')
          (fun a st => (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- READ: answer is the programmed RO step, independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((progGameRunImplTape psf M Salt domainSample pk (Sum.inl (Sum.inr mc))).run
                  (cache, tape) >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, tape))) <$>
                (progGameRunImplNoRec psf M Salt domainSample pk (Sum.inl (Sum.inr mc))).run cache)
                >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [progGameRunImplTape_run_read_eq_progGameRunImplNoRec psf M Salt domainSample pk mc
                  cache tape]
              rfl]
        exact OracleComp.DeferredSampling.evalSPMF_step_commute_tape
          ((progGameRunImplNoRec psf M Salt domainSample pk (Sum.inl (Sum.inr mc))).run cache)
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob a)).run c')
          (fun a st => (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- SIGN: peel the leading salt; consume the tape head.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalSPMF_gpvSignStep_commute_prog psf M Salt domainSample pk msg cache (qSrem - 1)
          ob (fun a c' => ih a (qSrem - 1) (hQ2 a) c')

open Classical in
omit [Fintype Salt] in
/-- **Real game-run front-tape factorization (pinned bridge).**

The *pinned* real EUF-CMA game run `realGameRun … adv pk sk` equals a front salt-tape draw
`drawList ($ᵗ Salt) qSign` followed by the tape-consuming real run of `adv.main pk`, with the salt
tape projected away. This is the bridge from the actual game run to the tape-consuming
`gpvRealImplTape` vehicle: it chains the single-impl normalization
`realGameRun_eq_run'_implReal` (`realGameRun … = 𝒮[(simulateQ gpvRealImpl (adv.main pk)).run' ∅]`)
with the front-tape factorization
`evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`
(instantiated at the empty cache, with the signing-query bound supplied by `hQ.1`).

The `StateT.run'` of the single-impl form is `Prod.fst <$> StateT.run`, so the front-tape
factorization — whose tape side is `(·.1, ·.2.1) <$> (… .run (∅, tape))` — composes to the same
`Prod.fst` projection once the (discarded) salt-tape component is dropped. This bridge front-loads
every adaptively-issued signing salt of the real game into one front block, leaving a tape-consuming
run; it is the FS-template factorization pinned to the *actual* game run, and is the prerequisite
for the `drawList`↔`signRunF` step bridge. -/
theorem realGameRun_eq_drawList_gpvRealImplTape (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    realGameRun psf hr M Salt adv pk sk =
      𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= fun tape =>
          (fun p : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.1) <$>
            (simulateQ (gpvRealImplTape psf M Salt pk sk) (adv.main pk)).run
              ((∅ : (Salt × M →ₒ Range).QueryCache), tape)] := by
  classical
  rw [realGameRun_eq_run'_implReal]
  rw [StateT.run']
  refine (evalSPMF_map_eq_of_evalSPMF_eq
    (evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape psf hr M Salt pk sk (adv.main pk) qSign hQ.1
      (∅ : (Salt × M →ₒ Range).QueryCache)) Prod.fst).trans ?_
  rw [map_bind]
  simp only [Functor.map_map]

open Classical in
omit [Fintype Salt] in
/-- **Programmed game-run front-tape factorization (pinned bridge).**

The *pinned* randomized sign-then-hash game run `progGameRun … adv domainSample pk` equals a front
salt-tape draw `drawList ($ᵗ Salt) qSign` followed by the tape-consuming programmed run of
`adv.main pk`, with the salt tape projected away. The programmed dual of
`realGameRun_eq_drawList_gpvRealImplTape`: it chains the record-free normalization
`progGameRun_eq_run'_implNoRec` with the programmed front-tape factorization
`evalSPMF_progGameRunImplNoRec_eq_drawList_progGameRunImplTape`
(signing bound from `hQ.1`). Together
the two bridges put both pinned game runs into the identical front-tape
`drawList ($ᵗ Salt) qSign >>= (tape-consuming run)` shape, the prerequisite for the
`drawList`↔`signRunF` step bridge. -/
theorem progGameRun_eq_drawList_progGameRunImplTape (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    progGameRun psf hr M Salt adv domainSample pk =
      𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= fun tape =>
          (fun p : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.1) <$>
            (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (adv.main pk)).run
              ((∅ : (Salt × M →ₒ Range).QueryCache), tape)] := by
  classical
  rw [progGameRun_eq_run'_implNoRec]
  rw [StateT.run']
  refine (evalSPMF_map_eq_of_evalSPMF_eq
    (evalSPMF_progGameRunImplNoRec_eq_drawList_progGameRunImplTape psf M Salt domainSample pk
      (adv.main pk) qSign hQ.1 (∅ : (Salt × M →ₒ Range).QueryCache)) Prod.fst).trans ?_
  rw [map_bind]
  simp only [Functor.map_map]

/-! ## Front-tape ingredients for the Step-1 TV bound

The pieces below are the tape-route ingredients for `gpv_tvDist_real_programmed_le_collisionBound`,
starting from the front-tape factorization (`realGameRun_eq_drawList_gpvRealImplTape` /
`progGameRun_eq_drawList_progGameRunImplTape`). They are not the route by which that bound is
proved: `GameIdentification.lean` derives it from the original-run reduction
`gpv_tvDist_orig_run_le_probEvent_flag` and the telescope `gpv_orig_flag_le_collisionBound`, with
every salt drawn inline. The tape-route coupling headline — a bound on the tape-averaged TV between
the real and programmed tape-consuming runs directly by `(collisionBound …).toReal` — is not
established in this development.

After the front-tape factorization both pinned game runs are `drawList ($ᵗ Salt) qSign` followed by
the tape-consuming run of `adv.main pk`. The tape route would bound the TV distance by:

* **(C) data processing** — `tvDist_drawList_bind_le` reduces the TV of the two factored runs to the
  expectation over the front salt tape of the per-tape TV distance (`tvDist_bind_left_le`).
* **(A) per-tape identical-until-bad** — the tape-averaged TV between the real and programmed
  tape-consuming runs of `adv.main pk` over the front tape, bounded by `(collisionBound …).toReal`.
  The per-tape bad event is a fresh tape salt hitting the actual running random-oracle cache; its
  salt-averaged probability telescopes to `collisionBound`. The per-step no-bad-path agreements
  below (`gpvImplTape_run_unif_eq`, `gpvImplTape_run_read_hit_eq`,
  `evalSPMF_gpvImplTape_run_read_miss_eq`, `gpvImplTapeFlag_h_agree_good`) are its ingredients.

The salt-tape birthday infrastructure (`tapeCheck`, `drawList_tapeCheck_eq_saltSeq`,
`probEvent_tapeCheck_drawList_le_collisionBound`) records the explicit-list form of the
salt-averaged `saltSeq` telescope; it is the analytic tool the run-level collision-flag charge of
`(A)` would reduce to via the flag-instrumented inductive coupling. -/

/-- **Salt-tape collision check.** `tapeCheck c n tape` is the explicit-list analogue of the
salt-averaged `saltSeq` disjunction: it reports `true` iff some head salt of the front `n`-block
tape `tape` lands in its recorded cache slice `c j`. The head salt of an `(n + 1)`-block is checked
against `c n` (mirroring `saltSeq`'s leading `decide (r ∈ c n)`), and the tail recurses on the
remaining `n`-block. On a tape shorter than `n` the missing entries are treated as non-colliding
(`false`), which never occurs for tapes drawn by `drawList ($ᵗ Salt) n`. -/
def tapeCheck (c : ℕ → Finset Salt) : ℕ → List Salt → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | n + 1, r :: tl => decide (r ∈ c n) || tapeCheck c n tl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **The tape-check process equals the salt-averaged `saltSeq` process.** Drawing a front salt tape
`drawList ($ᵗ Salt) n` and reporting its `tapeCheck` collision flag is the *same computation* as the
salt-averaged `saltSeq c n`: both draw `n` fresh uniform salts and OR together, at each step `j`,
the indicator that the `j`-th salt lands in `c j`. Proved by induction on `n`, matching `drawList`'s
head-cons recursion against `saltSeq`'s leading-draw recursion. -/
theorem drawList_tapeCheck_eq_saltSeq (c : ℕ → Finset Salt) (n : ℕ) :
    (do let tape ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) n
        pure (tapeCheck Salt c n tape)) = saltSeq (Salt := Salt) c n := by
  induction n with
  | zero => simp [OracleComp.drawList, tapeCheck, saltSeq]
  | succ n ih =>
      rw [OracleComp.drawList, saltSeq]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      rw [← ih]
      simp only [bind_assoc, pure_bind, tapeCheck]

omit [DecidableEq Range] [SampleableType Range] in
/-- **(B) drawList salt-tape birthday bound.** The probability that a front salt tape drawn by
`drawList ($ᵗ Salt) qSign` reports a `tapeCheck` collision is bounded by
`collisionBound Salt qSign qHash`, whenever the recorded cache slices satisfy the growth bound
`card (c j) ≤ j + qHash`.

This is the front-tape analogue of `probEvent_saltSeq_le_collisionBound`: it transports the
salt-averaged telescope to the explicit front-tape vehicle via `drawList_tapeCheck_eq_saltSeq`. It
is the birthday term charged by the data-processing reduction `(C)` against the per-tape
identical-until-bad coupling `(A)`. -/
theorem probEvent_tapeCheck_drawList_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    Pr[(· = true) | (do let tape ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign
                        pure (tapeCheck Salt c qSign tape))]
      ≤ collisionBound Salt qSign qHash := by
  rw [drawList_tapeCheck_eq_saltSeq]
  exact probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache

omit [DecidableEq Salt] [Fintype Salt] in
/-- **(C) Data-processing reduction for the factored game runs.** Given that both pinned game runs
have been put into the front-tape form `realGameRun = 𝒮[drawList ($ᵗ Salt) qSign >>= freal]` and
`progGameRun = 𝒮[drawList ($ᵗ Salt) qSign >>= fprog]` (supplied by the bridges
`realGameRun_eq_drawList_gpvRealImplTape` / `progGameRun_eq_drawList_progGameRunImplTape`), the TV
distance between the game runs is bounded by the expectation, over the front salt tape, of the
per-tape TV distance between the two tape-consuming runs.

This is the front-tape instance of the generic data-processing bound `tvDist_bind_left_le`: binding
two continuations over a common base computation (the salt tape `drawList ($ᵗ Salt) qSign`) costs at
most the tape-averaged per-fibre TV distance. It reduces the run-level coupling to the per-tape
identical-until-bad coupling `(A)`, whose tape-averaged charge is bounded by the birthday term
`(B)`. -/
theorem tvDist_drawList_bind_le {β : Type} (qSign : ℕ) (freal fprog : List Salt → ProbComp β)
    (realRun progRun : SPMF β)
    (hreal : realRun = 𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= freal])
    (hprog : progRun = 𝒮[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= fprog]) :
    SPMF.tvDist realRun progRun
      ≤ ∑' tape : List Salt,
          Pr[= tape | OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign].toReal *
            tvDist (freal tape) (fprog tape) := by
  subst hreal hprog
  exact tvDist_bind_left_le (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign) freal fprog

omit [DecidableEq Range] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] in
/-- **First marginal of the PSF regularity witness (the `hreg`-substitution bridge).**

PSF regularity `hreg` equates the *joint* distributions of the `(image, preimage)` pairs produced
by the forward sampler `domainSample` (programmed side) and by uniform-target trapdoor sampling
(real side). The programmed random oracle answers a cache miss with `psf.eval pk (domainSample pk)`,
while the real (lazy) random oracle answers with a fresh uniform `$ᵗ Range`; off the collision, the
two tape-consuming GPV runs diverge *only* in this answer. This lemma extracts exactly the *first
marginal* of `hreg` needed to identify those two answer distributions: the programmed answer
`psf.eval pk (domainSample pk)` is distributed uniformly on `Range`.

The trapdoor-sampler suffix `s ← psf.trapdoorSample pk sk c` on the real side is discarded using its
totality (`hNF : NeverFail`), so the real first marginal collapses to the bare uniform draw
`$ᵗ Range`. This is the per-step off-collision answer agreement underlying the tape-route
identical-until-bad coupling `(A)`: it is the distributional (not pointwise)
agreement of the real and programmed random-oracle answers that the identical-until-bad
machinery consumes as its no-bad-path agreement hypothesis. -/
theorem evalSPMF_eval_domainSample_eq_uniform (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    𝒮[(do let s ← domainSample pk; pure (psf.eval pk s) : ProbComp Range)] =
      𝒮[($ᵗ Range : ProbComp Range)] := by
  have h := congrArg (Functor.map (Prod.fst : Range × Domain → Range)) hreg
  simp only [← evalSPMF_map, map_bind, map_pure] at h
  rw [h]
  have hinner : ∀ a : Range,
      𝒮[(do let _ ← psf.trapdoorSample pk sk a; pure a : ProbComp Range)] =
        𝒮[(pure a : ProbComp Range)] := by
    intro a
    refine evalSPMF_ext fun y => ?_
    rw [probOutput_bind_const, (hNF a).probFailure_eq_zero]
    simp
  calc 𝒮[(do let a ← ($ᵗ Range); let _ ← psf.trapdoorSample pk sk a; pure a : ProbComp Range)]
      = 𝒮[((($ᵗ Range) >>= pure) : ProbComp Range)] :=
        evalSPMF_bind_congr' _ fun a => hinner a
    _ = 𝒮[($ᵗ Range : ProbComp Range)] := by rw [bind_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off-bad agreement of the two tape handlers on a uniform query.** The uniform-query branch of
`gpvRealImplTape` and `progGameRunImplTape` are *literally identical*: both run the bare uniform
sample on the random component and leave the cache and the salt tape untouched.

This is the trivial "free query" case of the per-step no-bad-path agreement underlying the
tape-route identical-until-bad coupling `(A)`: the two
tape-consuming GPV runs never diverge on a uniform query, so it contributes no charge to the bad
event. -/
theorem gpvImplTape_run_unif_eq (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (n : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run s =
      (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run s := by
  rw [gpvRealImplTape_run_unif, progGameRunImplTape_run_unif]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off-bad agreement of the two tape handlers on a random-oracle read at a cached key.** On a
cache *hit* `s.1 mc = some v`, the random-oracle-read branch of `gpvRealImplTape` and
`progGameRunImplTape` are *literally identical*: the real (lazy) oracle returns the recorded value
without touching the cache, and the programmed oracle likewise returns the recorded value; both
leave the salt tape untouched.

This is the "cached read" free case of the per-step no-bad-path agreement underlying the
tape-route identical-until-bad coupling `(A)`: a read that hits the
cache returns the same recorded answer on both sides (the divergence between the lazy and programmed
oracles can only arise on a *miss*, where a fresh answer is sampled). -/
theorem gpvImplTape_run_read_hit_eq (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (mc : Salt × M) (s : (Salt × M →ₒ Range).QueryCache × List Salt) (v : Range)
    (hhit : s.1 mc = some v) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s =
      (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s := by
  rw [gpvRealImplTape_run_read, progGameRunImplTape_run_read, hhit]
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1 = pure (v, s.1)
      from QueryImpl.withCaching_run_some uniformSampleImpl hhit]
  simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off-bad distributional agreement of the two tape handlers on a random-oracle read at a fresh
key (the `hreg`-substitution bridge, read case).** On a cache *miss* `s.1 mc = none`, the real
(lazy) random oracle answers with a fresh uniform target `$ᵗ Range`, while the programmed oracle
answers with `psf.eval pk (domainSample pk)`. By the first marginal of PSF regularity
(`evalSPMF_eval_domainSample_eq_uniform`) these two answer distributions coincide, and both handlers
apply the *same* deterministic post-processing of the answer (record it at `mc` in the cache and
return it, salt tape untouched). Hence the two tape handlers' read-on-miss transitions agree as
output distributions.

This is the genuinely distributional (not pointwise) per-step no-bad-path agreement underlying the
tape-route identical-until-bad coupling `(A)`: it is the
read-query case
of the `hreg`-substitution bridge that the identical-until-bad machinery consumes as its
no-bad agreement hypothesis. The lazy-vs-programmed *answer* divergence is invisible to the output
distribution off the collision; it becomes observable only when the freshly recorded key later
collides with a tape salt — which is exactly the bad event `tapeCheck` charges. -/
theorem evalSPMF_gpvImplTape_run_read_miss_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) (hmiss : s.1 mc = none)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒮[(gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s] =
      𝒮[(progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s] := by
  rw [gpvRealImplTape_run_read, progGameRunImplTape_run_read, hmiss]
  simp only []
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1
        = (fun u => (u, s.1.cacheQuery mc u)) <$> ($ᵗ Range : ProbComp Range)
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  have hfst := evalSPMF_eval_domainSample_eq_uniform psf pk sk domainSample hNF hreg
  set g : Range → Range × ((Salt × M →ₒ Range).QueryCache × List Salt) :=
    fun u => (u, (s.1.cacheQuery mc u, s.2)) with hg
  have hLHS : 𝒮[((fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, p.2, s.2)) <$>
            (fun u => (u, s.1.cacheQuery mc u)) <$> ($ᵗ Range : ProbComp Range))]
        = 𝒮[g <$> ($ᵗ Range : ProbComp Range)] := by rw [Functor.map_map]
  have hRHS : 𝒮[((fun sd => (psf.eval pk sd, s.1.cacheQuery mc (psf.eval pk sd), s.2)) <$>
            (domainSample pk : ProbComp Domain))]
        = 𝒮[g <$> (do let sd ← domainSample pk; pure (psf.eval pk sd) : ProbComp Range)] := by
    refine congrArg _ ?_
    rw [map_eq_bind_pure_comp]
    simp only [hg, map_bind, map_pure, Function.comp_def]
  exact hLHS.trans ((evalSPMF_map_eq_of_evalSPMF_eq hfst.symm g).trans hRHS.symm)

omit [DecidableEq Range] [Fintype Salt] in
open Classical in
/-- **Universal off-bad per-query agreement of the two flag-instrumented tape handlers (the
framework `h_agree_good`).** For *every* query `t` and *every* off-bad input state `(s, false)`,
the two flag handlers `gpvRealImplTapeFlag` / `progGameRunImplTapeFlag` assign equal probability to
every *off-bad output* `(u, (s', false))`.

This is the exact `h_agree_good` hypothesis of the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad`, made **universal** by the empty-tape-fires-the-flag
tweak in the flag handlers: the only state where the underlying tape handlers disagree off-flag is
the *empty-tape signing* state (where the underlying handler falls back to an inline fresh salt
draw); firing the flag there places that state inside the bad set, so on every off-bad output the
flag value is `false` exactly when the head salt is present and unkeyed — precisely the case the
per-query agreements (`gpvImplTape_run_unif_eq` for uniform, `gpvImplTape_run_read_hit_eq` /
`evalSPMF_gpvImplTape_run_read_miss_eq` for random-oracle reads, and
`evalSPMF_gpvImplTapeFlag_run_sign_offbad_eq` for unkeyed-head signing) cover. The flag bookkeeping
is `probOutput_flagTag_false`: where the flag fires the off-bad output probability is `0` on both
sides; where it stays `false` the two flagged steps reduce to their agreeing underlying steps.

It is *true-as-stated* and *pinned* to the concrete flag handlers (no free parameters); it is the
off-collision no-divergence ingredient the tape-route identical-until-bad coupling `(A)` would
consume (the cardinality telescope bounds the run-level flag probability by `collisionBound`). -/
theorem gpvImplTapeFlag_h_agree_good (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt)
    (u : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t)
    (s' : (Salt × M →ₒ Range).QueryCache × List Salt) :
    Pr[= (u, (s', false)) | (gpvRealImplTapeFlag psf M Salt pk sk t).run (s, false)]
      = Pr[= (u, (s', false)) |
          (progGameRunImplTapeFlag psf M Salt domainSample pk t).run (s, false)] := by
  cases t with
  | inl q =>
      -- Non-signing query: flag is passive (`F = false`), reduce to the underlying tape agreement.
      rw [gpvRealImplTapeFlag_run_inl, progGameRunImplTapeFlag_run_inl]
      rw [probOutput_flagTag_false, probOutput_flagTag_false, if_pos rfl, if_pos rfl]
      cases q with
      | inl n =>
          -- Uniform query: the two underlying handlers are literally identical.
          rw [gpvImplTape_run_unif_eq psf M Salt pk sk domainSample n s]
      | inr mc =>
          -- Random-oracle read: cache hit ⇒ identical; cache miss ⇒ agree by `hreg`.
          rcases h : s.1 mc with _ | v
          · exact probOutput_congr rfl
              (evalSPMF_gpvImplTape_run_read_miss_eq psf M Salt pk sk domainSample mc s h hNF hreg)
          · rw [gpvImplTape_run_read_hit_eq psf M Salt pk sk domainSample mc s v h]
  | inr msg =>
      -- Signing query: split on the tape.  Empty tape or keyed head ⇒ flag fires ⇒ both `0`.
      rw [gpvRealImplTapeFlag_run_inr, progGameRunImplTapeFlag_run_inr]
      rw [probOutput_flagTag_false, probOutput_flagTag_false]
      simp only [Bool.false_or]
      cases htape : s.2 with
      | nil =>
          -- Empty tape: the flag fires (`true`), both `false`-outputs have probability `0`.
          simp only [reduceCtorEq, if_false]
      | cons r tl =>
          -- Non-empty tape head `r`: split on whether it is already keyed.
          rcases hkey : saltKeyed M Salt s.1 r with _ | _
          · -- Unkeyed head: flag stays `false`; reduce to the underlying signing-miss agreement.
            simp only [hkey, if_true]
            have hmiss : s.1 (r, msg) = none := (saltKeyed_eq_false_iff M Salt s.1 r).1 hkey msg
            -- The underlying tape steps agree off-collision (joint `hreg` substitution).
            rw [show s = (s.1, r :: tl) from by rw [← htape]]
            exact probOutput_congr rfl
              (evalSPMF_gpvImplTape_run_sign_miss_eq psf M Salt pk sk domainSample
                msg r tl s.1 hmiss hreg)
          · -- Keyed head: the flag fires (`true`), both `false`-outputs have probability `0`.
            simp only [hkey, reduceCtorEq, if_false]

end GPVHashAndSign
