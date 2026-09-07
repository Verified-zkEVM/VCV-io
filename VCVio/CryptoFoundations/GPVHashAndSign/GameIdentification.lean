/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.CombinedHandler

/-! # GPV Hash-and-Sign: Game Identification

The cross-monad WriterT-log to signed-set run reconstruction, the verify-Bool
games on the freshness-tracking vehicle, the state-threading bridge from the
runtime to the bare random oracle, the U2 sign-then-hash hop up to the
programming bad event, and the Step-1 wiring toward the headline bounds.
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

/-! ### Cross-monad WriterT-log → signed-set reconstruction

The unforgeability experiment runs the adversary under the WriterT signing-log handler stack
`baseW + signingOracle pk sk` (logging each signing query) inside the runtime's
`withStateOracle randomOracle ∅` bundle, and its winning Bool reads the freshness mask
`!log.wasQueried msg` off the WriterT log.  The freshness vehicle `gpvRealImplFresh` instead
threads a `Finset M` signed-set through the random-oracle `StateT QueryCache ProbComp` surface.
The lemmas in this block reconstruct the WriterT log as that signed-set, identifying the two runs
across the WriterT/StateT monad divide.  The route mirrors the FiatShamir kernel inside
`FiatShamirWithAbort.probOutput_unforgeableExp_eq_hybridExpAtKey_real`: fuse the inner WriterT pass
with the outer cache simulation (`writerTMapBase`), replay the WriterT log into a `StateT (List M)`
input log (`appendInputLog`), flatten the nested `StateT` (`flattenStateT`), and project the
flattened handler onto `gpvRealImplFresh` with the signed-set reconstructed as the logged messages'
`toFinset`. -/

/-- **The fused real WriterT handler over the random-oracle cache.** The signing handler of the
unforgeability experiment, with the public/random-oracle base simulated by the runtime's
`withStateOracle` interpreter (`outerLift + randomOracle` over `StateT QueryCache ProbComp`).  This
is the GPV analogue of FiatShamir's fused `base.writerTMapBase implW`: it equals
`baseW + withLogging signBody`, where `signBody msg = gpvRealImpl … (Sum.inr msg)` is the real GPV
signing body run on the cache (`reconstructImplW_eq`). -/
@[expose] noncomputable def gpvOuter :
    QueryImpl (unifSpec + (Salt × M →ₒ Range))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
    (randomOracle : QueryImpl (Salt × M →ₒ Range)
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))

omit [Fintype Salt] in
/-- **`gpvRealImpl` is `gpvOuter ∘ₛ realGameRunImplNoLog`.** Restates the definition of
`gpvRealImpl` in terms of the named base handler `gpvOuter`. -/
lemma gpvRealImpl_eq_compose (pk : PK) (sk : SK) :
    gpvRealImpl psf hr M Salt pk sk =
      (gpvOuter M Salt ∘ₛ realGameRunImplNoLog psf hr M Salt pk sk) := rfl

omit [Fintype Salt] in
/-- **The base (non-signing) step of `gpvRealImpl` is `gpvOuter`.** On a public/random-oracle
query `Sum.inl q`, the composed real handler re-emits the query through `realGameRunImplNoLog`
(`= query q`) and the `gpvOuter` simulation answers it, so `gpvRealImpl … (Sum.inl q) = gpvOuter q`.
-/
lemma gpvRealImpl_inl_eq_gpvOuter (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain) :
    gpvRealImpl psf hr M Salt pk sk (Sum.inl q) = gpvOuter M Salt q := by
  simp only [gpvRealImpl_eq_compose, QueryImpl.compose, realGameRunImplNoLog, HAdd.hAdd,
    QueryImpl.add, HasQuery.toQueryImpl_apply, HasQuery.query]
  exact simulateQ_spec_query (gpvOuter M Salt) q

open Classical in
omit [Fintype Salt] in
/-- **Handler fusion: the fused WriterT stack is `baseW + withLogging signBody`.** Pushing the
runtime's `withStateOracle` interpreter `gpvOuter` through the base monad of the unforgeability
experiment's WriterT handler stack `baseW + signingOracle pk sk` (via `writerTMapBase`) yields the
WriterT handler `baseW' + withLogging signBody` over `StateT QueryCache ProbComp`, where the
public/random-oracle base re-emits its query through the cache (`baseW'`) and the signing body is
the real GPV signing computation run on the cache (`signBody msg = gpvRealImpl … (Sum.inr msg)`).
This is the GPV analogue of the FiatShamir `hHandler` step. -/
lemma gpvOuter_writerTMapBase_implW (pk : PK) (sk : SK) :
    (gpvOuter M Salt).writerTMapBase
        ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk) =
      (gpvOuter M Salt).liftTarget
          (WriterT (QueryLog (M →ₒ (Salt × Domain)))
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) +
        QueryImpl.withLogging
          (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
            QueryImpl (M →ₒ (Salt × Domain))
              (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) := by
  funext t
  rcases t with bq | sq
  · -- public/random-oracle base query: `writerTMapBase` runs the lifted query through `gpvOuter`.
    ext s
    simp only [QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.toHasQuery_query, WriterT.mk, HasQuery.toQueryImpl_apply]
    rfl
  · -- signing query: `signingOracle = withLogging sign`; `(withLogging sign sq).run = sign sq >>=
    -- fun u => (u, [⟨sq, u⟩])` re-emits the log, so the fused LHS commutes the monad-morphism
    -- `simulateQ gpvOuter` through that base bind, and the RHS `withLogging` of `gpvRealImpl`
    -- (`= simulateQ gpvOuter ∘ sign` by the `∘ₛ` definition) is the same bind.
    ext s
    -- `gpvRealImpl … (Sum.inr msg) = simulateQ gpvOuter ((GPVHashAndSign …).sign pk sk msg)` holds
    -- definitionally (the `∘ₛ` definition), so expanding both `withLogging` bodies and commuting
    -- the monad-morphism `simulateQ gpvOuter` through the `sign >>= fun u => (u, [⟨sq, u⟩])` bind
    -- aligns the two runs.  Mirrors the FiatShamir `fsBaseImpl_writerTMapBase_signingOracle_eq`
    -- signing case.
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle, QueryImpl.withLogging_apply,
      GPVHashAndSign, gpvRealImpl, gpvOuter, QueryImpl.compose, realGameRunImplNoLog,
      QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_pure, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, WriterT.run_pure, map_eq_bind_pure_comp]
    simp only [HAdd.hAdd, QueryImpl.add, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, Function.comp_def]

omit [Fintype Salt] in
/-- **Per-query state-projection of the flattened append-log handler onto `gpvRealImplFresh`.**
The flattened `StateT (List M × QueryCache)` handler — the lifted public/random-oracle base plus the
`appendInputLog`-instrumented GPV signing body `gpvRealImpl … (Sum.inr ·)` — projects, under
`proj (l, c) = (c, l.toFinset)`, onto the freshness vehicle `gpvRealImplFresh` step by step.  On a
non-signing query both leave the signed-set untouched and evolve the cache through `gpvRealImpl`; on
a signing query `appendInputLog` appends `msg` to the list (`l ++ [msg]`) while `gpvRealImplFresh`
inserts it into the signed-set, reconciled by `(l ++ [msg]).toFinset = insert msg l.toFinset` (the
list-order is invisible to the `Finset`).  This is the per-query hypothesis of the state-projection
transport `map_run_simulateQ_eq_of_query_map_eq`, the GPV analogue of the FiatShamir `hmatch`. -/
lemma flattenAppendLog_proj_gpvRealImplFresh (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : List M × (Salt × M →ₒ Range).QueryCache) :
    Prod.map id (fun s : List M × (Salt × M →ₒ Range).QueryCache => (s.2, s.1.toFinset)) <$>
        ((((gpvOuter M Salt).liftTarget
              (StateT (List M) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))) +
            QueryImpl.appendInputLog
              (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
                QueryImpl (M →ₒ (Salt × Domain))
                  (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))).flattenStateT t).run s =
      (gpvRealImplFresh psf hr M Salt pk sk t).run (s.2, s.1.toFinset) := by
  obtain ⟨l, c⟩ := s
  cases t with
  | inl q =>
      -- public/random-oracle base query: the list is untouched, the cache evolves through
      -- `gpvRealImpl`; both sides drop to the same base step `gpvOuter q = gpvRealImpl … (inl q)`.
      rw [gpvRealImplFresh_run_inl, gpvRealImpl_inl_eq_gpvOuter]
      simp only [QueryImpl.flattenStateT, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        StateT.run_mk, Prod.map, id_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_def]
      -- `(liftM (gpvOuter q)).run l = gpvOuter q >>= fun a => (a, l)` is definitional; rephrase the
      -- nested lifted run so the cache run distributes and the list rides through unchanged.
      change ((gpvOuter M Salt q >>= fun a => pure (a, l)).run c >>= fun x =>
          pure (x.1.1, x.2, x.1.2.toFinset)) = _
      rw [StateT.run_bind]
      simp only [StateT.run_pure, bind_assoc, pure_bind]
      rfl
  | inr msg =>
      -- signing query: `appendInputLog` appends `msg` to the list, `gpvRealImplFresh` inserts it
      -- into the signed-set, reconciled by `(l ++ [msg]).toFinset = insert msg l.toFinset`.
      rw [gpvRealImplFresh_run_inr]
      -- Normalize the logging/caching handler stack, splice in the explicit sign body via
      -- `gpvRealImpl_run_sign` under the outer projection, and renormalize; the appended log
      -- entry `(l ++ [msg]).toFinset = insert msg l.toFinset` reconciles the signed-set.
      simp only [OracleSpec.add_apply_inr, QueryImpl.add_apply_inr, QueryImpl.flattenStateT,
        QueryImpl.appendInputLog_apply, StateT.run_bind, StateT.run_modify,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, pure_bind, StateT.run_map,
        Functor.map_map, StateT.run_mk, Prod.map_apply, id_eq, List.toFinset_append,
        List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.union_singleton,
        QueryImpl.withCaching_apply, StateT.run_get]
      refine Eq.trans (congrArg _ (gpvRealImpl_run_sign psf hr M Salt pk sk msg c)) ?_
      simp only [OracleSpec.add_apply_inr, QueryImpl.withCaching_apply,
        StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp, map_bind, Functor.map_map]

omit [Fintype Salt] in
/-- **Cross-monad WriterT-log → signed-set run reconstruction.** Running `oa` under the
unforgeability experiment's WriterT signing-log handler stack `baseW + signingOracle pk sk`, then
interpreting its base random-oracle queries through the runtime's `withStateOracle` cache
(`gpvOuter`) and mapping the result to `(output, (log.map fst).toFinset, cache)`, coincides with the
freshness vehicle `gpvRealImplFresh` run started from `(∅, ∅), false`, projected to drop the passive
collision flag.

This is the kernel of the freshness game-identification (N)(a): it identifies the WriterT signing
log of `unforgeableExp` with the `Finset M` signed-set carried by `gpvRealImplFresh`, across the
WriterT/StateT monad divide.  The proof chains the reconstruction pieces, mirroring the
FiatShamir `probOutput_unforgeableExp_eq_hybridExpAtKey_real` kernel:
`simulateQ_writerTMapBase_run` + `gpvOuter_writerTMapBase_implW` (fuse the inner WriterT pass with
the outer cache simulation into `baseW' + withLogging signBody`),
`map_run_withLogging_inputs_eq_run_appendInputLog` (replay the WriterT log into a `StateT (List M)`
input log, `initialInputs = []`), `simulateQ_flattenStateT_run` (flatten the nested `StateT`), and
`flattenAppendLog_proj_gpvRealImplFresh` via `map_run_simulateQ_eq_of_query_map_eq` (project onto
`gpvRealImplFresh`, the signed-set reconstructed as the logged messages' `toFinset`). -/
lemma map_simulateQ_gpvOuter_writerLog_eq_gpvRealImplFresh (pk : PK) (sk : SK) {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    (fun z : (β × QueryLog (M →ₒ (Salt × Domain))) × (Salt × M →ₒ Range).QueryCache =>
        (z.1.1, z.2, (z.1.2.map (fun e => e.1)).toFinset)) <$>
        (simulateQ (gpvOuter M Salt)
          ((simulateQ
              ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                  (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                    (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                  psf hr M Salt).signingOracle pk sk)
              oa).run)).run (∅ : (Salt × M →ₒ Range).QueryCache)
      = (fun z : β × ((Salt × M →ₒ Range).QueryCache × Finset M) =>
          (z.1, z.2.1, z.2.2)) <$>
        (simulateQ (gpvRealImplFresh psf hr M Salt pk sk) oa).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)) := by
  classical
  -- The fused base `gpvOuter.liftTarget (WriterT …)` is `(HasQuery.toQueryImpl).liftTarget` for the
  -- `HasQuery` instance `gpvOuter.toHasQuery`; provide it so the replay lemma's `baseW` matches.
  let hq : HasQuery (unifSpec + (Salt × M →ₒ Range))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) := (gpvOuter M Salt).toHasQuery
  -- (1) Fuse the inner WriterT pass with the outer cache simulation `gpvOuter` via
  -- `writerTMapBase`, and rewrite the fused handler as `baseW' + withLogging signBody`.
  rw [QueryImpl.simulateQ_writerTMapBase_run, gpvOuter_writerTMapBase_implW]
  -- (2) Replay the WriterT log into a `StateT (List M)` input log starting from `[]`.
  have hreplay := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + (Salt × M →ₒ Range)) (loggedSpec := M →ₒ (Salt × Domain))
    (m₀ := StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)
    (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg)) oa ([] : List M)
  simp only [List.nil_append] at hreplay
  -- Apply the run, flatten the nested `StateT (List M) (StateT cache)`, and project to
  -- `gpvRealImplFresh` via the per-query `hmatch`.
  have hflatten := OracleComp.simulateQ_flattenStateT_run
    ((gpvOuter M Salt).liftTarget
        (StateT (List M) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) +
      QueryImpl.appendInputLog
        (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
          QueryImpl (M →ₒ (Salt × Domain))
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
    oa ([] : List M) (∅ : (Salt × M →ₒ Range).QueryCache)
  have hflat := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (((gpvOuter M Salt).liftTarget
        (StateT (List M) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) +
      QueryImpl.appendInputLog
        (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
          QueryImpl (M →ₒ (Salt × Domain))
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))).flattenStateT)
    (gpvRealImplFresh psf hr M Salt pk sk)
    (fun s : List M × (Salt × M →ₒ Range).QueryCache => (s.2, s.1.toFinset))
    (flattenAppendLog_proj_gpvRealImplFresh psf hr M Salt pk sk) oa
    (([], ∅) : List M × (Salt × M →ₒ Range).QueryCache)
  -- Rewrite the RHS `gpvRealImplFresh` run via `hflat` (the state-projection of the flattened
  -- append-log run), then `hflatten` (flatten = nested run) and `hreplay` (WriterT log → input
  -- list), reducing both sides to the same base computation; the three maps compose pointwise.
  simp only [List.toFinset_nil] at hflat
  rw [← hflat, Functor.map_map, hflatten]
  -- The fused base `HasQuery.toQueryImpl` (for the instance `hq := gpvOuter.toHasQuery`) is exactly
  -- `gpvOuter`, so the replay lemma's base matches the flattened run's base.
  have hbase : (@HasQuery.toQueryImpl _ (unifSpec + (Salt × M →ₒ Range))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) hq) = gpvOuter M Salt := rfl
  -- The flattened nested run (RHS, via `hflat`/`hflatten`) and the replayed WriterT-log input-list
  -- run (`hreplay`, applied at the cache `∅`) are the same base computation; the maps compose.
  have hreplay' := congrArg
    (fun (g : StateT ((Salt × M →ₒ Range).QueryCache) ProbComp _) => g.run ∅) hreplay
  simp only [StateT.run_map, hbase] at hreplay'
  rw [← hreplay']
  simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq]

/-! ### Verify-Bool games on the freshness-tracking vehicle

The verification read `gpvVerifyRead` recomputes the random-oracle value at the forged `(r, msg)`
and checks `eval pk s = c ∧ isShort s` — the GPV `verify` body, phrased over the sum spec as a
single random-oracle query (zero signing queries).  Appended after `adv.main pk` on the
freshness-tracking vehicle, it reads against the *shared* random-oracle cache (so a forgery on a
cached programmed point is observed) and the resulting state still carries the signed-set, so the
winning Bool can apply the EUF-CMA freshness mask (the forged message not being among the signed
messages).  These are the two
`SPMF Bool` games the fresh verify-Bool coupling `gpv_tvDist_orig_verify_fresh_le_collisionBound`
relates within `collisionBound`. -/

/-- **GPV verification read (sum-spec, signing-free).** On a forgery `out = (msg, (r, s))`, query
the random oracle at `(r, msg)` and return `eval pk s = c ∧ isShort s` — the `verify` body of the
GPV scheme phrased as a single random-oracle query into the sum spec.  It issues exactly one
random-oracle query and *no* signing query, so it is a valid signing-free continuation for the
verify-Bool coupling. -/
@[expose] def gpvVerifyRead (pk : PK) (out : M × (Salt × Domain)) :
    OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) Bool :=
  let (msg, (r, s)) := out
  (liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
      (Sum.inl (Sum.inr (r, msg)))) : OracleComp _ Range) >>= fun c =>
    pure (decide (psf.eval pk s = c) && psf.isShort s)

omit [SampleableType Range] [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
  [Fintype Salt] in
/-- **`gpvVerifyRead` is signing-free.** The verification read issues a single random-oracle query
(an `.inl (.inr _)` index) and no signing query, so it satisfies the signing-free query bound
`IsQueryBoundP (· matches .inr _) 0` required by the verify-Bool coupling. -/
lemma gpvVerifyRead_no_sign (pk : PK) (out : M × (Salt × Domain)) :
    (gpvVerifyRead psf M Salt pk out).IsQueryBoundP (· matches .inr _) 0 := by
  obtain ⟨msg, r, s⟩ := out
  simp only [gpvVerifyRead, bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
  refine (OracleComp.isQueryBoundP_query_iff _ (Sum.inl (Sum.inr (r, msg))) 0).mpr (fun h => ?_)
  simp at h

open Classical in
/-- **Real verify-Bool game on the freshness-tracking vehicle.** The adversary's main computation
followed by the verification read, simulated on the *real* fresh flag handler from the empty cache,
empty signed-set, and unset flag; the winning Bool combines the verification result `z.1.2` with the
EUF-CMA freshness mask `z.1.1.1 ∉ z.2.1.2` (the forged message is not among the signed messages). -/
@[expose] noncomputable def realGameVerifyFresh
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) : SPMF Bool :=
  𝒮[(fun z : ((M × (Salt × Domain)) × Bool) ×
        (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
        decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
      (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)]

open Classical in
/-- **Programmed verify-Bool game on the freshness-tracking vehicle.** The programmed dual of
`realGameVerifyFresh`: the same adversary-plus-verification computation simulated on the
*programmed* fresh flag handler. -/
@[expose] noncomputable def progGameVerifyFresh
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) : SPMF Bool :=
  𝒮[(fun z : ((M × (Salt × Domain)) × Bool) ×
        (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
        decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
      (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)]

omit [SampleableType Range] [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
  [Fintype Salt] in
/-- **The verification continuation is signing-free.** The freshness-game continuation
`fun out => (out, ·) <$> gpvVerifyRead pk out` issues exactly one random-oracle read (inside
`gpvVerifyRead`) and *no* signing query, so it meets the signing-free query bound
`IsQueryBoundP (· matches .inr _) 0` required by the fresh verify-Bool coupling. -/
lemma gpvVerifyKont_no_sign (pk : PK) (out : M × (Salt × Domain)) :
    ((fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out).IsQueryBoundP
      (· matches .inr _) 0 := by
  rw [OracleComp.isQueryBoundP_map_iff]
  exact gpvVerifyRead_no_sign psf M Salt pk out

/-- **Freshness-mask reconstruction bridge.** The EUF-CMA freshness check
`!log.wasQueried msg`, reading the WriterT signing log, equals the freshness predicate
`decide (msg ∉ (log.map fst).toFinset)` reading the signed-set reconstructed from the log: the
message is fresh iff it is not among the logged signing inputs. This is the pointwise identity that
lets the WriterT-log-keyed mask of the unforgeability experiment be read off the `Finset M`
signed-set carried by `gpvRealImplFlagFresh`. -/
lemma not_wasQueried_eq_decide_not_mem_toFinset {κ : Type} {spec : OracleSpec κ}
    [spec.DecidableEq] (log : QueryLog spec) (t : spec.Domain) :
    (!log.wasQueried t) = decide (t ∉ (log.map (fun e => e.1)).toFinset) := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst]
  simp only [List.mem_toFinset, decide_not]

/-- **Coupling hop (b) on the freshness-tracking verify-Bool games.** The real freshness verify-Bool
game's success probability is bounded by the programmed one plus `collisionBound`.

This is the bool-valued, data-processed shadow of the fresh verify-Bool coupling
`gpv_tvDist_orig_verify_fresh_le_collisionBound`: both `realGameVerifyFresh` and
`progGameVerifyFresh` are the *same* `decide (·.1.1.1 ∉ ·.2.1.2) && ·.1.2`-map of the two
vehicle runs of `adv.main pk >>= verify` on the real / programmed fresh flag handlers, so the
total-variation contraction `tvDist_map_le` reduces their bool TV to the run-level TV, which the
fresh coupling (with the signing-free verification continuation, `gpvVerifyKont_no_sign`)
bounds by `(collisionBound …).toReal`.  Transporting through the bool-valued bridge
`abs_probOutput_toReal_sub_le_tvDist` gives the `ℝ≥0∞` inequality. -/
theorem gpv_realGameVerifyFresh_le_progGameVerifyFresh_add_collisionBound
    [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk]
      ≤ Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
        + collisionBound Salt qSign qHash := by
  classical
  have hcb_lt_top : collisionBound Salt qSign qHash < ⊤ := by
    refine ENNReal.div_lt_top ?_ ?_
    · simp
    · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
      exact Fintype.card_ne_zero
  -- The two games are the same `decide (·) && ·`-map of the two vehicle runs; `tvDist_map_le`
  -- reduces their bool TV to the run-level TV bounded by the fresh coupling.
  let f : ((M × (Salt × Domain)) × Bool) ×
        (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) → Bool :=
    fun z => decide (z.1.1.1 ∉ z.2.1.2) && z.1.2
  let kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        ((M × (Salt × Domain)) × Bool) :=
    fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out
  let runReal := (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) (adv.main pk >>= kont)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)
  let runProg := (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
        (adv.main pk >>= kont)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)
  have hgoal : Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk]
      = Pr[= true | f <$> runReal] := rfl
  have hgoalProg : Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
      = Pr[= true | f <$> runProg] := rfl
  rw [hgoal, hgoalProg]
  rw [← ENNReal.ofReal_toReal probOutput_ne_top,
      ← ENNReal.ofReal_toReal (a := Pr[= true | f <$> runProg]) probOutput_ne_top,
      ← ENNReal.ofReal_toReal hcb_lt_top.ne,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbridge := abs_probOutput_toReal_sub_le_tvDist (f <$> runReal) (f <$> runProg)
  have hsub := (abs_le.mp hbridge).2
  have hmap : tvDist (f <$> runReal) (f <$> runProg) ≤ tvDist runReal runProg :=
    tvDist_map_le f runReal runProg
  have hcouple : tvDist runReal runProg ≤ (collisionBound Salt qSign qHash).toReal :=
    gpv_tvDist_orig_verify_fresh_le_collisionBound psf hr M Salt pk sk adv domainSample kont
      qSign qHash hQ (gpvVerifyKont_no_sign psf M Salt pk) hNF hreg
  linarith [le_trans hsub (le_trans hmap hcouple)]

omit [DecidableEq Range] [SampleableType Range] [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] [Fintype Salt] in
/-- **Lifted public-randomness run under the bundled state base.** Simulating a lifted
public-randomness `ProbComp` `oa` under the bundled identity base
`(QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)` runs `oa` verbatim, pairing
each output with the unchanged state `s`. The hidden state is inert for public-randomness queries.
This is the bundled-base analogue of `unifFwdImpl.simulateQ_run` for a general state type `σ`. -/
theorem simulateQ_ofLift_liftTarget_run {σ : Type} {α : Type} (oa : ProbComp α) (s : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp))
      (oa : OracleComp unifSpec α)).run s = (fun x => (x, s)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hlift : (liftM (liftM (OracleSpec.query t) : ProbComp (unifSpec.Range t)) :
        StateT σ ProbComp (unifSpec.Range t)).run s
        = (fun x => (x, s)) <$> (liftM (OracleSpec.query t) : ProbComp (unifSpec.Range t)) := by
      rw [StateT.run_monadLift]; rfl
    rw [hlift, map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_def]
    rw [show (liftM (OracleSpec.query t) : ProbComp (unifSpec.Range t)) >>= oa
        = liftM (OracleSpec.query t) >>= oa from rfl]
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun u => ?_
    rw [ih u]
    simp [map_eq_bind_pure_comp]

/-- **Keygen-averaging peel for the bundled `withStateOracle` semantics (reconstruction piece of the
game-identification (N)(a)).** A surface computation that begins by lifting a public-randomness
`ProbComp` prefix `oa` (e.g. the GPV key generation `liftM hr.gen`) into the oracle world and then
continues with `rest` factors, under the bundled `withStateOracle hashImpl ∅` `SPMF` semantics, as
the `SPMF`-average over `𝒮[oa]` of the semantics of the continuation.

The public-randomness prefix touches neither the random-oracle cache nor the hidden state: it is
simulated by the lifted identity implementation (`QueryImpl.simulateQ_add_liftComp_left` drops the
`hashImpl` summand on the lifted sub-computation, `unifFwdImpl.simulateQ_run` runs it as
`(·, ∅) <$> oa`), so its draws commute straight out of the bundle. This is the GPV-runtime keygen
peel of the game-identification (N)(a) — the analogue of the FiatShamir
`roSim.run'_liftM_bind`-style averaging step that opens
`probOutput_unforgeableExp_eq_hybridExpAtKey_real`. -/
theorem withStateOracle_evalSPMF_liftM_bind {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    {α β : Type} (oa : ProbComp α)
    (rest : α → OracleComp (unifSpec + hashSpec) β) :
    (SPMFSemantics.withStateOracle hashImpl ∅).evalSPMF (liftM oa >>= rest)
      = (𝒮[oa] : SPMF α) >>= fun x =>
          (SPMFSemantics.withStateOracle hashImpl ∅).evalSPMF (rest x) := by
  classical
  unfold SPMFSemantics.evalSPMF SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [show simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT hashSpec.QueryCache ProbComp) + hashImpl) (liftM oa)
      = simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT hashSpec.QueryCache ProbComp)) oa
      from QueryImpl.simulateQ_add_liftComp_left _ hashImpl oa]
  rw [simulateQ_ofLift_liftTarget_run oa ∅, map_bind, bind_map_left, liftM_bind]
  rfl

/-- **Step 1 (sign-then-hash ≡ real) TV bound, over the pinned GPV game runs.**

This is the salt-inclusive sign-then-hash hop *over the pinned GPV game runs*, with the run-level
coupling supplied by the original-run cardinality telescope `(A2)`
`gpv_orig_flag_le_collisionBound`.
The real run `realGameRun … adv pk sk` (the real EUF-CMA game) and the programmed run
`progGameRun … adv domainSample pk` (the randomized sign-then-hash game of the collision reduction)
are the two distributions of the sign-then-hash hop; given the query bound `hQ`, the trapdoor
totality `hNF`, and PSF regularity `hreg`, their total-variation distance is bounded by
`(collisionBound Salt qSign qHash).toReal`.

It is the GPV instance of the U2 surface
`tvDist_runtime_real_programmed_le_collisionBound_saltInclusive`, but unconditional and over the
actual game run.

**Proof route (original-run, inline salt).** The proof chains the identical-until-bad
reduction `gpv_tvDist_orig_run_le_probEvent_flag` — which bounds the Step-1 TV directly by the
run-level collision-flag probability of the flag-instrumented *original* (inline-salt) real handler
`gpvRealImplFlag` (consuming the universal off-bad agreement `gpvImplFlag_h_agree_good` and the
bad-monotonicity `h_mono`s) — with the original-run cardinality telescope `(A2)`
`gpv_orig_flag_le_collisionBound`, which bounds that flag probability by
`(collisionBound …).toReal`.  Because each signing salt is drawn inline at its step, this route
avoids the upfront-tape re-interleaving that a coupling over the front-loaded salt tape
(`TapeFactorization.lean`) would require; that tape-route coupling is not established here. -/
theorem gpv_tvDist_real_programmed_le_collisionBound
    [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    SPMF.tvDist (realGameRun psf hr M Salt adv pk sk)
        (progGameRun psf hr M Salt adv domainSample pk)
      ≤ (collisionBound Salt qSign qHash).toReal := by
  classical
  -- Original-run route: the identical-until-bad reduction bounds the Step-1 TV by the
  -- run-level collision-flag probability of the inline-salt flag handler
  -- (`gpv_tvDist_orig_run_le_probEvent_flag`), which the original-run cardinality telescope `(A2)`
  -- `gpv_orig_flag_le_collisionBound` bounds by `(collisionBound …).toReal`.
  refine le_trans
    (gpv_tvDist_orig_run_le_probEvent_flag psf hr M Salt pk sk adv domainSample hNF hreg) ?_
  exact gpv_orig_flag_le_collisionBound psf hr M Salt pk sk adv qSign qHash hQ

/-! ## State-threading bridge: runtime ↦ bare random oracle

The GPV `runtime` interprets the surface program over the *sum* spec
`unifSpec + (Salt × M →ₒ Range)` via
`simulateQ' ((QueryImpl.ofLift unifSpec ProbComp).liftTarget _ + randomOracle)`. The reusable
state-threading bridge in `ProgramLogic/Relational/ProgrammingOracle.lean`
(`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`) is instead stated for the bare
single-spec lazy random oracle `simulateQ randomOracle`. The lemma
`runtime_evalSPMF_liftComp` is the missing reduction connecting the two: on a sub-computation that
only touches the random oracle (a hash-only `OracleComp (Salt × M →ₒ Range)` lifted into the sum),
the runtime's bundled `SPMF` semantics collapse to the bare `randomOracle` run from the empty
cache. -/

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Pre-bridge.** On a random-oracle-only sub-computation `ob` lifted into the sum spec, the GPV
runtime's `SPMF` semantics equal the externally observed bare lazy random-oracle run from the empty
cache.

This is the reduction from the runtime's sum-spec `simulateQ'` interpreter down to the bare
`simulateQ randomOracle` form expected by the random-oracle state-threading bridge. It is
proved by unfolding `withStateOracle` and applying `QueryImpl.simulateQ_add_liftComp_right`, which
discards the (lifted-identity) uniform-sampling handler on a computation that never queries it. -/
theorem runtime_evalSPMF_liftComp {α : Type} (ob : OracleComp (Salt × M →ₒ Range) α) :
    (runtime M Salt).evalSPMF (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range)))
      = (liftM (StateT.run'
          (simulateQ (randomOracle :
            QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ob)
          ∅) : SPMF α) := by
  classical
  unfold ProbCompRuntime.evalSPMF runtime
  change (SPMFSemantics.withStateOracle _ ∅).evalSPMF _ = _
  unfold SPMFSemantics.evalSPMF SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]
  rw [QueryImpl.simulateQ_add_liftComp_right]

/-! ## U2: sign-then-hash ≡ real, up to the programming bad event

The "sign-then-hash ≡ real" hop replaces the real lazy random oracle by a `policy`-programmed one
(the simulator programs each fresh signing target with `psf.eval pk s` for a freshly sampled short
preimage `s`). This is **not** an exact distributional equality: it is exact up to the
*programming bad event*, namely that a freshly sampled signing salt collides with an entry already
present in the random-oracle cache. `tvDist_runtime_real_programmed_le_bad` is the exact
core of the hop: the total-variation distance between the real-runtime output and the
programmed-run output is bounded by the probability that the programming bad flag fires.

The `Fintype Range`/`Inhabited Range` hypotheses supply the `IsUniformSpec (Salt × M →ₒ Range)`
instance required by the state-threading bridge; they are mild for a hash range. -/

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **U2 core: sign-then-hash up-to-bad TV bound.**

For any random-oracle-only sub-computation `ob` and any programming `policy`, the total-variation
distance between the *real* GPV runtime output and the *programmed* (sign-then-hash) output is
bounded by the probability that the programming bad flag fires during the programmed run.

This is the exact, statistical-distance form of the sign-then-hash hop: it is one TV bound, **not**
an exact equality (stating it as equality would be false, since a fresh salt can collide with a
cached entry). It combines the pre-bridge `runtime_evalSPMF_liftComp` with
`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`. The downstream task is to bound
the right-hand bad-event probability by `collisionBound Salt qSign qHash` using regularity `hreg`
(to align the programmed value `psf.eval pk s` with the real uniform answer) and the salt-collision
union bound `probEvent_salt_collision_le_collisionBound`.

The `Finite Range`/`Inhabited Range` hypotheses supply the `IsUniformSpec (Salt × M →ₒ Range)`
instance required by the state-threading bridge; they are mild for a hash range. -/
theorem tvDist_runtime_real_programmed_le_bad [Finite Range] [Inhabited Range] {α : Type}
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α) :
    SPMF.tvDist
        ((runtime M Salt).evalSPMF (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ Pr[fun z : α × (Salt × M →ₒ Range).QueryCache × Bool => z.2.2 = true |
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob).run
            (∅, false)].toReal := by
  have : Fintype Range := Fintype.ofFinite Range
  have : IsUniformSpec (Salt × M →ₒ Range) := IsUniformSpec.ofFintypeInhabited _
  rw [runtime_evalSPMF_liftComp]
  exact tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad
    (spec := (Salt × M →ₒ Range)) policy ob ∅

/-! ## U2 (re-stated, salt-inclusive cache-hit bad event)

The up-to-bad core `tvDist_runtime_real_programmed_le_bad` above bounds the sign-then-hash TV
distance by the `withProgramming` *fire-on-miss* bad event over the random-oracle-only computation
`ob`. As the *salt-collision coupling and the hash-only granularity* section records, that bad event
is the wrong shape for GPV: the fire-on-miss flag is set the **first** time the policy fires on an
uncached point, so for the GPV
simulator (which programs at every fresh signing point) it fires *deterministically* — its
probability is near `1`, not `collisionBound`. Closing the core against `collisionBound` by way of
the fire-on-miss flag would therefore need the inequality "fire-on-miss ≤ salt-collision", which is
*false* for the GPV policy: the genuine salt-collision probability is `≈ collisionBound ≪ 1` while
the fire-on-miss probability is `≈ 1`. Moreover
the fresh signing salts — drawn in `unifSpec`, one step *before* each random-oracle query — are
invisible at `ob`'s granularity, so the `card / |Salt|` averaging is structurally absent from the
fire-on-miss flag.

`tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` re-states U2 so its bad event is
the genuine GPV salt-collision: a fresh signing salt drawn in `unifSpec` landing in the recorded
random-oracle cache restricted to its message slice (a cache *hit* at a programmed point), modelled
by the salt-averaged process `saltSeq c qSign` of the telescope section. The per-step caches `c j`
are the recorded random-oracle inputs seen by the `j`-th signing query; the standard GPV
cache-growth bound `card (c j) ≤ j + qHash` (the `j` prior signing salts plus the up to `qHash`
adversary hash queries) is supplied as `hcache`.

Crucially, the lemma does **not** route through the fire-on-miss bad event; it takes the
genuine *up-to-bad* coupling directly as `hcouple`: the total-variation distance between the real
and programmed runs is bounded by the salt-collision probability `Pr[saltSeq c qSign = true]`. This
is the correct identical-until-bad statement for the GPV game with bad event = cache-HIT salt
collision (the two runs differ only when a fresh salt collides with a recorded entry). It is
**true** (it is the real GPV up-to-bad bound, the cache-hit counterpart of the fire-on-miss
core `tvDist_runtime_real_programmed_le_bad`) and **non-vacuous** (`saltSeq c qSign` is a genuine
probabilistic process whose collision probability `probEvent_saltSeq_le_collisionBound` bounds it
strictly by `collisionBound < ⊤`, so `hcouple` is a real inequality between two `< ⊤` quantities,
not a `≤ ⊤` triviality; and the TV distance it bounds is in general positive, so it is not
vacuously `0 ≤ _`). Unlike the fire-on-miss route, `hcouple` is *satisfiable* by the GPV policy
precisely because its bad event is the small cache-hit collision rather than the deterministic
fire-on-miss.

`hcouple` names the joint-distribution coupling over the interleaved
salt-draw / random-oracle-query streams of the salt-inclusive signing run: each of the `qSign`
fresh salts is checked against the recorded cache slice of size `≤ j + qHash`, which is precisely
the `saltSeq` process. Once `hcouple` is discharged by the coupling, this lemma yields the loss-free
`tvDist ≤ (collisionBound Salt qSign qHash).toReal` consumed by the four GPV theorems.

The proof is loss-free: chain `hcouple` (TV distance ≤ `saltSeq` collision) with the
salt-averaged telescope `probEvent_saltSeq_le_collisionBound` (`saltSeq` collision ≤
`collisionBound`), then move to `ℝ` with `ENNReal.toReal_mono`. -/
omit [DecidableEq Range] in
theorem tvDist_runtime_real_programmed_le_collisionBound_saltInclusive
    [Finite Range] [Inhabited Range] [Nonempty Salt] {α : Type} (qSign qHash : ℕ)
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash)
    (hcouple : (SPMF.tvDist
        ((runtime M Salt).evalSPMF (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α) : ℝ)
        ≤ (Pr[ (· = true) | saltSeq (Salt := Salt) c qSign]).toReal) :
    SPMF.tvDist
        ((runtime M Salt).evalSPMF (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ (collisionBound Salt qSign qHash).toReal :=
  hcouple.trans (ENNReal.toReal_mono
    (by
      refine (ENNReal.div_lt_top ?_ ?_).ne
      · simp
      · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
        exact Fintype.card_ne_zero)
    (probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache))

/-! ## Step 1 and the wiring to the headline bounds

**Step 1 (sign-then-hash ≡ real).** `gpv_tvDist_real_programmed_le_collisionBound` is proved by
the *original-run* route, with every signing salt drawn inline at its step: the
identical-until-bad reduction `gpv_tvDist_orig_run_le_probEvent_flag` bounds the salt-inclusive
sign-then-hash hop `tvDist realRun progRun` by the run-level collision-flag probability of the
flag-instrumented real handler `gpvRealImplFlag`, and the original-run cardinality telescope `(A2)`
`gpv_orig_flag_le_collisionBound` bounds that flag probability by `collisionBound`. The front-tape
factorization of `TapeFactorization.lean` (both game runs as `drawList ($ᵗ Salt) qSign` followed
by a tape-consuming run) is not on this path: it is reusable infrastructure whose own coupling
headline over the tape is not established.

**Wiring Step 1 to the headline bounds.** Two facts connect
`gpv_tvDist_real_programmed_le_collisionBound` to the headline bounds:

1. *Game identification.* The headline LHS `adv.advantage (runtime)` is
   `Pr[= true | unforgeableExp (runtime) adv]`, whose body runs `simulateQ impl (adv.main pk)` — the
   signing oracle draws each fresh salt *internally* at an adversary-chosen point over the sum spec
   `unifSpec + (Salt × M →ₒ Range)`. Connecting this to the *pinned* hash-only run `ob` of
   `gpv_tvDist_real_programmed_le_collisionBound` (so that `abs_probOutput_toReal_sub_le_tvDist`
   converts the run-level `tvDist ≤ collisionBound` into `realAdv ≤ progAdv + collisionBound`) is
   the same deferred-sampling factorization as the front-tape coupling, now over the adversary's
   *adaptive* control flow rather than a fixed `ob`.
2. *Step 2 (collision extraction).* In the programmed sign-then-hash game every random-oracle entry
   carries the simulator's hidden short preimage; a fresh forgery on a programmed point with a
   *distinct* preimage is a collision under `psf.eval`, bounding `progAdv` by
   `collisionFindingAdvantage (reduction …)`. This is stated *pinned and true* over the concrete
   programmed forgery game and the concrete `reduction` body, with the exact-match branch handled by
   `programmedPreimageReduction`. -/

end GPVHashAndSign
