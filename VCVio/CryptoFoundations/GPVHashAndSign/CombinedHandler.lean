/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.FlagHandlers

/-! # GPV Hash-and-Sign: The Combined Programmed-Game and Collision-Reduction Handler

The combined handler running the programmed game and the collision reduction in
lockstep, its projections onto each factor, the write-only-table deferral, and
the cache/table coherence invariant.
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

/-! ### Stage-4 combined handler: programmed game ⊕ collision reduction

The distinct-collision transfer needs to relate the programmed freshness game handler
`progGameRunImplNoRecFlagFresh` (state `((cache × signedSet) × flag)`) to the collision
`reduction`'s internal handler (state `cache × table`, where `table : (Salt × M) → Option Domain`
records, for each programmed point, the hidden short preimage `s` used to define the random-oracle
value `psf.eval pk s` there). The reduction's handler is *not* a projection of the game handler: on
a random-oracle miss it draws `s ← domainSample pk`, caches `psf.eval pk s`, and stores `s` in the
table — and `s` is not recoverable from `psf.eval pk s` (`eval` is many-to-one).

The resolution is to build a single **combined** handler `progGameRunImplCombined` that draws each
programmed preimage `s` *once* and updates every component (cache, signed-set, flag, and the hidden
table) in one step, exactly matching the draw order of both games. It then projects definitionally
onto each:

* dropping the table recovers `progGameRunImplNoRecFlagFresh`
  (`map_run_progGameRunImplCombined_proj_table`);
* dropping the signed-set and the flag recovers the reduction's internal handler `reductionImpl`
  (`map_run_progGameRunImplCombined_proj_reduction`).

A support invariant (`progGameRunImplCombined_run_inv`) records that the table and the cache stay
coherent: at every programmed point `t`, `table t = some d → cache t = some (psf.eval pk d)`. -/

open Classical in
/-- **The collision reduction's internal oracle handler.** The named handler stack
`(unifImpl + roImpl) + signImpl` over `StateT (QueryCache × ((Salt × M) → Option Domain)) ProbComp`
that the collision `reduction` runs the adversary under. On a random-oracle miss it forward-samples
a short preimage `s ← domainSample pk`, sets the cache value to `psf.eval pk s`, and records `s` in
the hidden table at the queried point; the signing handler does the same at the freshly salted point
`(r, msg)`. Cache hits and uniform queries leave the table untouched. The reduction's body equals
running the adversary under this handler from `(∅, fun _ => none)` and reading the hidden preimage
off the final table (`reduction_eq_run_reductionImpl`). -/
@[expose] noncomputable def reductionImpl (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) ProbComp) :=
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
  (unifImpl + roImpl) + signImpl

omit [Fintype Salt] in
/-- **The collision reduction is `reductionImpl` run from the empty state.** Restates the body of
`reduction` in terms of the named internal handler `reductionImpl`: run the adversary under
`reductionImpl` from `(∅, fun _ => none)`, then read the hidden programmed preimage off the final
table at the forged point. The two are definitionally equal — `reduction`'s `let impl := …` block
*is* `reductionImpl`. -/
lemma reduction_eq_run_reductionImpl
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    reduction psf hr M Salt adv domainSample pk =
      (do
        let ((msgStar, (_rStar, sStar)), st) ←
          (simulateQ (reductionImpl psf M Salt domainSample pk) (adv.main pk)).run
            (∅, fun _ => none)
        match st.2 (_rStar, msgStar) with
        | some sHidden => pure (sHidden, sStar)
        | none => pure (sStar, sStar)) := rfl

/-- **Pre-sampled-index programmed-preimage handler.** Embeds the external target `y` at the
`w`-th programmed random-oracle entry (counting RO-query programming steps), caching `psf.eval pk s`
at every other entry and at every signing entry, and NEVER overwriting an already-cached slot. The
embed index `w` is fixed before the run, so the simulated random oracle is consistent under
re-query. Signing entries always return a valid signature `(r, s)` with `psf.eval pk s` the cached
value. -/
@[expose] noncomputable def embedAtIndexImpl (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ℕ
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          if st.2 = w then
            set ((st.1.cacheQuery t y, st.2 + 1) : State)
            pure y
          else
            set ((st.1.cacheQuery t (psf.eval pk s), st.2 + 1) : State)
            pure (psf.eval pk s)
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let st ← get
      set ((st.1.cacheQuery (r, msg) (psf.eval pk s), st.2 + 1) : State)
      pure (r, s)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- One-step unfolding of `embedAtIndexImpl` on a uniform query. -/
lemma embedAtIndexImpl_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    (embedAtIndexImpl psf M Salt domainSample pk w y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- One-step unfolding of `embedAtIndexImpl` on a random-oracle query. -/
lemma embedAtIndexImpl_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedAtIndexImpl psf M Salt domainSample pk w y (.inl (.inr q))).run s :
        ProbComp (Range × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (match s.1 q with
        | some v => pure (v, s)
        | none =>
            (fun sd : Domain =>
              (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
               else (psf.eval pk sd, (s.1.cacheQuery q (psf.eval pk sd), s.2 + 1)) :
                Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
              <$> (domainSample pk : ProbComp Domain)) := by
  cases hq : s.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedAtIndexImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun sd => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedAtIndexImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- One-step unfolding of `embedAtIndexImpl` on a signing query. -/
lemma embedAtIndexImpl_run_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (msg : M) (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedAtIndexImpl psf M Salt domainSample pk w y (.inr msg)).run s :
        ProbComp ((Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        (fun sd : Domain =>
          ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 + 1)) :
            Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
          <$> (domainSample pk : ProbComp Domain)) := by
  simp only [add_apply_inr, embedAtIndexImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

/-- **Trapdoor-uniform sibling of the pre-sampled-index handler.** Same state `cache × ℕ`, counter
logic, and never-overwrite discipline as `embedAtIndexImpl`, but every cached image is drawn
*uniformly* rather than as `psf.eval pk s`:

* on a non-winner random-oracle miss (`count ≠ w`) it caches a uniform `v ← $ᵗ Range` and returns
  `v` (output equals the cached value, as in `embedAtIndexImpl`);
* at the winner random-oracle miss (`count = w`) it still embeds the external target `y`;
* on a signing query it draws a uniform image `c ← $ᵗ Range`, caches `c`, and returns the
  *trapdoor preimage* `x ← psf.trapdoorSample pk sk c` as the signature's domain component.

Per-step this handler is equidistributed with `embedAtIndexImpl` under GPV regularity `hreg`
(`evalSPMF_embedAtIndex_step_eq_embedTrap`).  On a uniform query and on a random-oracle cache hit
the two handlers are literally identical.  On a non-winner random-oracle miss the only difference is
the cached/returned image, whose marginal law `hreg` equates (`psf.eval pk s ≡ $ᵗ Range`).  On a
signing step the joint law of the `(returned domain component, cached image)` pair is
`(s, psf.eval pk s)` for `s ← domainSample pk` on the `embedAtIndexImpl` side versus
`(psf.trapdoorSample pk sk c, c)` for `c ← $ᵗ Range` on this side — the two sides of `hreg`.

Threaded through the adaptive fold by the same-state engine
(`evalSPMF_run_embedAtIndexImpl_eq_embedTrap`), it makes the embed run an all-uniform consistent
random oracle (modulo `y` at the winner), matching the trapdoor-recording combined run's cache. -/
@[expose] noncomputable def embedTrapImpl (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ℕ
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          if st.2 = w then
            set ((st.1.cacheQuery t y, st.2 + 1) : State)
            pure y
          else
            set ((st.1.cacheQuery t v, st.2 + 1) : State)
            pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set ((st.1.cacheQuery (r, msg) c, st.2 + 1) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapImpl` on a uniform query. -/
lemma embedTrapImpl_run_inl_inl (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    (embedTrapImpl psf M Salt pk sk w y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapImpl` on a random-oracle query. -/
lemma embedTrapImpl_run_inl_inr (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapImpl psf M Salt pk sk w y (.inl (.inr q))).run s :
        ProbComp (Range × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (match s.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
               else (v, (s.1.cacheQuery q v, s.2 + 1)) :
                Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun v => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedTrapImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapImpl` on a signing query. -/
lemma embedTrapImpl_run_inr (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) (msg : M) (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapImpl psf M Salt pk sk w y (.inr msg)).run s :
        ProbComp ((Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1)) :
              Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **N3 — per-step equidistribution of `embedAtIndexImpl` and `embedTrapImpl`.** For every query
`t` and every embed state `s`, the two handlers produce *equal output distributions* on the same
state `s`, under GPV regularity `hreg` and trapdoor totality `hNF` at `(pk, sk)`.

On a uniform query and on a random-oracle cache *hit* the two handlers are literally identical.  On
a non-winner random-oracle *miss* the only difference is the cached/returned image, equated by the
first marginal of `hreg` (`psf.eval pk s ≡ $ᵗ Range`); the discarded trapdoor draw on the
`$ᵗ Range` side collapses by `hNF`.  At the winner random-oracle miss both handlers embed `y` and
discard the drawn image, so they agree.  On a signing step the joint law of the
`(returned domain component, cached image)` pair is `(s, psf.eval pk s)` for `s ← domainSample pk`
on the `embedAtIndexImpl` side versus `(psf.trapdoorSample pk sk c, c)` for `c ← $ᵗ Range` on the
`embedTrapImpl` side — the two sides of `hreg`, mapped through the (deterministic) cache update.
This is the local hypothesis of `evalSPMF_simulateQ_run_congr`. -/
lemma evalSPMF_embedAtIndex_step_eq_embedTrap
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (w : ℕ) (y : Range)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    𝒮[(embedAtIndexImpl psf M Salt domainSample pk w y t).run s] =
      𝒮[(embedTrapImpl psf M Salt pk sk w y t).run s] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedAtIndexImpl_run_inl_inl, embedTrapImpl_run_inl_inl]
      | inr q =>
          rw [embedAtIndexImpl_run_inl_inr, embedTrapImpl_run_inl_inr]
          cases hq : s.1 q with
          | some v => rfl
          | none =>
              -- Random-oracle miss: the cached/returned image is a function of `psf.eval pk sd`
              -- alone, so the first marginal of `hreg` (collapsed by `hNF`) suffices.
              have hfst : 𝒮[(domainSample pk : ProbComp Domain) >>= fun sd =>
                    (pure (psf.eval pk sd) : ProbComp Range)]
                  = 𝒮[($ᵗ Range : ProbComp Range)] :=
                evalSPMF_eval_domainSample_eq_uniform psf pk sk domainSample hNF hreg
              calc 𝒮[(fun sd : Domain =>
                      (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
                       else (psf.eval pk sd, (s.1.cacheQuery q (psf.eval pk sd), s.2 + 1)) :
                        Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
                    <$> (domainSample pk : ProbComp Domain)]
                  = 𝒮[(fun v : Range =>
                      (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
                       else (v, (s.1.cacheQuery q v, s.2 + 1)) :
                        Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
                    <$> ((domainSample pk : ProbComp Domain) >>= fun sd =>
                      (pure (psf.eval pk sd) : ProbComp Range))] := by
                      rw [map_bind, map_eq_bind_pure_comp]
                      simp only [map_pure, Function.comp_def]
                _ = 𝒮[(fun v : Range =>
                      (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
                       else (v, (s.1.cacheQuery q v, s.2 + 1)) :
                        Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
                    <$> ($ᵗ Range : ProbComp Range)] := by
                      rw [evalSPMF_map, evalSPMF_map, hfst]
  | inr msg =>
      rw [embedAtIndexImpl_run_inr, embedTrapImpl_run_inr]
      refine evalSPMF_bind_congr fun r _ => ?_
      -- The `(returned domain component, cached image)` joint is `(sd, eval sd)` vs
      -- `(trapdoorSample c, c)` — the two sides of `hreg`, mapped through the cache update.
      have h := congrArg (Functor.map
        (fun p : Range × Domain =>
          ((r, p.2), (s.1.cacheQuery (r, msg) p.1, s.2 + 1)) :
            Range × Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) hreg
      simp only [← evalSPMF_map, map_bind, map_pure] at h
      calc 𝒮[(fun sd : Domain =>
              ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 + 1)) :
                Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
            <$> (domainSample pk : ProbComp Domain)]
          = 𝒮[(domainSample pk : ProbComp Domain) >>= fun sd =>
              pure ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 + 1))] := by
              rw [map_eq_bind_pure_comp]; rfl
        _ = 𝒮[($ᵗ Range : ProbComp Range) >>= fun c =>
              (psf.trapdoorSample pk sk c : ProbComp Domain) >>= fun x =>
                pure ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1))] := h
        _ = 𝒮[($ᵗ Range : ProbComp Range) >>= fun c =>
              (fun x : Domain =>
                ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1)) :
                  Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
                <$> (psf.trapdoorSample pk sk c : ProbComp Domain)] := by
              refine evalSPMF_bind_congr fun c _ => ?_
              rw [map_eq_bind_pure_comp]; rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **N4 — run-level equidistribution of `embedAtIndexImpl` and `embedTrapImpl`.** For *any*
adaptive computation `oa` and any start embed state `s`, the full simulated run of the
pre-sampled-index handler `embedAtIndexImpl` over `oa` is *equidistributed* with the run of its
trapdoor-uniform sibling `embedTrapImpl`, under GPV regularity `hreg` and trapdoor totality `hNF`.

The two handlers agree query-by-query as output distributions on the same embed state
(`evalSPMF_embedAtIndex_step_eq_embedTrap`); the same-state distributional simulation engine
`evalSPMF_simulateQ_run_congr` threads that per-step equality through the entire
adaptive fold.  After this rewrite the embed run is an all-uniform consistent random oracle (modulo
the embedded target `y` at the winner slot), so its cache marginal coincides with the cache of the
trapdoor-recording combined run `progGameRunImplCombinedTrap`. -/
lemma evalSPMF_run_embedAtIndexImpl_eq_embedTrap {β : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (w : ℕ) (y : Range)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    𝒮[(simulateQ (embedAtIndexImpl psf M Salt domainSample pk w y) oa).run s] =
      𝒮[(simulateQ (embedTrapImpl psf M Salt pk sk w y) oa).run s] :=
  evalSPMF_simulateQ_run_congr
    (embedAtIndexImpl psf M Salt domainSample pk w y)
    (embedTrapImpl psf M Salt pk sk w y)
    (evalSPMF_embedAtIndex_step_eq_embedTrap psf M Salt domainSample pk sk w y hreg hNF) oa s

open Classical in
/-- **The combined programmed-game ⊕ collision-reduction handler.** A single handler that threads
the programmed freshness-game state `((cache × signedSet) × flag)` *together with* the collision
reduction's hidden preimage table `table : (Salt × M) → Option Domain`. Each programming step draws
the short preimage `s ← domainSample pk` *once* and uses it for both the game cache value
`psf.eval pk s` and the table record `s` at the programmed point, exactly matching the draw order of
`progGameRunImplNoRecFlagFresh` and `reductionImpl`.

* `.inl (.inl q)` (uniform): answer from `unifSpec`; cache, signed-set, flag, and table untouched.
* `.inl (.inr q)` (random-oracle read at `q`): on a hit reuse the cached value (table untouched); on
  a miss draw `s`, set the cache to `psf.eval pk s` and the table to `s` at `q`.
* `.inr msg` (signing): draw a fresh salt `r`, draw `s`, set the cache at `(r, msg)` to
  `psf.eval pk s`, insert `msg` into the signed-set, OR the collision flag with `saltKeyed`, and
  record `s` in the table at `(r, msg)`.

Dropping the table recovers `progGameRunImplNoRecFlagFresh`; dropping the signed-set and flag
recovers `reductionImpl`. -/
@[expose]
noncomputable def progGameRunImplCombined (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain))) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl (.inl q) => do
        let v ← (unifSpec.query q : ProbComp _)
        pure (v, s)
    | .inl (.inr q) =>
        match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd,
              (((s.1.1.1.cacheQuery q (psf.eval pk sd), s.1.1.2), s.1.2),
                fun t' => if t' = q then some sd else s.2 t'))
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sd ← (domainSample pk : ProbComp Domain)
        pure ((r, sd),
          (((s.1.1.1.cacheQuery (r, msg) (psf.eval pk sd), insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some sd else s.2 t'))

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombined` on a uniform query.** -/
lemma progGameRunImplCombined_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombined psf M Salt domainSample pk (.inl (.inl q))).run s =
      (do let v ← (unifSpec.query q : ProbComp _); pure (v, s)) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombined` on a random-oracle query.** -/
lemma progGameRunImplCombined_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombined psf M Salt domainSample pk (.inl (.inr q))).run s =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd,
              (((s.1.1.1.cacheQuery q (psf.eval pk sd), s.1.1.2), s.1.2),
                fun t' => if t' = q then some sd else s.2 t'))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombined` on a signing query.** -/
lemma progGameRunImplCombined_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombined psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sd ← (domainSample pk : ProbComp Domain)
        pure ((r, sd),
          (((s.1.1.1.cacheQuery (r, msg) (psf.eval pk sd), insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some sd else s.2 t'))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `reductionImpl` on a uniform query.** -/
lemma reductionImpl_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) :
    (reductionImpl psf M Salt domainSample pk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `reductionImpl` on a random-oracle query.** -/
lemma reductionImpl_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) :
    (reductionImpl psf M Salt domainSample pk (.inl (.inr q))).run s =
      (match s.1 q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd,
              (s.1.cacheQuery q (psf.eval pk sd),
                fun t' => if t' = q then some sd else s.2 t'))) := by
  cases hq : s.1 q with
  | none =>
      simp [reductionImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, StateT.run_set, bind_assoc, map_eq_bind_pure_comp, hq]
  | some v =>
      simp [reductionImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, hq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `reductionImpl` on a signing query.** -/
lemma reductionImpl_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) :
    (reductionImpl psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sd ← (domainSample pk : ProbComp Domain)
        pure ((r, sd),
          (s.1.cacheQuery (r, msg) (psf.eval pk sd),
            fun t' => if t' = (r, msg) then some sd else s.2 t'))) := by
  simp only [reductionImpl, QueryImpl.add_apply_inr]
  simp [StateT.run_bind, StateT.run_get, StateT.run_set, bind_assoc, map_eq_bind_pure_comp]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a uniform query.** -/
lemma progGameRunImplNoRec_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a random-oracle query.** -/
lemma progGameRunImplNoRec_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (Salt × M →ₒ Range).Domain) (s : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr q))).run s =
      (match s q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd, s.cacheQuery q (psf.eval pk sd))) := by
  cases hq : s q with
  | none =>
      simp [progGameRunImplNoRec, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, StateT.run_set, bind_assoc, map_eq_bind_pure_comp, hq]
  | some v =>
      simp [progGameRunImplNoRec, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, hq]

/-! #### D2. Projection of the combined handler onto the programmed game handler

Dropping the hidden preimage table (`proj = Prod.fst`) from the combined handler recovers the
programmed freshness-game handler `progGameRunImplNoRecFlagFresh`. The table is a passive auxiliary
over the game state: every game-state update (cache, signed-set, flag) is performed identically by
both handlers from the *same* drawn preimage, so projecting the table away commutes with each step
and hence with the whole simulation. -/

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query table projection of the combined handler.** Dropping the hidden table component
(`Prod.fst`, keeping the game state `((cache × signedSet) × flag)`) from one
`progGameRunImplCombined` query step recovers the corresponding `progGameRunImplNoRecFlagFresh`
step. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma progGameRunImplCombined_proj_table (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
          ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) <$>
        (progGameRunImplCombined psf M Salt domainSample pk t).run s =
      (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl, progGameRunImplNoRecFlagFresh_run_inl,
            progGameRunImplNoRec_run_inl_inl]
          rfl
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr, progGameRunImplNoRecFlagFresh_run_inl,
            progGameRunImplNoRec_run_inl_inr]
          cases s.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => rfl
  | inr msg =>
      rw [progGameRunImplCombined_run_inr, progGameRunImplNoRecFlagFresh_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Run-level table projection of the combined handler.** Dropping the hidden preimage table from
the full simulated run of `progGameRunImplCombined` over `oa` recovers the run of the programmed
game handler `progGameRunImplNoRecFlagFresh`. Transports the per-query
`progGameRunImplCombined_proj_table` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`: the table is a passive instrument over the game state. -/
lemma map_run_progGameRunImplCombined_proj_table (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
          ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) <$>
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s =
      (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
      ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)
    (progGameRunImplCombined_proj_table psf M Salt domainSample pk) oa s

/-! #### D2′. Write-only-table deferral: the `eval→trapdoor-recording` run rewrite

The combined handler `progGameRunImplCombined` writes the drawn short preimage `sd` into the hidden
table at each programming step, but it never *reads* that table during the run: every query answer
and every cache write uses only the *image* `psf.eval pk sd`, and the table is consulted only once,
at the final exact-match check.  The table is therefore *write-only* over the entire fold.

This lets the recorded preimage be re-coupled to its already-exposed image by the GPV regularity
`hreg`, target-by-target, without any adaptive interaction.  Concretely, define a sibling handler
`progGameRunImplCombinedTrap` that is identical except that at each programming step it draws the
*image* `v ← $ᵗ Range` uniformly, caches `v`, and records the *trapdoor* preimage
`trapdoorSample pk sk v` of that image in the table.  The two handlers agree query-by-query as
output *distributions* on the **same** state: the only difference is the joint law of the
`(cached image, recorded preimage)` pair, which is `(psf.eval pk sd, sd)` for `sd ← domainSample pk`
on one side and `(v, trapdoorSample pk sk v)` for `v ← $ᵗ Range` on the other — exactly the two
sides of `hreg`.  Mapping `hreg` through the (deterministic) cache/table update establishes the
per-step distributional equality for *any* update, and the distributional simulation engine
`evalSPMF_simulateQ_run_congr` threads it through the whole adaptive fold as an
exact equidistribution — no pointwise coupling between the two runs' successor states is required.

This is the clean *end-deferral* underlying the GPV Step-2 reservoir close: the recorded preimage is
re-expressed as the trapdoor preimage of the cached image, matching the reservoir reduction's
challenger preimage of the embedded uniform target. -/

open Classical in
/-- **The trapdoor-recording combined handler.** Identical to `progGameRunImplCombined` except that
each programming step draws the random-oracle *image* `v ← $ᵗ Range` uniformly, caches `v`, and
records the *trapdoor* preimage `x ← psf.trapdoorSample pk sk v` of that image in the hidden table.

Because the recorded preimage is never read during the run (the table is write-only, see
`map_run_progGameRunImplCombined_proj_table`), this handler is equidistributed run-for-run with
`progGameRunImplCombined` under GPV regularity `hreg`
(`evalSPMF_run_progGameRunImplCombinedTrap_eq`): the only per-step difference is the joint law of
the `(cached image, recorded preimage)` pair, which `hreg` equates. -/
@[expose] noncomputable def progGameRunImplCombinedTrap (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain))) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl (.inl q) => do
        let v ← (unifSpec.query q : ProbComp _)
        pure (v, s)
    | .inl (.inr q) =>
        match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              (((s.1.1.1.cacheQuery q v, s.1.1.2), s.1.2),
                fun t' => if t' = q then some x else s.2 t'))
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          (((s.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.2 t'))

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrap` on a uniform query.** -/
lemma progGameRunImplCombinedTrap_run_inl_inl (pk : PK)
    (sk : SK) (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inl q))).run s =
      (do let v ← (unifSpec.query q : ProbComp _); pure (v, s)) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrap` on a random-oracle query.** -/
lemma progGameRunImplCombinedTrap_run_inl_inr (pk : PK)
    (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inr q))).run s =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              (((s.1.1.1.cacheQuery q v, s.1.1.2), s.1.2),
                fun t' => if t' = q then some x else s.2 t'))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrap` on a signing query.** -/
lemma progGameRunImplCombinedTrap_run_inr (pk : PK)
    (sk : SK) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombinedTrap psf M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          (((s.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.2 t'))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step distributional equality of the combined handler and its trapdoor-recording sibling.**
For every query `t` and every state `s`, the combined handler `progGameRunImplCombined` and the
trapdoor-recording handler `progGameRunImplCombinedTrap` produce *equal output distributions* on the
same state `s`, under GPV regularity `hreg` at `(pk, sk)`.

On a uniform query and on a random-oracle cache *hit* the two handlers are literally identical.  On
a programming step (random-oracle miss or signing) the only difference is the joint law of the
`(cached image, recorded preimage)` pair drawn at that step: `(psf.eval pk sd, sd)` for
`sd ← domainSample pk` on the combined side, versus `(v, x)` for `v ← $ᵗ Range`,
`x ← trapdoorSample pk sk v` on the trapdoor side — the two sides of `hreg`.  Mapping `hreg` through
the (deterministic) cache/table update yields the per-step equality.  This is the local hypothesis
of `evalSPMF_simulateQ_run_congr`. -/
lemma evalSPMF_progGameRunImplCombined_step_eq_trap
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    𝒮[(progGameRunImplCombined psf M Salt domainSample pk t).run s] =
      𝒮[(progGameRunImplCombinedTrap psf M Salt pk sk t).run s] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl, progGameRunImplCombinedTrap_run_inl_inl]
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr, progGameRunImplCombinedTrap_run_inl_inr]
          cases hq : s.1.1.1 q with
          | some v => rfl
          | none =>
              -- Programming step (miss): map `hreg` through the cache/table update keyed at `q`.
              have h := congrArg (Functor.map
                (fun p : Range × Domain =>
                  (p.1,
                    (((s.1.1.1.cacheQuery q p.1, s.1.1.2), s.1.2),
                      fun t' => if t' = q then some p.2 else s.2 t'))
                    : Range × Domain →
                      Range × ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                        ((Salt × M) → Option Domain)))) hreg
              simpa only [OracleSpec.add_apply_inl, OracleSpec.add_apply_inr, ← evalSPMF_map,
                map_bind, map_pure, bind_assoc] using h
  | inr msg =>
      rw [progGameRunImplCombined_run_inr, progGameRunImplCombinedTrap_run_inr]
      -- Programming step (signing): draw salt `r`, then map `hreg` through the salt-keyed update.
      refine evalSPMF_bind_congr fun r _ => ?_
      have h := congrArg (Functor.map
        (fun p : Range × Domain =>
          ((r, p.2),
            (((s.1.1.1.cacheQuery (r, msg) p.1, insert msg s.1.1.2),
              s.1.2 || saltKeyed M Salt s.1.1.1 r),
              fun t' => if t' = (r, msg) then some p.2 else s.2 t'))
            : Range × Domain →
              (Salt × Domain) × ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                ((Salt × M) → Option Domain)))) hreg
      simpa only [OracleSpec.add_apply_inl, OracleSpec.add_apply_inr, ← evalSPMF_map,
                map_bind, map_pure, bind_assoc] using h

omit [DecidableEq Range] [Fintype Salt] in
/-- **Lemma A — write-only-table deferral / `eval→trapdoor-recording` run rewrite.** For *any*
adaptive computation `oa` and any start state `s`, the full simulated run of the combined handler
`progGameRunImplCombined` over `oa` is *equidistributed* with the run of the trapdoor-recording
handler `progGameRunImplCombinedTrap`, under GPV regularity `hreg` at `(pk, sk)`.

The two handlers agree query-by-query as output distributions on the same state
(`evalSPMF_progGameRunImplCombined_step_eq_trap`); the distributional simulation engine
`evalSPMF_simulateQ_run_congr` threads that per-step equality through the entire
adaptive fold as an exact equidistribution.  No pointwise relation between the two runs' successor
states is required: the only per-step difference is the *joint* law of the
`(cached image, recorded preimage)` pair, which `hreg` equates target-by-target — and because the
recorded preimage is never read during the run (the table is write-only), this purely local
substitution suffices.  This is the structural collapse of the GPV Step-2 reservoir coupling: the
recorded preimage `sd⋆` is re-expressed, run-for-run, as the trapdoor preimage `x⋆` of the cached
image, matching the reservoir reduction's challenger preimage of the embedded uniform target. -/
lemma evalSPMF_run_progGameRunImplCombinedTrap_eq {β : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    𝒮[(simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s] =
      𝒮[(simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk) oa).run s] :=
  evalSPMF_simulateQ_run_congr
    (progGameRunImplCombined psf M Salt domainSample pk)
    (progGameRunImplCombinedTrap psf M Salt pk sk)
    (evalSPMF_progGameRunImplCombined_step_eq_trap psf M Salt domainSample pk sk hreg) oa s

/-! #### D3. Projection of the combined handler onto the collision-reduction handler

Dropping the signed-set and the collision flag (`proj = fun s => (s.1.1.1, s.2)`, keeping the cache
and the hidden table) from the combined handler recovers the collision reduction's internal handler
`reductionImpl`. The signed-set and flag are passive auxiliaries over the reduction's cache/table
state: both handlers draw the *same* preimage and update the cache and table identically, so
projecting the game-only bookkeeping away commutes with each step and hence with the whole
simulation. -/

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query reduction projection of the combined handler.** Dropping the signed-set and the flag
(`fun s => (s.1.1.1, s.2)`, keeping the cache and the hidden table) from one
`progGameRunImplCombined` query step recovers the corresponding `reductionImpl` step. This is the
per-query hypothesis of the state-projection transport `map_run_simulateQ_eq_of_query_map_eq`. -/
lemma progGameRunImplCombined_proj_reduction (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (fun s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain) => (s.1.1.1, s.2)) <$>
        (progGameRunImplCombined psf M Salt domainSample pk t).run s =
      (reductionImpl psf M Salt domainSample pk t).run (s.1.1.1, s.2) := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl, reductionImpl_run_inl_inl]
          rfl
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr, reductionImpl_run_inl_inr]
          cases s.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => rfl
  | inr msg =>
      rw [progGameRunImplCombined_run_inr, reductionImpl_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Run-level reduction projection of the combined handler.** Dropping the signed-set and the flag
from the full simulated run of `progGameRunImplCombined` over `oa` recovers the run of the collision
reduction's internal handler `reductionImpl`. Transports the per-query
`progGameRunImplCombined_proj_reduction` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`: the signed-set and flag are passive over the reduction's
cache/table state. -/
lemma map_run_progGameRunImplCombined_proj_reduction (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (fun s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain) => (s.1.1.1, s.2)) <$>
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s =
      (simulateQ (reductionImpl psf M Salt domainSample pk) oa).run (s.1.1.1, s.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (fun s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain) => (s.1.1.1, s.2))
    (progGameRunImplCombined_proj_reduction psf M Salt domainSample pk) oa s

/-! #### D4. Cache/table coherence invariant of the combined handler

The combined handler keeps the cache and the hidden table coherent: at every programmed point `t`,
if the table records a hidden preimage `d`, then the cache value at `t` is exactly `psf.eval pk d`.
This holds because every table write `t ↦ s` is performed in lockstep with the cache write
`t ↦ psf.eval pk s` from the *same* drawn preimage `s`; cache hits and uniform queries touch
neither. The invariant is the structural certificate that lets the distinct-collision transfer read
a genuine `psf.eval`-collision off any forged fresh point. -/

/-- **Cache/table coherence predicate.** At every programmed point, a recorded hidden preimage in
the table is a `psf.eval pk`-preimage of the cached random-oracle value there. -/
@[expose] def combinedCacheTableInv (pk : PK)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prop :=
  ∀ t : Salt × M, ∀ d : Domain, s.2 t = some d → s.1.1.1 t = some (psf.eval pk d)

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-step preservation of cache/table coherence.** Each `progGameRunImplCombined` query step
preserves `combinedCacheTableInv`: a uniform query and a random-oracle cache hit leave cache and
table unchanged; a random-oracle miss and a signing step add a *matched* pair `t ↦ s` (table) and
`t ↦ psf.eval pk s` (cache) at the same point, preserving coherence everywhere. -/
lemma combinedCacheTableInv_step (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheTableInv psf M Salt pk s) :
    ∀ y ∈ support ((progGameRunImplCombined psf M Salt domainSample pk t).run s),
      combinedCacheTableInv psf M Salt pk y.2 := by
  intro y hy
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl] at hy
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
          obtain ⟨v, _, hw⟩ := hy
          subst hw
          exact hs
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr] at hy
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq] at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy
              exact hs
          | none =>
              rw [hq] at hy
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
              obtain ⟨sd, hsd, hw⟩ := hy
              subst hw
              intro t' d ht'
              dsimp only at ht' ⊢
              by_cases htq : t' = q
              · subst htq
                rw [if_pos rfl, Option.some_inj] at ht'
                subst ht'
                exact QueryCache.cacheQuery_self _ _ _
              · rw [if_neg htq] at ht'
                rw [QueryCache.cacheQuery_of_ne _ _ htq]
                exact hs t' d ht'
  | inr msg =>
      rw [progGameRunImplCombined_run_inr] at hy
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨r, _, sd, hsd, hw⟩ := hy
      subst hw
      intro t' d ht'
      dsimp only at ht' ⊢
      by_cases htq : t' = (r, msg)
      · subst htq
        rw [if_pos rfl, Option.some_inj] at ht'
        subst ht'
        exact QueryCache.cacheQuery_self _ _ _
      · rw [if_neg htq] at ht'
        rw [QueryCache.cacheQuery_of_ne _ _ htq]
        exact hs t' d ht'

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Cache/table coherence holds throughout the combined simulation.** Starting from any state
satisfying `combinedCacheTableInv` (in particular the empty start `((∅, ∅, false), fun _ => none)`,
where it holds vacuously), every final state in the support of the full combined run over `oa`
satisfies it. Transports `combinedCacheTableInv_step` through the whole simulation via
`simulateQ_run_preserves_inv_of_query`. -/
lemma progGameRunImplCombined_run_inv (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheTableInv psf M Salt pk s) :
    ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
      combinedCacheTableInv psf M Salt pk y.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (combinedCacheTableInv psf M Salt pk)
    (combinedCacheTableInv_step psf M Salt domainSample pk) oa s hs

/-- **Cache ⇒ table coherence predicate.** At every programmed point, a cached random-oracle value
is the `psf.eval pk`-image of a recorded hidden preimage in the table.  This is the direction the
distinct-collision transfer needs: a verifying forgery hits a *cached* point, and this invariant
exhibits the simulator's hidden preimage there. -/
@[expose] def combinedCacheImpliesTableInv (pk : PK)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prop :=
  ∀ t : Salt × M, ∀ v : Range, s.1.1.1 t = some v → ∃ d : Domain, s.2 t = some d ∧ v = psf.eval pk d

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-step preservation of cache ⇒ table coherence.** Each combined query step preserves
`combinedCacheImpliesTableInv`: uniform queries and cache hits leave both components untouched,
while random-oracle misses and signing steps write a matched pair `t ↦ psf.eval pk s` (cache) and
`t ↦ s` (table) at the same point. -/
lemma combinedCacheImpliesTableInv_step (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheImpliesTableInv psf M Salt pk s) :
    ∀ y ∈ support ((progGameRunImplCombined psf M Salt domainSample pk t).run s),
      combinedCacheImpliesTableInv psf M Salt pk y.2 := by
  intro y hy
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl] at hy
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
          obtain ⟨v, _, hw⟩ := hy
          subst hw
          exact hs
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr] at hy
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq] at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy
              exact hs
          | none =>
              rw [hq] at hy
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
              obtain ⟨sd, _hsd, hw⟩ := hy
              subst hw
              intro t' v' ht'
              dsimp only at ht' ⊢
              by_cases htq : t' = q
              · subst htq
                rw [QueryCache.cacheQuery_self, Option.some_inj] at ht'
                exact ⟨sd, by rw [if_pos rfl], ht'.symm⟩
              · rw [QueryCache.cacheQuery_of_ne _ _ htq] at ht'
                obtain ⟨d, hd, hv⟩ := hs t' v' ht'
                exact ⟨d, by rw [if_neg htq]; exact hd, hv⟩
  | inr msg =>
      rw [progGameRunImplCombined_run_inr] at hy
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨r, _, sd, _hsd, hw⟩ := hy
      subst hw
      intro t' v' ht'
      dsimp only at ht' ⊢
      by_cases htq : t' = (r, msg)
      · subst htq
        rw [QueryCache.cacheQuery_self, Option.some_inj] at ht'
        exact ⟨sd, by rw [if_pos rfl], ht'.symm⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ htq] at ht'
        obtain ⟨d, hd, hv⟩ := hs t' v' ht'
        exact ⟨d, by rw [if_neg htq]; exact hd, hv⟩

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Cache ⇒ table coherence holds throughout the combined simulation.** Starting from any state
satisfying `combinedCacheImpliesTableInv` (in particular the empty start, vacuously), every final
state of the combined run over `oa` satisfies it. -/
lemma progGameRunImplCombined_run_cacheImpliesTable (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheImpliesTableInv psf M Salt pk s) :
    ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
      combinedCacheImpliesTableInv psf M Salt pk y.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (combinedCacheImpliesTableInv psf M Salt pk)
    (combinedCacheImpliesTableInv_step psf M Salt domainSample pk) oa s hs

/-- **Table values are drawn preimages.** Every hidden preimage recorded in the combined run's table
lies in the support of the forward sampler `domainSample pk`. Every table write `t ↦ sd` records a
freshly drawn `sd ← domainSample pk`, so it is in the sampler's support; uniform queries and cache
hits leave the table untouched. -/
@[expose]
def combinedTableInDomainInv (M Salt : Type) (domainSample : PK → ProbComp Domain) (pk : PK)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prop :=
  ∀ t : Salt × M, ∀ d : Domain, s.2 t = some d → d ∈ support (domainSample pk)

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-step preservation of `combinedTableInDomainInv`.** -/
lemma combinedTableInDomainInv_step (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedTableInDomainInv M Salt domainSample pk s) :
    ∀ y ∈ support ((progGameRunImplCombined psf M Salt domainSample pk t).run s),
      combinedTableInDomainInv M Salt domainSample pk y.2 := by
  intro y hy
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl] at hy
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
          obtain ⟨v, _, hw⟩ := hy
          subst hw
          exact hs
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr] at hy
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq] at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy
              exact hs
          | none =>
              rw [hq] at hy
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
              obtain ⟨sd, hsd, hw⟩ := hy
              subst hw
              intro t' d ht'
              dsimp only at ht' ⊢
              by_cases htq : t' = q
              · subst htq
                rw [if_pos rfl, Option.some_inj] at ht'
                subst ht'
                exact hsd
              · rw [if_neg htq] at ht'
                exact hs t' d ht'
  | inr msg =>
      rw [progGameRunImplCombined_run_inr] at hy
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨r, _, sd, hsd, hw⟩ := hy
      subst hw
      intro t' d ht'
      dsimp only at ht' ⊢
      by_cases htq : t' = (r, msg)
      · subst htq
        rw [if_pos rfl, Option.some_inj] at ht'
        subst ht'
        exact hsd
      · rw [if_neg htq] at ht'
        exact hs t' d ht'

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **`combinedTableInDomainInv` holds throughout the combined simulation.** -/
lemma progGameRunImplCombined_run_tableInDomain (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedTableInDomainInv M Salt domainSample pk s) :
    ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
      combinedTableInDomainInv M Salt domainSample pk y.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (combinedTableInDomainInv M Salt domainSample pk)
    (combinedTableInDomainInv_step psf M Salt domainSample pk) oa s hs

end GPVHashAndSign
