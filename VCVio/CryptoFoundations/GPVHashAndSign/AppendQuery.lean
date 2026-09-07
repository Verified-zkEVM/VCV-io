/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.MinEntropy
public import VCVio.CryptoFoundations.GPVHashAndSign.Security

/-! # GPV Hash-and-Sign: The Append-Forgery-Query Compiler

The headline split bound `euf_cma_split_bound` is stated under the random-oracle
well-formedness convention `ForgesQueriedPoint`: the forger queries the random oracle at its
forgery point before outputting the forgery.  This module formalizes the standard on-paper
remark that the convention is *without loss of generality*: the compiler `appendForgeQuery`
transforms an arbitrary adversary into one satisfying the convention by appending a single
random-oracle query at the forgery point, at the cost of one extra hash query.

The compiled adversary satisfies the convention unconditionally
(`forgesQueriedPoint_appendForgeQuery`), obeys the query bound at `qHash + 1`
(`signHashQueryBound_appendForgeQuery`), and — because the verifier immediately re-queries the
same random-oracle point, making the appended query a cache-absorbed no-op — has *exactly* the
same EUF-CMA advantage as the original adversary (`advantage_appendForgeQuery`).  The
absorption is a term-level equality of the lazy-caching oracle
(`QueryImpl.withCaching_run_bind_run_self`): re-running a caching step from any state it just
produced is a deterministic cache hit.

Chaining these through `euf_cma_split_bound` yields the all-adversaries corollary
`euf_cma_split_bound_of_queryBound`, whose only structural hypothesis on the adversary is the
query bound: the `ForgesQueriedPoint` hypothesis is discharged by the compiler.  Pricing the
remaining exact-match term by the sampler's guessing probability
(`programmedPreimageAdvantage_le_trapdoorGuessingProbability`) gives the closed collision-style
headline `euf_cma_collision_bound_of_queryBound`.

These two `_of_queryBound` theorems are the public endpoints of the GPV development: they are the
statements a scheme instantiation should consume, so that `ForgesQueriedPoint` never becomes an
unstated convention at the instantiation. The `ForgesQueriedPoint`-hypothesis forms in
`Security.lean` are the primitives the compiler chains through.
-/

public section

open OracleComp OracleSpec ENNReal

universe u v

/-! ## Cache-hit absorption for `withCaching` -/

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
  {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- **Cache-hit absorption for the lazy-caching oracle.** Running a `withCaching` step at `t`
and then re-running the same step from the resulting state is the same as running it once: the
first step leaves the cache defined at `t` (either it was a hit, or the miss installed the drawn
value via `cacheQuery`), so the second step is a deterministic cache hit returning the same
value and state.  This is a term-level equality of computations, for any continuation `k`. -/
theorem withCaching_run_bind_run_self (so : QueryImpl spec m) (t : spec.Domain)
    (cache : spec.QueryCache) {β : Type u}
    (k : spec.Range t × spec.QueryCache → m β) :
    ((so.withCaching t).run cache >>= fun p => (so.withCaching t).run p.2 >>= k)
      = ((so.withCaching t).run cache >>= k) := by
  cases hcache : cache t with
  | some u =>
      rw [withCaching_run_some so hcache, pure_bind, pure_bind,
        withCaching_run_some so hcache, pure_bind]
  | none =>
      rw [withCaching_run_none so hcache, map_eq_bind_pure_comp, bind_assoc, bind_assoc]
      refine bind_congr fun u => ?_
      simp only [Function.comp_apply, pure_bind]
      rw [withCaching_run_some so (QueryCache.cacheQuery_self cache t u), pure_bind]

end QueryImpl

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! ## The compiler -/

/-- **The append-forgery-query compiler.** Runs the adversary, then queries the random oracle
once at the forgery point `(salt, msg) = (out.2.1, out.1)` (an ambient `.inl (.inr _)` index —
no signing query), and returns the forgery unchanged.  The compiled adversary satisfies the
`ForgesQueriedPoint` convention unconditionally, makes one extra hash query, and has the same
EUF-CMA advantage as `adv` (`advantage_appendForgeQuery`). -/
@[expose] def appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt) where
  main := fun pk =>
    adv.main pk >>= fun out =>
      liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
        (Sum.inl (Sum.inr (out.2.1, out.1)))) >>= fun _ =>
      pure out

omit [Fintype Salt] in
/-- Definitional unfolding of the compiled adversary's main computation. -/
lemma appendForgeQuery_main
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) :
    (appendForgeQuery psf hr M Salt adv).main pk =
      adv.main pk >>= fun out =>
        liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
          (Sum.inl (Sum.inr (out.2.1, out.1)))) >>= fun _ =>
        pure out := rfl

/-! ## The compiled adversary's query bound -/

omit [Fintype Salt] in
/-- **Query bound for the compiled adversary.** The appended random-oracle query is a single
`.inl (.inr _)` index: the signing count is unchanged and the hash count grows by one. -/
theorem signHashQueryBound_appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (qSign qHash : ℕ) (pk : PK)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := (appendForgeQuery psf hr M Salt adv).main pk) (qSign := qSign)
      (qHash := qHash + 1) := by
  obtain ⟨hSign, hHash⟩ := hQ
  rw [appendForgeQuery_main]
  constructor
  · refine Nat.add_zero qSign ▸ OracleComp.isQueryBoundP_bind hSign fun out _ => ?_
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun _ => trivial⟩
  · refine OracleComp.isQueryBoundP_bind hHash fun out _ => ?_
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-! ## The compiled adversary forges on a queried point -/

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **A programmed random-oracle read step caches its point.** After running the programmed
fresh-flag handler on the random-oracle query at `mc`, the resulting cache maps `mc` to a
`some` value, for every initial state: on a hit the entry is preserved, on a miss the handler
programs `cacheQuery mc _`.  This is the single-step core of the unconditional
`ForgesQueriedPoint` discharge `forgesQueriedPoint_appendForgeQuery`. -/
lemma progGameRunImplNoRecFlagFresh_read_caches (domainSample : PK → ProbComp Domain)
    (pk : PK) (mc : Salt × M)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)
    (z : Range × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool))
    (hz : z ∈ support ((progGameRunImplNoRecFlagFresh psf M Salt domainSample pk
      (.inl (.inr mc))).run s)) :
    z.2.1.1 mc ≠ none := by
  rw [progGameRunImplNoRecFlagFresh_run_inl, progGameRunImplNoRec_run_read] at hz
  cases h : s.1.1 mc with
  | some v =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map, support_pure, Set.image_singleton] at hz
      have hz : z = (v, (s.1.1, s.1.2), s.2) := hz
      subst hz
      simp only [h, ne_eq, reduceCtorEq, not_false_eq_true]
  | none =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map] at hz
      obtain ⟨_, ⟨sd, _, rfl⟩, rfl⟩ := hz
      simp only
      rw [QueryCache.cacheQuery_self]
      exact Option.some_ne_none _

omit [Fintype Salt] in
/-- **The compiled adversary forges on a queried point, unconditionally.** The appended
random-oracle query at the forgery point is the last step of the compiled run, so the final
cache is defined there — either as a preserved hit or as the freshly programmed entry.  This
discharges the `ForgesQueriedPoint` hypothesis of the headline bounds for every domain
sampler. -/
theorem forgesQueriedPoint_appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    ForgesQueriedPoint psf hr M Salt (appendForgeQuery psf hr M Salt adv) domainSample := by
  unfold ForgesQueriedPoint
  intro pk z hz
  rw [appendForgeQuery_main, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨out, smid⟩, _hmid, hrest⟩ := hz
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨c, sfin⟩, hstep, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  subst hpure
  exact progGameRunImplNoRecFlagFresh_read_caches psf M Salt domainSample pk
    (out.2.1, out.1) smid (c, sfin) hstep

/-! ## Advantage preservation

The appended query is immediately re-issued by the verification read at the same
random-oracle point, so under the lazy-caching real handler it is a cache-absorbed no-op:
the compiled adversary's real freshness verify-Bool game is *equal* to the original one,
and hence so is the EUF-CMA advantage. -/

omit [Fintype Salt] in
/-- **Cache-hit absorption on the real fresh-flag handler.** Running the real handler's
random-oracle read at `mc` twice in a row from any state is the same as running it once: the
signed-set and flag are passive on a read, and the underlying lazy random oracle absorbs the
repeated query (`QueryImpl.withCaching_run_bind_run_self`). -/
lemma gpvRealImplFlagFresh_run_read_bind_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) {β : Type}
    (k : Range × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) → ProbComp β) :
    ((gpvRealImplFlagFresh psf hr M Salt pk sk (.inl (.inr mc))).run s >>= fun p =>
        (gpvRealImplFlagFresh psf hr M Salt pk sk (.inl (.inr mc))).run p.2 >>= k)
      = ((gpvRealImplFlagFresh psf hr M Salt pk sk (.inl (.inr mc))).run s >>= k) := by
  simp only [gpvRealImplFlagFresh_run_inl, gpvRealImpl_run_read, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_def]
  exact QueryImpl.withCaching_run_bind_run_self _ mc s.1.1 _

omit [Fintype Salt] in
/-- **One-step run of the real fresh-flag handler on a lifted random-oracle read, at the
`Range`-ascribed elaboration.** The verification read `gpvVerifyRead` lifts its query with the
result type ascribed to `Range` (rather than the definitionally equal
`((unifSpec + (Salt × M →ₒ Range)) + _).Range (.inl (.inr mc))`), which blocks the syntactic
`simulateQ_spec_query` rewrite under binders; this restatement is keyed to that exact
elaboration so it can rewrite the verification read in place. -/
lemma gpvRealImplFlagFresh_run_liftM_query (pk : PK) (sk : SK) (mc : Salt × M)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk)
        (liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
          (Sum.inl (Sum.inr mc))) : OracleComp _ Range)).run s
      = (gpvRealImplFlagFresh psf hr M Salt pk sk (.inl (.inr mc))).run s := by
  erw [simulateQ_spec_query]

omit [Fintype Salt] in
/-- **The appended forgery query is absorbed by the verification read.** The real freshness
verify-Bool game of the compiled adversary equals that of the original adversary: the appended
random-oracle query targets exactly the point the verification read re-queries, so under the
lazy-caching real handler the two adjacent reads collapse to one
(`gpvRealImplFlagFresh_run_read_bind_run_read`). -/
theorem realGameVerifyFresh_appendForgeQuery (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    realGameVerifyFresh psf hr M Salt (appendForgeQuery psf hr M Salt adv) pk sk
      = realGameVerifyFresh psf hr M Salt adv pk sk := by
  have hrun : (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk)
        ((appendForgeQuery psf hr M Salt adv).main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)
      = (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false) := by
    rw [appendForgeQuery_main]
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun x => ?_
    obtain ⟨⟨msg, r, sig⟩, s₁⟩ := x
    simp only [gpvVerifyRead, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def]
    exact gpvRealImplFlagFresh_run_read_bind_run_read psf hr M Salt pk sk (r, msg) s₁ _
  unfold realGameVerifyFresh
  rw [hrun]

open Classical in
omit [Fintype Salt] in
/-- **The GPV EUF-CMA advantage is the keygen-averaged real freshness verify-Bool game.**
Chains the keygen-averaging peel `probOutput_unforgeableExp_eq_keygen_average` with the per-key
WriterT-log → signed-set reconstruction `signedSet_eq_wasQueried`.  This is the equational
prefix of the game-identification chain, exposed so that game-level identities (such as the
appended-query absorption `realGameVerifyFresh_appendForgeQuery`) transfer to the headline
advantage. -/
lemma advantage_eq_keygen_average_realGameVerifyFresh
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    adv.advantage (runtime M Salt)
      = Pr[= true | (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
          realGameVerifyFresh psf hr M Salt adv pksk.1 pksk.2] := by
  classical
  rw [SignatureAlg.unforgeableAdv.advantage,
    probOutput_unforgeableExp_eq_keygen_average psf hr M Salt adv]
  rw [show (fun pksk : PK × SK =>
        (SPMFSemantics.withStateOracle
          (randomOracle : QueryImpl (Salt × M →ₒ Range)
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalSPMF
          (letI : DecidableEq M := Classical.decEq M
           letI : DecidableEq (Salt × Domain) := Classical.decEq (Salt × Domain)
           do
            let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
              (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                  psf hr M Salt).signingOracle pksk.1 pksk.2
            let ((msg, σ), log) ← (simulateQ impl (adv.main pksk.1)).run
            let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).verify pksk.1 msg σ
            return !log.wasQueried msg && verified))
      = (fun pksk : PK × SK => realGameVerifyFresh psf hr M Salt adv pksk.1 pksk.2) from
    funext fun pksk => signedSet_eq_wasQueried psf hr M Salt pksk.1 pksk.2 adv]

omit [Fintype Salt] in
/-- **Advantage preservation (obligation 4 of the WLOG compiler).** The compiled adversary has
exactly the EUF-CMA advantage of the original adversary: the appended random-oracle query is
re-issued by the verification read at the same point, so the lazy-caching semantics absorbs it
without affecting the output distribution, the signing log, or the freshness mask. -/
theorem advantage_appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (appendForgeQuery psf hr M Salt adv).advantage (runtime M Salt)
      = adv.advantage (runtime M Salt) := by
  rw [advantage_eq_keygen_average_realGameVerifyFresh psf hr M Salt
      (appendForgeQuery psf hr M Salt adv),
    advantage_eq_keygen_average_realGameVerifyFresh psf hr M Salt adv]
  exact congrArg (fun d : SPMF Bool => Pr[= true | d])
    (bind_congr fun pksk =>
      realGameVerifyFresh_appendForgeQuery psf hr M Salt pksk.1 pksk.2 adv)

/-! ## The all-adversaries split bound -/

/-- **Split GPV PFDH bound without the `ForgesQueriedPoint` hypothesis.** For *any* adversary
obeying the query bound `(qSign, qHash)`, the EUF-CMA advantage satisfies the split GPV bound
at hash budget `qHash + 1`: the append-forgery-query compiler `appendForgeQuery` discharges the
forger-queries-its-forgery-point convention at the cost of one extra hash query
(`forgesQueriedPoint_appendForgeQuery`, `signHashQueryBound_appendForgeQuery`) while preserving
the advantage exactly (`advantage_appendForgeQuery`).  This is the all-adversaries form of
`euf_cma_split_bound`; the witnesses are the reductions built from the compiled adversary. -/
theorem euf_cma_split_bound_of_queryBound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (hreg : ∃ domainSample : PK → ProbComp Domain, ∀ (pk : PK) (sk : SK),
      (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionRed : CollisionAdversary (PK := PK) (Domain := Domain))
      (exactMatchRed : ProgrammedPreimageAdversary
        (PK := PK) (Domain := Domain) (Range := Range)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) collisionRed +
          ((qSign + (qHash + 1) : ℕ) : ENNReal) *
            programmedPreimageAdvantage (psf := psf) (hr := hr) exactMatchRed +
          collisionBound Salt qSign (qHash + 1) := by
  obtain ⟨collisionRed, exactMatchRed, hbound⟩ :=
    euf_cma_split_bound psf hr M Salt hcorrect hreg qSign (qHash + 1)
      (appendForgeQuery psf hr M Salt adv) hNF
      (fun ds => forgesQueriedPoint_appendForgeQuery psf hr M Salt adv ds)
      (fun pk => signHashQueryBound_appendForgeQuery psf hr M Salt adv qSign qHash pk (hQ pk))
  refine ⟨collisionRed, exactMatchRed, ?_⟩
  rw [← advantage_appendForgeQuery psf hr M Salt adv]
  exact hbound

/-- **Collision-style GPV PFDH bound for every query-bounded adversary, with the exact-match branch
already priced by the trapdoor sampler's min-entropy.** For *any* adversary obeying the query bound
`(qSign, qHash)`, the EUF-CMA advantage is at most

  `Adv^collision(B) + (qSign + qHash + 1) · trapdoorGuessingProbability + collisionBound`

at hash budget `qHash + 1`.  Both structural side conditions of `euf_cma_collision_bound` are
discharged here rather than assumed: the forger-queries-its-forgery-point convention by the
append-forgery-query compiler (`euf_cma_split_bound_of_queryBound`), and the exact-match parameter
`εpp` by the generic guessing-probability bound
`programmedPreimageAdvantage_le_trapdoorGuessingProbability`, which prices the programmed-preimage
branch at the largest pointwise output mass `psf.trapdoorSample` assigns at an honest key.  What
remains for a concrete PSF is to bound `trapdoorGuessingProbability` — for a discrete-Gaussian
trapdoor sampler above the smoothing parameter this is negligible. -/
theorem euf_cma_collision_bound_of_queryBound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (hreg : ∃ domainSample : PK → ProbComp Domain, ∀ (pk : PK) (sk : SK),
      (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ collisionRed : CollisionAdversary (PK := PK) (Domain := Domain),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) collisionRed +
          ((qSign + (qHash + 1) : ℕ) : ENNReal) * trapdoorGuessingProbability psf hr +
          collisionBound Salt qSign (qHash + 1) := by
  obtain ⟨collisionRed, exactMatchRed, hbound⟩ :=
    euf_cma_split_bound_of_queryBound psf hr M Salt hcorrect hreg qSign qHash adv hNF hQ
  refine ⟨collisionRed, hbound.trans ?_⟩
  gcongr
  exact programmedPreimageAdvantage_le_trapdoorGuessingProbability psf hr exactMatchRed

end GPVHashAndSign
