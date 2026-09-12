/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.GameIdentification

/-! # GPV Hash-and-Sign: The Verification Bridge

The O1 data-processing bridge from Step-1 to the post-processed verification
game, the forger-queries-its-forgery-point predicate, and the programmed
verify-game machinery it feeds.
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

/-! ## O1: the data-processing bridge from Step-1 to a post-processed (verification) game

Step-1 (`gpv_tvDist_real_programmed_le_collisionBound`) bounds the total-variation distance between
the *forgery* distributions `realGameRun` and `progGameRun` (both `SPMF (M × (Salt × Domain))`) by
`collisionBound`. The headline games are obtained by post-processing each forgery `out = (msg, σ)`
through a verification step `k : M × (Salt × Domain) → SPMF Bool`. The lemma below is the
data-processing transfer of Step-1 across that post-processing: for *any* `SPMF`-valued
post-processor `k`, the success probability of the real post-processed game exceeds that of the
programmed post-processed game by at most `collisionBound`.

It is a pure consequence of the data-processing inequality `tvDist_bind_right_le` (binding both runs
with the same continuation `k` does not increase TV distance) chained with Step-1, transported to
`ℝ≥0∞` through the bool-valued TV bridge `abs_probOutput_toReal_sub_le_tvDist`. It carries no new
probabilistic content beyond Step-1 and is reusable for any verification post-processor. -/
theorem gpv_realGameVerify_le_progGameVerify_add_collisionBound
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
            : ProbComp (Range × Domain))])
    (k : M × (Salt × Domain) → SPMF Bool) :
    Pr[= true | realGameRun psf hr M Salt adv pk sk >>= k]
      ≤ Pr[= true | progGameRun psf hr M Salt adv domainSample pk >>= k]
        + collisionBound Salt qSign qHash := by
  -- Both probabilities are `< ⊤`, so it suffices to prove the `toReal` inequality.
  have hcb_lt_top : collisionBound Salt qSign qHash < ⊤ := by
    refine ENNReal.div_lt_top ?_ ?_
    · simp
    · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
      exact Fintype.card_ne_zero
  set pProg := Pr[= true | progGameRun psf hr M Salt adv domainSample pk >>= k] with hpProg
  rw [← ENNReal.ofReal_toReal probOutput_ne_top,
      ← ENNReal.ofReal_toReal (a := pProg) probOutput_ne_top,
      ← ENNReal.ofReal_toReal hcb_lt_top.ne]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `Pr[real⋯].toReal ≤ Pr[prog⋯].toReal + tvDist(real⋯)(prog⋯)` via the bool TV bridge,
  -- then `tvDist(real⋯)(prog⋯) ≤ tvDist(real)(prog) ≤ collisionBound` (DPI + Step-1).
  have hbridge :=
    abs_probOutput_toReal_sub_le_tvDist
      (realGameRun psf hr M Salt adv pk sk >>= k)
      (progGameRun psf hr M Salt adv domainSample pk >>= k)
  have hsub :=
    (abs_le.mp hbridge).2
  have hdpi : SPMF.tvDist
        (realGameRun psf hr M Salt adv pk sk >>= k)
        (progGameRun psf hr M Salt adv domainSample pk >>= k)
      ≤ (collisionBound Salt qSign qHash).toReal :=
    le_trans (SPMF.tvDist_bind_right_le k _ _)
      (gpv_tvDist_real_programmed_le_collisionBound psf hr M Salt pk sk adv domainSample
        qSign qHash hQ hNF hreg)
  linarith [le_trans hsub hdpi]

open Classical in
omit [Fintype Salt] in
/-- **Keygen-averaging peel of the GPV unforgeability experiment (sub-build (3) of the
game-identification (N)(a)).** The success probability of the GPV unforgeability experiment is the
`SPMF`-average over the key pair `(pk, sk) ← hr.gen` of the success probability of the per-key
verify-extended WriterT signing-log experiment under the bundled `withStateOracle` random-oracle
semantics.

The GPV `keygen` is `liftM hr.gen`, a public-randomness prefix that touches neither the
random-oracle cache nor the hidden state; the keygen-peel `withStateOracle_evalSPMF_liftM_bind`
commutes its draw straight out of the bundled `withStateOracle` semantics as an `SPMF`-average over
`𝒮[hr.gen]`. This is the GPV-runtime analogue of the FiatShamir `roSim.run'_liftM_bind`-style
averaging step that
opens `probOutput_unforgeableExp_eq_hybridExpAtKey_real`; it isolates the keygen average so the
remaining game-identification work is a per-key WriterT-log → signed-set reconstruction. -/
theorem probOutput_unforgeableExp_eq_keygen_average
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | SignatureAlg.unforgeableExp (runtime M Salt) adv]
      = Pr[= true | (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
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
              return !log.wasQueried msg && verified)] := by
  classical
  unfold SignatureAlg.unforgeableExp
  rw [show (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
        psf hr M Salt).keygen
      = (liftM hr.gen : OracleComp (unifSpec + (Salt × M →ₒ Range)) (PK × SK)) from rfl]
  refine congrArg (fun d : SPMF Bool => Pr[= true | d]) ?_
  rw [GPVHashAndSign.runtime]
  change (SPMFSemantics.withStateOracle
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalSPMF (liftM hr.gen >>= _)
    = (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        (SPMFSemantics.withStateOracle
          (randomOracle : QueryImpl (Salt × M →ₒ Range)
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalSPMF _
  rw [withStateOracle_evalSPMF_liftM_bind]
  refine bind_congr fun pksk => ?_
  obtain ⟨pk, sk⟩ := pksk
  rfl

open Classical in
omit [Fintype Salt] in
/-- **Verify-extended WriterT-run fold.** Running `adv.main pk` under the WriterT signing-log stack
and then the verification read `verify pk msg σ` (as a separate `OracleComp` continuation on the
shared random-oracle base) coincides with running the *single* WriterT computation
`adv.main pk >>= fun out => (out, ·) <$> verify pk out.1 out.2`: the verification read issues no
signing query, so it leaves the WriterT log untouched (the empty log appends nothing), and
`simulateQ` distributes over the adversary-then-verify bind.  This folds the outer verification
continuation of the unforgeability experiment into the single adversary computation that the
reconstruction `map_simulateQ_gpvOuter_writerLog_eq_gpvRealImplFresh` consumes. -/
lemma simulateQ_writerImpl_verify_fold (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    ((simulateQ
        ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
          (WriterT (QueryLog (M →ₒ (Salt × Domain)))
            (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk)
        (adv.main pk)).run >>=
        fun z => (fun v => ((z.1, v), z.2)) <$>
          ((GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).verify pk z.1.1 z.1.2
            : OracleComp (unifSpec + (Salt × M →ₒ Range)) Bool))
      = (simulateQ
        ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
          (WriterT (QueryLog (M →ₒ (Salt × Domain)))
            (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run := by
  classical
  rw [simulateQ_bind, WriterT.run_bind]
  refine bind_congr fun z => ?_
  obtain ⟨⟨msg, σ⟩, log⟩ := z
  -- The verification read is a single `.inl (.inr _)` RO query routed through the lifted base
  -- `baseW`, which logs nothing; `verify` and `gpvVerifyRead` are the same RO read + check.
  obtain ⟨r, s⟩ := σ
  -- The RHS `gpvVerifyRead` is a single `Sum.inl (Sum.inr (r, msg))` RO read; route it through the
  -- lifted base `baseW` (`simulateQ_spec_query` + `add_apply_inl` + `liftTarget_apply`).
  simp only [gpvVerifyRead, GPVHashAndSign, simulateQ_map, bind_pure_comp]
  erw [simulateQ_spec_query]
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
    WriterT.run_bind, WriterT.run_pure, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def]
  erw [WriterT.run_liftM]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, List.append_nil,
    EmptyCollection.emptyCollection]
  rfl

open Classical in
omit [Fintype Salt] in
/-- **Per-key game-identification (N)(a): WriterT-log unforgeability experiment ≡ freshness
verify-Bool game.**
The per-key body of the GPV unforgeability experiment (the keygen-peel summand of
`probOutput_unforgeableExp_eq_keygen_average`) — running `adv.main pk` under the WriterT signing-log
handler stack, then `verify`, then masking with the WriterT-log freshness check
`!log.wasQueried msg` — coincides with the freshness verify-Bool game `realGameVerifyFresh`, whose
winning Bool reads the `Finset M` signed-set carried by `gpvRealImplFlagFresh`.  This identifies the
WriterT signing log with the reconstructed signed-set across the WriterT/StateT divide, folding in
the verification continuation; it is the per-key bridge of the game-identification (N)(a). -/
lemma signedSet_eq_wasQueried
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
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
              psf hr M Salt).signingOracle pk sk
        let ((msg, σ), log) ← (simulateQ impl (adv.main pk)).run
        let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).verify pk msg σ
        return !log.wasQueried msg && verified)
      = realGameVerifyFresh psf hr M Salt adv pk sk := by
  classical
  -- Reassociate the verification continuation into the WriterT run
  -- (`simulateQ_writerImpl_verify_fold`) at the `OracleComp` level, before exposing the bundled
  -- `withStateOracle` semantics.
  have heq : (letI : DecidableEq M := Classical.decEq M
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
              psf hr M Salt).signingOracle pk sk
        let ((msg, σ), log) ← (simulateQ impl (adv.main pk)).run
        let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).verify pk msg σ
        return !log.wasQueried msg && verified)
      = (fun w : ((M × (Salt × Domain)) × Bool) × QueryLog (M →ₒ (Salt × Domain)) =>
            !w.2.wasQueried w.1.1.1 && w.1.2) <$>
          (simulateQ ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
              (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
              (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk)
            (adv.main pk >>= fun out =>
              (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run := by
    rw [← simulateQ_writerImpl_verify_fold]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun x => bind_congr fun v => congrArg pure ?_
    congr!
  rw [heq, withStateOracle_evalSPMF_eq, simulateQ_map, StateT.run'_eq, StateT.run_map]
  simp only [Functor.map_map]
  simp only [not_wasQueried_eq_decide_not_mem_toFinset]
  -- Factor the freshness mask through the kernel's `(output, cache, signedSet)` reshaping, then
  -- rewrite the WriterT run as the freshness vehicle `gpvRealImplFresh` via the kernel.
  rw [show ((fun a : (((M × (Salt × Domain)) × Bool) × QueryLog (M →ₒ (Salt × Domain))) ×
        (Salt × M →ₒ Range).QueryCache =>
      decide (a.1.1.1.1 ∉ (List.map (fun e => e.1) a.1.2).toFinset) && a.1.1.2) <$>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
          (randomOracle : QueryImpl (Salt × M →ₒ Range)
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
        ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
              (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk)
          (adv.main pk >>= fun out =>
            (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run)).run
        (∅ : (Salt × M →ₒ Range).QueryCache))
      = (fun z : ((M × (Salt × Domain)) × Bool) ×
            (Salt × M →ₒ Range).QueryCache × Finset M =>
          decide (z.1.1.1 ∉ z.2.2) && z.1.2) <$>
        ((fun z : (((M × (Salt × Domain)) × Bool) × QueryLog (M →ₒ (Salt × Domain))) ×
              (Salt × M →ₒ Range).QueryCache =>
            (z.1.1, z.2, (z.1.2.map (fun e => e.1)).toFinset)) <$>
          (simulateQ (gpvOuter M Salt)
            ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                  (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                    (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                  psf hr M Salt).signingOracle pk sk)
              (adv.main pk >>= fun out =>
                (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run)).run
            (∅ : (Salt × M →ₒ Range).QueryCache)) from by rw [Functor.map_map]; rfl,
    map_simulateQ_gpvOuter_writerLog_eq_gpvRealImplFresh]
  -- Bridge the flag-free run back to the flag handler that `realGameVerifyFresh` carries: the flag
  -- is passive, so projecting it away (`map_run_gpvRealImplFlagFresh_proj_flag`) recovers the
  -- flag-free run.
  rw [realGameVerifyFresh, ← map_run_gpvRealImplFlagFresh_proj_flag psf hr M Salt pk sk
    (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)
    ((∅, ∅), false)]
  simp only [Functor.map_map, Prod.map, id_eq]

open Classical in
/-- **Game-identification (N): the GPV EUF-CMA advantage is bounded by the keygen-averaged
programmed freshness verify-Bool game plus `collisionBound`.** Chains the keygen-averaging peel
`probOutput_unforgeableExp_eq_keygen_average`, the per-key WriterT-log → signed-set reconstruction
`signedSet_eq_wasQueried`, and the real↔programmed coupling hop
`gpv_realGameVerifyFresh_le_progGameVerifyFresh_add_collisionBound`, averaged over the key pair
`(pk, sk) ← hr.gen`.  It reduces closing the split bound to bounding the programmed game
`progGameVerifyFresh` (the remaining reservoir-sampling extraction). -/
theorem gpv_advantage_le_progGameVerifyFreshAvg_add_collisionBound
    [Inhabited Range] [Nonempty Salt]
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      Pr[= true | (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
        + collisionBound Salt qSign qHash := by
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
  rw [probOutput_bind_eq_tsum (𝒮[hr.gen] : SPMF (PK × SK)), probOutput_bind_eq_tsum
    (𝒮[hr.gen] : SPMF (PK × SK))]
  -- Average the per-key coupling hop over `(pk, sk) ← hr.gen`: weight each per-key bound by its
  -- keygen mass `Pr[= x | 𝒮[hr.gen]]`, pull the constant `collisionBound` out using
  -- `∑' x, Pr[= x | 𝒮[hr.gen]] ≤ 1`.
  have hper : ∀ x ∈ support hr.gen,
      Pr[= true | realGameVerifyFresh psf hr M Salt adv x.1 x.2] ≤
        Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1]
          + collisionBound Salt qSign qHash := fun x hx =>
    gpv_realGameVerifyFresh_le_progGameVerifyFresh_add_collisionBound psf hr M Salt
      x.1 x.2 adv domainSample qSign qHash (hQ x.1)
      (fun c => hNF x.1 x.2 hx c) (hreg x.1 x.2 hx)
  calc ∑' x : PK × SK,
        Pr[= x | 𝒮[hr.gen]] * Pr[= true | realGameVerifyFresh psf hr M Salt adv x.1 x.2]
      ≤ ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1]
          + Pr[= x | 𝒮[hr.gen]] * collisionBound Salt qSign qHash) :=
        ENNReal.tsum_le_tsum fun x => by
          by_cases hx : x ∈ support hr.gen
          · rw [← mul_add]; gcongr; exact hper x hx
          · have hzero : Pr[= x | (𝒮[hr.gen] : SPMF (PK × SK))] = 0 :=
              probOutput_eq_zero_of_not_mem_support (mx := hr.gen) hx
            simp [hzero]
    _ = ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1])
          + (∑' x : PK × SK, Pr[= x | 𝒮[hr.gen]]) * collisionBound Salt qSign qHash := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1])
          + 1 * collisionBound Salt qSign qHash := by
        gcongr
        exact tsum_probOutput_le_one
    _ = ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1])
          + collisionBound Salt qSign qHash := by rw [one_mul]

open Classical in
/-- **The forger queries its forgery point (standard random-oracle well-formedness).** For every
public key, every forgery `(msg, (r, s))` the adversary outputs in the programmed sign-then-hash
game lands on a random-oracle point `(r, msg)` that was already programmed during the adversary's
run — i.e. the forger queried `RO(r, msg)` before forging, so the verification read is a cache hit.
This is the textbook ROM convention (matching the "fresh forgery on a *programmed* point" framing of
the collision extraction): any adversary is transformed into one satisfying it by appending a single
hash query at its forgery point (absorbed into `qHash`).  It rules out the degenerate
"forge on a never-queried point" case, in which the verification read would program the point
*fresh* — a value independent of the forged preimage — which neither the collision nor the
programmed-preimage reduction observes. -/
@[expose] def ForgesQueriedPoint
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) : Prop :=
  ∀ (pk : PK), ∀ z ∈ support ((simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
      (adv.main pk)).run (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)),
    z.2.1.1 (z.1.2.1, z.1.1) ≠ none

omit [Fintype Salt] in
/-- **SL-C: the collision-finding advantage unfolds to an averaged collision-event
probability.** The success probability of the collision reduction in the keyed collision game is
exactly the chance, over a freshly generated public key `pk` and the reduction's candidate pair
`(x₁, x₂)`, that the pair is a genuine `psf.eval`-collision of two distinct short preimages.  This
exposes the collision event as a plain `Pr[= true | …]` so the Step-2 extraction can bound the
programmed game's distinct-collision mass against it. -/
theorem collisionFindingAdvantage_reduction_eq [DecidableEq Domain]
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    collisionFindingAdvantage (psf := psf) (hr := hr)
        (reduction psf hr M Salt adv domainSample)
      = Pr[= true | (do
          let pk ← (Prod.fst <$> hr.gen : ProbComp PK)
          let xs ← reduction psf hr M Salt adv domainSample pk
          pure (decide (xs.1 ≠ xs.2) &&
            decide (psf.eval pk xs.1 = psf.eval pk xs.2) &&
            psf.isShort xs.1 && psf.isShort xs.2) : ProbComp Bool)] := by
  unfold collisionFindingAdvantage collisionFindingExp
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Hidden programmed preimages are short.** Every preimage `s` in the support of the forward
sampler `domainSample pk` is accepted by the verifier's shortness predicate (`psf.isShort s`),
under PSF correctness `hcorrect` and the regularity equality `hreg` at `(pk, sk)`.

The forward-sampled `(psf.eval pk s, s)` lands in the support of the regularity LHS, hence — by the
distributional equality `hreg` — in the support of the RHS `do c ← $ᵗ Range; s' ← trapdoorSample pk
sk c; pure (c, s')`.  That exhibits `s` as a trapdoor preimage of the matching target `c`, so
`hcorrect` certifies `psf.isShort s`.  This is the shortness witness for the simulator's hidden
preimage recorded at each programmed random-oracle entry by the collision reduction. -/
lemma isShort_of_mem_support_domainSample
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hcorrect : psf.CorrectAt pk sk)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (s : Domain) (hs : s ∈ support (domainSample pk)) :
    psf.isShort s = true := by
  classical
  have hmemL : (psf.eval pk s, s) ∈
      support (do let s' ← domainSample pk; pure (psf.eval pk s', s') :
        ProbComp (Range × Domain)) := by
    simp only [support_bind, support_pure, Set.mem_iUnion]
    exact ⟨s, hs, rfl⟩
  have hmemR : (psf.eval pk s, s) ∈
      support (do let c ← ($ᵗ Range); let s' ← psf.trapdoorSample pk sk c; pure (c, s') :
        ProbComp (Range × Domain)) := by
    rw [← mem_support_evalSPMF_iff, ← hreg, mem_support_evalSPMF_iff]
    exact hmemL
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmemR
  obtain ⟨c, _hc, s', hs', heq1, heq2⟩ := hmemR
  subst heq2
  exact (hcorrect c s hs').2

omit [SampleableType Range] [Fintype Salt] in
/-- **The verification read is table-passive on a cache hit.** When the forged point `(r, msg)` is
already cached in the combined run state `st` with value `v`, running the GPV verification read
`gpvVerifyRead pk (msg, (r, s))` under the combined handler from `st` reads back `v`, returns the
verification Bool `decide (psf.eval pk s = v) && psf.isShort s`, and leaves the *entire* combined
state — cache, signed-set, flag, and hidden table — unchanged.  The verification read issues a
single random-oracle query at the forged point, which on a hit is a pure `get`/return. -/
lemma run_combined_gpvVerifyRead_of_cache_hit (domainSample : PK → ProbComp Domain) (pk : PK)
    (msg : M) (r : Salt) (s : Domain) (v : Range)
    (st : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hhit : st.1.1.1 (r, msg) = some v) :
    (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
        (gpvVerifyRead psf M Salt pk (msg, (r, s)))).run st =
      pure (decide (psf.eval pk s = v) && psf.isShort s, st) := by
  rw [gpvVerifyRead]
  rw [simulateQ_bind, simulateQ_query, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, StateT.run_map, simulateQ_pure,
    StateT.run_pure]
  rw [progGameRunImplCombined_run_inl_inr, hhit]
  simp only [id_eq, map_pure, pure_bind]

omit [SampleableType Range] [Fintype Salt] in
/-- **The verification continuation is table-passive on a cache hit.** The `verifyKont`-shaped
continuation `(out, ·) <$> gpvVerifyRead pk out` of the freshness verify game, run under the
combined handler from a state `st` whose cache hits the forged point with value `v`, returns the
pair of the forgery output `out` and the verification Bool, leaving the entire combined state
unchanged. -/
lemma run_combined_verifyKont_of_cache_hit (domainSample : PK → ProbComp Domain) (pk : PK)
    (msg : M) (r : Salt) (s : Domain) (v : Range)
    (st : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hhit : st.1.1.1 (r, msg) = some v) :
    (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
        ((fun w => ((msg, (r, s)), w)) <$>
          gpvVerifyRead psf M Salt pk (msg, (r, s)))).run st =
      pure (((msg, (r, s)), decide (psf.eval pk s = v) && psf.isShort s), st) := by
  rw [simulateQ_map, StateT.run_map,
    run_combined_gpvVerifyRead_of_cache_hit psf M Salt domainSample pk msg r s v st hhit]
  simp only [map_pure]

omit [Fintype Salt] in
/-- **`hForge` transported to the combined run.** Under `ForgesQueriedPoint`, every final state of
the combined run over `adv.main pk` (from the empty start) has its cache defined at the forged point
`(r⋆, msg⋆)`.  Projecting the combined run onto the game handler
(`map_run_progGameRunImplCombined_proj_table`) sends each combined final state to a game final
state, to which `hForge` applies; the cache component is preserved by the table projection. -/
lemma combined_cache_forge_point_ne_none (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (w : (M × (Salt × Domain)) ×
      ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)))
    (hw : w ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
      (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
        fun _ => none))) :
    w.2.1.1.1 (w.1.2.1, w.1.1) ≠ none := by
  have hproj := map_run_progGameRunImplCombined_proj_table psf M Salt domainSample pk
    (adv.main pk) ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)
  have hmem : (Prod.map id
      (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)) w ∈
      support ((simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
        (adv.main pk)).run (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)) := by
    rw [← hproj, support_map]
    exact ⟨w, hw, rfl⟩
  exact hForge pk _ hmem

open Classical in
omit [Fintype Salt] in
/-- **The programmed verify game success is a winning event on the combined run.** Projecting the
combined run over `adv.main pk >>= verifyKont` onto the game handler recovers the programmed
freshness verify game (`map_run_progGameRunImplCombined_proj_table`), so the game's success
probability equals the probability, over the combined run, of the *winning event*: the forged
message is fresh (not in the signed set) and the verification Bool is `true`. -/
lemma progGameVerifyFresh_eq_probEvent_combined (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
      = Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk >>= fun out =>
              (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  have hgame : Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
      = Pr[= true | (fun z : ((M × (Salt × Domain)) × Bool) ×
            (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
            decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
          (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
            (adv.main pk >>= fun out =>
              (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
            (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)] := rfl
  rw [hgame, ← map_run_progGameRunImplCombined_proj_table psf M Salt domainSample pk
    (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)
    ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
    ← probEvent_eq_eq_probOutput, Functor.map_map, probEvent_map]
  rfl

open Classical in
omit [Fintype Salt] in
/-- **The collision-reduction success is a collision event on the combined run.** The collision
reduction runs `reductionImpl` over `adv.main pk` and reads its hidden table at the forged point;
projecting the combined run onto `reductionImpl` (`map_run_progGameRunImplCombined_proj_reduction`)
re-expresses the reduction's collision-success probability as the probability, over the combined run
*of `adv.main pk` alone*, that the table records a hidden preimage `sHidden` at the forged point
with `(sHidden, s⋆)` a genuine `psf.eval`-collision of two distinct short preimages. -/
lemma reduction_collision_eq_probEvent_combined [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | (reduction psf hr M Salt adv domainSample pk >>= fun xs =>
        pure (decide (xs.1 ≠ xs.2) && decide (psf.eval pk xs.1 = psf.eval pk xs.2) &&
          psf.isShort xs.1 && psf.isShort xs.2) : ProbComp Bool)]
      = Pr[fun w : (M × (Salt × Domain)) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              ∃ sHidden : Domain, w.2.2 (w.1.2.1, w.1.1) = some sHidden ∧
                (decide (sHidden ≠ w.1.2.2) &&
                  decide (psf.eval pk sHidden = psf.eval pk w.1.2.2) &&
                  psf.isShort sHidden && psf.isShort w.1.2.2) = true |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  rw [reduction_eq_run_reductionImpl psf hr M Salt adv domainSample pk]
  rw [← map_run_progGameRunImplCombined_proj_reduction psf M Salt domainSample pk
    (adv.main pk) ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)]
  rw [← probEvent_eq_eq_probOutput, bind_assoc, bind_map_left, probEvent_bind_eq_tsum]
  conv_rhs => rw [← bind_pure ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
    (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)), probEvent_bind_eq_tsum]
  refine tsum_congr fun w => ?_
  congr 1
  rcases w with ⟨out, st⟩
  obtain ⟨msgStar, rStar, sStar⟩ := out
  simp only [Prod.map, id_eq]
  rcases hlk : st.2 (rStar, msgStar) with _ | sHidden
  · simp only [hlk, pure_bind, probEvent_pure, ne_eq, not_true_eq_false,
      decide_false, Bool.false_and]
    simp
  · simp only [hlk, pure_bind, probEvent_pure, Option.some.injEq, exists_eq_left']

open Classical in
omit [Fintype Salt] in
/-- **Pointwise distinct-collision transfer.** For any final state `(out, st)` of the combined run
over `adv.main pk` whose forged point is cached (guaranteed by `hForge`), the distinct-preimage
winning event on the verify-extended run implies the collision event on the table: the cache hit at
the forged point exhibits a hidden preimage `sHidden` with `psf.eval pk sHidden = psf.eval pk s⋆`
(the verifier's check), with `sHidden ≠ s⋆` (distinctness), and both short (`s⋆` by the verifier,
`sHidden` by `hcorrect`/`hreg` on the drawn preimage). -/
lemma distinct_implies_collision_pointwise [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hcorrect : psf.CorrectAt pk sk)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (out : M × (Salt × Domain))
    (st : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hmem : (out, st) ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
      (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
        fun _ => none)))
    (vb : Bool)
    (hvb : vb = (decide (psf.eval pk out.2.2 =
      (st.1.1.1 (out.2.1, out.1)).getD (psf.eval pk out.2.2)) && psf.isShort out.2.2))
    (hwin : (decide (out.1 ∉ st.1.1.2) && vb) = true)
    (hdist : st.2 (out.2.1, out.1) ≠ some out.2.2) :
    ∃ sHidden : Domain, st.2 (out.2.1, out.1) = some sHidden ∧
      (decide (sHidden ≠ out.2.2) && decide (psf.eval pk sHidden = psf.eval pk out.2.2) &&
        psf.isShort sHidden && psf.isShort out.2.2) = true := by
  -- Cache hit at the forged point (from `hForge`).
  have hcache_ne : st.1.1.1 (out.2.1, out.1) ≠ none :=
    combined_cache_forge_point_ne_none psf hr M Salt domainSample pk adv hForge (out, st) hmem
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hcache_ne
  -- Cache ⇒ table coherence: the hidden preimage and the eval relation.
  have hci : combinedCacheImpliesTableInv psf M Salt pk st :=
    progGameRunImplCombined_run_cacheImpliesTable psf M Salt domainSample pk (adv.main pk)
      _ (by intro t v ht; simp at ht) (out, st) hmem
  obtain ⟨sHidden, htbl, hveq⟩ := hci (out.2.1, out.1) v hv
  -- Table values are drawn preimages, hence short.
  have htd : combinedTableInDomainInv M Salt domainSample pk st :=
    progGameRunImplCombined_run_tableInDomain psf M Salt domainSample pk (adv.main pk)
      _ (by intro t d ht; simp at ht) (out, st) hmem
  have hHidden_mem : sHidden ∈ support (domainSample pk) := htd (out.2.1, out.1) sHidden htbl
  have hHidden_short : psf.isShort sHidden = true :=
    isShort_of_mem_support_domainSample psf domainSample pk sk hcorrect hreg sHidden hHidden_mem
  -- Unpack the winning Bool: verification holds, so `eval pk s⋆ = v` and `isShort s⋆`.
  rw [hvb] at hwin
  simp only [hv, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨_hfresh, hverify_eq, hshort_star⟩ := hwin
  -- Assemble the collision.
  refine ⟨sHidden, htbl, ?_⟩
  have hsHidden_ne : sHidden ≠ out.2.2 := by
    intro h; exact hdist (h ▸ htbl)
  have heval : psf.eval pk sHidden = psf.eval pk out.2.2 := by
    rw [← hveq, ← hverify_eq]
  simp only [hsHidden_ne, hverify_eq, hshort_star, hHidden_short, heval, decide_true,
    Bool.and_self, ne_eq, not_false_eq_true]

omit [SampleableType Range] [SampleableType Salt] in
/-- **Table-domain of a combined-run state.** The finite set of random-oracle keys `(r, m)` at
which the hidden-preimage table `s.2` of a `progGameRunImplCombined` state has recorded an entry.
Each entry was programmed by exactly one signing (`.inr`) or random-oracle-miss (`.inl (.inr)`)
query, so its cardinality is the number of programmed entries — the reservoir over which the
exact-match reduction guesses (`combined_run_table_card_le`). -/
noncomputable def combinedTableSupport [Fintype M]
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Finset (Salt × M) :=
  Finset.univ.filter (fun t => s.2 t ≠ none)

omit [DecidableEq Range] [SampleableType Range] [SampleableType Salt] in
/-- **Table-domain growth on writing one entry.** Overwriting the table at a single key `q` with
`some sd` enlarges the table-domain by at most one element (the key `q`); every other key's status
is unchanged. -/
lemma combinedTableSupport_write_card_le [Fintype M]
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (q : Salt × M) (sd : Domain)
    (s' : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs' : s'.2 = fun t' => if t' = q then some sd else s.2 t') :
    (combinedTableSupport M Salt s').card ≤ (combinedTableSupport M Salt s).card + 1 := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (le_trans (Finset.card_insert_le q (combinedTableSupport M Salt s)) (by rw [add_comm]))
  intro t ht
  simp only [combinedTableSupport, Finset.mem_filter, Finset.mem_univ, true_and, hs'] at ht
  simp only [Finset.mem_insert, combinedTableSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases htq : t = q
  · exact Or.inl htq
  · rw [if_neg htq] at ht
    exact Or.inr ht

omit [DecidableEq Range] [SampleableType Range] in
/-- **Table-domain growth through the whole combined run.** Over any adversary computation `oa`
making at most `qS` signing queries and `qH` random-oracle queries, every final state of the
combined run `progGameRunImplCombined` enlarges the table-domain by at most `qS + qH` entries:
uniform steps and random-oracle cache hits leave the table untouched, while each signing step and
each random-oracle miss writes a single key (`combinedTableSupport_write_card_le`), charged against
the residual signing or hash budget. -/
lemma combinedTableSupport_run_card_le [Fintype M] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
      (qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
        (combinedTableSupport M Salt y.2).card
          ≤ (combinedTableSupport M Salt s).card + qS + qH := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s qS qH _ _ y hy
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact le_add_right (Nat.le_add_right _ _)
  | query_bind t mx ih =>
      intro s qS qH hQS hQH y hy
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hy
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases (mem_support_bind_iff _ _ _).1 hy with ⟨⟨pv, pst⟩, hps, hy⟩
      rcases t with (n | mc) | msg
      · -- uniform query: table untouched, both budgets pass through
        rw [progGameRunImplCombined_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, hpv, hpst⟩ := hps
        subst pst
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        exact ih pv s qS qH hbS hbH y hy
      · -- random-oracle query: hit leaves the table fixed, miss writes one key
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqH : 0 < qH := by simpa using hQH1
        rw [progGameRunImplCombined_run_inl_inr] at hps
        cases hq : s.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            subst pst
            exact le_trans (ih pv s qS (qH - 1) hbS hbH y hy) (by omega)
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨sd, -, -, hpst⟩ := hps
            have hgrow : (combinedTableSupport M Salt pst).card
                ≤ (combinedTableSupport M Salt s).card + 1 :=
              combinedTableSupport_write_card_le M Salt s mc sd pst (by rw [hpst])
            exact le_trans (ih pv pst qS (qH - 1) hbS hbH y hy) (by omega)
      · -- signing query: writes one key, charged against the signing budget
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqS : 0 < qS := by simpa using hQS1
        rw [progGameRunImplCombined_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, sd, -, -, hpst⟩ := hps
        have hgrow : (combinedTableSupport M Salt pst).card
            ≤ (combinedTableSupport M Salt s).card + 1 :=
          combinedTableSupport_write_card_le M Salt s (r, msg) sd pst (by rw [hpst])
        exact le_trans (ih pv pst (qS - 1) qH hbS hbH y hy) (by omega)

omit [DecidableEq Range] [SampleableType Range] in
/-- **D1 — entry-count bound.** Starting from the empty hidden-preimage table, every final state of
the combined run of an adversary `oa` obeying `signHashQueryBound` records at most `qSign + qHash`
table entries.  This is the reservoir size over which the exact-match programmed-preimage reduction
samples its embedding slot in the GPV Step-2 collision extraction. -/
lemma combined_run_table_card_le [Fintype M] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (qSign qHash : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := β)
      (oa := oa) (qSign := qSign) (qHash := qHash))
    {y : β × ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
      ((Salt × M) → Option Domain))}
    (hmem : y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none))) :
    (combinedTableSupport M Salt y.2).card ≤ qSign + qHash := by
  have hbase : (combinedTableSupport M Salt
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
        (fun _ => none : (Salt × M) → Option Domain)))).card = 0 := by
    simp [combinedTableSupport]
  refine le_trans (combinedTableSupport_run_card_le psf M Salt domainSample pk oa _ qSign qHash
    hQ.1 hQ.2 y hmem) ?_
  rw [hbase]
  omega

open Classical in
omit [Fintype Salt] in
/-- **Distinct-collision transfer (probability level).** The distinct-preimage winning mass on the
combined verify-extended run is bounded by the collision event on the combined run of `adv.main pk`.
The verify continuation is table-passive on the cache hit (`run_combined_verifyKont_of_cache_hit`),
so the distinct event on the verify-extended run reduces, support-pointwise, to the distinct event
on `adv.main pk`'s final state, which the pointwise transfer `distinct_implies_collision_pointwise`
turns into the table collision. -/
lemma gpv_perKey_distinct_le_collision [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hcorrect : psf.CorrectAt pk sk)
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) ≠ some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ Pr[fun w : (M × (Salt × Domain)) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              ∃ sHidden : Domain, w.2.2 (w.1.2.1, w.1.1) = some sHidden ∧
                (decide (sHidden ≠ w.1.2.2) &&
                  decide (psf.eval pk sHidden = psf.eval pk w.1.2.2) &&
                  psf.isShort sHidden && psf.isShort w.1.2.2) = true |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum_subtype]
  conv_rhs => rw [← bind_pure ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
    (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)), probEvent_bind_eq_tsum_subtype]
  refine ENNReal.tsum_le_tsum fun p => ?_
  gcongr
  obtain ⟨⟨out, st⟩, hmem⟩ := p
  obtain ⟨msg, r, s⟩ := out
  rw [run_combined_verifyKont_of_cache_hit psf M Salt domainSample pk msg r s
      ((st.1.1.1 (r, msg)).getD (psf.eval pk s)) st ?_, probEvent_pure, probEvent_pure]
  · by_cases hwin : (decide (msg ∉ st.1.1.2) &&
        (decide (psf.eval pk s = (st.1.1.1 (r, msg)).getD (psf.eval pk s)) &&
          psf.isShort s)) = true ∧ st.2 (r, msg) ≠ some s
    · obtain ⟨sHidden, htbl, hcoll⟩ :=
        distinct_implies_collision_pointwise psf hr M Salt domainSample pk sk hcorrect hreg adv
          hForge (msg, (r, s)) st hmem _ rfl hwin.1 hwin.2
      rw [if_pos hwin, if_pos ⟨sHidden, htbl, hcoll⟩]
    · rw [if_neg hwin]
      exact zero_le
  · have hcache_ne : st.1.1.1 (r, msg) ≠ none :=
      combined_cache_forge_point_ne_none psf hr M Salt domainSample pk adv hForge
        ((msg, (r, s)), st) hmem
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hcache_ne
    rw [hv, Option.getD_some]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] [Fintype Salt] in
/-- **Reservoir per-step embedding mass.** At the `k`-th programmed entry the reservoir step of
`programmedPreimageReduction` draws `b ← $ᵗ Fin (k + 1)` and embeds the external target precisely
when `b = 0`, i.e. with probability `1 / (k + 1)`.  This is the atomic per-entry win probability of
the reservoir-sampling embedding: summing it telescopes to the uniform `1 / N` over the `N`
programmed entries that drives the multi-target `qSign + qHash` guessing loss. -/
lemma probOutput_reservoirStep_win (k : ℕ) :
    Pr[= (0 : Fin (k + 1)) | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))]
      = ((k : ℝ≥0∞) + 1)⁻¹ := by
  rw [probOutput_uniformSample]
  simp [Fintype.card_fin]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] [Fintype Salt] in
/-- **Reservoir per-step miss mass.** Complementary to `probOutput_reservoirStep_win`: at the
`k`-th programmed entry the reservoir step keeps the previous winner (draws `b ≠ 0`) with
probability `k / (k + 1)`.  This is the per-entry survival factor whose telescoping product over a
trace of `N` entries gives each fixed entry the uniform reservoir mass `1 / N`. -/
lemma probEvent_reservoirStep_miss (k : ℕ) :
    Pr[(· ≠ (0 : Fin (k + 1))) | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))]
      = (k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1) := by
  rw [probEvent_uniformSample]
  simp only [Fintype.card_fin]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_fin]

/-- **Pure reservoir winner-index process.** This abstracts the winner-selection coins of
`programmedPreimageReduction` away from all cache/value data: it runs `n` reservoir steps, and at
step `k` (the `k`-th programmed entry, with running count `k`) draws the reservoir coin
`b ← $ᵗ Fin (k + 1)`; on `b = 0` the new entry `k` becomes the winner, otherwise the current winner
survives.  The recorded winner is the index of the entry at which the reduction would embed its
external target.  Its winner marginal is the data-independent core of the reservoir analysis:
`probOutput_reservoirWinnerIndex_eq` shows each of the `N` entries is the winner with probability
exactly `1 / N`. -/
@[expose] noncomputable def reservoirWinnerIndex : ℕ → ProbComp (Option ℕ)
  | 0 => pure none
  | k + 1 => do
      let w ← reservoirWinnerIndex k
      let b ← ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))
      pure (if b = 0 then some k else w)

/-- One-step unfolding of `reservoirWinnerIndex` as an explicit double bind, used to feed the
per-step reservoir atoms (`probOutput_reservoirStep_win` / `probEvent_reservoirStep_miss`). -/
lemma reservoirWinnerIndex_succ (k : ℕ) :
    reservoirWinnerIndex (k + 1) = (reservoirWinnerIndex k >>= fun w =>
      ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
        pure (if b = 0 then some k else w)) := rfl

/-- **Reservoir survival sum.** The total mass of the non-winning coins `b ≠ 0` at the `k`-th
reservoir step is `k / (k + 1)`; this is `probEvent_reservoirStep_miss` rephrased as a `tsum`, the
per-step survival factor of a fixed prior winner. -/
lemma tsum_reservoirStep_survival (k : ℕ) :
    (∑' x : Fin (k + 1),
        (if x ≠ 0 then Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] else 0))
      = (k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1) := by
  rw [← probEvent_eq_tsum_ite, probEvent_uniformSample]
  simp only [Fintype.card_fin]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_fin]

/-- **Reservoir step, earlier target.** At the `k`-th reservoir step, for a fixed prior winner `w`
and a target index `j ≠ k`, the step lands on `some j` exactly when the coin misses (`b ≠ 0`) and
the prior winner already equals `some j`; that mass is the survival factor `k / (k + 1)` when
`w = some j`, and `0` otherwise. -/
lemma probOutput_reservoirStep_ne (k : ℕ) (w : Option ℕ) (j : ℕ) (hjk : j ≠ k) :
    Pr[= some j | (($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
        pure (if b = 0 then some k else w) : ProbComp (Option ℕ))]
      = (if w = some j then ((k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)) else 0) := by
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_pure]
  have hrw : ∀ x : Fin (k + 1),
      Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] *
        (if some j = if x = 0 then some k else w then (1 : ℝ≥0∞) else 0)
        = (if x ≠ 0 then Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] else 0) *
            (if w = some j then (1 : ℝ≥0∞) else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [if_true, ne_eq, not_true_eq_false, if_false, zero_mul]
      rw [if_neg (fun h => hjk (Option.some.inj h)), mul_zero]
    · rw [if_neg hx, if_pos (show x ≠ 0 from hx)]
      by_cases hw : w = some j
      · rw [if_pos hw, if_pos hw.symm]
      · rw [if_neg hw, if_neg (fun h => hw h.symm), mul_zero]
  rw [tsum_congr hrw, ENNReal.tsum_mul_right, tsum_reservoirStep_survival]
  by_cases hw : w = some j
  · rw [if_pos hw, if_pos hw, mul_one]
  · rw [if_neg hw, if_neg hw, mul_zero]

/-- **Reservoir step, new target.** At the `k`-th reservoir step, for any prior winner `w ≠ some k`,
the step lands on the new entry `some k` exactly when the coin hits (`b = 0`), with probability
`1 / (k + 1)` (`probOutput_reservoirStep_win`). -/
lemma probOutput_reservoirStep_eq (k : ℕ) (w : Option ℕ) (hw : w ≠ some k) :
    Pr[= some k | (($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
        pure (if b = 0 then some k else w) : ProbComp (Option ℕ))]
      = ((k : ℝ≥0∞) + 1)⁻¹ := by
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_pure]
  have hrw : ∀ x : Fin (k + 1),
      Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] *
        (if some k = if x = 0 then some k else w then (1 : ℝ≥0∞) else 0)
        = (if x = 0 then Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [if_true, mul_one]
    · simp only [if_neg hx]
      rw [if_neg (fun h => hw h.symm), mul_zero]
  rw [tsum_congr hrw, tsum_eq_single 0 (fun x hx => by rw [if_neg hx]), if_pos rfl,
    probOutput_uniformSample]
  simp [Fintype.card_fin]

/-- **Reservoir winner index is bounded.** Every winner index in the support of an `n`-step
reservoir run is strictly below `n`: a winner is only ever recorded at an entry that has already
been processed.  This guarantees the prior winner `w` from `reservoirWinnerIndex k` is never the
yet-unseen index `k`, the side condition consumed by `probOutput_reservoirStep_eq`. -/
lemma reservoirWinnerIndex_support_lt :
    ∀ (n : ℕ) (w : Option ℕ), w ∈ support (reservoirWinnerIndex n) →
      ∀ i, w = some i → i < n
  | 0, w, hw, i, hi => by
      simp only [reservoirWinnerIndex, support_pure, Set.mem_singleton_iff] at hw
      rw [hw] at hi; exact absurd hi (by simp)
  | k + 1, w, hw, i, hi => by
      rw [reservoirWinnerIndex_succ] at hw
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
      obtain ⟨w', hw', b, _, hwb⟩ := hw
      by_cases hb0 : b = 0
      · rw [if_pos hb0] at hwb
        rw [hwb] at hi
        have : i = k := Option.some.inj hi.symm
        omega
      · rw [if_neg hb0] at hwb
        rw [hwb] at hi
        exact Nat.lt_succ_of_lt (reservoirWinnerIndex_support_lt k w' hw' i hi)

/-- The pure reservoir winner-index process never fails: it is built from `pure` and the
never-failing uniform coin draws `$ᵗ Fin (k + 1)`. -/
lemma reservoirWinnerIndex_neverFail : ∀ n, NeverFail (reservoirWinnerIndex n)
  | 0 => by rw [reservoirWinnerIndex]; infer_instance
  | k + 1 => by
      rw [reservoirWinnerIndex]
      have := reservoirWinnerIndex_neverFail k
      exact NeverFail.bind_of_forall

/-- The winner marginal of the reservoir process is a genuine distribution: its outputs sum to `1`
(it never fails), so the per-index probabilities partition the unit mass. -/
lemma tsum_probOutput_reservoirWinnerIndex (n : ℕ) :
    ∑' w : Option ℕ, Pr[= w | reservoirWinnerIndex n] = 1 :=
  tsum_probOutput_eq_one' (reservoirWinnerIndex_neverFail n).probFailure_eq_zero

/-- **D2a — reservoir winner uniformity.** After `N` programmed entries, the reservoir winner is
each entry with probability exactly `1 / N`.  The winner marginal depends only on the reservoir
coins `b_k ← $ᵗ Fin (k + 1)` — drawn independently of every cache value — so it is computed purely
by the recursion `reservoirWinnerIndex`; the telescoping of the per-step embedding mass
`1 / (k + 1)` against the survival product `∏ k / (k + 1)` collapses to the uniform `1 / N`. This is
the
data-independent winner-selection core of the GPV Step-2 reservoir close, separable from the
embedding-indistinguishability coupling `hreg`. -/
lemma probOutput_reservoirWinnerIndex_eq :
    ∀ (N j : ℕ), j < N → Pr[= some j | reservoirWinnerIndex N] = (N : ℝ≥0∞)⁻¹
  | 0, j, hj => absurd hj (by omega)
  | k + 1, j, hj => by
      rw [reservoirWinnerIndex_succ, probOutput_bind_eq_tsum]
      by_cases hjk : j = k
      · -- the target is the new entry; every prior winner `w ≠ some j` loses to it
        subst hjk
        have hcongr : ∀ w : Option ℕ,
            Pr[= w | reservoirWinnerIndex j] *
              Pr[= some j | (($ᵗ Fin (j + 1) : ProbComp (Fin (j + 1))) >>= fun b =>
                pure (if b = 0 then some j else w) : ProbComp (Option ℕ))]
              = Pr[= w | reservoirWinnerIndex j] * ((j : ℝ≥0∞) + 1)⁻¹ := by
          intro w
          by_cases hw : w ∈ support (reservoirWinnerIndex j)
          · rw [probOutput_reservoirStep_eq j w (fun hwk =>
              absurd (reservoirWinnerIndex_support_lt j w hw j hwk) (by omega))]
          · rw [probOutput_eq_zero_of_not_mem_support hw, zero_mul, zero_mul]
        rw [tsum_congr hcongr, ENNReal.tsum_mul_right,
          tsum_probOutput_reservoirWinnerIndex, one_mul]
        push_cast; ring_nf
      · -- the target is an earlier entry `j < k`; it must survive (`b ≠ 0`) and already be `w`
        rw [tsum_congr (fun w => by rw [probOutput_reservoirStep_ne k w j hjk] :
          ∀ w : Option ℕ, Pr[= w | reservoirWinnerIndex k] *
              Pr[= some j | (($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
                pure (if b = 0 then some k else w) : ProbComp (Option ℕ))]
            = Pr[= w | reservoirWinnerIndex k] *
                (if w = some j then ((k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)) else 0))]
        rw [tsum_eq_single (some j) (fun w hw => by rw [if_neg (fun h => hw h), mul_zero]),
          if_pos rfl, probOutput_reservoirWinnerIndex_eq k j (by omega)]
        have hk : (k : ℝ≥0∞) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]; omega
        rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm ((k : ℝ≥0∞))⁻¹ ((k : ℝ≥0∞) + 1)⁻¹,
          mul_assoc, ENNReal.inv_mul_cancel hk (by simp), mul_one]
        push_cast
        ring_nf

/-- **D2b — the reservoir winner index always lands on a programmed entry.** Starting from at least
one programmed entry, the reservoir winner marginal places no mass on `none`: every run of
`reservoirWinnerIndex (N + 1)` selects one of the recorded slots.  This is the exhaustiveness fact
the in-fold lift consumes: the union of the per-slot winning events `{winner = some j}` exhausts the
winner marginal, so summing the per-slot uniform mass `1 / N` (`probOutput_reservoirWinnerIndex_eq`)
over the `N` slots recovers the whole probability with no leftover `none` branch. Proved by
partitioning the unit total mass (`tsum_probOutput_reservoirWinnerIndex`) into the `none` atom and
the `some j` atoms, the latter summing to `∑_{j < N} 1 / N = 1` by D2a together with the support
bound `reservoirWinnerIndex_support_lt`. -/
lemma probOutput_reservoirWinnerIndex_none_eq_zero (N : ℕ) (hN : N ≠ 0) :
    Pr[= (none : Option ℕ) | reservoirWinnerIndex N] = 0 := by
  have hsplit : ∑' w : Option ℕ, Pr[= w | reservoirWinnerIndex N]
      = Pr[= (none : Option ℕ) | reservoirWinnerIndex N]
        + ∑' j : ℕ, Pr[= some j | reservoirWinnerIndex N] := by
    rw [tsum_option _ ENNReal.summable]
  rw [tsum_probOutput_reservoirWinnerIndex] at hsplit
  have hsome : ∑' j : ℕ, Pr[= some j | reservoirWinnerIndex N] = 1 := by
    have hpt : ∀ j : ℕ,
        Pr[= some j | reservoirWinnerIndex N] = if j < N then (N : ℝ≥0∞)⁻¹ else 0 := by
      intro j
      by_cases hj : j < N
      · rw [if_pos hj, probOutput_reservoirWinnerIndex_eq N j hj]
      · rw [if_neg hj]
        exact probOutput_eq_zero_of_not_mem_support
          (fun hmem => hj (reservoirWinnerIndex_support_lt N (some j) hmem j rfl))
    rw [tsum_congr hpt,
      tsum_eq_sum (s := Finset.range N) (fun j hj => by rw [if_neg]; simpa using hj)]
    rw [Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj)])]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by exact_mod_cast hN) (by simp)]
  rw [hsome] at hsplit
  have h1 : Pr[= (none : Option ℕ) | reservoirWinnerIndex N] + 1 = 0 + 1 := by
    rw [zero_add]; exact hsplit.symm
  exact WithTop.add_right_cancel one_ne_top h1

/-- **D2b — reservoir winner uniform lower bound.** When the realized programmed-entry count `N` is
at most the multi-target budget `Q := qSign + qHash`, the reservoir winner lands on any fixed slot
`j < N` with probability at least `1 / Q`.  This converts the exact per-`N` uniformity of D2a
(`probOutput_reservoirWinnerIndex_eq`, each slot has mass exactly `1 / N`) into the budget-uniform
lower bound `1 / Q` that the multi-target factor `qSign + qHash` of the exact-match reduction pays:
since `N ≤ Q`, `1 / N ≥ 1 / Q`.  Lifting this per-slot bound into the in-fold run (where `N` and the
slot identities are adaptive, but always `N ≤ qSign + qHash` by `combined_run_table_card_le`) is the
data-independent core of the reservoir close. -/
lemma probOutput_reservoirWinnerIndex_ge (N j Q : ℕ) (hj : j < N) (hNQ : N ≤ Q) :
    (Q : ℝ≥0∞)⁻¹ ≤ Pr[= some j | reservoirWinnerIndex N] := by
  rw [probOutput_reservoirWinnerIndex_eq N j hj]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hNQ)

/-- **Pre-sampled-index programmed-preimage reduction.** Draws the embed index up front via
`reservoirWinnerIndex (qSign + qHash)` (uniform over the at-most-`qSign + qHash` programmed entries;
`none` only when there is no budget, mapped to an out-of-range index that never embeds), then runs
the adversary under `embedAtIndexImpl` from the empty state and returns the forged preimage. Unlike
the online reservoir handler, the embed index is fixed before the run, so the simulated random
oracle is consistent under re-query. -/
@[expose] noncomputable def programmedPreimageReduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ) :
    ProgrammedPreimageAdversary (PK := PK) (Domain := Domain) (Range := Range) :=
  fun pk y => do
    let wOpt ← reservoirWinnerIndex (qSign + qHash)
    let ((_msgStar, (_rStar, sStar)), _st) ←
      (simulateQ (embedAtIndexImpl psf M Salt domainSample pk (wOpt.getD (qSign + qHash)) y)
        (adv.main pk)).run ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
    pure sStar

omit [Fintype Salt] in
/-- **The pre-sampled-index reduction, unfolded to its index draw and handler run.** Restates the
reduction body in terms of the named handler `embedAtIndexImpl`: draw the embed index, run the
adversary under the handler from the empty state, and read off the forged preimage. -/
lemma programmedPreimageReduction_eq_run
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ) (pk : PK) (y : Range) :
    programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y =
      (do
        let wOpt ← reservoirWinnerIndex (qSign + qHash)
        let r ← (simulateQ (embedAtIndexImpl psf M Salt domainSample pk
            (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure r.1.2.2) := rfl

omit [Fintype Salt] in
/-- **Advantage of the pre-sampled-index reduction as an averaged exact-match probability.** The
success probability of the reduction in the keyed programmed-preimage game equals the chance,
averaged over a fresh key pair `(pk, sk) ← hr.gen` and a uniform target `y`, that the reduction
reproduces the challenger's hidden short preimage `x`. Exposes the exact-match event as a plain
`Pr[= true | …]` bind so the Step-2 extraction can average it against the same keygen mass. -/
theorem programmedPreimageAdvantage_reduction_eq [DecidableEq Domain]
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ) :
    programmedPreimageAdvantage (psf := psf) (hr := hr)
        (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash)
      = Pr[= true | (hr.gen >>= fun pksk => (do
          let y ← ($ᵗ Range : ProbComp Range)
          let x ← psf.trapdoorSample pksk.1 pksk.2 y
          let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash
            pksk.1 y
          pure (decide (x' = x))) : ProbComp Bool)] := by
  unfold programmedPreimageAdvantage programmedPreimageExp
  rfl

open Classical in
omit [Fintype Salt] in
/-- **SL-A: the 3-term averaging reduction skeleton.** Reduces the Step-2 keygen-averaged
programmed-game bound to a single per-key `(pk, sk)` bound by expanding all three advantage terms
over the common keygen mass `𝒮[hr.gen]`.  Given a per-key hypothesis `h` bounding the programmed
freshness game at `pk` by the reduction's collision event at `pk` plus the multi-target factor
`qSign + qHash` times the exact-match event at `(pk, sk)`, averaging `h` over `(pk, sk) ← hr.gen`
re-folds the right-hand averages into `collisionFindingAdvantage (reduction …)` (via SL-C, whose
`Prod.fst` keygen pushforward matches the full keygen mass) and `programmedPreimageAdvantage
(programmedPreimageReduction …)` (via its preimage analog). -/
theorem gpv_progGameVerifyFreshAvg_le_of_perKey [DecidableEq Domain]
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (h : ∀ pksk ∈ support hr.gen,
      Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
        ≤ Pr[= true | (reduction psf hr M Salt adv domainSample pksk.1 >>= fun xs =>
              pure (decide (xs.1 ≠ xs.2) &&
                decide (psf.eval pksk.1 xs.1 = psf.eval pksk.1 xs.2) &&
                psf.isShort xs.1 && psf.isShort xs.2) : ProbComp Bool)]
          + ((qSign + qHash : ℕ) : ENNReal) *
            Pr[= true | (do
              let y ← ($ᵗ Range : ProbComp Range)
              let x ← psf.trapdoorSample pksk.1 pksk.2 y
              let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash
                pksk.1 y
              pure (decide (x' = x)) : ProbComp Bool)]) :
    Pr[= true | (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
      ≤ collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample)
        + ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) := by
  classical
  rw [collisionFindingAdvantage_reduction_eq psf hr M Salt adv domainSample,
    programmedPreimageAdvantage_reduction_eq psf hr M Salt adv domainSample qSign qHash,
    bind_map_left]
  rw [probOutput_bind_eq_tsum (𝒮[hr.gen] : SPMF (PK × SK)),
    probOutput_bind_eq_tsum hr.gen, probOutput_bind_eq_tsum hr.gen]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support hr.gen
  · rw [mul_left_comm (↑(qSign + qHash) : ENNReal), ← mul_add]
    exact mul_le_mul' le_rfl (h x hx)
  · have hzero : Pr[= x | hr.gen] = 0 := probOutput_eq_zero_of_not_mem_support hx
    have hzero' : Pr[= x | (𝒮[hr.gen] : SPMF (PK × SK))] = 0 :=
      probOutput_eq_zero_of_not_mem_support (mx := hr.gen) hx
    simp [hzero, hzero']

omit [Fintype Salt] in
/-- **D0 — exact-match advantage as a target-averaged reservoir win.** The per-key exact-match term
of the programmed-preimage reduction expands, over the uniform target draw `y ← $ᵗ Range`, into the
weighted sum of the reduction's exact-match win probability at each fixed target `y`.  This is the
entry point for the reservoir analysis: the inner factor `Pr[= true | …]` is the success
probability of `programmedPreimageReduction … pk y` reproducing the trapdoor preimage `x` of the
fixed embedded target `y`, which the reservoir-sampling argument then bounds. -/
lemma programmedPreimage_perKey_eq_tsum [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let x ← psf.trapdoorSample pk sk y
        let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
        pure (decide (x' = x)) : ProbComp Bool)]
      = ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
          Pr[= true | (do
            let x ← psf.trapdoorSample pk sk y
            let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
            pure (decide (x' = x)) : ProbComp Bool)] := by
  rw [probOutput_bind_eq_tsum]

open Classical in
omit [Fintype Salt] in
/-- **Exact-match verify-strip (Step-2).** The exact-match winning mass on the combined
*verify-extended* run is bounded by the exact-match event on the combined run of `adv.main pk`
*alone*.  As in the distinct-preimage transfer `gpv_perKey_distinct_le_collision`, the verify
continuation is table-passive on the forced cache hit at the forged point
(`run_combined_verifyKont_of_cache_hit`, the forged point is cached by `hForge`), so the
verify-extended event reduces, support-pointwise, to the corresponding event on the final state of
`adv.main pk`'s combined run: the forged message is fresh, the recomputed verification holds, and
the hidden-preimage table records exactly the forged preimage `s⋆` at the forged point.

This is the exact-match twin of the distinct-branch verify-strip embedded in
`gpv_perKey_distinct_le_collision`; it separates the verify-elimination bookkeeping from the
reservoir coupling, leaving a per-key bound that reads only `adv.main pk`'s combined final state. -/
lemma gpv_perKey_exactMatch_verifyStrip_le
    (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ Pr[fun w : (M × (Salt × Domain)) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              (decide (w.1.1 ∉ w.2.1.1.2) &&
                  (decide (psf.eval pk w.1.2.2 =
                      (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                    psf.isShort w.1.2.2)) = true ∧
                w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum_subtype]
  conv_rhs => rw [← bind_pure ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
    (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)), probEvent_bind_eq_tsum_subtype]
  refine ENNReal.tsum_le_tsum fun p => ?_
  gcongr
  obtain ⟨⟨out, st⟩, hmem⟩ := p
  obtain ⟨msg, r, s⟩ := out
  have hhit : st.1.1.1 (r, msg) = some ((st.1.1.1 (r, msg)).getD (psf.eval pk s)) := by
    have hcache_ne : st.1.1.1 (r, msg) ≠ none :=
      combined_cache_forge_point_ne_none psf hr M Salt domainSample pk adv hForge
        ((msg, (r, s)), st) hmem
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hcache_ne
    rw [hv, Option.getD_some]
  rw [run_combined_verifyKont_of_cache_hit psf M Salt domainSample pk msg r s
      ((st.1.1.1 (r, msg)).getD (psf.eval pk s)) st hhit, probEvent_pure, probEvent_pure]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **N2 — embed-index handler counter bound.** Over any adversary computation `oa` making at most
`qS` signing queries and `qH` random-oracle queries, every final state of the pre-sampled-index
embedding run `embedAtIndexImpl … w y` advances the running programming counter `.2` by at most
`qS + qH`: uniform steps and random-oracle cache hits leave it untouched, while each signing step
and each random-oracle miss increments it by one (charged against the residual signing or hash
budget).  Starting from counter `0` this bounds the final counter by `qSign + qHash`, the reservoir
size over which `reservoirWinnerIndex` samples its embedding slot. -/
lemma embedAtIndexImpl_run_count_le (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (Salt × M →ₒ Range).QueryCache × ℕ) (qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      ∀ z ∈ support ((simulateQ (embedAtIndexImpl psf M Salt domainSample pk w y) oa).run s),
        z.2.2 ≤ s.2 + qS + qH := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s qS qH _ _ z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_add_right (Nat.le_add_right _ _)
  | query_bind t mx ih =>
      intro s qS qH hQS hQH z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: counter untouched, both budgets pass through
        rw [embedAtIndexImpl_run_inl_inl, map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = s := (Prod.ext_iff.mp hh).2
        have hpst2 : pst.2 = s.2 := by rw [hps']
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        exact le_trans (ih pv pst qS qH hbS hbH z hz) (by omega)
      · -- random-oracle query: hit leaves the counter fixed, miss increments by one
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqH : 0 < qH := by simpa using hQH1
        rw [embedAtIndexImpl_run_inl_inr] at hps
        cases hq : s.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have hpst2 : pst.2 = s.2 := by rw [← hpst]
            exact le_trans (ih pv pst qS (qH - 1) hbS hbH z hz) (by omega)
        | none =>
            rw [hq, map_eq_bind_pure_comp] at hps
            obtain ⟨sd, -, hpst⟩ := (mem_support_bind_iff _ _ _).1 hps
            simp only [Function.comp_apply] at hpst
            have hpst2 : pst.2 = s.2 + 1 := by
              have h2 := congrArg (Prod.snd ∘ Prod.snd) hpst
              split_ifs at h2 <;> simpa using h2
            exact le_trans (ih pv pst qS (qH - 1) hbS hbH z hz) (by omega)
      · -- signing query: increments the counter, charged against the signing budget
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqS : 0 < qS := by simpa using hQS1
        rw [embedAtIndexImpl_run_inr] at hps
        obtain ⟨r, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        rw [map_eq_bind_pure_comp] at hps
        obtain ⟨sd, -, hpst⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hpst
        have hpst2 : pst.2 = s.2 + 1 := by
          have h2 := congrArg (Prod.snd ∘ Prod.snd) hpst
          simpa using h2
        exact le_trans (ih pv pst (qS - 1) qH hbS hbH z hz) (by omega)

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **N2 (corollary) — embed-index counter bounded by the reservoir budget.** From the empty start
state `(∅, 0)`, every final state of the pre-sampled-index embedding run of an adversary `oa`
obeying `signHashQueryBound` has running programming counter at most `qSign + qHash`.  This is the
budget the reservoir winner index `reservoirWinnerIndex (qSign + qHash)` samples over. -/
lemma embedAtIndexImpl_run_count_le_budget (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (qSign qHash : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := β)
      (oa := oa) (qSign := qSign) (qHash := qHash))
    {z : β × ((Salt × M →ₒ Range).QueryCache × ℕ)}
    (hmem : z ∈ support ((simulateQ (embedAtIndexImpl psf M Salt domainSample pk w y) oa).run
      ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)))) :
    z.2.2 ≤ qSign + qHash := by
  have := embedAtIndexImpl_run_count_le psf M Salt domainSample pk w y oa
    ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)) qSign qHash hQ.1 hQ.2 z hmem
  simpa using this

end GPVHashAndSign
