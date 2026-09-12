/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
public import VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
public import VCVio.CryptoFoundations.FiatShamir.QueryBounds
public import VCVio.ProgramLogic.Relational.SimulateQ

import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
import all VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import all VCVio.CryptoFoundations.FiatShamir.QueryBounds
import all VCVio.ProgramLogic.Relational.SimulateQ
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.ForkBounds
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.ForkBounds

/-!
# Stateful Fiat-Shamir CMA-to-NMA reduction chain
-/

public section

universe u

open ENNReal OracleSpec OracleComp ProbComp OracleComp.ProgramLogic.Relational

namespace FiatShamir.Stateful

/-! Tag the CMA-to-NMA simulator handler family from `Sigma/CmaToNma.lean`
into the local `fs_simp` simp set. These defs live upstream (not under
`Sigma/Stateful/`), so we attach the FS-stateful local attribute here rather
than at the definition sites. -/

attribute [fs_simp]
  simulatedNmaFwd
  simulatedNmaUnifSim
  simulatedNmaRoSim
  simulatedNmaBaseSim
  simulatedNmaSigSim
  simulatedNmaImpl

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [Finite Chal] [Inhabited Chal]

attribute [local instance] instIsUniformSpecChalSingleton

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma forkLoggedProbImpl_run_bind_verify_eq_simulatedNma_aux
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) (M × (Commit × Resp))) :
    ((simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        (forkInitialState M Commit Chal) >>= fun x =>
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x.1 x.2)) =
    ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x.1 x.2) := by
  let : Fintype Chal := Fintype.ofFinite Chal
  obtain ⟨defaultChal, _⟩ := support_uniformSample_nonempty (α := Chal)
  let : Inhabited Chal := ⟨defaultChal⟩
  calc
    ((simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        (forkInitialState M Commit Chal) >>= fun x =>
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x.1 x.2))
        =
      (Prod.map id (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal)) <$>
        (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) oa).run
          (forkInitialState M Commit Chal)) >>= fun x =>
        simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x.1 x.2 := by
          simp only [bind_map_left, Prod.map_fst, id_eq, Prod.map_snd]
          exact bind_congr fun x => forkVerifyFreshComp_project (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x.1 x.2
    _ =
      ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x.1 x.2) := by
        rw [show
          Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
            (Chal := Chal)) <$>
              (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) simT pk) oa).run
                (forkInitialState M Commit Chal) =
            (simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT pk) oa).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) by
          have hrun := (forkLoggedProbOrnament (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT pk).run_eq oa
            (forkInitialState M Commit Chal)
            (forkInitialState_liveCacheAdvCacheInv (M := M) (Commit := Commit)
              (Chal := Chal))
          simpa [forkLoggedProj, forkInitialState, forkLoggedProbOrnament] using hrun]

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
          (signedFreshAdv σ hr M adv))
      =
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
      (forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ hr adv simT) := by
  let : Fintype Chal := Fintype.ofFinite Chal
  unfold QueryImpl.Stateful.runProb
  rw [← cmaSim_run_eq_nma_run_shiftLeft_cmaToNma (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT (signedFreshAdv σ hr M adv)]
  unfold QueryImpl.Stateful.run signedFreshAdv signedCandidateAdv candidateAdv
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]
  conv_lhs =>
    simp [cmaSim, cmaToNma, nma, nmaPublic, postKeygenCandidateAdv,
      SourceSigAlg, _root_.FiatShamir, forkH5Body, forkWrappedUniformImpl,
      forkLoggedImpl, forkInitialState, forkVerifyFreshComp, forkBaseImpl,
      simulatedNmaImpl, simulatedNmaBaseSim, cmaInit, cmaDataInit, cmaFrame,
      cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
      Functor.map_map]
  conv_rhs =>
    simp [cmaSim, cmaToNma, nma, nmaPublic, postKeygenCandidateAdv,
      SourceSigAlg, _root_.FiatShamir, forkH5Body, forkWrappedUniformImpl,
      forkLoggedImpl, forkInitialState, forkVerifyFreshComp, forkBaseImpl,
      simulatedNmaImpl, simulatedNmaBaseSim, cmaInit, cmaDataInit, cmaFrame,
      cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
      Functor.map_map]
  have hkeyLiftComp :
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (OracleComp.liftComp
            (hr.gen : OracleComp unifSpec (Stmt × Wit))
            (Fork.wrappedSpec Chal)) =
        (hr.gen : ProbComp (Stmt × Wit)) := by
    simpa using QueryImpl.simulateQ_liftComp_left_eq_of_apply
      (impl := QueryImpl.id' unifSpec +
        (uniformSampleImpl (spec := (Unit →ₒ Chal))))
      (impl₁ := QueryImpl.id' unifSpec)
      (h := fun t => by rfl)
      (oa := (hr.gen : OracleComp unifSpec (Stmt × Wit)))
  rw (occs := .pos [1]) [← hkeyLiftComp]
  change (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
      (OracleComp.liftComp
        (hr.gen : OracleComp unifSpec (Stmt × Wit))
        (Fork.wrappedSpec Chal)) >>= fun ps => _) =
    (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
      (OracleComp.liftComp
        (hr.gen : OracleComp unifSpec (Stmt × Wit))
        (Fork.wrappedSpec Chal)) >>= fun ps => _)
  apply bind_congr
  intro ps
  change _ =
    ((simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
          (forkInitialState M Commit Chal))) >>= fun x =>
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ ps.1 x.1 x.2))
  rw [forkLoggedProbImpl_run (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT ps.1 (adv.main ps.1) (forkInitialState M Commit Chal),
    forkLoggedProbImpl_run_bind_verify_eq_simulatedNma_aux (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) σ simT ps.1 (adv.main ps.1)]
  let st0 : List M × CmaState M Commit Chal Stmt Wit :=
    cmaSimFixedKeyInitialState (M := M) (Commit := Commit)
      (Chal := Chal) (Stmt := Stmt) (Wit := Wit) ps
  have hfixed :
      cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) ps.1 ps.2 st0 := by
    simp [st0, cmaSimFixedKeyInitialState, cmaSimFixedKeyInv]
  have hproj0 :
      cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) st0 =
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) := by
    ext t <;> cases t <;> simp [st0, cmaSimLoggedProj, cmaSimFixedKeyInitialState]
  have hcmaRun :
      Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
          (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
            hr simT) (adv.main ps.1)).run st0 =
        (simulateQ (simulatedNmaLoggedProbImpl (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) simT ps.1)
          (adv.main ps.1)).run
          ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) := by
    let : Fintype Chal := Fintype.ofFinite Chal
    simpa [hproj0, cmaSimLoggedLeftOrnament] using
      (cmaSimLoggedLeftOrnament (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT ps.1 ps.2).run_eq (adv.main ps.1) st0 hfixed
  have hrunExpanded :
      (simulateQ (QueryImpl.Stateful.linkWith
          (cmaFrame M Commit Chal Stmt Wit)
          (cmaToNma M Commit Chal simT)
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr))
        ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
          (liftM (adv.main ps.1) :
            OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))).run
          ([] : List M))).run
          ((([] : List M), (∅ : RoCache M Commit Chal), some ps), false) =
        (fun z : (M × (Commit × Resp)) ×
            (List M × CmaState M Commit Chal Stmt Wit) => ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
            hr simT) (adv.main ps.1)).run st0 := by
    simpa [cmaSim, st0, cmaSimFixedKeyInitialState] using
      cmaSimLoggedImpl_liftAdv_run_expanded (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT (adv.main ps.1) st0.2
  unfold cmaFrame cmaOuterLens cmaNmaLens at hrunExpanded
  rw [hrunExpanded]
  calc
    _ =
      (Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
          (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
            hr simT) (adv.main ps.1)).run st0) >>= fun x =>
          simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ ps.1 x.1 x.2 := by
        simp only [bind_map_left]
        refine bind_congr fun x => ?_
        have hproject := cmaSimVerifyFreshComp_project (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp)
          (Stmt := Stmt) (Wit := Wit) simT ps.1 x.1 x.2
        simpa [cmaFrame, cmaOuterLens, cmaNmaLens, cmaSim,
          _root_.FiatShamir, monad_norm] using hproject
    _ =
      ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
        simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ ps.1 x.1 x.2) := by
        rw [hcmaRun]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
/-- H5 boundary in shifted-NMA form. This is the fork-side statement after the
native H4 normalization has moved `cmaSim` to `nma ∘ cmaToNma`. The bound is in
terms of the verify-wrapped adversary `nmaAdvFromCmaWithFinalQuery` at fork
slot parameter `qH` (the framework's `Fin (qH + 1)` indexing accommodates the
wrapper's verifier-point query). -/
theorem nma_runProb_shiftLeft_signedFreshAdv_le_fork
    [Finite Chal] [Finite Commit] [Finite Resp]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          (nmaInit M Commit Chal Stmt Wit)
          ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
            (signedFreshAdv σ hr M adv))]
      ≤ Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
          qH := by
  let : Fintype Chal := Fintype.ofFinite Chal
  have hbridge :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            (nmaInit M Commit Chal Stmt Wit)
            ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
              (signedFreshAdv σ hr M adv))]
        =
      Pr[= true |
          forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr adv simT] := by
    rw [nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT]
    exact probOutput_simulateQ_forkWrappedUniformImpl
      (Chal := Chal)
      (oa := forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ hr adv simT) true
  have hbody := forkH5Body_prob_true_le_fork_advantage (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    adv simT hQ
  exact hbridge.trans_le hbody

/-! ## H3 cost factoring -/

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- The final freshness/verification continuation performs no signing queries,
hence contributes zero cumulative H3 signing cost. -/
private lemma verifyFreshComp_expectedQuerySlack_eq_zero
    (G : QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (CmaData M Commit Chal Stmt Wit × Bool) (OracleComp unifSpec)))
    (ε : CmaData M Commit Chal Stmt Wit → ℝ≥0∞)
    (p : (Stmt × (M × (Commit × Resp))) × List M)
    (qS : ℕ)
    (s : CmaData M Commit Chal Stmt Wit × Bool) :
    expectedQuerySlack G
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      ε
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) p)
      qS s = 0 := by
  rcases p with ⟨⟨pk, msg, sig⟩, signed⟩
  rcases sig with ⟨c, resp⟩
  rcases s with ⟨s, bad⟩
  cases bad
  · change expectedQuerySlack G
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        ε
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro (msg, c))) >>= fun a =>
          pure (!decide (msg ∈ signed) && σ.verify pk c a resp))
        qS (s, false) = 0
    rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free] <;> simp [IsCostlyQuery]
  · simp [verifyFreshComp, expectedQuerySlack_bad_eq_zero]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Tight native H3 bound for the freshness-preserving adversary, using the
candidate/verifier split so the final verifier hash query is not charged to H3
signing replacement. -/
private theorem signedFreshAdv_H3_bound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ENNReal.ofReal (cmaH3Advantage M Commit Chal σ hr simT
      (signedFreshAdv σ hr M adv)) ≤
      (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β := by
  let A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv
  let Apre : OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) :=
    signedCandidateAdv σ hr M adv
  have h_cost_candidate :
      cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β Apre qS ≤
        (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β :=
    cmaH3ExpectedLoss_le_queryBounds M Commit Chal σ hr ζ_zk β Apre
      (signedCandidateAdv_isQueryBoundP_costly (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
      (signedCandidateAdv_isQueryBoundP_hash (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
  have h_cost_bind :
      cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β A qS =
        cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β Apre qS := by
    simp only [A, Apre, signedFreshAdv, cmaH3ExpectedLoss]
    exact expectedQuerySlack_bind_eq_of_right_zero
      (cmaReal M Commit Chal σ hr)
      (cmaH3Costly (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEpsCore M Commit Chal ζ_zk β)
      (signedCandidateAdv σ hr M adv)
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (fun x q p => verifyFreshComp_expectedQuerySlack_eq_zero (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (G := cmaReal M Commit Chal σ hr)
        (ε := cmaSignEpsCore M Commit Chal ζ_zk β) x q p)
      qS (cmaInit M Commit Chal Stmt Wit)
  exact cmaReal_cmaSim_advantage_le_H3_bound_of_expectedQuerySlack
    M Commit Chal σ hr simT ζ_zk β A qS
    ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β)
    (cmaH3StepFacts_of_hvzk_predictability M Commit Chal σ hr simT
      ζ_zk β hζ_zk hHVZK hCommit)
    (cmaH3RunFacts_of_queryBound_expectedLoss M Commit Chal σ hr ζ_zk β A qS
      ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β)
      (by
        simpa [A] using signedFreshAdv_isQueryBoundP_costly (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          adv qS qH hQ)
      (by rwa [h_cost_bind]))

/-! ## H4: linked simulation as shifted NMA execution -/

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Native H4 hop in probability form. -/
theorem cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool) :
    (cmaSim M Commit Chal hr simT).runProb
        (cmaInit M Commit Chal Stmt Wit) A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) A) :=
  cmaSim_run_eq_nma_run_shiftLeft_cmaToNma (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT A

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
/-- Convert the shifted-NMA H5 boundary into the linked simulated-CMA form used
by the top-level chain. -/
theorem cmaSim_signedFreshAdv_le_fork_of_shifted_h5
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qH : ℕ)
    (hH5 :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            (nmaInit M Commit Chal Stmt Wit)
            ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
              (signedFreshAdv σ hr M adv))] ≤
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
          qH) :
    Pr[= true |
        (cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit)
          (signedFreshAdv σ hr M adv)] ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
        qH := by
  rwa [cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT (signedFreshAdv σ hr M adv)]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
/-- Native H5 boundary in the linked simulated-CMA form used by the top-level
chain. -/
theorem cmaSim_signedFreshAdv_le_fork
    [Finite Chal] [Finite Commit] [Finite Resp]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true |
        (cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit)
          (signedFreshAdv σ hr M adv)] ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
        qH :=
  cmaSim_signedFreshAdv_le_fork_of_shifted_h5 (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) adv simT qH
    (nma_runProb_shiftLeft_signedFreshAdv_le_fork (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Stmt := Stmt) (Wit := Wit) adv simT qS qH hQ)

/-! ## Top-level chain factored over H5 -/

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
/-- Native stateful top-level chain, assuming the H5 replay-forking boundary.

This theorem carries the H1/H2/H3/H4 arithmetic directly in the stateful chain.
The bound is in terms of the verify-wrapped adversary
`nmaAdvFromCmaWithFinalQuery` at fork slot parameter `qH`. -/
theorem cma_advantage_le_fork_bound_of_h5
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (hH1H2 :
      adv.advantage (FiatShamir.runtime M) ≤
        Pr[= true | (cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) (signedFreshAdv σ hr M adv)])
    (hH5 :
      Pr[= true |
          (cmaSim M Commit Chal hr simT).runProb
            (cmaInit M Commit Chal Stmt Wit)
            (signedFreshAdv σ hr M adv)] ≤
        Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH) :
    adv.advantage (FiatShamir.runtime M) ≤
      Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
        ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β := by
  let A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv
  have hζ_zk_lt : ENNReal.ofReal ζ_zk < ∞ := ENNReal.ofReal_lt_top
  have hHVZK' : σ.HVZK simT (ENNReal.ofReal ζ_zk).toReal := by
    rwa [ENNReal.toReal_ofReal hζ_zk]
  have hH3_abs :
      ENNReal.ofReal
          (((cmaReal M Commit Chal σ hr).runProb
              (cmaInit M Commit Chal Stmt Wit) A).boolDistAdvantage
            ((cmaSim M Commit Chal hr simT).runProb
              (cmaInit M Commit Chal Stmt Wit) A))
        ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
    simpa [A, cmaH3Advantage, QueryImpl.Stateful.advantage] using
      signedFreshAdv_H3_bound (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv simT (ENNReal.ofReal ζ_zk) β hζ_zk_lt hHVZK' hPredSim qS qH hQ
  have hH3_prob :
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb
        (cmaInit M Commit Chal Stmt Wit) A] ≤
      Pr[= true | (cmaSim M Commit Chal hr simT).runProb
        (cmaInit M Commit Chal Stmt Wit) A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
    le_trans
      (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        ((cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) A)
        ((cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit) A))
      (add_le_add le_rfl hH3_abs)
  calc
    adv.advantage (FiatShamir.runtime M)
        ≤ Pr[= true | (cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) A] := by
            simpa [A] using hH1H2
    _ ≤ Pr[= true | (cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit) A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) := hH3_prob
    _ ≤ Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
        add_le_add hH5 le_rfl
    _ = Fork.advantage σ hr M
            (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg qS), ENNReal.ofReal_natCast]
        ring_nf

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Native stateful chain with H5 discharged by the replay-forking boundary,
leaving only the public-to-stateful H1/H2 compatibility premise. -/
theorem cma_advantage_le_fork_bound_of_h1h2
    [Finite Commit] [Finite Resp]
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (hH1H2 :
      adv.advantage (FiatShamir.runtime M) ≤
        Pr[= true | (cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) (signedFreshAdv σ hr M adv)]) :
    adv.advantage (FiatShamir.runtime M) ≤
      Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
        ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β :=
  cma_advantage_le_fork_bound_of_h5 (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT ζ_zk hζ_zk hHVZK β hPredSim
    adv qS qH hQ hH1H2
    (cmaSim_signedFreshAdv_le_fork (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Stmt := Stmt) (Wit := Wit) adv simT qS qH hQ)

end FiatShamir.Stateful
