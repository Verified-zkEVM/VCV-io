/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.DataEncapMech
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
import VCVio.EvalDist.Defs.LawfulSemantics

/-!
# KEM + DEM Composition

This file defines the textbook KEM+DEM public-key encryption construction and the proof-ladders A1
reduction skeleton against the repo's existing KEM and one-time IND-CPA interfaces.
-/

universe u v

open OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {m : Type → Type v} {K PK SK CKEM M CDEM : Type}

/-- Textbook KEM+DEM composition. The composed scheme inherits the KEM execution method. -/
def composeWithDEM [Monad m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM) :
    AsymmEncAlg m M PK SK (CKEM × CDEM) where
  keygen := kem.keygen
  encrypt := fun pk msg => do
    let (c₁, k) ← kem.encaps pk
    let c₂ ← dem.encrypt k msg
    return (c₁, c₂)
  decrypt := fun sk c => do
    let k? ← kem.decaps sk c.1
    match k? with
    | none => return none
    | some k => return some (← dem.decrypt k c.2)

section Correct

variable [DecidableEq K] [DecidableEq M] [Monad m] [HasEvalSPMF m]

/-- From KEM correctness at the monadic probability level, every reachable decapsulation of an
honest ciphertext returns the encapsulated key. -/
private lemma kem_decaps_mem_support
    {kem : KEMScheme m K PK SK CKEM}
    (hkem : Pr[= true | kem.CorrectExp] = 1)
    {pk : PK} {sk : SK} (hks : (pk, sk) ∈ support kem.keygen)
    {c : CKEM} {k : K} (hck : (c, k) ∈ support (kem.encaps pk))
    {kOpt : Option K} (hkOpt : kOpt ∈ support (kem.decaps sk c)) :
    kOpt = some k := by
  have hsup : support kem.CorrectExp = {true} :=
    (probOutput_eq_one_iff (mx := kem.CorrectExp) (x := true)).mp hkem |>.2
  rw [KEMScheme.CorrectExp] at hsup
  have : decide (kOpt = some k) ∈ ({true} : Set Bool) := by
    rw [← hsup]
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      decide_eq_decide, exists_prop, Prod.exists]
    exact ⟨pk, sk, hks, c, k, hck, kOpt, hkOpt, Iff.rfl⟩
  simpa using this

/-- If a KEM and externally keyed DEM are both perfectly correct in the concrete probabilistic
semantics of `m`, then their composition is also perfectly correct. -/
theorem perfectlyCorrect_composeWithDEM
    [LawfulMonad m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM)
    (hkem : Pr[= true | kem.CorrectExp] = 1)
    (hdem : ∀ k : K, ∀ msg : M, Pr[= true | dem.CorrectExp k msg] = 1) :
    ∀ msg, Pr[= true | (kem.composeWithDEM dem).CorrectExp msg] = 1 := by
  intro msg
  simp only [AsymmEncAlg.CorrectExp, composeWithDEM]
  rw [← hkem]
  unfold KEMScheme.CorrectExp
  simp only [monad_norm]
  apply probOutput_bind_congr
  intro ⟨pk, sk⟩ hks
  apply probOutput_bind_congr
  intro ⟨kc, k⟩ hck
  rw [probOutput_bind_bind_swap
    (mx := dem.encrypt k msg)
    (my := kem.decaps sk kc)
    (f := fun dc kOpt => do
      let msgOpt ← (
        match kOpt with
        | none => return none
        | some k' => return some (← dem.decrypt k' dc))
      return decide (msgOpt = some msg))
    (z := true)]
  apply probOutput_bind_congr
  intro kOpt hkOpt
  have hkEq := kem_decaps_mem_support hkem hks hck hkOpt
  subst hkEq
  simp only [probOutput_pure]
  simpa [DEMScheme.CorrectExp, bind_assoc]
    using (hdem k msg)

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- Left KEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. -/
def composeWithDEM_toKEMLeftReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    kem.IND_CPA_Adversary where
  State := M × adversary.State
  preChallenge pk := do
    let (m₀, _m₁, st) ← adversary.chooseMessages pk
    return (m₀, st)
  postChallenge st kc k := do
    let dc ← dem.encrypt k st.1
    adversary.distinguish st.2 (kc, dc)

/-- Right KEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. -/
def composeWithDEM_toKEMRightReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    kem.IND_CPA_Adversary where
  State := M × adversary.State
  preChallenge pk := do
    let (_m₀, m₁, st) ← adversary.chooseMessages pk
    return (m₁, st)
  postChallenge st kc k := do
    let dc ← dem.encrypt k st.1
    adversary.distinguish st.2 (kc, dc)

/-- DEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. It samples
the public key and KEM ciphertext during the message-selection phase so that the simulatee sees
the same `encaps`-then-`encrypt` effect order as the composed scheme. -/
def composeWithDEM_toDEMReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    dem.IND_CPA_Adversary where
  State := CKEM × adversary.State
  chooseMessages := do
    let (pk, _sk) ← kem.keygen
    let (m₀, m₁, st) ← adversary.chooseMessages pk
    let (kc, _k) ← kem.encaps pk
    return (m₀, m₁, (kc, st))
  distinguish st dc := do
    adversary.distinguish st.2 (st.1, dc)

/-- Proof-ladders A1 reduction statement: the one-time IND-CPA advantage of textbook KEM+DEM is
bounded by two KEM IND-CPA advantages plus one DEM IND-CPA advantage, using the canonical
left/right and DEM reductions defined above.

The proof goes via signed advantage and a 3-hop hybrid argument over the four "leaf" SPMFs
indexed by (real/random KEM key) × (left/right message). Each game's `signedBoolAdv` decomposes
as `(s_X - s_Y)/2` for two of these four leaves, and the standard real triangle inequality then
gives the stated bound after dividing by `2`. The decomposition uses
`SPMF.signedBoolAdv_bind_uniformBool` (in `SecExp.lean`) once per game; the runtime hypotheses
`[Lawful]` and `[LiftCoherent]` push `runtime.evalDist` through the bind structure of each
game body.

**Runtime scope.** The `[ProbCompRuntime.Lawful runtime]` hypothesis restricts this theorem
to runtimes whose `evalDist` is a monad morphism. This holds for the canonical
`ProbCompRuntime.probComp` runtime but **not** for `withStateOracle`-style runtimes such as
`FiatShamir.runtime` (any ROM-based instantiation). Generalizing the bound to ROM-based
KEM-DEM constructions (e.g. ML-KEM, where the underlying KEM/DEM use a hash modeled as a
random oracle) would require replacing `[Lawful]` with shape-specific bind lemmas; the
building block is `withStateOracle_evalDist_bind_liftM` in
`OracleComp.SimSemantics.BundledSemantics`. TODO: factor an ROM-friendly variant once a
concrete consumer needs it. -/
theorem ind_cpa_one_time_bias_advantage_compose_with_dem_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    [ProbCompRuntime.Lawful runtime] [ProbCompRuntime.LiftCoherent runtime]
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM dem) runtime adversary ≤
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMRightReduction dem adversary) +
      dem.IND_CPA_Advantage runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) := by
  -- The four "leaf" SPMFs, packaged as `OracleComp`s. These are the corners of the four-game
  -- diamond: real-or-random KEM key × left-or-right adversary message.
  let A_rL : OracleComp spec Bool := do
    let (pk, _) ← kem.keygen
    let (m₀, _m₁, st) ← adversary.chooseMessages pk
    let (kc, k) ← kem.encaps pk
    let dc ← dem.encrypt k m₀
    adversary.distinguish st (kc, dc)
  let A_rR : OracleComp spec Bool := do
    let (pk, _) ← kem.keygen
    let (_m₀, m₁, st) ← adversary.chooseMessages pk
    let (kc, k) ← kem.encaps pk
    let dc ← dem.encrypt k m₁
    adversary.distinguish st (kc, dc)
  let A_rndL : OracleComp spec Bool := do
    let (pk, _) ← kem.keygen
    let (m₀, _m₁, st) ← adversary.chooseMessages pk
    let (kc, _kReal) ← kem.encaps pk
    let kRand ← runtime.liftProbComp ($ᵗ K)
    let dc ← dem.encrypt kRand m₀
    adversary.distinguish st (kc, dc)
  let A_rndR : OracleComp spec Bool := do
    let (pk, _) ← kem.keygen
    let (_m₀, m₁, st) ← adversary.chooseMessages pk
    let (kc, _kReal) ← kem.encaps pk
    let kRand ← runtime.liftProbComp ($ᵗ K)
    let dc ← dem.encrypt kRand m₁
    adversary.distinguish st (kc, dc)
  -- Step 1: show the LHS one-time game's `signedBoolAdv` decomposes as
  -- `((evalDist A_rL).signedBoolAdv - (evalDist A_rR).signedBoolAdv) / 2`.
  have h_LHS_form :
      AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem) adversary runtime =
      (do
        let t ← (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)
        let z ← if t then runtime.evalDist A_rL else runtime.evalDist A_rR
        pure (t == z) : SPMF Bool) := by
    unfold AsymmEncAlg.IND_CPA_OneTime_Game KEMScheme.composeWithDEM
    simp only [ProbCompRuntime.Lawful.evalDist_bind, ProbCompRuntime.Lawful.evalDist_pure,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp]
    refine bind_congr fun b => ?_
    cases b
    · simp [A_rR, ProbCompRuntime.Lawful.evalDist_bind, bind_pure_comp]
    · simp [A_rL, ProbCompRuntime.Lawful.evalDist_bind, bind_pure_comp]
  have h_uniformBool_fail :
      Pr[⊥ | (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)] = 0 := by simp
  have h_uniformBool_half :
      Pr[= true | (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)] = 1 / 2 := by
    simp [Fintype.card_bool]
  have h_LHS_signed :
      (AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem)
          adversary runtime).signedBoolAdv =
      ((runtime.evalDist A_rL).signedBoolAdv - (runtime.evalDist A_rR).signedBoolAdv) / 2 := by
    rw [h_LHS_form]
    exact SPMF.signedBoolAdv_uniformBool_branch _ _ _ h_uniformBool_fail h_uniformBool_half
  -- Step 2: expose `kRand`-augmented variants of `A_rL` and `A_rR` so the natural shape of the
  -- KEM-LEFT/RIGHT game bodies (which always sample `kRand` regardless of `b`) factors cleanly
  -- through the prefix lemma. The SPMFs of these augmented variants agree with the canonical
  -- `A_rL`, `A_rR` because `liftProbComp ($ᵗ K)` is total (no failure mass).
  let A_rL_KL : OracleComp spec Bool := do
    let (pk, _) ← kem.keygen
    let (m₀, _m₁, st) ← adversary.chooseMessages pk
    let (kc, k) ← kem.encaps pk
    let _kRand ← runtime.liftProbComp ($ᵗ K)
    let dc ← dem.encrypt k m₀
    adversary.distinguish st (kc, dc)
  let A_rR_KR : OracleComp spec Bool := do
    let (pk, _) ← kem.keygen
    let (_m₀, m₁, st) ← adversary.chooseMessages pk
    let (kc, k) ← kem.encaps pk
    let _kRand ← runtime.liftProbComp ($ᵗ K)
    let dc ← dem.encrypt k m₁
    adversary.distinguish st (kc, dc)
  have h_uniformK_fail :
      Pr[⊥ | (𝒟[($ᵗ K : ProbComp K)] : SPMF K)] = 0 := by
    change Pr[⊥ | ($ᵗ K : ProbComp K)] = 0
    exact probFailure_uniformSample K
  -- Bridge: the unused `kRand` sample doesn't shift any output probability.
  have h_AL_pr : ∀ y : Bool,
      Pr[= y | runtime.evalDist A_rL_KL] = Pr[= y | runtime.evalDist A_rL] := by
    intro y
    simp only [A_rL_KL, A_rL, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp]
    refine probOutput_bind_congr' _ y ?_; intro ⟨pk, _sk⟩
    refine probOutput_bind_congr' _ y ?_; intro ⟨m₀, _m₁, st⟩
    refine probOutput_bind_congr' _ y ?_; intro ⟨kc, k⟩
    rw [probOutput_bind_const, h_uniformK_fail, tsub_zero, one_mul]
  have h_AR_pr : ∀ y : Bool,
      Pr[= y | runtime.evalDist A_rR_KR] = Pr[= y | runtime.evalDist A_rR] := by
    intro y
    simp only [A_rR_KR, A_rR, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp]
    refine probOutput_bind_congr' _ y ?_; intro ⟨pk, _sk⟩
    refine probOutput_bind_congr' _ y ?_; intro ⟨_m₀, m₁, st⟩
    refine probOutput_bind_congr' _ y ?_; intro ⟨kc, k⟩
    rw [probOutput_bind_const, h_uniformK_fail, tsub_zero, one_mul]
  have h_AL_signedBoolAdv :
      (runtime.evalDist A_rL_KL).signedBoolAdv = (runtime.evalDist A_rL).signedBoolAdv :=
    SPMF.signedBoolAdv_congr h_AL_pr
  have h_AR_signedBoolAdv :
      (runtime.evalDist A_rR_KR).signedBoolAdv = (runtime.evalDist A_rR).signedBoolAdv :=
    SPMF.signedBoolAdv_congr h_AR_pr
  -- Step 3: KEM-LEFT signed advantage decomposition.
  have h_KEMLEFT_form :
      kem.IND_CPA_Game runtime (kem.composeWithDEM_toKEMLeftReduction dem adversary) =
      (do
        let a ← runtime.evalDist (do
          let (pk, _sk) ← kem.keygen
          let (m₀, _m₁, st) ← adversary.chooseMessages pk
          pure (pk, m₀, st))
        let t ← (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)
        let z ← if t then runtime.evalDist (do
            let (kc, k) ← kem.encaps a.1
            let _kRand ← runtime.liftProbComp ($ᵗ K)
            let dc ← dem.encrypt k a.2.1
            adversary.distinguish a.2.2 (kc, dc))
          else runtime.evalDist (do
            let (kc, _kReal) ← kem.encaps a.1
            let kRand ← runtime.liftProbComp ($ᵗ K)
            let dc ← dem.encrypt kRand a.2.1
            adversary.distinguish a.2.2 (kc, dc))
        pure (t == z) : SPMF Bool) := by
    unfold KEMScheme.IND_CPA_Game KEMScheme.composeWithDEM_toKEMLeftReduction
    simp only [ProbCompRuntime.Lawful.evalDist_bind, ProbCompRuntime.Lawful.evalDist_pure,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp, monad_norm]
    refine bind_congr fun pk_sk => ?_
    refine bind_congr fun mst => ?_
    refine bind_congr fun b => ?_
    cases b
    · simp
    · simp
  have h_KEMLEFT_pref_real :
      (do
        let a ← runtime.evalDist (do
          let (pk, _sk) ← kem.keygen
          let (m₀, _m₁, st) ← adversary.chooseMessages pk
          pure (pk, m₀, st))
        runtime.evalDist (do
          let (kc, k) ← kem.encaps a.1
          let _kRand ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt k a.2.1
          adversary.distinguish a.2.2 (kc, dc)) : SPMF Bool) =
      runtime.evalDist A_rL_KL := by
    simp only [A_rL_KL, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.Lawful.evalDist_pure, ProbCompRuntime.LiftCoherent.evalDist_liftProbComp,
      monad_norm]
  have h_KEMLEFT_pref_rand :
      (do
        let a ← runtime.evalDist (do
          let (pk, _sk) ← kem.keygen
          let (m₀, _m₁, st) ← adversary.chooseMessages pk
          pure (pk, m₀, st))
        runtime.evalDist (do
          let (kc, _kReal) ← kem.encaps a.1
          let kRand ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt kRand a.2.1
          adversary.distinguish a.2.2 (kc, dc)) : SPMF Bool) =
      runtime.evalDist A_rndL := by
    simp only [A_rndL, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.Lawful.evalDist_pure, ProbCompRuntime.LiftCoherent.evalDist_liftProbComp,
      monad_norm]
  have h_KEMLEFT_signed :
      (kem.IND_CPA_Game runtime
        (kem.composeWithDEM_toKEMLeftReduction dem adversary)).signedBoolAdv =
      ((runtime.evalDist A_rL).signedBoolAdv -
        (runtime.evalDist A_rndL).signedBoolAdv) / 2 := by
    rw [h_KEMLEFT_form]
    rw [SPMF.signedBoolAdv_bind_uniformBool _ _ _ _ h_uniformBool_fail h_uniformBool_half]
    rw [h_KEMLEFT_pref_real, h_KEMLEFT_pref_rand, h_AL_signedBoolAdv]
  -- Step 4: KEM-RIGHT signed advantage decomposition (mirror of Step 3 with `m₁`).
  have h_KEMRIGHT_form :
      kem.IND_CPA_Game runtime (kem.composeWithDEM_toKEMRightReduction dem adversary) =
      (do
        let a ← runtime.evalDist (do
          let (pk, _sk) ← kem.keygen
          let (_m₀, m₁, st) ← adversary.chooseMessages pk
          pure (pk, m₁, st))
        let t ← (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)
        let z ← if t then runtime.evalDist (do
            let (kc, k) ← kem.encaps a.1
            let _kRand ← runtime.liftProbComp ($ᵗ K)
            let dc ← dem.encrypt k a.2.1
            adversary.distinguish a.2.2 (kc, dc))
          else runtime.evalDist (do
            let (kc, _kReal) ← kem.encaps a.1
            let kRand ← runtime.liftProbComp ($ᵗ K)
            let dc ← dem.encrypt kRand a.2.1
            adversary.distinguish a.2.2 (kc, dc))
        pure (t == z) : SPMF Bool) := by
    unfold KEMScheme.IND_CPA_Game KEMScheme.composeWithDEM_toKEMRightReduction
    simp only [ProbCompRuntime.Lawful.evalDist_bind, ProbCompRuntime.Lawful.evalDist_pure,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp, monad_norm]
    refine bind_congr fun pk_sk => ?_
    refine bind_congr fun mst => ?_
    refine bind_congr fun b => ?_
    cases b
    · simp
    · simp
  have h_KEMRIGHT_pref_real :
      (do
        let a ← runtime.evalDist (do
          let (pk, _sk) ← kem.keygen
          let (_m₀, m₁, st) ← adversary.chooseMessages pk
          pure (pk, m₁, st))
        runtime.evalDist (do
          let (kc, k) ← kem.encaps a.1
          let _kRand ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt k a.2.1
          adversary.distinguish a.2.2 (kc, dc)) : SPMF Bool) =
      runtime.evalDist A_rR_KR := by
    simp only [A_rR_KR, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.Lawful.evalDist_pure, ProbCompRuntime.LiftCoherent.evalDist_liftProbComp,
      monad_norm]
  have h_KEMRIGHT_pref_rand :
      (do
        let a ← runtime.evalDist (do
          let (pk, _sk) ← kem.keygen
          let (_m₀, m₁, st) ← adversary.chooseMessages pk
          pure (pk, m₁, st))
        runtime.evalDist (do
          let (kc, _kReal) ← kem.encaps a.1
          let kRand ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt kRand a.2.1
          adversary.distinguish a.2.2 (kc, dc)) : SPMF Bool) =
      runtime.evalDist A_rndR := by
    simp only [A_rndR, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.Lawful.evalDist_pure, ProbCompRuntime.LiftCoherent.evalDist_liftProbComp,
      monad_norm]
  have h_KEMRIGHT_signed :
      (kem.IND_CPA_Game runtime
        (kem.composeWithDEM_toKEMRightReduction dem adversary)).signedBoolAdv =
      ((runtime.evalDist A_rR).signedBoolAdv -
        (runtime.evalDist A_rndR).signedBoolAdv) / 2 := by
    rw [h_KEMRIGHT_form]
    rw [SPMF.signedBoolAdv_bind_uniformBool _ _ _ _ h_uniformBool_fail h_uniformBool_half]
    rw [h_KEMRIGHT_pref_real, h_KEMRIGHT_pref_rand, h_AR_signedBoolAdv]
  -- Step 5: DEM signed advantage decomposition. Here `b` is at the top of the game body, so the
  -- no-prefix variant of the lemma applies. The two leaves both sample `kRand`; they differ only
  -- in whether the encrypted message is the second (`m₁`, b=true) or first (`m₀`, b=false).
  -- Define helper leaves matching the DEM body shape (kRand sampled before keygen).
  let A_DEMb_real : OracleComp spec Bool := do
    let kRand ← runtime.liftProbComp ($ᵗ K)
    let (pk, _sk) ← kem.keygen
    let (_m₀, m₁, st) ← adversary.chooseMessages pk
    let (kc, _) ← kem.encaps pk
    let dc ← dem.encrypt kRand m₁
    adversary.distinguish st (kc, dc)
  let A_DEMb_rand : OracleComp spec Bool := do
    let kRand ← runtime.liftProbComp ($ᵗ K)
    let (pk, _sk) ← kem.keygen
    let (m₀, _m₁, st) ← adversary.chooseMessages pk
    let (kc, _) ← kem.encaps pk
    let dc ← dem.encrypt kRand m₀
    adversary.distinguish st (kc, dc)
  have h_DEM_form :
      dem.IND_CPA_Game runtime (kem.composeWithDEM_toDEMReduction dem adversary) =
      (do
        let t ← (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)
        let z ← if t then runtime.evalDist A_DEMb_real else runtime.evalDist A_DEMb_rand
        pure (t == z) : SPMF Bool) := by
    unfold DEMScheme.IND_CPA_Game KEMScheme.composeWithDEM_toDEMReduction
    simp only [ProbCompRuntime.Lawful.evalDist_bind, ProbCompRuntime.Lawful.evalDist_pure,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp, monad_norm]
    refine bind_congr fun b => ?_
    cases b
    · simp [A_DEMb_rand]
    · simp [A_DEMb_real]
  -- Bridges from DEM-shape leaves to canonical A_rndL/A_rndR via three bind-swaps moving the
  -- `kRand` sample past `keygen`, `chooseMessages`, and `encaps` (all independent of `kRand`).
  have h_DEMb_real_pr : ∀ y : Bool,
      Pr[= y | runtime.evalDist A_DEMb_real] = Pr[= y | runtime.evalDist A_rndR] := by
    intro y
    simp only [A_DEMb_real, A_rndR, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp]
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_congr' _ y ?_; intro pk_sk
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_congr' _ y ?_; intro mst
    rw [probOutput_bind_bind_swap]
  have h_DEMb_rand_pr : ∀ y : Bool,
      Pr[= y | runtime.evalDist A_DEMb_rand] = Pr[= y | runtime.evalDist A_rndL] := by
    intro y
    simp only [A_DEMb_rand, A_rndL, ProbCompRuntime.Lawful.evalDist_bind,
      ProbCompRuntime.LiftCoherent.evalDist_liftProbComp]
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_congr' _ y ?_; intro pk_sk
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_congr' _ y ?_; intro mst
    rw [probOutput_bind_bind_swap]
  have h_DEMb_real_signedBoolAdv :
      (runtime.evalDist A_DEMb_real).signedBoolAdv =
        (runtime.evalDist A_rndR).signedBoolAdv :=
    SPMF.signedBoolAdv_congr h_DEMb_real_pr
  have h_DEMb_rand_signedBoolAdv :
      (runtime.evalDist A_DEMb_rand).signedBoolAdv =
        (runtime.evalDist A_rndL).signedBoolAdv :=
    SPMF.signedBoolAdv_congr h_DEMb_rand_pr
  have h_DEM_signed :
      (dem.IND_CPA_Game runtime
        (kem.composeWithDEM_toDEMReduction dem adversary)).signedBoolAdv =
      ((runtime.evalDist A_rndR).signedBoolAdv -
        (runtime.evalDist A_rndL).signedBoolAdv) / 2 := by
    rw [h_DEM_form]
    rw [SPMF.signedBoolAdv_uniformBool_branch _ _ _ h_uniformBool_fail h_uniformBool_half]
    rw [h_DEMb_real_signedBoolAdv, h_DEMb_rand_signedBoolAdv]
  -- Step 6: triangle inequality on signed advantages, then convert back to bias advantages.
  -- The four signedBoolAdv's at the diamond corners satisfy the linear identity
  --   2 * signedBoolAdv(LHS) = (sAL - sAR)
  --                          = (sAL - sAndL) - (sAR - sAndR) - (sAndR - sAndL)
  --                          = 2 * signedBoolAdv(KEMLEFT) - 2 * signedBoolAdv(KEMRIGHT)
  --                            - 2 * signedBoolAdv(DEM).
  -- Taking absolute values and using the standard triangle inequality on real numbers gives the
  -- claimed bound on the bias advantages (since boolBiasAdvantage = |signedBoolAdv|).
  unfold AsymmEncAlg.IND_CPA_OneTime_biasAdvantage KEMScheme.IND_CPA_Advantage
    DEMScheme.IND_CPA_Advantage
  rw [SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv,
      SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv,
      SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv,
      SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv]
  rw [h_LHS_signed, h_KEMLEFT_signed, h_KEMRIGHT_signed, h_DEM_signed]
  -- Goal: |(sAL - sAR) / 2| ≤
  --       |(sAL - sAndL) / 2| + |(sAR - sAndR) / 2| + |(sAndR - sAndL) / 2|.
  set sAL := (runtime.evalDist A_rL).signedBoolAdv
  set sAR := (runtime.evalDist A_rR).signedBoolAdv
  set sAndL := (runtime.evalDist A_rndL).signedBoolAdv
  set sAndR := (runtime.evalDist A_rndR).signedBoolAdv
  have h_decomp : (sAL - sAR) / 2 =
      (sAL - sAndL) / 2 + (-((sAR - sAndR) / 2)) + (-((sAndR - sAndL) / 2)) := by ring
  rw [h_decomp]
  calc |(sAL - sAndL) / 2 + (-((sAR - sAndR) / 2)) + (-((sAndR - sAndL) / 2))|
      _ ≤ |(sAL - sAndL) / 2 + (-((sAR - sAndR) / 2))| + |(-((sAndR - sAndL) / 2))| :=
          abs_add_le _ _
      _ ≤ (|(sAL - sAndL) / 2| + |(-((sAR - sAndR) / 2))|) + |(-((sAndR - sAndL) / 2))| := by
          gcongr; exact abs_add_le _ _
      _ = |(sAL - sAndL) / 2| + |(sAR - sAndR) / 2| + |(sAndR - sAndL) / 2| := by
          rw [abs_neg, abs_neg]

/-! ## Generalized form: LHS rewrite under `LiftBindCoherent`

The **LHS** of the KEMDEM bound — the one-time IND-CPA game's `signedBoolAdv` — admits a
branch-game decomposition using only the weaker `[LiftBindCoherent runtime]` hypothesis. This is
the easy half of the bound: the hidden bit `b ← liftProbComp ($ᵗ Bool)` is at the top of the
OneTime game body, so a single `evalDist_liftProbComp_bind` extracts it without needing to push
`evalDist` past any non-lift binds. The two per-branch obligations are then closed by
`monad_norm`-driven OracleComp bind normalization plus `evalDist_bind_pure_comp` to fold the
trailing `pure (b == b')`.

The KEM and DEM sides of the full bound additionally need `BindLiftSwap` (to commute the buried
hidden bit and the unused `kRand` sample past `keygen`/`preChallenge`/`encaps`); a full
`_general` proof is sketched in the comment block below but not yet wired up. `BindLiftSwap`
for `withStateOracle` runtimes — needed for ROM applicability — requires a swap lemma derivable
from `roSim.run'_liftM_bind` plus `ProbComp` bind-commutativity, but isn't in the repo as of
writing. -/
omit [SampleableType K] in
theorem ind_cpa_one_time_signed_eq_branch_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    [ProbCompRuntime.LiftBindCoherent runtime]
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    let A_rL : OracleComp spec Bool := do
      let (pk, _) ← kem.keygen
      let (m₀, _m₁, st) ← adversary.chooseMessages pk
      let (kc, k) ← kem.encaps pk
      let dc ← dem.encrypt k m₀
      adversary.distinguish st (kc, dc)
    let A_rR : OracleComp spec Bool := do
      let (pk, _) ← kem.keygen
      let (_m₀, m₁, st) ← adversary.chooseMessages pk
      let (kc, k) ← kem.encaps pk
      let dc ← dem.encrypt k m₁
      adversary.distinguish st (kc, dc)
    (AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem)
        adversary runtime).signedBoolAdv =
      ((runtime.evalDist A_rL).signedBoolAdv -
        (runtime.evalDist A_rR).signedBoolAdv) / 2 := by
  intro A_rL A_rR
  have h_form :
      AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem) adversary runtime =
      (do
        let t ← (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)
        let z ← if t then runtime.evalDist A_rL else runtime.evalDist A_rR
        pure (t == z) : SPMF Bool) := by
    unfold AsymmEncAlg.IND_CPA_OneTime_Game KEMScheme.composeWithDEM
    rw [ProbCompRuntime.LiftBindCoherent.evalDist_liftProbComp_bind]
    refine bind_congr fun b => ?_
    cases b <;>
      simp [A_rL, A_rR, monad_norm, ← ProbCompRuntime.LiftBindCoherent.evalDist_bind_pure_comp]
  -- Apply branch-game signed-advantage decomposition.
  have h_uniformBool_fail :
      Pr[⊥ | (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)] = 0 := by simp
  have h_uniformBool_half :
      Pr[= true | (𝒟[($ᵗ Bool : ProbComp Bool)] : SPMF Bool)] = 1 / 2 := by
    simp [Fintype.card_bool]
  rw [h_form]
  exact SPMF.signedBoolAdv_uniformBool_branch _ _ _ h_uniformBool_fail h_uniformBool_half

/-! ## Generalized KEMDEM bound: foundations under `LiftBindCoherent + BindLiftSwap`

The original `ind_cpa_one_time_bias_advantage_compose_with_dem_le` requires
`[Lawful runtime] [LiftCoherent runtime]`, which excludes ROM-style runtimes built on
`SPMFSemantics.withStateOracle` (e.g. `FiatShamir.runtimeWithCache`). The strictly weaker
typeclasses `[LiftBindCoherent runtime] [BindLiftSwap runtime]` (in
`VCVio.EvalDist.Defs.LawfulSemantics`) are satisfied by ROM-style runtimes via
`SPMFSemantics.withStateOracle_evalDist_bind_liftM_swap` and the canonical
`ProbCompRuntime.withStateOracle` instances. They are also satisfied by every
`Lawful + LiftCoherent` runtime via a generic derivation, so any future `_general` theorem
under these classes will subsume the original.

The two helpers below — generic enough to be reused across any KEM/DEM-shaped game — package
the central manoeuvre needed: dropping an unused `liftProbComp ($ᵗ K)` sample. Combined with
`SPMF.signedBoolAdv_uniformBool_branch` (in `SecExp.lean`) and
`ind_cpa_one_time_signed_eq_branch_le` (above), they reduce a full `_general` proof to
mechanical KEM-LEFT / KEM-RIGHT / DEM `BindLiftSwap` chains plus the triangle inequality.

A sketch of the full proof (with each `simp only [Lawful.evalDist_bind, ...]` step replaced by
the corresponding `BindLiftSwap` + `LiftBindCoherent` rewrite chain) is folded into the docs
agents `proof-workflows.md`. Closing it is the natural follow-up to wiring the typeclasses. -/

/-- Helper: a `liftProbComp ($ᵗ K)` sample buried after a one-binder prefix collapses out of
`runtime.evalDist` because the sample's value is unused. Combines `BindLiftSwap` (to surface)
plus `LiftBindCoherent` (to factor) plus totality of `$ᵗ K` (no failure). -/
lemma evalDist_drop_kRand_after_one
    (runtime : ProbCompRuntime (OracleComp spec))
    [ProbCompRuntime.LiftBindCoherent runtime] [ProbCompRuntime.BindLiftSwap runtime]
    {α β : Type} (pref : OracleComp spec α) (rest : α → OracleComp spec β) :
    runtime.evalDist (pref >>= fun a =>
        runtime.liftProbComp ($ᵗ K) >>= fun _ => rest a) =
      runtime.evalDist (pref >>= rest) := by
  rw [ProbCompRuntime.BindLiftSwap.evalDist_bind_liftProbComp_swap pref ($ᵗ K)
    (fun a _ => rest a)]
  rw [ProbCompRuntime.LiftBindCoherent.evalDist_liftProbComp_bind ($ᵗ K)
    (fun _ => pref >>= rest)]
  -- Goal: SPMF identity `𝒟[$ᵗ K] >>= fun _ => evalDist (pref >>= rest) = evalDist (pref >>= rest)`.
  -- Pointwise via `evalDist_ext` + `probOutput_bind_const` + `probFailure_uniformSample = 0`.
  have h := evalDist_ext (m := SPMF) (n := SPMF)
    (mx := (𝒟[($ᵗ K : ProbComp K)] : SPMF K) >>= fun _ =>
      runtime.evalDist (pref >>= rest))
    (mx' := runtime.evalDist (pref >>= rest))
    (fun y => by
      rw [probOutput_bind_const]
      rw [show Pr[⊥ | (𝒟[($ᵗ K : ProbComp K)] : SPMF K)] = 0 by
        change Pr[⊥ | ($ᵗ K : ProbComp K)] = 0
        exact probFailure_uniformSample K]
      rw [tsub_zero, one_mul])
  simpa using h

/-- Helper: a `liftProbComp ($ᵗ K)` sample buried after a three-binder prefix collapses out.
Reduces to `evalDist_drop_kRand_after_one` after pairing the three prefix outputs into a tuple
so the sample sits behind a single composite binder. -/
lemma evalDist_drop_kRand_after_three
    (runtime : ProbCompRuntime (OracleComp spec))
    [ProbCompRuntime.LiftBindCoherent runtime] [ProbCompRuntime.BindLiftSwap runtime]
    {α₁ α₂ α₃ β : Type} (p₁ : OracleComp spec α₁) (p₂ : α₁ → OracleComp spec α₂)
    (p₃ : α₁ → α₂ → OracleComp spec α₃)
    (rest : α₁ → α₂ → α₃ → OracleComp spec β) :
    runtime.evalDist (p₁ >>= fun x₁ => p₂ x₁ >>= fun x₂ => p₃ x₁ x₂ >>= fun x₃ =>
        runtime.liftProbComp ($ᵗ K) >>= fun _ => rest x₁ x₂ x₃) =
      runtime.evalDist (p₁ >>= fun x₁ => p₂ x₁ >>= fun x₂ => p₃ x₁ x₂ >>= fun x₃ =>
        rest x₁ x₂ x₃) := by
  rw [show (p₁ >>= fun x₁ => p₂ x₁ >>= fun x₂ => p₃ x₁ x₂ >>= fun x₃ =>
        runtime.liftProbComp ($ᵗ K) >>= fun _ => rest x₁ x₂ x₃) =
      ((p₁ >>= fun x₁ => p₂ x₁ >>= fun x₂ => p₃ x₁ x₂ >>= fun x₃ => pure (x₁, x₂, x₃)) >>=
        fun t => runtime.liftProbComp ($ᵗ K) >>= fun _ => rest t.1 t.2.1 t.2.2) by
    simp [bind_assoc]]
  rw [evalDist_drop_kRand_after_one runtime
    (p₁ >>= fun x₁ => p₂ x₁ >>= fun x₂ => p₃ x₁ x₂ >>= fun x₃ => pure (x₁, x₂, x₃))
    (fun t => rest t.1 t.2.1 t.2.2)]
  congr 1
  simp [bind_assoc]

end IND_CPA

end KEMScheme
