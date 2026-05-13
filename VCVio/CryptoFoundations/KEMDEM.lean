/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.DataEncapMech
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
import VCVio.ProgramLogic.Relational.Quantitative

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
  simpa [DEMScheme.CorrectExp, monad_norm]
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

The runtime coherence hypotheses require `runtime.evalDist` to be a monad morphism (preserves
`pure` and distributes `>>=`) and to produce total distributions on `Bool` (no failure mass).
These hold for all standard runtime constructions, including `withStateOracle`. -/
theorem ind_cpa_one_time_bias_advantage_compose_with_dem_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem))
    (heval_pure : ∀ {α : Type} (a : α),
        runtime.evalDist (pure a : OracleComp spec α) = pure a)
    (heval_bind : ∀ {α β : Type} (mx : OracleComp spec α)
        (f : α → OracleComp spec β),
        runtime.evalDist (mx >>= f) =
        runtime.evalDist mx >>= fun a => runtime.evalDist (f a))
    (heval_liftProbComp : ∀ {α : Type} (pc : ProbComp α),
        runtime.evalDist (runtime.liftProbComp pc) = 𝒟[pc])
    (hno_fail : ∀ (mx : OracleComp spec Bool),
        Pr[= true | runtime.evalDist mx] +
        Pr[= false | runtime.evalDist mx] = 1) :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM dem) runtime adversary ≤
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMRightReduction dem adversary) +
      dem.IND_CPA_Advantage runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) := by
  -- Derived: runtime.evalDist preserves map
  have heval_map : ∀ {α β : Type} (g : α → β) (mx : OracleComp spec α),
      runtime.evalDist (g <$> mx) = g <$> runtime.evalDist mx := by
    intro α β g mx
    simp only [map_eq_bind_pure_comp, Function.comp_def, heval_bind]
    congr 1; funext a; exact heval_pure (g a)
  -- Four intermediate SPMFs (hidden bit fixed):
  let real_m₀ : SPMF Bool := runtime.evalDist do
    let (pk, _) ← kem.keygen
    let (m₀, _, st) ← adversary.chooseMessages pk
    let (kc, k) ← kem.encaps pk
    let dc ← dem.encrypt k m₀
    adversary.distinguish st (kc, dc)
  let rand_m₀ : SPMF Bool := runtime.evalDist do
    let (pk, _) ← kem.keygen
    let (m₀, _, st) ← adversary.chooseMessages pk
    let (kc, _) ← kem.encaps pk
    let kR ← runtime.liftProbComp ($ᵗ K)
    let dc ← dem.encrypt kR m₀
    adversary.distinguish st (kc, dc)
  let rand_m₁ : SPMF Bool := runtime.evalDist do
    let (pk, _) ← kem.keygen
    let (_, m₁, st) ← adversary.chooseMessages pk
    let (kc, _) ← kem.encaps pk
    let kR ← runtime.liftProbComp ($ᵗ K)
    let dc ← dem.encrypt kR m₁
    adversary.distinguish st (kc, dc)
  let real_m₁ : SPMF Bool := runtime.evalDist do
    let (pk, _) ← kem.keygen
    let (_, m₁, st) ← adversary.chooseMessages pk
    let (kc, k) ← kem.encaps pk
    let dc ← dem.encrypt k m₁
    adversary.distinguish st (kc, dc)
  -- Shared helpers for all four game-SPMF decompositions
  have bind_swap : ∀ {α β γ : Type} (mx : SPMF α) (my : SPMF β) (f : α → β → SPMF γ),
      (mx >>= fun a => my >>= fun b => f a b) =
      (my >>= fun b => mx >>= fun a => f a b) := by
    intro α β γ mx my f
    ext x; exact probOutput_bind_bind_swap mx my (fun a b => f a b) x
  have hite_false : (false : Bool) = true ↔ False := ⟨Bool.noConfusion, False.elim⟩
  have hite_true : (true : Bool) = true ↔ True := ⟨fun _ => trivial, fun _ => rfl⟩
  -- Step 1: Composed bias = dist(real_m₀, real_m₁) via SPMF hidden-bit decomposition
  have h_composed : AsymmEncAlg.IND_CPA_OneTime_biasAdvantage
      (kem.composeWithDEM dem) runtime adversary =
      SPMF.boolDistAdvantage real_m₀ real_m₁ := by
    -- Show game SPMF = coin >>= fun b => (if b then real_m₀ else real_m₁) >>= pure ∘ (b == ·)
    have hspmf : AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem)
        adversary runtime =
        𝒟[$ᵗ Bool] >>= fun b =>
          (if b then real_m₀ else real_m₁) >>= fun z => pure (b == z) := by
      simp only [AsymmEncAlg.IND_CPA_OneTime_Game, KEMScheme.composeWithDEM,
        heval_bind, heval_liftProbComp]
      congr 1; funext b
      -- After distributing, the body for each b must match the intermediate game
      -- The only b-dependent part is the message selection and the final (b == ·)
      simp only [heval_pure]
      cases b
      · -- false: distributed = real_m₁ >>= pure ∘ (false == ·)
        simp only [hite_false, ite_false, bind_assoc, pure_bind]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (_, m₁, st) ← adversary.chooseMessages pk
          let (kc, k) ← kem.encaps pk; let dc ← dem.encrypt k m₁
          adversary.distinguish st (kc, dc)) >>= fun a => pure (false == a)
        simp only [heval_bind, bind_assoc]
      · -- true: distributed = real_m₀ >>= pure ∘ (true == ·)
        simp only [ite_true, bind_assoc, pure_bind]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (m₀, _, st) ← adversary.chooseMessages pk
          let (kc, k) ← kem.encaps pk; let dc ← dem.encrypt k m₀
          adversary.distinguish st (kc, dc)) >>= fun a => pure (true == a)
        simp only [heval_bind, bind_assoc]
    change (AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem) adversary
        runtime).boolBiasAdvantage = _
    rw [hspmf]
    exact SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch
      (𝒟[$ᵗ Bool]) real_m₀ real_m₁
      (by simp [Fintype.card_bool])
      (by simp [Fintype.card_bool])
      (hno_fail _) (hno_fail _)
  -- Step 2: KEM left bias = dist(real_m₀, rand_m₀)
  have h_kem_left : kem.IND_CPA_Advantage runtime
      (kem.composeWithDEM_toKEMLeftReduction dem adversary) =
      SPMF.boolDistAdvantage real_m₀ rand_m₀ := by
    have hspmf : KEMScheme.IND_CPA_Game runtime
        (kem.composeWithDEM_toKEMLeftReduction dem adversary) =
        𝒟[$ᵗ Bool] >>= fun b =>
          (if b then real_m₀ else rand_m₀) >>= fun z => pure (b == z) := by
      simp only [KEMScheme.IND_CPA_Game, composeWithDEM_toKEMLeftReduction,
        heval_bind, heval_pure, heval_liftProbComp]
      -- Move coin 𝒟[$ᵗ Bool] past keygen and chooseMessages (under binders)
      simp_rw [bind_swap (my := 𝒟[$ᵗ Bool])]
      congr 1; funext b
      -- Flatten any bundled pure from preChallenge unfolding
      conv_lhs => simp only [bind_assoc, pure_bind]
      cases b
      · -- false: encrypt uses kRand, matches rand_m₀ structure
        simp only [hite_false, ite_false]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (m₀, _, st) ← adversary.chooseMessages pk
          let (kc, _) ← kem.encaps pk; let kR ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt kR m₀; adversary.distinguish st (kc, dc)) >>= fun z =>
          pure (false == z)
        simp only [heval_bind, heval_liftProbComp, bind_assoc]
      · -- true: encrypt uses kReal, unused kRand eliminated by bind_const
        simp only [ite_true]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (m₀, _, st) ← adversary.chooseMessages pk
          let (kc, k) ← kem.encaps pk
          let dc ← dem.encrypt k m₀; adversary.distinguish st (kc, dc)) >>= fun z =>
          pure (true == z)
        simp only [heval_bind, bind_assoc]
        -- Eliminate unused 𝒟[$ᵗ K] >>= fun _ => cont = cont
        congr 1; funext pksk; congr 1; funext cms; congr 1; funext ckr
        exact OracleComp.ProgramLogic.Relational.spmf_bind_const_of_no_failure
          (OracleComp.ProgramLogic.Relational.probFailure_evalDist_eq_zero _) _
    change (KEMScheme.IND_CPA_Game runtime _).boolBiasAdvantage = _
    rw [hspmf]
    exact SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch
      (𝒟[$ᵗ Bool]) real_m₀ rand_m₀
      (by simp [Fintype.card_bool])
      (by simp [Fintype.card_bool])
      (hno_fail _) (hno_fail _)
  -- Step 3: KEM right bias = dist(real_m₁, rand_m₁)
  have h_kem_right : kem.IND_CPA_Advantage runtime
      (kem.composeWithDEM_toKEMRightReduction dem adversary) =
      SPMF.boolDistAdvantage real_m₁ rand_m₁ := by
    have hspmf : KEMScheme.IND_CPA_Game runtime
        (kem.composeWithDEM_toKEMRightReduction dem adversary) =
        𝒟[$ᵗ Bool] >>= fun b =>
          (if b then real_m₁ else rand_m₁) >>= fun z => pure (b == z) := by
      simp only [KEMScheme.IND_CPA_Game, composeWithDEM_toKEMRightReduction,
        heval_bind, heval_pure, heval_liftProbComp]
      simp_rw [bind_swap (my := 𝒟[$ᵗ Bool])]
      congr 1; funext b
      conv_lhs => simp only [bind_assoc, pure_bind]
      cases b
      · -- false: encrypt uses kRand, matches rand_m₁ structure
        simp only [hite_false, ite_false]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (_, m₁, st) ← adversary.chooseMessages pk
          let (kc, _) ← kem.encaps pk; let kR ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt kR m₁; adversary.distinguish st (kc, dc)) >>= fun z =>
          pure (false == z)
        simp only [heval_bind, heval_liftProbComp, bind_assoc]
      · -- true: encrypt uses kReal, unused kRand eliminated by bind_const
        simp only [ite_true]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (_, m₁, st) ← adversary.chooseMessages pk
          let (kc, k) ← kem.encaps pk
          let dc ← dem.encrypt k m₁; adversary.distinguish st (kc, dc)) >>= fun z =>
          pure (true == z)
        simp only [heval_bind, bind_assoc]
        congr 1; funext pksk; congr 1; funext cms; congr 1; funext ckr
        exact OracleComp.ProgramLogic.Relational.spmf_bind_const_of_no_failure
          (OracleComp.ProgramLogic.Relational.probFailure_evalDist_eq_zero _) _
    change (KEMScheme.IND_CPA_Game runtime _).boolBiasAdvantage = _
    rw [hspmf]
    exact SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch
      (𝒟[$ᵗ Bool]) real_m₁ rand_m₁
      (by simp [Fintype.card_bool])
      (by simp [Fintype.card_bool])
      (hno_fail _) (hno_fail _)
  -- Step 4: DEM bias = dist(rand_m₀, rand_m₁)
  have h_dem : dem.IND_CPA_Advantage runtime
      (kem.composeWithDEM_toDEMReduction dem adversary) =
      SPMF.boolDistAdvantage rand_m₀ rand_m₁ := by
    -- Show game SPMF = coin >>= fun b => (if b then rand_m₁ else rand_m₀) >>= pure ∘ (b == ·)
    have hspmf : DEMScheme.IND_CPA_Game runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) =
        𝒟[$ᵗ Bool] >>= fun b =>
          (if b then rand_m₁ else rand_m₀) >>= fun z => pure (b == z) := by
      simp only [DEMScheme.IND_CPA_Game, KEMScheme.composeWithDEM_toDEMReduction,
        heval_bind, heval_pure, heval_liftProbComp]
      congr 1; funext b
      -- Swap 𝒟[$ᵗ K] past keygen, chooseMessages, encaps using conv
      conv_lhs => rw [bind_swap]
      -- Flatten bundle: (keygen >>= choose >>= encaps >>= pure tuple) >>= cont
      -- into keygen >>= choose >>= encaps >>= cont[tuple]
      conv_lhs => simp only [bind_assoc, pure_bind]
      -- Now LHS has flat binds matching rand_m₀/rand_m₁ structure
      -- RHS: (if b then rand_m₁ else rand_m₀) >>= fun z => pure (b == z)
      -- After cases b: unfold let-bound rand and distribute to match flat LHS
      cases b
      · -- false: reduce ite, then distribute rand_m₀ on RHS to match flat LHS
        simp only [hite_false, ite_false]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (m₀, _, st) ← adversary.chooseMessages pk
          let (kc, _) ← kem.encaps pk; let kR ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt kR m₀; adversary.distinguish st (kc, dc)) >>= fun a =>
          pure (false == a)
        simp only [heval_bind, heval_liftProbComp, bind_assoc]
      · -- true: reduce ite, then distribute rand_m₁ on RHS to match flat LHS
        simp only [ite_true]
        change _ = (runtime.evalDist do
          let (pk, _) ← kem.keygen; let (_, m₁, st) ← adversary.chooseMessages pk
          let (kc, _) ← kem.encaps pk; let kR ← runtime.liftProbComp ($ᵗ K)
          let dc ← dem.encrypt kR m₁; adversary.distinguish st (kc, dc)) >>= fun a =>
          pure (true == a)
        simp only [heval_bind, heval_liftProbComp, bind_assoc]
    change (DEMScheme.IND_CPA_Game runtime _).boolBiasAdvantage = _
    rw [hspmf, SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch
      (𝒟[$ᵗ Bool]) rand_m₁ rand_m₀
      (by simp [Fintype.card_bool])
      (by simp [Fintype.card_bool])
      (hno_fail _) (hno_fail _)]
    unfold SPMF.boolDistAdvantage; rw [abs_sub_comm]
  -- Assembly: triangle inequality
  rw [h_composed]
  calc SPMF.boolDistAdvantage real_m₀ real_m₁
    _ ≤ SPMF.boolDistAdvantage real_m₀ rand_m₀ +
        SPMF.boolDistAdvantage rand_m₀ rand_m₁ +
        SPMF.boolDistAdvantage rand_m₁ real_m₁ := by
      have := SPMF.boolDistAdvantage_triangle real_m₀ rand_m₀ real_m₁
      have := SPMF.boolDistAdvantage_triangle rand_m₀ rand_m₁ real_m₁
      linarith
    _ = kem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
        SPMF.boolDistAdvantage rand_m₀ rand_m₁ +
        SPMF.boolDistAdvantage rand_m₁ real_m₁ := by rw [← h_kem_left]
    _ = kem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
        dem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toDEMReduction dem adversary) +
        SPMF.boolDistAdvantage rand_m₁ real_m₁ := by rw [← h_dem]
    _ = kem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
        dem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toDEMReduction dem adversary) +
        SPMF.boolDistAdvantage real_m₁ rand_m₁ := by
      congr 1; unfold SPMF.boolDistAdvantage; rw [abs_sub_comm]
    _ = kem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
        kem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toKEMRightReduction dem adversary) +
        dem.IND_CPA_Advantage runtime
          (kem.composeWithDEM_toDEMReduction dem adversary) := by
      rw [← h_kem_right]; ring

end IND_CPA

end KEMScheme
