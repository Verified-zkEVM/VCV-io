/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.DataEncapMech
public import VCVio.CryptoFoundations.KeyEncapMech
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
public import VCVio.CryptoFoundations.KEMDEM.Measure
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# KEM + DEM Composition

This file defines the textbook KEM+DEM public-key encryption construction and the proof-ladders A1
reduction skeleton against the repo's existing KEM and one-time IND-CPA interfaces.
-/

@[expose] public section

universe u v

open OracleSpec OracleComp ENNReal MeasureTheory

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

variable [DecidableEq K] [DecidableEq M] [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

omit [LawfulMonadLiftT m SPMF] in
/-- From KEM correctness at the monadic probability level, every reachable decapsulation of an
honest ciphertext returns the encapsulated key. -/
private lemma kem_decaps_mem_support
    {kem : KEMScheme m K PK SK CKEM}
    (hkem : Pr[= true | kem.CorrectExp] = 1)
    {pk : PK} {sk : SK} (hks : (pk, sk) ∈ support kem.keygen)
    {c : CKEM} {k : K} (hck : (c, k) ∈ support (kem.encaps pk))
    {kOpt : Option K} (hkOpt : kOpt ∈ support (kem.decaps sk c)) :
    kOpt = some k := by
  have hmem : decide (kOpt = some k) ∈ support kem.CorrectExp := by
    simp only [KEMScheme.CorrectExp, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, decide_eq_decide, exists_prop, Prod.exists]
    exact ⟨pk, sk, hks, c, k, hck, kOpt, hkOpt, Iff.rfl⟩
  simpa [((probOutput_eq_one_iff (mx := kem.CorrectExp) (x := true)).mp hkem).2] using hmem

/-- If a KEM and externally keyed DEM are both perfectly correct in the concrete probabilistic
semantics of `m`, then their composition is also perfectly correct. -/
theorem perfectlyCorrect_composeWithDEM
    [LawfulMonad m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM)
    (hkem : Pr[= true | kem.CorrectExp] = 1)
    (hdem : ∀ k : K, ∀ msg : M, Pr[= true | dem.CorrectExp k msg] = 1) :
    ∀ msg, Pr[= true | (kem.composeWithDEM dem).CorrectExp msg] = 1 := by
  intro msg
  rw [← hkem]
  simp only [AsymmEncAlg.CorrectExp, composeWithDEM, KEMScheme.CorrectExp, monad_norm]
  refine probOutput_bind_congr fun ⟨pk, sk⟩ hks => ?_
  refine probOutput_bind_congr fun ⟨kc, k⟩ hck => ?_
  rw [probOutput_bind_bind_swap (mx := dem.encrypt k msg) (my := kem.decaps sk kc)]
  refine probOutput_bind_congr fun kOpt hkOpt => ?_
  obtain rfl := kem_decaps_mem_support hkem hks hck hkOpt
  simpa [DEMScheme.CorrectExp, probOutput_pure, monad_norm] using hdem k msg

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

The probability-free games and shared hybrid argument live in
`VCVio.CryptoFoundations.KEMDEM.Measure`. This theorem calibrates them to the bundled runtime.

The runtime coherence hypotheses require `runtime.evalSPMF` to be a monad morphism (preserves
`pure` and distributes `>>=`) and to produce total distributions on `Bool` (no failure mass).
These hold for all standard runtime constructions, including `withStateOracle`. -/
theorem ind_cpa_one_time_bias_advantage_compose_with_dem_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem))
    (heval_pure : ∀ {α : Type} (a : α),
        runtime.evalSPMF (pure a : OracleComp spec α) = pure a)
    (heval_bind : ∀ {α β : Type} (mx : OracleComp spec α)
        (f : α → OracleComp spec β),
        runtime.evalSPMF (mx >>= f) =
        runtime.evalSPMF mx >>= fun a => runtime.evalSPMF (f a))
    (heval_liftProbComp : ∀ {α : Type} (pc : ProbComp α),
        runtime.evalSPMF (runtime.liftProbComp pc) = 𝒮[pc])
    (hno_fail : ∀ (mx : OracleComp spec Bool),
        Pr[= true | runtime.evalSPMF mx] +
        Pr[= false | runtime.evalSPMF mx] = 1) :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM dem) runtime adversary ≤
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMRightReduction dem adversary) +
      dem.IND_CPA_Advantage runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) := by
  let : MeasurableSpace K := ⊤
  let : MeasurableSpace (CKEM × K) := ⊤
  let : MeasurableSpace (PK × M × M × adversary.State) := ⊤
  let : EvalDistSemantics (OracleComp spec) := {
    denote mx := (runtime.evalSPMF mx).toMeasure
    apply_univ_le_one mx := SPMF.toMeasure_apply_univ_le_one _ }
  let : LawfulEvalDistSemantics (OracleComp spec) := {
    denote_pure a := by
      change (runtime.evalSPMF (pure a)).toMeasure = _
      rw [heval_pure, SPMF.toMeasure_pure]
    denote_bind mx f hf := by
      change (runtime.evalSPMF (mx >>= f)).toMeasure = _
      rw [heval_bind]
      exact SPMF.toMeasure_bind' _ _ hf }
  let prepare : OracleComp spec (PK × M × M × adversary.State) := do
    let (pk, _) ← kem.keygen
    let (m₀, m₁, st) ← adversary.chooseMessages pk
    pure (pk, m₀, m₁, st)
  let encaps (p : PK × M × M × adversary.State) := kem.encaps p.1
  let finish (p : PK × M × M × adversary.State) (kc : CKEM) (k : K) (side : Bool) := do
    let dc ← dem.encrypt k (if side then p.2.1 else p.2.2.1)
    adversary.distinguish p.2.2.2 (kc, dc)
  have hcoin (b : Bool) : 𝒟[runtime.liftProbComp ($ᵗ Bool)] {b} = 1 / 2 := by
    change (runtime.evalSPMF (runtime.liftProbComp ($ᵗ Bool))).toMeasure {b} = _
    rw [heval_liftProbComp, SPMF.toMeasure_apply_singleton]
    change Pr[= b | $ᵗ Bool] = _
    simp [Fintype.card_bool]
  have hkey : 𝒟[runtime.liftProbComp ($ᵗ K)] Set.univ = 1 := by
    change (runtime.evalSPMF (runtime.liftProbComp ($ᵗ K))).toMeasure Set.univ = _
    rw [heval_liftProbComp]
    change 𝒟[$ᵗ K] Set.univ = _
    rw [evalDist_uniformSample]
    simp
  have htotal (real side : Bool) :
      𝒟[KEMDEM.hybrid prepare encaps finish (runtime.liftProbComp ($ᵗ K)) real side] {true} +
      𝒟[KEMDEM.hybrid prepare encaps finish (runtime.liftProbComp ($ᵗ K)) real side] {false} =
        1 := by
    change (runtime.evalSPMF _).toMeasure {true} + (runtime.evalSPMF _).toMeasure {false} = _
    simpa only [SPMF.toMeasure_apply_singleton, probOutput_def, evalSPMF_id] using hno_fail
      (KEMDEM.hybrid prepare encaps finish (runtime.liftProbComp ($ᵗ K)) real side)
  have h := KEMDEM.bias_compose_le prepare encaps finish
    (runtime.liftProbComp ($ᵗ Bool)) (runtime.liftProbComp ($ᵗ K))
    (hcoin true) (hcoin false) hkey htotal
  change (runtime.evalSPMF _).toMeasure.boolBias ≤
    (runtime.evalSPMF _).toMeasure.boolBias + (runtime.evalSPMF _).toMeasure.boolBias +
    (runtime.evalSPMF _).toMeasure.boolBias at h
  have hnot (b : Bool) (x y : M) : (if !b then x else y) = (if b then y else x) := by
    cases b <;> rfl
  simpa only [Measure.boolBias, SPMF.toMeasure_apply_singleton,
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage, KEMScheme.IND_CPA_Advantage,
    DEMScheme.IND_CPA_Advantage, SPMF.boolBiasAdvantage, probOutput_def, evalSPMF_id,
    AsymmEncAlg.IND_CPA_OneTime_Game, KEMScheme.IND_CPA_Game, DEMScheme.IND_CPA_Game,
    KEMDEM.composedGame, KEMDEM.kemGame, KEMDEM.demGame, prepare, encaps, finish,
    composeWithDEM, composeWithDEM_toKEMLeftReduction, composeWithDEM_toKEMRightReduction,
    composeWithDEM_toDEMReduction, bind_assoc, pure_bind, ite_true, Bool.false_eq_true,
    ite_false, hnot] using h

end IND_CPA

end KEMScheme
