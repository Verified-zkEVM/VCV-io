/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.DataEncapMech
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime

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
    let (m₁, _m₂, st) ← adversary.chooseMessages pk
    return (m₁, st)
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
    let (_m₁, m₂, st) ← adversary.chooseMessages pk
    return (m₂, st)
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
    let (m₁, m₂, st) ← adversary.chooseMessages pk
    let (kc, _k) ← kem.encaps pk
    return (m₁, m₂, (kc, st))
  distinguish st dc := do
    adversary.distinguish st.2 (st.1, dc)

/-- Equivalence between the DEM-reduction's `b = false` experiment and the KEM-left reduction's
`b = false` experiment. Both compute the same probability of the underlying composed-game
adversary outputting `true` on `(KEM-ciphertext, encrypt uniform-key first-message)`, just with
the `uniform-key` sample placed differently in the bind chain. -/
private lemma probOutput_dem_exp_false_eq_kem_left_exp_false
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (h : LawfulProbCompRuntime runtime)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    Pr[= true | dem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) false] =
    Pr[= true | kem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toKEMLeftReduction dem adversary) false] := by
  congr 1
  -- Unfold both Exp definitions into raw `runtime.evalDist do …` blocks, then expand each
  -- via `h.evalDist_bind` so that we are working at the SPMF level with explicit binds.
  simp only [DEMScheme.IND_CPA_Exp, KEMScheme.IND_CPA_Exp,
    composeWithDEM_toDEMReduction, composeWithDEM_toKEMLeftReduction,
    h.evalDist_bind, h.evalDist_liftProbComp,
    Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  -- Both sides are now SPMF bind chains over the same atomic SPMFs (in different orders).
  -- Pull the uniform-key sample to a common position by `SPMF.bind_bind_swap`.
  rw [SPMF.bind_bind_swap (𝒟[$ᵗ K] : SPMF K) (runtime.evalDist kem.keygen)]
  refine bind_congr fun ⟨pk, _sk⟩ => ?_
  rw [SPMF.bind_bind_swap (𝒟[$ᵗ K] : SPMF K)
    (runtime.evalDist (adversary.chooseMessages pk))]
  refine bind_congr fun ⟨m₁, _m₂, st⟩ => ?_
  rw [SPMF.bind_bind_swap (𝒟[$ᵗ K] : SPMF K)
    (runtime.evalDist (kem.encaps pk))]

/-- Equivalence between the DEM-reduction's `b = true` experiment and the KEM-right reduction's
`b = false` experiment. Symmetric to `probOutput_dem_exp_false_eq_kem_left_exp_false`, with the
second message in place of the first. -/
private lemma probOutput_dem_exp_true_eq_kem_right_exp_false
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (h : LawfulProbCompRuntime runtime)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    Pr[= true | dem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) true] =
    Pr[= true | kem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toKEMRightReduction dem adversary) false] := by
  congr 1
  simp only [DEMScheme.IND_CPA_Exp, KEMScheme.IND_CPA_Exp,
    composeWithDEM_toDEMReduction, composeWithDEM_toKEMRightReduction,
    h.evalDist_bind, h.evalDist_liftProbComp,
    Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  rw [SPMF.bind_bind_swap (𝒟[$ᵗ K] : SPMF K) (runtime.evalDist kem.keygen)]
  refine bind_congr fun ⟨pk, _sk⟩ => ?_
  rw [SPMF.bind_bind_swap (𝒟[$ᵗ K] : SPMF K)
    (runtime.evalDist (adversary.chooseMessages pk))]
  refine bind_congr fun ⟨_m₁, m₂, st⟩ => ?_
  rw [SPMF.bind_bind_swap (𝒟[$ᵗ K] : SPMF K)
    (runtime.evalDist (kem.encaps pk))]

/-- The inner composed-game body (everything after the random bit `b` and before
`pure (b == b')`). Used as the `Bool`-indexed family to apply the pi-form branch lemma in the
composition theorem; callers also need `NeverFail` on this for `b = true` and `b = false`. -/
def composedInner
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) (b : Bool) :
    OracleComp spec Bool := do
  let (pk, _sk) ← kem.keygen
  let (m₁, m₂, state) ← adversary.chooseMessages pk
  let (c₁, k) ← kem.encaps pk
  let c₂ ← dem.encrypt k (if b then m₁ else m₂)
  adversary.distinguish state (c₁, c₂)

/-- The composed-game `Pr[= true]` decomposes against the two KEM-side fixed-branch
experiments. The proof has three movements: factor the composed game so the random bit `b` is
at the top, apply `SPMF.probOutput_true_uniformBool_pi_branch_toReal`, then drop the unused
`kRand ← uniformK` sample from each KEM Exp body. -/
private lemma probOutput_composed_eq_half_left_plus_half_right
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (h : LawfulProbCompRuntime runtime)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem))
    [NeverFail (runtime.evalDist (composedInner kem dem adversary true))]
    [NeverFail (runtime.evalDist (composedInner kem dem adversary false))] :
    (Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game
        (encAlg := kem.composeWithDEM dem) adversary runtime]).toReal =
      1 / 2 * (Pr[= true | kem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toKEMLeftReduction dem adversary) true]).toReal +
      1 / 2 * (1 - (Pr[= true | kem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toKEMRightReduction dem adversary) true]).toReal) := by
  -- Step 1: rewrite the composed game so it has the form
  -- `bool >>= fun b => runtime.evalDist (composedInner b) >>= fun b' => pure (b == b')`.
  have hfactor : AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem)
      adversary runtime =
      (liftM (PMF.uniformOfFintype Bool) : SPMF Bool) >>= fun b =>
        runtime.evalDist (composedInner kem dem adversary b) >>= fun b' =>
          pure (b == b') := by
    simp only [AsymmEncAlg.IND_CPA_OneTime_Game, KEMScheme.composeWithDEM,
      composedInner, h.evalDist_bind, h.evalDist_liftProbComp, h.evalDist_pure,
      bind_assoc, pure_bind, evalDist_uniformSample]
  rw [hfactor]
  -- Step 2: apply the pi-form `Pr[= true]` branch helper.
  rw [SPMF.probOutput_true_uniformBool_pi_branch_toReal
    (fun b => runtime.evalDist (composedInner kem dem adversary b))]
  -- Step 3: reduce each inner probability to the corresponding KEM-side `Pr[= true]`.
  -- For b=true (LHS): drop the unused `kRand ← uniformK` from `KEMLeft Exp true`.
  have h_true : Pr[= true | runtime.evalDist (composedInner kem dem adversary true)] =
      Pr[= true | kem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toKEMLeftReduction dem adversary) true] := by
    congr 1
    simp only [composedInner, KEMScheme.IND_CPA_Exp, composeWithDEM_toKEMLeftReduction,
      h.evalDist_bind, h.evalDist_liftProbComp,
      ↓reduceIte, bind_assoc, pure_bind]
    -- Both SPMFs now have the same atomic operations. The KEM side has an extra
    -- `𝒟[$ᵗ K] >>= fun _ => …` step that drops via `SPMF.bind_const_of_neverFail`.
    refine bind_congr fun ⟨pk, _sk⟩ => ?_
    refine bind_congr fun ⟨m₁, _m₂, st⟩ => ?_
    refine bind_congr fun ⟨c₁, k⟩ => ?_
    haveI hNF : NeverFail (𝒟[$ᵗ K] : SPMF K) := by
      refine NeverFail.of_probFailure_eq_zero _ ?_
      change Pr[⊥ | ($ᵗ K : ProbComp K)] = 0
      exact probFailure_uniformSample K
    rw [SPMF.bind_const_of_neverFail (𝒟[$ᵗ K] : SPMF K)]
  -- For b=false: same drop-unused, plus convert `Pr[= false | _]` to `1 - Pr[= true | _]`.
  have h_false : (Pr[= false | runtime.evalDist (composedInner kem dem adversary false)]).toReal =
      1 - (Pr[= true | kem.IND_CPA_Exp runtime
        (kem.composeWithDEM_toKEMRightReduction dem adversary) true]).toReal := by
    have h_eq : Pr[= true | runtime.evalDist (composedInner kem dem adversary false)] =
        Pr[= true | kem.IND_CPA_Exp runtime
          (kem.composeWithDEM_toKEMRightReduction dem adversary) true] := by
      congr 1
      simp only [composedInner, KEMScheme.IND_CPA_Exp, composeWithDEM_toKEMRightReduction,
        h.evalDist_bind, h.evalDist_liftProbComp,
        Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr fun ⟨pk, _sk⟩ => ?_
      refine bind_congr fun ⟨_m₁, m₂, st⟩ => ?_
      refine bind_congr fun ⟨c₁, k⟩ => ?_
      haveI hNF : NeverFail (𝒟[$ᵗ K] : SPMF K) := by
        refine NeverFail.of_probFailure_eq_zero _ ?_
        change Pr[⊥ | ($ᵗ K : ProbComp K)] = 0
        exact probFailure_uniformSample K
      rw [SPMF.bind_const_of_neverFail (𝒟[$ᵗ K] : SPMF K)]
    have hsum : Pr[= true | runtime.evalDist (composedInner kem dem adversary false)] +
        Pr[= false | runtime.evalDist (composedInner kem dem adversary false)] = 1 :=
      probOutput_true_add_false_of_neverFail
    have hr : (Pr[= true | runtime.evalDist
        (composedInner kem dem adversary false)]).toReal +
        (Pr[= false | runtime.evalDist
          (composedInner kem dem adversary false)]).toReal = 1 := by
      rw [← ENNReal.toReal_add probOutput_ne_top probOutput_ne_top, hsum,
        ENNReal.toReal_one]
    rw [← h_eq]; linarith
  rw [h_true, h_false]

/-- Proof-ladders A1 reduction statement: the one-time IND-CPA advantage of textbook KEM+DEM is
bounded by two KEM IND-CPA advantages plus one DEM IND-CPA advantage, using the canonical
left/right and DEM reductions defined above.

**Hypotheses.** The runtime must be `LawfulProbCompRuntime` (i.e. its `evalDist` is a monad
homomorphism), and the four games involved must never fail. These conditions hold for the
canonical `ProbCompRuntime.probComp` and for any adversary built from `pure` / sampling / oracle
queries without explicit `failure`.

**Proof outline.** Following the parent `IND_CPA_OneTime_Game` convention where
`(m₁, m₂, _) ← chooseMessages pk` and `b = true` encrypts `m₁`, let
`A := Pr[adv true | encrypt m₁ with real KEM key]`,
`A' := Pr[adv true | encrypt m₁ with uniform key]`,
`B := Pr[adv true | encrypt m₂ with real KEM key]`,
`B' := Pr[adv true | encrypt m₂ with uniform key]`.

Then under NeverFail hypotheses:
- composed bias = `|A − B|`
- KEM left advantage = `|A − A'|`
- KEM right advantage = `|B − B'|`
- DEM advantage = `|B' − A'|`

The triangle inequality
`|A − B| ≤ |A − A'| + |A' − B'| + |B' − B|`
gives the result.

The detailed game-equivalence chain (showing each Exp game's `Pr[= true]` equals the
corresponding F-value) is the bulk of the remaining work, supported by the
`IND_CPA_Game_eq_branch` connectors for `KEMScheme` and `DEMScheme`. -/
theorem ind_cpa_one_time_bias_advantage_compose_with_dem_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (h : LawfulProbCompRuntime runtime)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem))
    -- NeverFail for the four KEM/DEM Exp games that the connectors will reduce to.
    [NeverFail (kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMLeftReduction dem adversary) true)]
    [NeverFail (kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMLeftReduction dem adversary) false)]
    [NeverFail (kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMRightReduction dem adversary) true)]
    [NeverFail (kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMRightReduction dem adversary) false)]
    [NeverFail (dem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toDEMReduction dem adversary) true)]
    [NeverFail (dem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toDEMReduction dem adversary) false)]
    -- NeverFail for the composed one-time IND-CPA game.
    [NeverFail (AsymmEncAlg.IND_CPA_OneTime_Game (encAlg := kem.composeWithDEM dem)
      adversary runtime)]
    -- NeverFail for the two composed inner experiments (used by the composed-game
    -- decomposition lemma `probOutput_composed_eq_half_left_plus_half_right`).
    [NeverFail (runtime.evalDist (composedInner kem dem adversary true))]
    [NeverFail (runtime.evalDist (composedInner kem dem adversary false))] :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM dem) runtime adversary ≤
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMRightReduction dem adversary) +
      dem.IND_CPA_Advantage runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) := by
  -- Abbreviations: A/B are real-key probabilities, A'/B' are random-key probabilities;
  -- A/A' use the **left** reduction (first message), B/B' use the **right** (second message).
  set A := (Pr[= true | kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMLeftReduction dem adversary) true]).toReal with hA
  set B := (Pr[= true | kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMRightReduction dem adversary) true]).toReal with hB
  set A' := (Pr[= true | kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMLeftReduction dem adversary) false]).toReal with hA'
  set B' := (Pr[= true | kem.IND_CPA_Exp runtime
      (kem.composeWithDEM_toKEMRightReduction dem adversary) false]).toReal with hB'
  -- Convert KEM advantages to |A - A'| and |B - B'| via the connector.
  have h_kem_left_adv : kem.IND_CPA_Advantage runtime
      (kem.composeWithDEM_toKEMLeftReduction dem adversary) = |A - A'| := by
    unfold KEMScheme.IND_CPA_Advantage
    rw [KEMScheme.IND_CPA_Game_eq_branch _ h _]
    rw [SPMF.boolBiasAdvantage_uniformBool_pi_eq_boolDistAdvantage]
    rfl
  have h_kem_right_adv : kem.IND_CPA_Advantage runtime
      (kem.composeWithDEM_toKEMRightReduction dem adversary) = |B - B'| := by
    unfold KEMScheme.IND_CPA_Advantage
    rw [KEMScheme.IND_CPA_Game_eq_branch _ h _]
    rw [SPMF.boolBiasAdvantage_uniformBool_pi_eq_boolDistAdvantage]
    rfl
  -- Convert DEM advantage to |B' - A'| using the connector + the two proven equivalence
  -- lemmas `probOutput_dem_exp_{true,false}_eq_kem_{right,left}_exp_false`.
  have h_dem_adv : dem.IND_CPA_Advantage runtime
      (kem.composeWithDEM_toDEMReduction dem adversary) = |B' - A'| := by
    unfold DEMScheme.IND_CPA_Advantage
    rw [DEMScheme.IND_CPA_Game_eq_branch _ h _]
    rw [SPMF.boolBiasAdvantage_uniformBool_pi_eq_boolDistAdvantage]
    change |(Pr[= true | dem.IND_CPA_Exp runtime
            (kem.composeWithDEM_toDEMReduction dem adversary) true]).toReal -
          (Pr[= true | dem.IND_CPA_Exp runtime
            (kem.composeWithDEM_toDEMReduction dem adversary) false]).toReal| = |B' - A'|
    rw [probOutput_dem_exp_true_eq_kem_right_exp_false kem dem runtime h adversary,
        probOutput_dem_exp_false_eq_kem_left_exp_false kem dem runtime h adversary]
  -- Convert composed bias to |A - B| via the composed-game decomposition lemma.
  have h_composed_bias : AsymmEncAlg.IND_CPA_OneTime_biasAdvantage
      (kem.composeWithDEM dem) runtime adversary = |A - B| := by
    unfold AsymmEncAlg.IND_CPA_OneTime_biasAdvantage
    rw [SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half,
      probOutput_composed_eq_half_left_plus_half_right kem dem runtime h adversary]
    rw [show 1 / 2 * A + 1 / 2 * (1 - B) - 1 / 2 = (A - B) / 2 from by ring,
      abs_div, show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]
    ring
  -- Apply triangle.
  rw [h_composed_bias, h_kem_left_adv, h_kem_right_adv, h_dem_adv]
  have triangle : |A - B| ≤ |A - A'| + |A' - B'| + |B' - B| := by
    calc |A - B|
        = |(A - A') + ((A' - B') + (B' - B))| := by ring_nf
      _ ≤ |A - A'| + |(A' - B') + (B' - B)| := abs_add_le _ _
      _ ≤ |A - A'| + (|A' - B'| + |B' - B|) := by linarith [abs_add_le (A' - B') (B' - B)]
      _ = |A - A'| + |A' - B'| + |B' - B| := by ring
  have hDEM : |A' - B'| = |B' - A'| := abs_sub_comm _ _
  have hBB' : |B' - B| = |B - B'| := abs_sub_comm _ _
  linarith

end IND_CPA

end KEMScheme
