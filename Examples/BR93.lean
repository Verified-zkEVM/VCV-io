/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.CryptoFoundations.HardnessAssumptions.OneWay
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append

/-!
# Bellare-Rogaway 1993 Encryption

This file sets up the Bellare-Rogaway 1993 public-key encryption construction from:

- a trapdoor permutation `f(pk, ·)` over a randomness space `Rand`
- a hash/random oracle `H : Rand → M`
- an additive message space `M`

Encryption samples `r ← Rand` and returns `(f(pk, r), H(r) + m)`. Decryption inverts the
trapdoor permutation and unmasks by subtraction.

The security proof follows the standard three-step outline:

1. Real CPA game.
2. Replace the challenge hash query with a fresh uniform mask, up to the bad event that the
   adversary queries the hidden `r`.
3. Replace the masked challenge message with a uniform ciphertext component, yielding success
   probability `1/2`.

The bad event is then reduced to the repo's trapdoor-preimage experiment
(`tdpAdvantage`) by inspecting the adversary's random-oracle queries. The proof
bodies remain `sorry` for now.
-/

open OracleComp OracleSpec ENNReal OneWay

namespace BR93

variable {PK SK Rand M : Type}
variable [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [SampleableType Rand]
variable [Inhabited M] [Fintype M] [DecidableEq M] [SampleableType M] [AddCommGroup M]

/-- The concrete BR93 scheme instantiated with an explicit hash function `hash : Rand → M`. -/
@[simps!] def br93AsymmEnc (tdp : TrapdoorPermutation PK SK Rand) (hash : Rand → M) :
    AsymmEncAlg ProbComp (M := M) (PK := PK) (SK := SK) (C := Rand × M) where
  keygen := tdp.keygen
  encrypt pk msg := do
    let r ← $ᵗ Rand
    return (tdp.forward pk r, hash r + msg)
  decrypt sk c :=
    return (some (c.2 - hash (tdp.inverse sk c.1)))

namespace br93AsymmEnc

variable {tdp : TrapdoorPermutation PK SK Rand} {hash : Rand → M}

omit [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [Inhabited M] [Fintype M]
  [SampleableType M] in
/-- Correctness of BR93 follows from correctness of the underlying trapdoor permutation. -/
theorem correct (hcorrect : tdp.Correct) :
    (br93AsymmEnc (M := M) tdp hash).PerfectlyCorrect ProbCompRuntime.probComp := by
  intro msg
  let mx : ProbComp Bool := do
    let x ← tdp.keygen
    let c ← (do let r ← $ᵗ Rand; pure (tdp.forward x.1 r, hash r + msg))
    let msg' ← pure (some (c.2 - hash (tdp.inverse x.2 c.1)))
    pure (decide (msg' = some msg))
  change Pr[= true | ProbCompRuntime.probComp.evalDist mx] = 1
  simp only [mx]
  have huniq : ∀ y ∈ support mx, y = true := by
    intro y hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨⟨pk, sk⟩, hpksk, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨c, hc, hy⟩ := hy
    rw [mem_support_bind_iff] at hc
    obtain ⟨r, _, hc⟩ := hc
    rw [mem_support_bind_iff] at hy
    obtain ⟨msg', hmsg', hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hc hmsg' hy
    obtain rfl := hc
    obtain rfl := hmsg'
    obtain rfl := hy
    simp [hcorrect pk sk hpksk r]
  change Pr[= true | mx] = 1
  exact probOutput_eq_one_of_support_subset_singleton
    (NeverFail.probFailure_eq_zero (mx := mx)) huniq

/-! ## One-time IND-CPA in the random-oracle model -/

/-- The shared oracle interface for BR93 games: unrestricted uniform sampling plus a
lazy random oracle `Rand → M`. -/
abbrev RO_Spec (Rand M : Type) := unifSpec + (Rand →ₒ M)

/-- A one-time CPA adversary for BR93. Both phases share access to the same random oracle. -/
structure CPA_Adv where
  State : Type
  choose : PK → OracleComp (RO_Spec Rand M) (M × M × State)
  guess : State → Rand × M → OracleComp (RO_Spec Rand M) Bool

/-- Shared implementation of the BR93 random-oracle world: the left component handles uniform
sampling, while the right component is a lazy random oracle on `Rand → M`. -/
private def roQueryImpl :
    QueryImpl (RO_Spec Rand M) (StateT ((Rand →ₒ M).QueryCache) ProbComp) :=
  let ro : QueryImpl (Rand →ₒ M) (StateT ((Rand →ₒ M).QueryCache) ProbComp) := randomOracle
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((Rand →ₒ M).QueryCache) ProbComp)
  idImpl + ro

/-- Lift a `ProbComp` computation into the BR93 random-oracle world. -/
private def liftProbComp {α : Type} (px : ProbComp α) : OracleComp (RO_Spec Rand M) α :=
  px

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- The BR93 random-oracle handler is transparent on a computation lifted in from `unifSpec`,
threading the cache unchanged: simulating such a computation just lifts it into the cache state
monad. -/
private lemma simulateQ_roQueryImpl_liftProbComp {β : Type} (ob : ProbComp β) :
    simulateQ (roQueryImpl (Rand := Rand) (M := M)) (liftProbComp ob)
      = (liftM ob : StateT ((Rand →ₒ M).QueryCache) ProbComp β) := by
  have h : liftProbComp ob = OracleComp.liftComp ob (RO_Spec Rand M) := by
    induction ob using OracleComp.inductionOn with
    | pure x => rfl
    | query_bind t k ih =>
      simp only [liftProbComp, liftComp_bind] at *
      simp [ih, monad_norm]
      rfl
  rw [h]
  unfold roQueryImpl
  rw [QueryImpl.simulateQ_add_liftComp_left, HasQuery.toQueryImpl_eq_id',
      simulateQ_liftTarget, simulateQ_id']

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- A lifted `ProbComp` sample never touches the cache, so it commutes to the front of a run. -/
private lemma run'_liftProbComp_bind {β γ : Type} (p : ProbComp β)
    (k : β → OracleComp (RO_Spec Rand M) γ) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (liftProbComp p >>= k)).run' s
      = p >>= fun a => (simulateQ roQueryImpl (k a)).run' s := by
  rw [simulateQ_bind, simulateQ_roQueryImpl_liftProbComp]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] in
/-- Running a lifted `ProbComp` sample returns the sample paired with the unchanged cache. -/
private lemma run_liftProbComp {β : Type} (p : ProbComp β) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (liftProbComp p)).run s = p >>= fun a => pure (a, s) := by
  rw [simulateQ_roQueryImpl_liftProbComp]
  simp [StateT.run_monadLift]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited Rand]
  [Inhabited M] [AddCommGroup M] in
/-- Splitting the random-oracle run at a bind: the first computation threads the cache forward. -/
private lemma run'_simulateQ_bind {β γ : Type} (mx : OracleComp (RO_Spec Rand M) β)
    (k : β → OracleComp (RO_Spec Rand M) γ) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (mx >>= k)).run' s
      = (simulateQ roQueryImpl mx).run s >>=
          fun p => (simulateQ roQueryImpl (k p.1)).run' p.2 := by
  rw [simulateQ_bind]
  simp [StateT.run'_eq, StateT.run_bind]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited Rand]
  [Inhabited M] [AddCommGroup M] in
/-- A final `pure` of a state-free value can be pulled out of the run. -/
private lemma run'_simulateQ_bind_pure {β γ : Type} (mx : OracleComp (RO_Spec Rand M) β)
    (f : β → γ) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (mx >>= fun b => pure (f b))).run' s
      = (simulateQ roQueryImpl mx).run' s >>= fun b => pure (f b) := by
  rw [simulateQ_bind]
  simp [StateT.run'_eq, Functor.map_map]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited Rand]
  [Inhabited M] in
/-- Right-translating a uniform challenge mask by a constant preserves the output distribution. -/
private lemma evalDist_bind_add_right_uniform {γ : Type} (m : M) (f : M → ProbComp γ) :
    𝒟[(do let h ← $ᵗ M; f (h + m))] = 𝒟[(do let h ← $ᵗ M; f h)] := by
  refine evalDist_ext fun z => ?_
  exact probOutput_bind_add_right_uniform (α := M) m f z

/-- Real one-time CPA game in the random-oracle model. -/
def cpaGame (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← liftProbComp ($ᵗ Bool)
    let (pk, _sk) ← liftProbComp tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← liftProbComp ($ᵗ Rand)
    let h : M ← (RO_Spec Rand M).query (Sum.inr r)
    let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
    let b' ← adv.guess st c
    return (b == b'))).run' ∅

/-- Game 1: replace the challenge hash value with a fresh uniform mask. The adversary still
interacts with the same lazy random oracle, so this only changes the game if it queries the
hidden challenge randomness `r`. -/
def game1 (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← liftProbComp ($ᵗ Bool)
    let (pk, _sk) ← liftProbComp tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← liftProbComp ($ᵗ Rand)
    let h ← liftProbComp ($ᵗ M)
    let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
    let b' ← adv.guess st c
    return (b == b'))).run' ∅

/-- Game 2: after replacing the challenge hash with a uniform mask, translation by the
challenge message preserves uniformity, so the challenge ciphertext no longer depends on `b`. -/
def game2 (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  do
    let b ← ($ᵗ Bool)
    let b' ← (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
    return (b == b')

/-- Bad event for the Game 0 → Game 1 hop: the adversary queries the random oracle at the
hidden challenge randomness `r`. -/
def badEventExp (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool := do
  let loggedRun :
      StateT ((Rand →ₒ M).QueryCache) ProbComp
        (Rand × QueryLog (RO_Spec Rand M)) :=
    (simulateQ roQueryImpl.withLogging <| (show OracleComp (RO_Spec Rand M) Rand from do
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (m₁, m₂, st) ← adv.choose pk
      let b ← liftProbComp ($ᵗ Bool)
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
      let _b' ← adv.guess st c
      return r)).run
  let (r, log) ← loggedRun.run' ∅
  return decide (log.any fun entry => match entry.1 with
    | Sum.inl _ => false
    | Sum.inr r' => r' = r)

/-- Probability of the bad event. -/
noncomputable def badEventProb (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ℝ :=
  (Pr[= true | badEventExp tdp adv]).toReal

/-- Inversion reduction: run the BR93 adversary in the idealized challenge game, log its
random-oracle queries, and return the first query whose image under the trapdoor permutation
matches the challenge `y`. -/
def inverter (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : TDPAdversary PK Rand :=
  fun pk y => do
    let loggedRun :
        StateT ((Rand →ₒ M).QueryCache) ProbComp
          (Unit × QueryLog (RO_Spec Rand M)) :=
      (simulateQ roQueryImpl.withLogging <| (show OracleComp (RO_Spec Rand M) Unit from do
        let (m₁, m₂, st) ← adv.choose pk
        let b ← liftProbComp ($ᵗ Bool)
        let h ← liftProbComp ($ᵗ M)
        let c : Rand × M := (y, h + if b then m₁ else m₂)
        let _b' ← adv.guess st c
        return ())).run
    let (_result, log) ← loggedRun.run' ∅
    match log.find? (fun entry => match entry.1 with
      | Sum.inl _ => false
      | Sum.inr r => tdp.forward pk r = y) with
    | some entry =>
        match entry.1 with
        | Sum.inl _ => return default
        | Sum.inr r => return r
    | none => return default

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- Up-to-bad step: replacing the challenge hash query with a fresh uniform mask changes the
game by at most the bad-event probability. -/
theorem cpaGame_gap_le_badEvent (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    |(Pr[= true | cpaGame tdp adv]).toReal -
      (Pr[= true | game1 tdp adv]).toReal| ≤
      badEventProb tdp adv := by
  sorry

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] in
/-- Uniform masking step: once the challenge hash output is replaced by a fresh uniform mask,
adding either challenge message yields the same ciphertext distribution. -/
theorem game1_eq_game2 (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    𝒟[game1 tdp adv] = 𝒟[game2 tdp adv] := by
  have congr_bind : ∀ {γ δ : Type} (oa : ProbComp γ) (f g : γ → ProbComp δ),
      (∀ a, 𝒟[f a] = 𝒟[g a]) → 𝒟[oa >>= f] = 𝒟[oa >>= g] := by
    intro γ δ oa f g hfg
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext a
    exact hfg a
  rw [game1, game2]
  -- Push the random-oracle simulation through both games: lifted samples become plain
  -- `ProbComp` binds, the adversary's `choose`/`guess` thread the cache, and the trailing
  -- `pure` collapses, leaving identical computations save for the challenge mask.
  simp only [run'_simulateQ_bind, run_liftProbComp, simulateQ_pure, bind_assoc, pure_bind]
  simp only [StateT.run'_eq, StateT.run_pure, map_eq_bind_pure_comp, Function.comp,
    bind_assoc, pure_bind]
  refine congr_bind _ _ _ fun b => ?_
  refine congr_bind _ _ _ fun ks => ?_
  refine congr_bind _ _ _ fun mmst => ?_
  refine congr_bind _ _ _ fun r => ?_
  exact evalDist_bind_add_right_uniform (if b = true then mmst.1.1 else mmst.1.2.1)
    (fun x => (simulateQ roQueryImpl (adv.guess mmst.1.2.2 (tdp.forward ks.1 r, x))).run mmst.2 >>=
      fun p => pure (b == p.1))

omit [Fintype Rand] [Inhabited M] [Fintype M] [DecidableEq M] [AddCommGroup M] in
/-- In the all-random game, the challenge ciphertext is independent of the hidden bit, so the
adversary succeeds with probability exactly `1/2`. -/
theorem game2_eq_half (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    Pr[= true | game2 tdp adv] = 1 / 2 := by
  let f : Bool → ProbComp Bool := fun _ =>
    (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
  simpa [game2, f] using
    (probOutput_decide_eq_uniformBool_half f (by rfl))

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- The bad event is bounded by the trapdoor-preimage advantage of the inverter
constructed from the adversary's random-oracle transcript. -/
theorem badEventProb_le_tdpAdvantage (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    badEventProb tdp adv ≤
      (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  sorry

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- Main BR93 bound for this file's custom one-time ROM CPA game: the distinguishing
bias is bounded by the trapdoor-preimage advantage via the standard up-to-bad
reduction. -/
theorem indcpa_bound (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    |(Pr[= true | cpaGame tdp adv]).toReal - 1 / 2| ≤
      (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  have hg12 : Pr[= true | game1 tdp adv] = Pr[= true | game2 tdp adv] :=
    congr_fun (congr_arg _ (game1_eq_game2 adv)) true
  calc |(Pr[= true | cpaGame tdp adv]).toReal - 1 / 2|
      = |(Pr[= true | cpaGame tdp adv]).toReal -
          (Pr[= true | game1 tdp adv]).toReal| := by
        congr 1; rw [hg12, game2_eq_half adv]; norm_num
    _ ≤ badEventProb tdp adv := cpaGame_gap_le_badEvent adv
    _ ≤ (tdpAdvantage tdp (inverter tdp adv)).toReal :=
        badEventProb_le_tdpAdvantage adv

end br93AsymmEnc

end BR93
