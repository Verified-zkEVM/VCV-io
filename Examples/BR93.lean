/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.CryptoFoundations.HardnessAssumptions.OneWay
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.EvalDist.Monad.Measure

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
(`tdpAdvantage`) by inspecting the adversary's random-oracle queries. The bad-event
reduction uses a shared transcript and measure-event inclusion. The up-to-bad game
hop is the remaining proof obligation.
-/

@[expose] public section

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
  change Pr[= true | ProbCompRuntime.probComp.evalSPMF mx] = 1
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
def roQueryImpl :
    QueryImpl (RO_Spec Rand M) (StateT ((Rand →ₒ M).QueryCache) ProbComp) :=
  let ro : QueryImpl (Rand →ₒ M) (StateT ((Rand →ₒ M).QueryCache) ProbComp) := randomOracle
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((Rand →ₒ M).QueryCache) ProbComp)
  idImpl + ro

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- The BR93 random-oracle handler is transparent on a computation lifted in from `unifSpec`,
threading the cache unchanged: simulating such a computation just lifts it into the cache state
monad. -/
private lemma simulateQ_roQueryImpl_liftM {β : Type} (ob : ProbComp β) :
    simulateQ (roQueryImpl (Rand := Rand) (M := M))
        (liftM ob : OracleComp (RO_Spec Rand M) β)
      = (liftM ob : StateT ((Rand →ₒ M).QueryCache) ProbComp β) := by
  simp [roQueryImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- A lifted `ProbComp` sample never touches the cache, so it commutes to the front of a run. -/
private lemma run'_liftM_bind {β γ : Type} (p : ProbComp β)
    (k : β → OracleComp (RO_Spec Rand M) γ) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (liftM p >>= k)).run' s
      = p >>= fun a => (simulateQ roQueryImpl (k a)).run' s := by
  rw [simulateQ_bind, simulateQ_roQueryImpl_liftM]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] in
/-- Running a lifted `ProbComp` sample returns the sample paired with the unchanged cache. -/
private lemma run_liftM {β : Type} (p : ProbComp β) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (liftM p)).run s = p >>= fun a => pure (a, s) := by
  rw [simulateQ_roQueryImpl_liftM]
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
/-- Splitting a logged run at a bind: the first computation threads both the cache and the
accumulated transcript forward, and the two transcripts are concatenated. -/
private lemma run_run_withLogging_bind {β γ : Type} (mx : OracleComp (RO_Spec Rand M) β)
    (k : β → OracleComp (RO_Spec Rand M) γ) (s : (Rand →ₒ M).QueryCache) :
    ((simulateQ roQueryImpl.withLogging (mx >>= k)).run).run s
      = ((simulateQ roQueryImpl.withLogging mx).run).run s >>= fun p =>
          ((simulateQ roQueryImpl.withLogging (k p.1.1)).run).run p.2 >>= fun q =>
            pure ((q.1.1, p.1.2 ++ q.1.2), q.2) := by
  rw [simulateQ_bind]
  simp only [WriterT.run_bind', StateT.run_bind, StateT.run_map, bind_pure_comp, Prod.map, id_eq]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited Rand]
  [Inhabited M] [AddCommGroup M] in
/-- A final `pure` of a state-free value can be pulled out of the run. -/
private lemma run'_simulateQ_bind_pure {β γ : Type} (mx : OracleComp (RO_Spec Rand M) β)
    (f : β → γ) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (mx >>= fun b => pure (f b))).run' s
      = (simulateQ roQueryImpl mx).run' s >>= fun b => pure (f b) := by
  rw [simulateQ_bind]
  simp [StateT.run'_eq, Functor.map_map]

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- Simulating a lifted `ProbComp` under the logging handler produces a transcript whose every
entry is a left-oracle (uniform-sampling) query: lifted computations never touch the right random
oracle, so their transcript is invisible to any right-oracle (`Sum.inr`) predicate. -/
private lemma forall_inl_of_mem_support_liftLog {β : Type} (p : ProbComp β)
    (s : (Rand →ₒ M).QueryCache) :
    ∀ x ∈ support (((simulateQ roQueryImpl.withLogging (liftM p)).run).run s),
      ∀ e ∈ x.1.2, ∃ a, e.1 = Sum.inl a := by
  rw [← OracleComp.liftComp_eq_liftM]
  induction p using OracleComp.inductionOn generalizing s with
  | pure x =>
    intro y hy e he
    simp only [liftComp_pure, simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact absurd he (by simp)
  | query_bind t k ih =>
    intro y hy e he
    rw [liftComp_bind, run_run_withLogging_bind] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨pp, hpp, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨qq, hqq, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only at he
    rw [List.mem_append] at he
    rcases he with he | he
    · -- the single lifted query logs a left-oracle entry
      rw [liftComp_query] at hpp
      simp only [OracleQuery.input_query, OracleQuery.cont_query, Functor.map_id, id_eq] at hpp
      have hinput :=
        QueryImpl.fst_eq_input_of_mem_support_run_simulateQ_withLogging_liftM_stateT
          (so := roQueryImpl (Rand := Rand) (M := M))
          (q := (liftM (unifSpec.query t) : OracleQuery (RO_Spec Rand M) _))
          (s := s) hpp he
      exact ⟨t, by simpa [OracleQuery.liftM_add_left_def] using hinput⟩
    · exact ih pp.1.1 pp.2 qq hqq e he

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
/-- A logged run of a lifted `ProbComp` sample whose transcript is discarded collapses to the
plain sample threading the cache unchanged: only the sampled value and resulting cache survive. -/
private lemma bind_logged_lift_of_log_unused {β γ : Type} (p : ProbComp β)
    (s : (Rand →ₒ M).QueryCache)
    (cont : β → (Rand →ₒ M).QueryCache → ProbComp γ) :
    ((simulateQ roQueryImpl.withLogging (liftM p)).run.run s >>=
        fun x => cont x.1.1 x.2) = p >>= fun a => cont a s := by
  have hfst : (fun x => (x.1.1, x.2)) <$>
      (simulateQ roQueryImpl.withLogging (liftM p)).run.run s
      = p >>= fun a => pure (a, s) := by
    have h1 : Prod.fst <$> (simulateQ roQueryImpl.withLogging (liftM p)).run
        = simulateQ roQueryImpl (liftM p) :=
      QueryImpl.fst_map_run_withLogging (roQueryImpl (Rand := Rand) (M := M)) (liftM p)
    have h2 := congrArg (fun (g : StateT _ ProbComp β) => g.run s) h1
    simp only [StateT.run_map] at h2
    rw [h2, run_liftM]
  calc ((simulateQ roQueryImpl.withLogging (liftM p)).run.run s >>=
          fun x => cont x.1.1 x.2)
      = ((fun x => (x.1.1, x.2)) <$>
          (simulateQ roQueryImpl.withLogging (liftM p)).run.run s) >>=
            fun q => cont q.1 q.2 := by rw [bind_map_left]
    _ = (p >>= fun a => pure (a, s)) >>= fun q => cont q.1 q.2 := by rw [hfst]
    _ = p >>= fun a => cont a s := by rw [bind_assoc]; simp only [pure_bind]

/-! ## Random-oracle transcript observations -/

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
private def rightLog (log : QueryLog (RO_Spec Rand M)) : QueryLog (RO_Spec Rand M) :=
  log.filter fun entry => entry.1.isRight

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
private def runRightLog {α : Type} (mx : OracleComp (RO_Spec Rand M) α)
    (cache : (Rand →ₒ M).QueryCache) :
    ProbComp ((α × QueryLog (RO_Spec Rand M)) × (Rand →ₒ M).QueryCache) :=
  (fun x => ((x.1.1, rightLog x.1.2), x.2)) <$>
    (simulateQ roQueryImpl.withLogging mx).run.run cache

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
private lemma runRightLog_bind {α β : Type} (mx : OracleComp (RO_Spec Rand M) α)
    (f : α → OracleComp (RO_Spec Rand M) β) (cache : (Rand →ₒ M).QueryCache) :
    runRightLog (mx >>= f) cache = (do
      let x ← runRightLog mx cache
      let y ← runRightLog (f x.1.1) x.2
      pure ((y.1.1, x.1.2 ++ y.1.2), y.2)) := by
  simp only [runRightLog, run_run_withLogging_bind, map_bind, map_pure, bind_map_left,
    rightLog, List.filter_append]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
private lemma runRightLog_pure {α : Type} (a : α) (cache : (Rand →ₒ M).QueryCache) :
    runRightLog (pure a) cache = pure ((a, []), cache) := by
  simp [runRightLog, rightLog, StateT.run_pure]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
private lemma runRightLog_lift {α : Type} (p : ProbComp α)
    (cache : (Rand →ₒ M).QueryCache) :
    runRightLog (liftM p) cache = p >>= fun a => pure ((a, []), cache) := by
  unfold runRightLog
  rw [map_eq_pure_bind]
  trans (simulateQ roQueryImpl.withLogging (liftM p)).run.run cache >>=
    fun x => pure ((x.1.1, []), x.2)
  · apply bind_congr_of_forall_mem_support
    intro x hx
    have hlog : rightLog x.1.2 = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      obtain ⟨a, ha⟩ := forall_inl_of_mem_support_liftLog p cache x hx e he
      simp [ha]
    rw [hlog]
  · exact bind_logged_lift_of_log_unused p cache (fun a s => pure ((a, []), s))

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] [DecidableEq Rand] [SampleableType M] in
private lemma any_rightLog (log : QueryLog (RO_Spec Rand M)) (p : Rand → Bool) :
    (rightLog log).any (fun e => match e.1 with | .inl _ => false | .inr r => p r) =
      log.any (fun e => match e.1 with | .inl _ => false | .inr r => p r) := by
  simp only [rightLog, List.any_filter]
  congr 1
  funext ⟨t, u⟩
  cases t <;> simp

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] [DecidableEq Rand] [SampleableType M] in
private lemma find?_rightLog (log : QueryLog (RO_Spec Rand M)) (p : Rand → Bool) :
    (rightLog log).find? (fun e => match e.1 with | .inl _ => false | .inr r => p r) =
      log.find? (fun e => match e.1 with | .inl _ => false | .inr r => p r) := by
  simp only [rightLog, List.find?_filter]
  congr 1
  funext ⟨t, u⟩
  cases t <;> simp

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited Rand]
  [Inhabited M] in
/-- Right-translating a uniform challenge mask by a constant preserves the output distribution. -/
private lemma evalSPMF_bind_add_right_uniform {γ : Type} (m : M) (f : M → ProbComp γ) :
    𝒮[(do let h ← $ᵗ M; f (h + m))] = 𝒮[(do let h ← $ᵗ M; f h)] := by
  refine evalSPMF_ext fun z => ?_
  exact probOutput_bind_add_right_uniform (α := M) m f z

/-- Real one-time CPA game in the random-oracle model. -/
def cpaGame (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← liftM ($ᵗ Bool)
    let (pk, _sk) ← liftM tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← liftM ($ᵗ Rand)
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
    let b ← liftM ($ᵗ Bool)
    let (pk, _sk) ← liftM tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← liftM ($ᵗ Rand)
    let h ← liftM ($ᵗ M)
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
      let (pk, _sk) ← liftM tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftM ($ᵗ Rand)
      let h ← liftM ($ᵗ M)
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
      let (pk, _sk) ← liftM tdp.keygen
      let (m₁, m₂, st) ← adv.choose pk
      let b ← liftM ($ᵗ Bool)
      let r ← liftM ($ᵗ Rand)
      let h ← liftM ($ᵗ M)
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
        let b ← liftM ($ᵗ Bool)
        let h ← liftM ($ᵗ M)
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

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] [Inhabited Rand] in
/-- Uniform masking step: once the challenge hash output is replaced by a fresh uniform mask,
adding either challenge message yields the same ciphertext distribution. -/
theorem game1_eq_game2 (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    𝒮[game1 tdp adv] = 𝒮[game2 tdp adv] := by
  rw [game1, game2]
  -- Push the random-oracle simulation through both games: lifted samples become plain
  -- `ProbComp` binds, the adversary's `choose`/`guess` thread the cache, and the trailing
  -- `pure` collapses, leaving identical computations save for the challenge mask.
  simp only [run'_simulateQ_bind, run_liftM, simulateQ_pure, bind_assoc, pure_bind]
  simp only [StateT.run'_eq, StateT.run_pure, map_eq_bind_pure_comp, Function.comp,
    bind_assoc, pure_bind]
  refine evalSPMF_bind_congr' _ fun b => ?_
  refine evalSPMF_bind_congr' _ fun ks => ?_
  refine evalSPMF_bind_congr' _ fun mmst => ?_
  refine evalSPMF_bind_congr' _ fun r => ?_
  exact evalSPMF_bind_add_right_uniform (if b = true then mmst.1.1 else mmst.1.2.1)
    (fun x => (simulateQ roQueryImpl (adv.guess mmst.1.2.2 (tdp.forward ks.1 r, x))).run mmst.2 >>=
      fun p => pure (b == p.1))

omit [Inhabited Rand] [Fintype Rand] [Inhabited M] [Fintype M] [DecidableEq M]
  [AddCommGroup M] in
/-- In the all-random game, the challenge ciphertext is independent of the hidden bit, so the
adversary succeeds with probability exactly `1/2`. -/
theorem game2_eq_half (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    Pr[= true | game2 tdp adv] = 1 / 2 := by
  let f : Bool → ProbComp Bool := fun _ =>
    (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftM tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftM ($ᵗ Rand)
      let h ← liftM ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
  change Pr[= true | do let b ← $ᵗ Bool; let b' ← f b; return decide (b = b')] = 1 / 2
  simpa [game2, f] using
    (probOutput_decide_eq_uniformBool_half f (by rfl))

omit [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [SampleableType Rand] [Inhabited M]
  [Fintype M] [DecidableEq M] [SampleableType M] [AddCommGroup M] in
/-- A prefix on which the predicate is uniformly `false` is invisible to `List.any`. -/
private lemma any_append_left_false {α : Type} (xs ys : List α) (pred : α → Bool)
    (h : ∀ e ∈ xs, pred e = false) : (xs ++ ys).any pred = ys.any pred := by
  rw [List.any_append, List.any_eq_false.2 fun x hx => by rw [h x hx]; exact Bool.false_ne_true,
    Bool.false_or]

omit [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [SampleableType Rand] [Inhabited M]
  [Fintype M] [DecidableEq M] [SampleableType M] [AddCommGroup M] in
/-- A prefix on which the predicate is uniformly `false` is invisible to `List.find?`. -/
private lemma find?_append_left_false {α : Type} (xs ys : List α) (pred : α → Bool)
    (h : ∀ e ∈ xs, pred e = false) : (xs ++ ys).find? pred = ys.find? pred := by
  rw [List.find?_append,
    List.find?_eq_none.2 fun x hx => by rw [h x hx]; exact Bool.false_ne_true, Option.none_or]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited Rand]
  [Inhabited M] [SampleableType M] [AddCommGroup M] in
/-- If the transcript contains a right-oracle query at `r`, then searching it for a query whose
forward image matches `tdp.forward pk r` succeeds with a right-oracle entry whose preimage has the
matching forward image. This is the pointwise heart of the bad-event reduction: a bad transcript
yields a valid trapdoor preimage. -/
private lemma find?_inr_of_anyInr (pk : PK) (r : Rand)
    (log : QueryLog (RO_Spec Rand M))
    (hbad : (log.any fun entry => match entry.1 with
      | Sum.inl _ => false
      | Sum.inr r' => r' = r) = true) :
    ∃ (r₀ : Rand) (m₀ : M),
      (log.find? fun entry => match entry.1 with
        | Sum.inl _ => false
        | Sum.inr r' => tdp.forward pk r' = tdp.forward pk r) =
        some ⟨Sum.inr r₀, m₀⟩ ∧
      tdp.forward pk r₀ = tdp.forward pk r := by
  classical
  set P : (Σ t : (RO_Spec Rand M).Domain, (RO_Spec Rand M).Range t) → Bool :=
    fun entry => match entry.1 with
      | Sum.inl _ => false
      | Sum.inr r' => decide (tdp.forward pk r' = tdp.forward pk r) with hP
  -- The bad-event witness satisfies the (weaker) forward predicate, so `find?` succeeds.
  have hex : ∃ entry ∈ log, P entry = true := by
    rw [List.any_eq_true] at hbad
    obtain ⟨entry, hmem, hentry⟩ := hbad
    refine ⟨entry, hmem, ?_⟩
    revert hentry
    simp only [hP]
    cases h : entry.1 with
    | inl a => simp
    | inr r' => intro hr'; simp only [decide_eq_true_eq] at hr' ⊢; rw [hr']
  obtain ⟨entry, hmem, hentry⟩ := hex
  obtain ⟨found, hfound⟩ :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hentry⟩)
  have hfp : P found = true := List.find?_some hfound
  rw [hfound]
  -- The found entry satisfies `P`, which is false on left queries, hence it is a right query.
  obtain ⟨t, u⟩ := found
  revert hfp
  simp only [hP]
  cases t with
  | inl a => simp
  | inr r' =>
    intro hr'
    simp only [decide_eq_true_eq] at hr'
    exact ⟨r', u, rfl, hr'⟩

/-- Whether a transcript contains a query at the hidden challenge input. -/
private def transcriptBad (r : Rand) (log : QueryLog (RO_Spec Rand M)) : Bool :=
  log.any fun entry => match entry.1 with
    | .inl _ => false
    | .inr r' => decide (r' = r)

/-- The first logged preimage of the challenge, with the inverter's default on failure. -/
private def transcriptPreimage (pk : PK) (y : Rand) (log : QueryLog (RO_Spec Rand M)) : Rand :=
  match log.find? (fun entry => match entry.1 with
    | .inl _ => false
    | .inr r => decide (tdp.forward pk r = y)) with
  | some entry => match entry.1 with
    | .inl _ => default
    | .inr r => r
  | none => default

/-- The logged challenge interaction, including the cache threaded from selection to guessing. -/
private def challengeTranscript (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M))
    (pk : PK) (y : Rand) : ProbComp (QueryLog (RO_Spec Rand M)) := do
  let choice ← runRightLog (adv.choose pk) ∅
  let b ← $ᵗ Bool
  let h ← $ᵗ M
  let guess ← runRightLog (adv.guess choice.1.1.2.2
    (y, h + if b then choice.1.1.1 else choice.1.1.2.1)) choice.2
  return choice.1.2 ++ guess.1.2

/-- One shared challenge and transcript for the bad-event and inversion observations. -/
private def challengeTranscriptExp (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    ProbComp (PK × Rand × QueryLog (RO_Spec Rand M)) := do
  let (pk, _) ← tdp.keygen
  let r ← $ᵗ Rand
  let log ← challengeTranscript adv pk (tdp.forward pk r)
  return (pk, r, log)

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] [Inhabited Rand] in
private lemma badEventExp_eq (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    badEventExp tdp adv = (do
      let (pk, _) ← tdp.keygen
      let choice ← runRightLog (adv.choose pk) ∅
      let b ← $ᵗ Bool
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let guess ← runRightLog (adv.guess choice.1.1.2.2
        (tdp.forward pk r, h + if b then choice.1.1.1 else choice.1.1.2.1)) choice.2
      return transcriptBad r (choice.1.2 ++ guess.1.2)) := by
  have projected : badEventExp tdp adv = (do
      let x ← runRightLog (show OracleComp (RO_Spec Rand M) Rand from do
        let (pk, _) ← liftM tdp.keygen
        let (m₁, m₂, st) ← adv.choose pk
        let b ← liftM ($ᵗ Bool)
        let r ← liftM ($ᵗ Rand)
        let h ← liftM ($ᵗ M)
        let _ ← adv.guess st (tdp.forward pk r, h + if b then m₁ else m₂)
        return r) ∅
      return transcriptBad x.1.1 x.1.2) := by
    simp only [badEventExp, runRightLog, StateT.run'_eq, bind_map_left]
    apply bind_congr
    intro x
    simp only [transcriptBad, any_rightLog, Bool.decide_eq_true]
    rfl
  rw [projected]
  simp only [runRightLog_bind, runRightLog_lift, runRightLog_pure, bind_assoc,
    pure_bind, List.nil_append, List.append_nil]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] [SampleableType Rand] in
private lemma inverter_eq (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) (pk : PK)
    (y : Rand) :
    inverter tdp adv pk y = transcriptPreimage (tdp := tdp) pk y <$>
      challengeTranscript adv pk y := by
  have projected : inverter tdp adv pk y = (do
      let x ← runRightLog (show OracleComp (RO_Spec Rand M) Unit from do
        let (m₁, m₂, st) ← adv.choose pk
        let b ← liftM ($ᵗ Bool)
        let h ← liftM ($ᵗ M)
        let _ ← adv.guess st (y, h + if b then m₁ else m₂)
        return ()) ∅
      return transcriptPreimage (tdp := tdp) pk y x.1.2) := by
    simp only [inverter, runRightLog, StateT.run'_eq, bind_map_left]
    apply bind_congr
    intro x
    simp only [transcriptPreimage, find?_rightLog]
    have hpure (found : Option ((t : (RO_Spec Rand M).Domain) ×
        (RO_Spec Rand M).Range t)) :
        (match found with
        | some entry => match entry.1 with
          | .inl _ => (pure default : ProbComp Rand)
          | .inr r => pure r
        | none => pure default) = pure (match found with
        | some entry => match entry.1 with
          | .inl _ => default
          | .inr r => r
        | none => default) := by
      rcases found with _ | ⟨t, u⟩
      · rfl
      · cases t <;> rfl
    exact hpure _
  rw [projected]
  simp only [challengeTranscript, runRightLog_bind, runRightLog_lift, runRightLog_pure,
    bind_assoc, pure_bind, List.nil_append, List.append_nil, map_bind, map_pure]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] in
private lemma tdpExp_eq_observation (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    tdpExp tdp (inverter tdp adv) = (fun x : PK × Rand × QueryLog (RO_Spec Rand M) =>
      decide (tdp.forward x.1 (transcriptPreimage (tdp := tdp) x.1
        (tdp.forward x.1 x.2.1) x.2.2) = tdp.forward x.1 x.2.1)) <$>
      challengeTranscriptExp (tdp := tdp) adv := by
  simp only [tdpExp, inverter_eq, challengeTranscriptExp, map_bind, map_pure,
    bind_map_left]

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] [Inhabited Rand] in
/-- The bad-event experiment observes the shared challenge transcript under any lawful
measure semantics. Only independent challenge draws are reordered. -/
private theorem measure_badEventExp_eq_observation
    [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    𝒟[badEventExp tdp adv] = 𝒟[(fun x : PK × Rand × QueryLog (RO_Spec Rand M) =>
      transcriptBad x.2.1 x.2.2) <$> challengeTranscriptExp (tdp := tdp) adv] := by
  let : MeasurableSpace (PK × SK) := ⊤
  let : MeasurableSpace Rand := ⊤
  let : MeasurableSpace
      (((M × M × adv.State) × QueryLog (RO_Spec Rand M)) × (Rand →ₒ M).QueryCache) := ⊤
  rw [badEventExp_eq]
  simp only [challengeTranscriptExp, challengeTranscript, map_bind, map_pure,
    bind_assoc, pure_bind, evalDist_bind_of_discrete tdp.keygen]
  apply MeasureTheory.Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pksk
  exact evalDist_bind_bind_bind_rotate _ _ _ _
    (measurable_from_prod_countable_left fun _ => .of_discrete)

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] [SampleableType Rand]
  [SampleableType M] [AddCommGroup M] in
private lemma transcriptBad_implies_preimage (pk : PK) (r : Rand)
    (log : QueryLog (RO_Spec Rand M)) (hbad : transcriptBad r log = true) :
    tdp.forward pk (transcriptPreimage (tdp := tdp) pk (tdp.forward pk r) log) =
      tdp.forward pk r := by
  obtain ⟨r₀, m₀, hfind, hforward⟩ :=
    find?_inr_of_anyInr (tdp := tdp) pk r log hbad
  unfold transcriptPreimage
  rw [hfind]
  exact hforward

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] in
/-- Bad BR93 challenge transcripts are a subevent of successful trapdoor inversion.
The proof uses the shared transcript's measure and pointwise event inclusion. -/
theorem measure_badEventExp_le_tdpExp
    [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    𝒟[badEventExp tdp adv] {true} ≤ 𝒟[tdpExp tdp (inverter tdp adv)] {true} := by
  let : MeasurableSpace (PK × Rand × QueryLog (RO_Spec Rand M)) := ⊤
  rw [measure_badEventExp_eq_observation, tdpExp_eq_observation,
    evalDist_map_of_discrete, evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply .of_discrete (by measurability),
    MeasureTheory.Measure.map_apply .of_discrete (by measurability)]
  apply MeasureTheory.measure_mono
  intro x hx
  change decide (_ = _) = true
  exact decide_eq_true (transcriptBad_implies_preimage (tdp := tdp) x.1 x.2.1 x.2.2 hx)

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] in
/-- The bad event is bounded by the trapdoor-preimage advantage of the inverter
constructed from the adversary's random-oracle transcript. -/
theorem badEventProb_le_tdpAdvantage (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    badEventProb tdp adv ≤ (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  rw [badEventProb, tdpAdvantage]
  apply ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one)
  simpa only [evalDist_apply_singleton] using measure_badEventExp_le_tdpExp (tdp := tdp) adv

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
