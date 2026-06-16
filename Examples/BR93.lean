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

omit [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [SampleableType Rand] [Inhabited M]
  [Fintype M] [DecidableEq M] [SampleableType M] [AddCommGroup M] in
/-- A `ProbComp` lifted into the BR93 random-oracle world is the generic `liftComp` coercion,
which threads every uniform sample through the left (`Sum.inl`) summand of the spec. -/
private lemma liftProbComp_eq_liftComp {β : Type} (ob : ProbComp β) :
    liftProbComp ob = OracleComp.liftComp ob (RO_Spec Rand M) := rfl

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- The BR93 random-oracle handler is transparent on a computation lifted in from `unifSpec`,
threading the cache unchanged: simulating such a computation just lifts it into the cache state
monad. -/
private lemma simulateQ_roQueryImpl_liftProbComp {β : Type} (ob : ProbComp β) :
    simulateQ (roQueryImpl (Rand := Rand) (M := M)) (liftProbComp ob)
      = (liftM ob : StateT ((Rand →ₒ M).QueryCache) ProbComp β) := by
  rw [liftProbComp_eq_liftComp]
  unfold roQueryImpl
  rw [QueryImpl.simulateQ_add_liftComp_left, HasQuery.toQueryImpl_eq_id',
      simulateQ_liftTarget, simulateQ_id']

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [AddCommGroup M] in
/-- A lifted `ProbComp` sample never touches the cache, so it commutes to the front of a run. -/
private lemma run'_liftProbComp_bind {β γ : Type} (p : ProbComp β)
    (k : β → OracleComp (RO_Spec Rand M) γ) (s : (Rand →ₒ M).QueryCache) :
    (simulateQ roQueryImpl (liftProbComp p >>= k)).run' s
      = p >>= fun a => (simulateQ roQueryImpl (k a)).run' s := by
  rw [simulateQ_bind, simulateQ_roQueryImpl_liftProbComp]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

omit [Inhabited Rand] [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
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
    ∀ x ∈ support (((simulateQ roQueryImpl.withLogging (liftProbComp p)).run).run s),
      ∀ e ∈ x.1.2, ∃ a, e.1 = Sum.inl a := by
  rw [liftProbComp_eq_liftComp]
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
      have hlog : pp.1.2 = [⟨Sum.inl t, pp.1.1⟩] := by
        rw [liftComp_query] at hpp
        simp only [OracleQuery.input_query, OracleQuery.cont_query, Functor.map_id, id_eq] at hpp
        rw [show (liftM (OracleSpec.query t) :
            OracleComp (RO_Spec Rand M) (unifSpec.Range t)) =
            liftM (OracleSpec.query (Sum.inl t) :
              OracleQuery (RO_Spec Rand M) (unifSpec.Range t)) from rfl] at hpp
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          Functor.map_id, id_eq, roQueryImpl, QueryImpl.withLogging_apply, add_apply_inl,
          WriterT.run_bind', WriterT.run_monadLift', StateT.run_bind, bind_pure_comp,
          support_bind, Set.mem_iUnion] at hpp
        obtain ⟨i, hi, rfl⟩ := hpp
        rw [StateT.run_map, support_map] at hi
        obtain ⟨j, _, rfl⟩ := hi
        rfl
      rw [hlog] at he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨t, rfl⟩
    · exact ih pp.1.1 pp.2 qq hqq e he

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand]
  [Inhabited M] [AddCommGroup M] [Inhabited Rand] in
/-- A logged run of a lifted `ProbComp` sample whose transcript is discarded collapses to the
plain sample threading the cache unchanged: only the sampled value and resulting cache survive. -/
private lemma bind_logged_lift_of_log_unused {β : Type} (p : ProbComp β)
    (s : (Rand →ₒ M).QueryCache)
    (cont : β → (Rand →ₒ M).QueryCache → ProbComp Bool) :
    ((simulateQ roQueryImpl.withLogging (liftProbComp p)).run.run s >>=
        fun x => cont x.1.1 x.2) = p >>= fun a => cont a s := by
  have hfst : (fun x => (x.1.1, x.2)) <$>
      (simulateQ roQueryImpl.withLogging (liftProbComp p)).run.run s
      = p >>= fun a => pure (a, s) := by
    have h1 : Prod.fst <$> (simulateQ roQueryImpl.withLogging (liftProbComp p)).run
        = simulateQ roQueryImpl (liftProbComp p) :=
      QueryImpl.fst_map_run_withLogging (roQueryImpl (Rand := Rand) (M := M)) (liftProbComp p)
    have h2 := congrArg (fun (g : StateT _ ProbComp β) => g.run s) h1
    simp only [StateT.run_map] at h2
    rw [h2, run_liftProbComp]
  calc ((simulateQ roQueryImpl.withLogging (liftProbComp p)).run.run s >>=
          fun x => cont x.1.1 x.2)
      = ((fun x => (x.1.1, x.2)) <$>
          (simulateQ roQueryImpl.withLogging (liftProbComp p)).run.run s) >>=
            fun q => cont q.1 q.2 := by rw [bind_map_left]
    _ = (p >>= fun a => pure (a, s)) >>= fun q => cont q.1 q.2 := by rw [hfst]
    _ = p >>= fun a => cont a s := by rw [bind_assoc]; simp only [pure_bind]

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

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] [Inhabited Rand] in
/-- Uniform masking step: once the challenge hash output is replaced by a fresh uniform mask,
adding either challenge message yields the same ciphertext distribution. -/
theorem game1_eq_game2 (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    𝒟[game1 tdp adv] = 𝒟[game2 tdp adv] := by
  rw [game1, game2]
  -- Push the random-oracle simulation through both games: lifted samples become plain
  -- `ProbComp` binds, the adversary's `choose`/`guess` thread the cache, and the trailing
  -- `pure` collapses, leaving identical computations save for the challenge mask.
  simp only [run'_simulateQ_bind, run_liftProbComp, simulateQ_pure, bind_assoc, pure_bind]
  simp only [StateT.run'_eq, StateT.run_pure, map_eq_bind_pure_comp, Function.comp,
    bind_assoc, pure_bind]
  refine evalDist_bind_congr' _ fun b => ?_
  refine evalDist_bind_congr' _ fun ks => ?_
  refine evalDist_bind_congr' _ fun mmst => ?_
  refine evalDist_bind_congr' _ fun r => ?_
  exact evalDist_bind_add_right_uniform (if b = true then mmst.1.1 else mmst.1.2.1)
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
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
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

omit [Fintype Rand] [Fintype M] [DecidableEq M] [SampleableType Rand] [Inhabited M]
  [SampleableType M] [AddCommGroup M] in
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

omit [Fintype Rand] [Fintype M] [DecidableEq M] [Inhabited M] in
/-- The bad event is bounded by the trapdoor-preimage advantage of the inverter
constructed from the adversary's random-oracle transcript. -/
theorem badEventProb_le_tdpAdvantage (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    badEventProb tdp adv ≤
      (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  rw [badEventProb, tdpAdvantage]
  refine (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one)
    (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one)).mpr ?_
  -- Couple the bad-event experiment with the trapdoor-inversion experiment by identifying the
  -- freshly sampled challenge randomness `r` of `badEventExp` with the inversion challenge `x`.
  -- Both experiments run the same logged guessing game; peel each logged run into a plain
  -- `ProbComp` via `run_run_withLogging_bind`, drop the uniform-sample (`Sum.inl`) transcript
  -- entries from the bad/inverter predicates using `forall_inl_of_mem_support_liftLog` (they are
  -- invisible to the right-oracle `List.any`/`List.find?`), and align the challenge randomness.
  -- On every transcript where the bad event fires, `find?_inr_of_anyInr` exhibits a logged query
  -- whose forward image matches the challenge, so the inverter returns a valid preimage and the
  -- inversion experiment succeeds; hence `bad ⟹ win` pointwise and the probabilities compare.
  have hbad : Pr[= true | badEventExp tdp adv] = Pr[= true | (do
      let x ← (simulateQ roQueryImpl.withLogging (liftProbComp tdp.keygen)).run.run ∅
      let x_1 ← (simulateQ roQueryImpl.withLogging (adv.choose x.1.1.1)).run.run x.2
      let x_2 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Bool))).run.run x_1.2
      let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Rand))).run.run x_2.2
      let x_4 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run x_3.2
      let x_5 ← (simulateQ roQueryImpl.withLogging
        (adv.guess x_1.1.1.2.2
          (tdp.forward x.1.1.1 x_3.1.1,
            x_4.1.1 + if x_2.1.1 = true then x_1.1.1.1 else x_1.1.1.2.1))).run.run x_4.2
      pure (decide ((List.any (x_1.1.2 ++ x_5.1.2) fun entry =>
        match entry.fst with
        | Sum.inl _ => false
        | Sum.inr r' => decide (r' = x_3.1.1)) = true)) : ProbComp Bool)] := by
    unfold badEventExp
    simp only [StateT.run'_eq, run_run_withLogging_bind, map_bind, map_pure, bind_assoc, pure_bind,
      simulateQ_pure, WriterT.run_pure', StateT.run_pure]
    refine probOutput_bind_congr fun x hx => ?_
    refine probOutput_bind_congr fun x_1 _ => ?_
    refine probOutput_bind_congr fun x_2 hx2 => ?_
    refine probOutput_bind_congr fun x_3 hx3 => ?_
    refine probOutput_bind_congr fun x_4 hx4 => ?_
    refine probOutput_bind_congr fun x_5 _ => ?_
    have inlFalse : ∀ {β : Type} (p : ProbComp β) (s : (Rand →ₒ M).QueryCache)
        (y : (β × QueryLog (RO_Spec Rand M)) × (Rand →ₒ M).QueryCache),
        y ∈ support ((simulateQ roQueryImpl.withLogging (liftProbComp p)).run.run s) →
        ∀ e ∈ y.1.2, (match e.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = x_3.1.1)) = false := by
      intro β p s y hy e he
      obtain ⟨a, ha⟩ := forall_inl_of_mem_support_liftLog p s y hy e he
      rw [ha]
    have hkg := inlFalse _ _ _ hx
    have hb := inlFalse _ _ _ hx2
    have hr := inlFalse _ _ _ hx3
    have hh := inlFalse _ _ _ hx4
    simp only [probOutput_pure]
    congr 2
    have toFalse : ∀ (l : QueryLog (RO_Spec Rand M)),
        (∀ e ∈ l, (match e.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = x_3.1.1)) = false) →
        (List.any l fun entry => match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = x_3.1.1)) = false :=
      fun l hl => List.any_eq_false.2 fun e he => by rw [hl e he]; exact Bool.false_ne_true
    simp only [List.any_append, toFalse _ hkg, toFalse _ hb, toFalse _ hr,
      toFalse _ hh, Bool.false_or, Bool.or_false,
      show (∅ : QueryLog (RO_Spec Rand M)) = [] from rfl, List.any_nil]
  have hbadCollapse : Pr[= true | (do
      let x ← (simulateQ roQueryImpl.withLogging (liftProbComp tdp.keygen)).run.run ∅
      let x_1 ← (simulateQ roQueryImpl.withLogging (adv.choose x.1.1.1)).run.run x.2
      let x_2 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Bool))).run.run x_1.2
      let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Rand))).run.run x_2.2
      let x_4 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run x_3.2
      let x_5 ← (simulateQ roQueryImpl.withLogging
        (adv.guess x_1.1.1.2.2
          (tdp.forward x.1.1.1 x_3.1.1,
            x_4.1.1 + if x_2.1.1 = true then x_1.1.1.1 else x_1.1.1.2.1))).run.run x_4.2
      pure (decide ((List.any (x_1.1.2 ++ x_5.1.2) fun entry =>
        match entry.fst with
        | Sum.inl _ => false
        | Sum.inr r' => decide (r' = x_3.1.1)) = true)) : ProbComp Bool)] =
      Pr[= true | (do
      let pksk ← tdp.keygen
      let cR ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅
      let b ← ($ᵗ Bool)
      let r ← ($ᵗ Rand)
      let h ← ($ᵗ M)
      let gR ← (simulateQ roQueryImpl.withLogging
        (adv.guess cR.1.1.2.2
          (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cR.2
      pure (decide ((List.any (cR.1.2 ++ gR.1.2) fun entry =>
        match entry.fst with
        | Sum.inl _ => false
        | Sum.inr r' => decide (r' = r)) = true)) : ProbComp Bool)] := by
    rw [bind_logged_lift_of_log_unused (p := tdp.keygen) (s := ∅)
      (cont := fun pksk cache => do
        let x_1 ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run cache
        let x_2 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Bool))).run.run x_1.2
        let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Rand))).run.run x_2.2
        let x_4 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run x_3.2
        let x_5 ← (simulateQ roQueryImpl.withLogging
          (adv.guess x_1.1.1.2.2
            (tdp.forward pksk.1 x_3.1.1,
              x_4.1.1 + if x_2.1.1 = true then x_1.1.1.1 else x_1.1.1.2.1))).run.run x_4.2
        pure (decide ((List.any (x_1.1.2 ++ x_5.1.2) fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = x_3.1.1)) = true)))]
    refine probOutput_bind_congr fun pksk _ => ?_
    refine probOutput_bind_congr fun cR _ => ?_
    rw [bind_logged_lift_of_log_unused (p := ($ᵗ Bool)) (s := cR.2)
      (cont := fun b cache_b => do
        let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Rand))).run.run cache_b
        let x_4 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run x_3.2
        let x_5 ← (simulateQ roQueryImpl.withLogging
          (adv.guess cR.1.1.2.2
            (tdp.forward pksk.1 x_3.1.1,
              x_4.1.1 + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run x_4.2
        pure (decide ((List.any (cR.1.2 ++ x_5.1.2) fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = x_3.1.1)) = true)))]
    refine probOutput_bind_congr fun b _ => ?_
    rw [bind_logged_lift_of_log_unused (p := ($ᵗ Rand)) (s := cR.2)
      (cont := fun r cache_r => do
        let x_4 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run cache_r
        let x_5 ← (simulateQ roQueryImpl.withLogging
          (adv.guess cR.1.1.2.2
            (tdp.forward pksk.1 r,
              x_4.1.1 + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run x_4.2
        pure (decide ((List.any (cR.1.2 ++ x_5.1.2) fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = r)) = true)))]
    refine probOutput_bind_congr fun r _ => ?_
    rw [bind_logged_lift_of_log_unused (p := ($ᵗ M)) (s := cR.2)
      (cont := fun h cache_h => do
        let x_5 ← (simulateQ roQueryImpl.withLogging
          (adv.guess cR.1.1.2.2
            (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cache_h
        pure (decide ((List.any (cR.1.2 ++ x_5.1.2) fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r' => decide (r' = r)) = true)))]
  have hbadReloc : Pr[= true | (do
      let pksk ← tdp.keygen
      let cR ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅
      let b ← ($ᵗ Bool)
      let r ← ($ᵗ Rand)
      let h ← ($ᵗ M)
      let gR ← (simulateQ roQueryImpl.withLogging
        (adv.guess cR.1.1.2.2
          (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cR.2
      pure (decide ((List.any (cR.1.2 ++ gR.1.2) fun entry =>
        match entry.fst with
        | Sum.inl _ => false
        | Sum.inr r' => decide (r' = r)) = true)) : ProbComp Bool)] =
      Pr[= true | (do
      let pksk ← tdp.keygen
      let r ← ($ᵗ Rand)
      let cR ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅
      let b ← ($ᵗ Bool)
      let h ← ($ᵗ M)
      let gR ← (simulateQ roQueryImpl.withLogging
        (adv.guess cR.1.1.2.2
          (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cR.2
      pure (decide ((List.any (cR.1.2 ++ gR.1.2) fun entry =>
        match entry.fst with
        | Sum.inl _ => false
        | Sum.inr r' => decide (r' = r)) = true)) : ProbComp Bool)] := by
    calc Pr[= true | (do
          let pksk ← tdp.keygen
          let cR ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅
          let b ← ($ᵗ Bool)
          let r ← ($ᵗ Rand)
          let h ← ($ᵗ M)
          let gR ← (simulateQ roQueryImpl.withLogging
            (adv.guess cR.1.1.2.2
              (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cR.2
          pure (decide ((List.any (cR.1.2 ++ gR.1.2) fun entry =>
            match entry.fst with
            | Sum.inl _ => false
            | Sum.inr r' => decide (r' = r)) = true)) : ProbComp Bool)]
        = Pr[= true | (do
          let pksk ← tdp.keygen
          let cR ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅
          let r ← ($ᵗ Rand)
          let b ← ($ᵗ Bool)
          let h ← ($ᵗ M)
          let gR ← (simulateQ roQueryImpl.withLogging
            (adv.guess cR.1.1.2.2
              (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cR.2
          pure (decide ((List.any (cR.1.2 ++ gR.1.2) fun entry =>
            match entry.fst with
            | Sum.inl _ => false
            | Sum.inr r' => decide (r' = r)) = true)) : ProbComp Bool)] := by
          refine probOutput_bind_congr fun pksk _ => ?_
          refine probOutput_bind_congr fun cR _ => ?_
          exact probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ Rand) _ _
      _ = _ := by
          refine probOutput_bind_congr fun pksk _ => ?_
          exact probOutput_bind_bind_swap
            ((simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅) ($ᵗ Rand) _ _
  rw [hbad, hbadCollapse, hbadReloc]
  have hinv : Pr[= true | tdpExp tdp (inverter tdp adv)] = Pr[= true | (do
      let __discr ← tdp.keygen
      let x ← ($ᵗ Rand)
      let x_1 ← (simulateQ roQueryImpl.withLogging (adv.choose __discr.1)).run.run ∅
      let x_2 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Bool))).run.run x_1.2
      let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run x_2.2
      let x_4 ← (simulateQ roQueryImpl.withLogging
        (adv.guess x_1.1.1.2.2
          (tdp.forward __discr.1 x, x_3.1.1 + if x_2.1.1 = true then x_1.1.1.1 else x_1.1.1.2.1)
          )).run.run x_3.2
      let x' ← (match List.find? (fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x))
          (x_1.1.2 ++ x_4.1.2) with
        | some entry =>
          match entry.fst with
          | Sum.inl _ => (pure default : ProbComp Rand)
          | Sum.inr r'' => pure r''
        | none => pure default)
      pure (decide (tdp.forward __discr.1 x' = tdp.forward __discr.1 x)) : ProbComp Bool)] := by
    unfold tdpExp inverter
    simp only [StateT.run'_eq, run_run_withLogging_bind, map_bind, map_pure, bind_assoc, pure_bind,
      simulateQ_pure, WriterT.run_pure', StateT.run_pure]
    refine probOutput_bind_congr fun __discr _ => ?_
    refine probOutput_bind_congr fun x _ => ?_
    refine probOutput_bind_congr fun x_1 _ => ?_
    refine probOutput_bind_congr fun x_2 hx2 => ?_
    refine probOutput_bind_congr fun x_3 hx3 => ?_
    refine probOutput_bind_congr fun x_4 _ => ?_
    have inlFalseF : ∀ {β : Type} (p : ProbComp β) (s : (Rand →ₒ M).QueryCache)
        (y : (β × QueryLog (RO_Spec Rand M)) × (Rand →ₒ M).QueryCache),
        y ∈ support ((simulateQ roQueryImpl.withLogging (liftProbComp p)).run.run s) →
        ∀ e ∈ y.1.2, (match e.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x))
          = false := by
      intro β p s y hy e he
      obtain ⟨a, ha⟩ := forall_inl_of_mem_support_liftLog p s y hy e he
      rw [ha]
    have hb := inlFalseF _ _ _ hx2
    have hh := inlFalseF _ _ _ hx3
    have toNone : ∀ (l : QueryLog (RO_Spec Rand M)),
        (∀ e ∈ l, (match e.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x)) = false) →
        (List.find? (fun entry => match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x)) l)
          = none :=
      fun l hl => List.find?_eq_none.2 fun e he => by rw [hl e he]; exact Bool.false_ne_true
    have hfind : (x_1.1.2 ++ (x_2.1.2 ++ (x_3.1.2 ++ (x_4.1.2 ++
        (∅ : QueryLog (RO_Spec Rand M)))))).find? (fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x))
        = (x_1.1.2 ++ x_4.1.2).find? (fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x)) := by
      simp only [List.find?_append, toNone _ hb, toNone _ hh, Option.none_or, Option.or_none,
        show (∅ : QueryLog (RO_Spec Rand M)) = [] from rfl, List.find?_nil]
    rw [hfind]
  have hinvCollapse : Pr[= true | (do
      let __discr ← tdp.keygen
      let x ← ($ᵗ Rand)
      let x_1 ← (simulateQ roQueryImpl.withLogging (adv.choose __discr.1)).run.run ∅
      let x_2 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ Bool))).run.run x_1.2
      let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run x_2.2
      let x_4 ← (simulateQ roQueryImpl.withLogging
        (adv.guess x_1.1.1.2.2
          (tdp.forward __discr.1 x, x_3.1.1 + if x_2.1.1 = true then x_1.1.1.1 else x_1.1.1.2.1)
          )).run.run x_3.2
      let x' ← (match List.find? (fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward __discr.1 r'' = tdp.forward __discr.1 x))
          (x_1.1.2 ++ x_4.1.2) with
        | some entry =>
          match entry.fst with
          | Sum.inl _ => (pure default : ProbComp Rand)
          | Sum.inr r'' => pure r''
        | none => pure default)
      pure (decide (tdp.forward __discr.1 x' = tdp.forward __discr.1 x)) : ProbComp Bool)] =
      Pr[= true | (do
      let pksk ← tdp.keygen
      let r ← ($ᵗ Rand)
      let cR ← (simulateQ roQueryImpl.withLogging (adv.choose pksk.1)).run.run ∅
      let b ← ($ᵗ Bool)
      let h ← ($ᵗ M)
      let gR ← (simulateQ roQueryImpl.withLogging
        (adv.guess cR.1.1.2.2
          (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1))).run.run cR.2
      let x' ← (match List.find? (fun entry =>
          match entry.fst with
          | Sum.inl _ => false
          | Sum.inr r'' => decide (tdp.forward pksk.1 r'' = tdp.forward pksk.1 r))
          (cR.1.2 ++ gR.1.2) with
        | some entry =>
          match entry.fst with
          | Sum.inl _ => (pure default : ProbComp Rand)
          | Sum.inr r'' => pure r''
        | none => pure default)
      pure (decide (tdp.forward pksk.1 x' = tdp.forward pksk.1 r)) : ProbComp Bool)] := by
    refine probOutput_bind_congr fun pksk _ => ?_
    refine probOutput_bind_congr fun r _ => ?_
    refine probOutput_bind_congr fun cR _ => ?_
    rw [bind_logged_lift_of_log_unused (p := ($ᵗ Bool)) (s := cR.2)
      (cont := fun b cache_b => do
        let x_3 ← (simulateQ roQueryImpl.withLogging (liftProbComp ($ᵗ M))).run.run cache_b
        let x_4 ← (simulateQ roQueryImpl.withLogging
          (adv.guess cR.1.1.2.2
            (tdp.forward pksk.1 r, x_3.1.1 + if b = true then cR.1.1.1 else cR.1.1.2.1)
            )).run.run x_3.2
        let x' ← (match List.find? (fun entry =>
            match entry.fst with
            | Sum.inl _ => false
            | Sum.inr r'' => decide (tdp.forward pksk.1 r'' = tdp.forward pksk.1 r))
            (cR.1.2 ++ x_4.1.2) with
          | some entry =>
            match entry.fst with
            | Sum.inl _ => (pure default : ProbComp Rand)
            | Sum.inr r'' => pure r''
          | none => pure default)
        pure (decide (tdp.forward pksk.1 x' = tdp.forward pksk.1 r)))]
    refine probOutput_bind_congr fun b _ => ?_
    rw [bind_logged_lift_of_log_unused (p := ($ᵗ M)) (s := cR.2)
      (cont := fun h cache_h => do
        let x_4 ← (simulateQ roQueryImpl.withLogging
          (adv.guess cR.1.1.2.2
            (tdp.forward pksk.1 r, h + if b = true then cR.1.1.1 else cR.1.1.2.1)
            )).run.run cache_h
        let x' ← (match List.find? (fun entry =>
            match entry.fst with
            | Sum.inl _ => false
            | Sum.inr r'' => decide (tdp.forward pksk.1 r'' = tdp.forward pksk.1 r))
            (cR.1.2 ++ x_4.1.2) with
          | some entry =>
            match entry.fst with
            | Sum.inl _ => (pure default : ProbComp Rand)
            | Sum.inr r'' => pure r''
          | none => pure default)
        pure (decide (tdp.forward pksk.1 x' = tdp.forward pksk.1 r)))]
  rw [hinv, hinvCollapse]
  refine probOutput_bind_mono fun pksk _ => ?_
  refine probOutput_bind_mono fun r _ => ?_
  refine probOutput_bind_mono fun cR _ => ?_
  refine probOutput_bind_mono fun b _ => ?_
  refine probOutput_bind_mono fun h _ => ?_
  refine probOutput_bind_mono fun gR _ => ?_
  rw [probOutput_pure]
  by_cases hbadfire : (List.any (cR.1.2 ++ gR.1.2) fun entry =>
      match entry.fst with
      | Sum.inl _ => false
      | Sum.inr r' => decide (r' = r)) = true
  · obtain ⟨r₀, m₀, hf, hfwd⟩ :=
      find?_inr_of_anyInr (tdp := tdp) pksk.1 r (cR.1.2 ++ gR.1.2) hbadfire
    rw [hf]
    simp only [pure_bind, probOutput_pure, hfwd, hbadfire, decide_true, if_pos, le_refl]
  · rw [Bool.not_eq_true] at hbadfire
    simp only [hbadfire]
    exact bot_le

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
