/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Converting rejection-on-arrival adversaries to source-final-validity adversaries

The rejection-on-arrival games and the source-final-validity games enforce the same tweak discipline
at different times: the first rejects a violating query as it arrives and leaves the state
untouched, the second answers every query and conjoins a sticky monitor into the winning condition.
The two families have distinct adversary types, so an adversary against one is not an adversary
against the other.

This file relates them in the direction a reduction needs, one conversion per game: an explicit map
sending an adversary against the rejection-on-arrival game to an adversary against the corresponding
source-final-validity game with *the same* success probability. `SM_DT_TCR_*` and `SM_DT_PRE_*` are
covered; the same construction applies to any further pair of games sharing this shape.

Each game contributes `Problem.toSourceFinalValidity`, `Adversary.toSourceFinalValidity`, and the
three theorems `..._experiment_toSourceFinalValidity`, `..._advantage_toSourceFinalValidity` and
`..._advantage_le_toSourceFinalValidity`.

The conversion is a wrapper handler holding a replica of the two tweak histories. It evaluates the
acceptance test itself and, on a query its rejection-on-arrival counterpart would refuse, answers
`none` **without querying**. The suppressed query is exactly the one that would have poisoned the
monitor, so the monitor stays valid and the two runs couple exactly — hence an equality of
advantages, with the inequality as a corollary.

The replica records tweaks alone. That is all the acceptance test reads, and it is what
`TweakableHash.collectionOracle`'s history-through-`tweakOf` interface is for.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6 for the `VQS_t`
  presentation the source-final-validity games render.
-/

public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M M' Y Q : Type}

/-! ## Reading a challenge history through its tweaks

A wrapper that holds only the tweaks of the challenge history decides the same acceptance test as
the game, which holds whole queries. -/

/-- Reservation is decided by the tweaks of the challenge history alone. -/
private theorem tweakReserved_map_iff (tweakOf : Q → Tweak) (qs : List Q) (t : Tweak) :
    TweakReserved id (qs.map tweakOf) t ↔ TweakReserved tweakOf qs t := by
  simp [TweakReserved]

/-- Freshness is decided by the tweaks of the challenge history alone. -/
private theorem tweakFresh_map_iff (tweakOf : Q → Tweak) (qs : List Q) (twsColl : List Tweak)
    (t : Tweak) :
    TweakFresh id (qs.map tweakOf) twsColl t ↔ TweakFresh tweakOf qs twsColl t := by
  simp [TweakFresh, tweakReserved_map_iff]

/-! ## SM-DT-TCR -/

/-- The source-final-validity problem attacked by the converted adversary.

Reducible: the collection it carries indexes the oracle specs on both sides of the conversion, so
`prob.toSourceFinalValidity.thColl` and `prob.thColl` have to agree at instance transparency for the
wrapper and the monitor's oracles to compose. -/
@[reducible] def SM_DT_TCR_Problem.toSourceFinalValidity
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) :
    SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := prob.numTargets

/-- The challenge half of the wrapper: a query over the target cap, or at a tweak the replica
already records on either oracle, is answered `none` and not forwarded. The test is
`SM_DT_TCR_challengeOracle`'s, read through the replica. -/
private def SM_DT_TCR_toSourceFinalValidityChallengeOracle [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) :
    QueryImpl (SM_DT_TCR_challengeSpec Tweak M Y)
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) :=
  fun tm => StateT.mk fun s =>
    if prob.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 tm.1 then
      pure (none, s)
    else
      (liftM ((SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y).query tm) :
        OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
          SourceFinalValidity.collectionSpec prob.thColl)) Y) >>=
        fun y => pure (some y, (s.1 ++ [tm.1], s.2))

/-- The collection half of the wrapper: a query at a tweak the challenge oracle has reserved is
answered `none` and not forwarded; otherwise it is forwarded and its tweak recorded. -/
private def SM_DT_TCR_toSourceFinalValidityCollectionOracle [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) :
    QueryImpl (collectionSpec prob.thColl)
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) :=
  fun q => StateT.mk fun s =>
    if TweakReserved id s.1 q.2.1 then
      pure (none, s)
    else
      (liftM ((SourceFinalValidity.collectionSpec prob.thColl).query q) :
        OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
          SourceFinalValidity.collectionSpec prob.thColl)) Y) >>=
        fun y => pure (some y, (s.1, s.2 ++ [q.2.1]))

/-- The rejection-on-arrival oracles, simulated against the source-final-validity oracles over a
replica of the two tweak histories.

Private randomness passes straight through. A query the rejection-on-arrival oracles would refuse is
answered `none` and **not forwarded**, so the monitor never sees the query that would poison it; an
accepted query is forwarded verbatim and its tweak appended to the replica. -/
private def SM_DT_TCR_toSourceFinalValidityOracles [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) :
    QueryImpl (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl))
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) :=
  (QueryImpl.ofLift unifSpec
      (OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
        SourceFinalValidity.collectionSpec prob.thColl)))).liftTarget
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) +
    (SM_DT_TCR_toSourceFinalValidityChallengeOracle prob +
      SM_DT_TCR_toSourceFinalValidityCollectionOracle prob)

/-- The converted adversary. Target selection runs against the wrapper over an initially empty
replica; the forgery phase is the original one, unchanged — its type is the same on both sides and
the public seed is sampled once from `prob.th.seedGen` in either experiment. -/
def SM_DT_TCR_Adversary.toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.Adversary prob.toSourceFinalValidity where
  State := adv.State × (List Tweak × List Tweak)
  choose := (simulateQ (SM_DT_TCR_toSourceFinalValidityOracles prob) adv.choose).run ([], [])
  forge state pk := adv.forge state.1 pk

/-! ### The coupling

Interpreting the wrapper's base oracles by the monitor's handler fuses the two into one handler over
the product state, at the rejection-on-arrival interface. Both handlers then speak the same oracle
spec, so the run-level agreement is a state projection gated by an invariant. -/

/-- Replica and monitor state, as carried by the fused handler. -/
private abbrev JointState (Tweak M : Type) : Type :=
  (List Tweak × List Tweak) × SM_DT_TCR_SourceFinalValidity.State Tweak M

/-- The replica mirrors the monitor's two histories, and the monitor is unpoisoned. -/
private def Coupled (s : JointState Tweak M) : Prop :=
  s.1.1 = s.2.challenges.map Prod.fst ∧ s.1.2 = s.2.collectionTweaks ∧ s.2.valid = true

/-- The rejection-on-arrival state a joint state projects onto. -/
private def project (s : JointState Tweak M) : SM_DT_TCR_State Tweak M :=
  (s.2.challenges, s.2.collectionTweaks)

/-- The wrapper and the monitor's oracles as a single handler over the joint state. -/
private def fused [DecidableEq Tweak] (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) :
    QueryImpl (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl))
      (StateT (JointState Tweak M) ProbComp) :=
  ((SM_DT_TCR_SourceFinalValidity.oracles prob.toSourceFinalValidity pk).mapStateTBase
    (SM_DT_TCR_toSourceFinalValidityOracles prob)).flattenStateT

/-- One step of the fused handler: run the wrapper on the replica, then interpret the base oracles
it queried against the monitor. -/
private theorem fused_run [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (t : (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl)).Domain)
    (s : JointState Tweak M) :
    (fused prob pk t).run s =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles prob.toSourceFinalValidity pk)
          ((SM_DT_TCR_toSourceFinalValidityOracles prob t).run s.1)).run s.2 := by
  rfl

private theorem fused_project_step [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (t : (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl)).Domain)
    (s : JointState Tweak M) (hs : Coupled s) :
    Prod.map id project <$> (fused prob pk t).run s =
      (SM_DT_TCR_oracles prob pk t).run (project s) := by
  obtain ⟨⟨twsChal, twsColl⟩, ⟨qsChal, cs, valid⟩⟩ := s
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  cases t with
  | inl q =>
    rw [fused_run]
    simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
      SM_DT_TCR_oracles, project, QueryImpl.ofLift_apply, Functor.map_map]
  | inr t =>
    cases t with
    | inl tm =>
      rw [fused_run]
      simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
        SM_DT_TCR_oracles, project, SM_DT_TCR_toSourceFinalValidityChallengeOracle,
        SM_DT_TCR_challengeOracle, SM_DT_TCR_SourceFinalValidity.challengeOracle,
        SourceFinalValidity.State.recordTarget, tweakFresh_map_iff,
        StateT.run_bind, Functor.map_map]
      split <;> simp
    | inr q =>
      rw [fused_run]
      simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
        SM_DT_TCR_oracles, project, SM_DT_TCR_toSourceFinalValidityCollectionOracle,
        collectionOracle, SourceFinalValidity.collectionOracle,
        SourceFinalValidity.State.recordCollection, tweakReserved_map_iff,
        StateT.run_bind, Functor.map_map]
      split <;> simp

private theorem fused_preserves_coupled [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (t : (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl)).Domain)
    (s : JointState Tweak M) (hs : Coupled s) :
    ∀ z ∈ support ((fused prob pk t).run s), Coupled z.2 := by
  obtain ⟨⟨twsChal, twsColl⟩, ⟨qsChal, cs, valid⟩⟩ := s
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  cases t with
  | inl q =>
    rw [fused_run]
    simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
      Coupled, QueryImpl.ofLift_apply, Functor.map_map]
  | inr t =>
    cases t with
    | inl tm =>
      rw [fused_run]
      by_cases hrej : prob.numTargets ≤ qsChal.length ∨
          ¬ TweakFresh Prod.fst qsChal twsColl tm.1
      · simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
          SM_DT_TCR_toSourceFinalValidityChallengeOracle, tweakFresh_map_iff, Coupled, hrej]
      · rw [not_or, not_not, Nat.not_le] at hrej
        simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
          SM_DT_TCR_toSourceFinalValidityChallengeOracle,
          SM_DT_TCR_SourceFinalValidity.challengeOracle,
          SourceFinalValidity.State.recordTarget, tweakFresh_map_iff, Coupled,
          Nat.not_le.mpr hrej.1, hrej.1, hrej.2, List.map_append, Functor.map_map]
    | inr q =>
      rw [fused_run]
      by_cases hrej : TweakReserved Prod.fst qsChal q.2.1 <;>
        simp [SM_DT_TCR_toSourceFinalValidityOracles, SM_DT_TCR_SourceFinalValidity.oracles,
          SM_DT_TCR_toSourceFinalValidityCollectionOracle,
          SourceFinalValidity.collectionOracle,
          SourceFinalValidity.State.recordCollection, tweakReserved_map_iff, Coupled, hrej,
          Functor.map_map]

/-- Over a whole selection phase, the fused run projects onto the rejection-on-arrival run. -/
private theorem fused_simulateQ_run [DecidableEq Tweak] {α : Type}
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      collectionSpec prob.thColl)) α) (s : JointState Tweak M) (hs : Coupled s) :
    Prod.map id project <$> (simulateQ (fused prob pk) oa).run s =
      (simulateQ (SM_DT_TCR_oracles prob pk) oa).run (project s) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ Coupled project
    (fused_preserves_coupled prob pk) (fused_project_step prob pk) oa s hs

/-- Every state the fused run can reach stays coupled; in particular the monitor stays valid. -/
private theorem fused_simulateQ_run_coupled [DecidableEq Tweak] {α : Type}
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      collectionSpec prob.thColl)) α) (s : JointState Tweak M) (hs : Coupled s) :
    ∀ z ∈ support ((simulateQ (fused prob pk) oa).run s), Coupled z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ Coupled
    (fused_preserves_coupled prob pk) oa s hs

/-! ### The bridge -/

/-- Converting a rejection-on-arrival adversary leaves the experiment's output distribution
unchanged: the wrapper suppresses exactly the queries that would have poisoned the monitor, so the
monitor is valid on every reachable run and the two winning conditions agree pointwise. -/
theorem SM_DT_TCR_experiment_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.Experiment adv.toSourceFinalValidity =
      SM_DT_TCR_Experiment adv := by
  have hinit : Coupled ((([], []) : List Tweak × List Tweak),
      (SourceFinalValidity.State.initial : SM_DT_TCR_SourceFinalValidity.State Tweak M)) := by
    simp [Coupled, SourceFinalValidity.State.initial]
  simp only [SM_DT_TCR_SourceFinalValidity.Experiment, SM_DT_TCR_Experiment,
    SM_DT_TCR_Adversary.toSourceFinalValidity]
  refine bind_congr fun pk => ?_
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    show (([], []) : SM_DT_TCR_State Tweak M) =
      project ((([], []) : List Tweak × List Tweak),
        (SourceFinalValidity.State.initial : SM_DT_TCR_SourceFinalValidity.State Tweak M)) from rfl,
    ← fused_simulateQ_run prob pk adv.choose _ hinit]
  simp only [fused, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  obtain ⟨-, -, hvalid⟩ := fused_simulateQ_run_coupled prob pk adv.choose _ hinit z hz
  simp only [project, hvalid, Bool.true_and, Prod.map_fst, Prod.map_snd, id_eq]
  rfl

/-- The conversion is advantage-preserving, not merely advantage-bounding. -/
theorem SM_DT_TCR_advantage_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_Advantage adv =
      SM_DT_TCR_SourceFinalValidity.Advantage adv.toSourceFinalValidity := by
  rw [SM_DT_TCR_Advantage, SM_DT_TCR_SourceFinalValidity.Advantage,
    SM_DT_TCR_experiment_toSourceFinalValidity]

/-- A rejection-on-arrival bound follows from any source-final-validity bound: whatever hardness is
assumed of the monitor presentation transfers to this one. -/
theorem SM_DT_TCR_advantage_le_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_Advantage adv ≤
      SM_DT_TCR_SourceFinalValidity.Advantage adv.toSourceFinalValidity :=
  le_of_eq (SM_DT_TCR_advantage_toSourceFinalValidity adv)

/-! ## SM-DT-PRE

The same construction, at the game whose challenge oracle draws its own message. The wrapper never
learns the drawn message — it only ever sees the digest — which is why the replica records tweaks
alone; the projection reads the drawn messages back out of the monitor's own history. -/

/-- The source-final-validity problem attacked by the converted adversary. Reducible for the same
reason as its SM-TCR counterpart. -/
@[reducible] def SM_DT_PRE_Problem.toSourceFinalValidity
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) :
    SM_DT_PRE_SourceFinalValidity.Problem ι PkSeed Tweak M M' Y where
  th := prob.th
  emb := prob.emb
  emb_injective := prob.emb_injective
  thColl := prob.thColl
  numTargets := prob.numTargets

/-- The challenge half of the wrapper. On the accepting path the message is drawn by the monitor's
oracle, not here; on the rejecting path nothing is drawn at all, exactly as
`SM_DT_PRE_challengeOracle` does. -/
private def SM_DT_PRE_toSourceFinalValidityChallengeOracle [DecidableEq Tweak]
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) :
    QueryImpl (SM_DT_PRE_challengeSpec Tweak Y)
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) :=
  fun t => StateT.mk fun s =>
    if prob.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then
      pure (none, s)
    else
      (liftM ((SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y).query t) :
        OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
          SourceFinalValidity.collectionSpec prob.thColl)) Y) >>=
        fun y => pure (some y, (s.1 ++ [t], s.2))

/-- The collection half of the wrapper. -/
private def SM_DT_PRE_toSourceFinalValidityCollectionOracle [DecidableEq Tweak]
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) :
    QueryImpl (collectionSpec prob.thColl)
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) :=
  fun q => StateT.mk fun s =>
    if TweakReserved id s.1 q.2.1 then
      pure (none, s)
    else
      (liftM ((SourceFinalValidity.collectionSpec prob.thColl).query q) :
        OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
          SourceFinalValidity.collectionSpec prob.thColl)) Y) >>=
        fun y => pure (some y, (s.1, s.2 ++ [q.2.1]))

/-- Private randomness passes through; the two game oracles are wrapped. -/
private def SM_DT_PRE_toSourceFinalValidityOracles [DecidableEq Tweak]
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) :
    QueryImpl (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.thColl))
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) :=
  (QueryImpl.ofLift unifSpec
      (OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
        SourceFinalValidity.collectionSpec prob.thColl)))).liftTarget
      (StateT (List Tweak × List Tweak)
        (OracleComp (unifSpec + (SM_DT_PRE_SourceFinalValidity.challengeSpec Tweak Y +
          SourceFinalValidity.collectionSpec prob.thColl)))) +
    (SM_DT_PRE_toSourceFinalValidityChallengeOracle prob +
      SM_DT_PRE_toSourceFinalValidityCollectionOracle prob)

/-- The converted adversary. -/
def SM_DT_PRE_Adversary.toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_SourceFinalValidity.Adversary prob.toSourceFinalValidity where
  State := adv.State × (List Tweak × List Tweak)
  choose := (simulateQ (SM_DT_PRE_toSourceFinalValidityOracles prob) adv.choose).run ([], [])
  invert state pk := adv.invert state.1 pk

/-- Replica and monitor state, as carried by the fused SM-PRE handler. -/
private abbrev PreJointState (Tweak M' : Type) : Type :=
  (List Tweak × List Tweak) × SM_DT_PRE_SourceFinalValidity.State Tweak M'

/-- The replica mirrors the monitor's two histories, and the monitor is unpoisoned. -/
private def PreCoupled (s : PreJointState Tweak M') : Prop :=
  s.1.1 = s.2.challenges.map Prod.fst ∧ s.1.2 = s.2.collectionTweaks ∧ s.2.valid = true

/-- The rejection-on-arrival state a joint state projects onto. -/
private def preProject (s : PreJointState Tweak M') : SM_DT_PRE_State Tweak M' :=
  (s.2.challenges, s.2.collectionTweaks)

/-- The wrapper and the monitor's oracles as a single handler over the joint state. -/
private noncomputable def preFused [DecidableEq Tweak] [SampleableType M']
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.thColl))
      (StateT (PreJointState Tweak M') ProbComp) :=
  ((SM_DT_PRE_SourceFinalValidity.oracles prob.toSourceFinalValidity pk).mapStateTBase
    (SM_DT_PRE_toSourceFinalValidityOracles prob)).flattenStateT

private theorem preFused_run [DecidableEq Tweak] [SampleableType M']
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)
    (t : (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.thColl)).Domain)
    (s : PreJointState Tweak M') :
    (preFused prob pk t).run s =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (SM_DT_PRE_SourceFinalValidity.oracles prob.toSourceFinalValidity pk)
          ((SM_DT_PRE_toSourceFinalValidityOracles prob t).run s.1)).run s.2 := by
  rfl

private theorem preFused_project_step [DecidableEq Tweak] [SampleableType M']
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)
    (t : (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.thColl)).Domain)
    (s : PreJointState Tweak M') (hs : PreCoupled s) :
    Prod.map id preProject <$> (preFused prob pk t).run s =
      (SM_DT_PRE_oracles prob pk t).run (preProject s) := by
  obtain ⟨⟨twsChal, twsColl⟩, ⟨qsChal, cs, valid⟩⟩ := s
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  cases t with
  | inl q =>
    rw [preFused_run]
    simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
      SM_DT_PRE_oracles, preProject, QueryImpl.ofLift_apply, Functor.map_map]
  | inr t =>
    cases t with
    | inl tw =>
      rw [preFused_run]
      simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
        SM_DT_PRE_oracles, preProject, SM_DT_PRE_toSourceFinalValidityChallengeOracle,
        SM_DT_PRE_challengeOracle, SM_DT_PRE_SourceFinalValidity.challengeOracle,
        SourceFinalValidity.State.recordTarget, tweakFresh_map_iff,
        StateT.run_bind, Functor.map_map]
      split <;> simp [Functor.map_map]
    | inr q =>
      rw [preFused_run]
      simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
        SM_DT_PRE_oracles, preProject, SM_DT_PRE_toSourceFinalValidityCollectionOracle,
        collectionOracle, SourceFinalValidity.collectionOracle,
        SourceFinalValidity.State.recordCollection, tweakReserved_map_iff,
        StateT.run_bind, Functor.map_map]
      split <;> simp

private theorem preFused_preserves_coupled [DecidableEq Tweak] [SampleableType M']
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)
    (t : (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.thColl)).Domain)
    (s : PreJointState Tweak M') (hs : PreCoupled s) :
    ∀ z ∈ support ((preFused prob pk t).run s), PreCoupled z.2 := by
  obtain ⟨⟨twsChal, twsColl⟩, ⟨qsChal, cs, valid⟩⟩ := s
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  cases t with
  | inl q =>
    rw [preFused_run]
    simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
      PreCoupled, QueryImpl.ofLift_apply, Functor.map_map]
  | inr t =>
    cases t with
    | inl tw =>
      rw [preFused_run]
      by_cases hrej : prob.numTargets ≤ qsChal.length ∨
          ¬ TweakFresh Prod.fst qsChal twsColl tw
      · simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
          SM_DT_PRE_toSourceFinalValidityChallengeOracle, tweakFresh_map_iff, PreCoupled, hrej]
      · rw [not_or, not_not, Nat.not_le] at hrej
        simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
          SM_DT_PRE_toSourceFinalValidityChallengeOracle,
          SM_DT_PRE_SourceFinalValidity.challengeOracle,
          SourceFinalValidity.State.recordTarget, tweakFresh_map_iff, PreCoupled,
          Nat.not_le.mpr hrej.1, hrej.1, hrej.2, List.map_append, Functor.map_map]
    | inr q =>
      rw [preFused_run]
      by_cases hrej : TweakReserved Prod.fst qsChal q.2.1 <;>
        simp [SM_DT_PRE_toSourceFinalValidityOracles, SM_DT_PRE_SourceFinalValidity.oracles,
          SM_DT_PRE_toSourceFinalValidityCollectionOracle,
          SourceFinalValidity.collectionOracle,
          SourceFinalValidity.State.recordCollection, tweakReserved_map_iff, PreCoupled, hrej,
          Functor.map_map]

private theorem preFused_simulateQ_run [DecidableEq Tweak] [SampleableType M'] {α : Type}
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y +
      collectionSpec prob.thColl)) α) (s : PreJointState Tweak M') (hs : PreCoupled s) :
    Prod.map id preProject <$> (simulateQ (preFused prob pk) oa).run s =
      (simulateQ (SM_DT_PRE_oracles prob pk) oa).run (preProject s) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ PreCoupled preProject
    (preFused_preserves_coupled prob pk) (preFused_project_step prob pk) oa s hs

private theorem preFused_simulateQ_run_coupled [DecidableEq Tweak] [SampleableType M'] {α : Type}
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)
    (oa : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y +
      collectionSpec prob.thColl)) α) (s : PreJointState Tweak M') (hs : PreCoupled s) :
    ∀ z ∈ support ((simulateQ (preFused prob pk) oa).run s), PreCoupled z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ PreCoupled
    (preFused_preserves_coupled prob pk) oa s hs

/-- The SM-PRE twin of `SM_DT_TCR_experiment_toSourceFinalValidity`. -/
theorem SM_DT_PRE_experiment_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq Y]
    [SampleableType M'] {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_SourceFinalValidity.Experiment adv.toSourceFinalValidity =
      SM_DT_PRE_Experiment adv := by
  have hinit : PreCoupled ((([], []) : List Tweak × List Tweak),
      (SourceFinalValidity.State.initial : SM_DT_PRE_SourceFinalValidity.State Tweak M')) := by
    simp [PreCoupled, SourceFinalValidity.State.initial]
  simp only [SM_DT_PRE_SourceFinalValidity.Experiment, SM_DT_PRE_Experiment,
    SM_DT_PRE_Adversary.toSourceFinalValidity]
  refine bind_congr fun pk => ?_
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    show (([], []) : SM_DT_PRE_State Tweak M') =
      preProject ((([], []) : List Tweak × List Tweak),
        (SourceFinalValidity.State.initial :
          SM_DT_PRE_SourceFinalValidity.State Tweak M')) from rfl,
    ← preFused_simulateQ_run prob pk adv.choose _ hinit]
  simp only [preFused, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  obtain ⟨-, -, hvalid⟩ := preFused_simulateQ_run_coupled prob pk adv.choose _ hinit z hz
  simp only [preProject, hvalid, Bool.true_and, Prod.map_fst, Prod.map_snd, id_eq]
  rfl

/-- The SM-PRE conversion is advantage-preserving. -/
theorem SM_DT_PRE_advantage_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq Y]
    [SampleableType M'] {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_Advantage adv =
      SM_DT_PRE_SourceFinalValidity.Advantage adv.toSourceFinalValidity := by
  rw [SM_DT_PRE_Advantage, SM_DT_PRE_SourceFinalValidity.Advantage,
    SM_DT_PRE_experiment_toSourceFinalValidity]

/-- A rejection-on-arrival SM-PRE bound follows from any source-final-validity bound. -/
theorem SM_DT_PRE_advantage_le_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq Y]
    [SampleableType M'] {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_Advantage adv ≤
      SM_DT_PRE_SourceFinalValidity.Advantage adv.toSourceFinalValidity :=
  le_of_eq (SM_DT_PRE_advantage_toSourceFinalValidity adv)

end TweakableHash
