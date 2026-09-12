/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# The tweak-discipline bridge, over an abstract challenge oracle

The rejection-on-arrival games and the source-final-validity games differ only in how they enforce
the tweak discipline: the first refuses a violating query, the second answers it and poisons a
sticky bit that the winning condition conjoins. Relating them is the same argument every time, and
this file states it once.

A challenge oracle of either presentation is determined by what it draws (`draw`), what it records
(`entry`), what it answers (`resp`), and how the discipline reads a tweak off a query
(`tweakOfQuery`) and off a recorded entry (`tweakOfHist`). The two presentations then differ only in
what they do when the discipline is violated: `roaChallengeOracle` refuses, `monitorChallengeOracle`
answers and records. Everything else — the collection halves, the wrapper that converts an
adversary, the coupling invariant, and the run-level agreement — is shared.

The parameters are the *data* of a challenge oracle, not an opaque handler with equational
hypotheses. Both oracles are defined here, so a game relates itself to this file by an equation
between two definitions rather than by re-deriving the argument.

## Main definitions

- `roaChallengeOracle`, `roaOracles` — the rejection-on-arrival presentation
- `monitorChallengeOracle`, `monitorOracles` — the source-final-validity presentation
- `toMonitorOracles` — the wrapper: run the rejection test against a replica of the two tweak
  histories and decline to forward a query that would poison the monitor
- `Coupled` — the replica mirrors both monitor histories and the monitor is unpoisoned

## Main statements

- `fused_project_step`, `fused_preserves_coupled` — the two per-query facts the coupling rests on
- `run_toMonitor_bind_eq` — a whole selection phase run against the wrapper, followed by any
  continuation that ignores a valid monitor, equals the rejection-on-arrival run followed by the
  corresponding continuation

`run_toMonitor_bind_eq` is stated for arbitrary continuations, so a game obtains its
experiment-level bridge by supplying its two winning conditions and the fact that they agree once
`SourceFinalValidity.State.valid` holds.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2, Def. 3 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6 for the `VQS_t`
  presentation the source-final-validity games render.
-/

public section

namespace TweakableHash

open OracleComp OracleSpec

variable {ι PkSeed Tweak Y Qq Qh V : Type}

/-! ## Reading a challenge history through its tweaks

The replica the wrapper carries records tweaks alone, never entries. That is sound because the
acceptance test reads nothing else, which these two lemmas make precise. -/

/-- Reservation is decided by the tweaks of the challenge history alone. -/
theorem tweakReserved_map_iff (tweakOf : Qh → Tweak) (qs : List Qh) (t : Tweak) :
    TweakReserved id (qs.map tweakOf) t ↔ TweakReserved tweakOf qs t := by
  simp [TweakReserved]

/-- Freshness is decided by the tweaks of the challenge history alone. -/
theorem tweakFresh_map_iff (tweakOf : Qh → Tweak) (qs : List Qh) (twsColl : List Tweak)
    (t : Tweak) :
    TweakFresh id (qs.map tweakOf) twsColl t ↔ TweakFresh tweakOf qs twsColl t := by
  simp [TweakFresh, tweakReserved_map_iff]

namespace ToFinalValidity

/-! ## The two challenge interfaces -/

/-- The challenge interface of a rejection-on-arrival game: a refused query is answered `none`. -/
abbrev roaChallengeSpec (Qq Y : Type) : OracleSpec Qq := Qq →ₒ Option Y

/-- The challenge interface of a source-final-validity game: every query is answered. -/
abbrev monitorChallengeSpec (Qq Y : Type) : OracleSpec Qq := Qq →ₒ Y

variable (tweakOfQuery : Qq → Tweak) (tweakOfHist : Qh → Tweak) (numTargets : ℕ)
  (draw : Qq → ProbComp V) (entry : Qq → V → Qh) (resp : Qq → V → Y)

/-- The rejection test, read off the rejection-on-arrival state: the target cap is reached, or the
query's tweak is not fresh for the two histories. -/
@[expose] def Refuses (s : List Qh × List Tweak) (q : Qq) : Prop :=
  numTargets ≤ s.1.length ∨ ¬ TweakFresh tweakOfHist s.1 s.2 (tweakOfQuery q)

instance [DecidableEq Tweak] (s : List Qh × List Tweak) (q : Qq) :
    Decidable (Refuses tweakOfQuery tweakOfHist numTargets s q) := by
  unfold Refuses; infer_instance

/-! ## The two challenge oracles -/

/-- The rejection-on-arrival challenge oracle. A refused query draws nothing and leaves the state
untouched, so refusal consumes no randomness. -/
@[expose] def roaChallengeOracle [DecidableEq Tweak] :
    QueryImpl (roaChallengeSpec Qq Y) (StateT (List Qh × List Tweak) ProbComp) :=
  fun q => do
    let s ← get
    if Refuses tweakOfQuery tweakOfHist numTargets s q then
      return none
    else
      let v ← (draw q : StateT (List Qh × List Tweak) ProbComp V)
      set (s.1 ++ [entry q v], s.2)
      return some (resp q v)

/-- The source-final-validity challenge oracle. Every query draws, is answered, and is recorded; a
violation poisons the monitor without suppressing either the draw or the response. -/
@[expose] def monitorChallengeOracle [DecidableEq Tweak] :
    QueryImpl (monitorChallengeSpec Qq Y)
      (StateT (SourceFinalValidity.State Qh Tweak) ProbComp) :=
  fun q => do
    let v ← (draw q : StateT (SourceFinalValidity.State Qh Tweak) ProbComp V)
    let st ← get
    set (st.recordTarget numTargets tweakOfHist (entry q v))
    return resp q v

/-! ## The two oracle bundles -/

variable (thColl : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed)

/-- Both oracles of a rejection-on-arrival game over its shared state, at a public seed. Private
randomness passes straight through. -/
@[expose] def roaOracles [DecidableEq Tweak] :
    QueryImpl (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl))
      (StateT (List Qh × List Tweak) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List Qh × List Tweak) ProbComp) +
    (roaChallengeOracle tweakOfQuery tweakOfHist numTargets draw entry resp +
      TweakableHash.collectionOracle tweakOfHist thColl pk)

/-- Both oracles of a source-final-validity game over their shared monitor, at a public seed. -/
@[expose] def monitorOracles [DecidableEq Tweak] :
    QueryImpl (unifSpec + (monitorChallengeSpec Qq Y + SourceFinalValidity.collectionSpec thColl))
      (StateT (SourceFinalValidity.State Qh Tweak) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SourceFinalValidity.State Qh Tweak) ProbComp) +
    (monitorChallengeOracle tweakOfHist numTargets draw entry resp +
      SourceFinalValidity.collectionOracle tweakOfHist thColl pk)

/-! ## The wrapper

The converted adversary keeps a replica of the two tweak histories, evaluates the rejection test
itself, and declines to forward a query the rejection-on-arrival oracles would have refused. The
monitor therefore never sees a query that would poison it, while the answer distribution the
adversary observes is unchanged.

The replica records tweaks alone. That is all the acceptance test reads, and it is what
`TweakableHash.collectionOracle`'s history-through-`tweakOf` interface is for. -/

/-- The oracle computation the wrapper's handlers target: the source-final-validity interface, with
private randomness still available. -/
abbrev Wrapped (Qq Y : Type) (thColl : TweakableHashCollection ι PkSeed Tweak Y) :=
  OracleComp (unifSpec +
    (monitorChallengeSpec Qq Y + SourceFinalValidity.collectionSpec thColl))

/-- The challenge half of the wrapper: a query over the target cap, or at a tweak the replica
already records on either oracle, is answered `none` and not forwarded. The test is
`roaChallengeOracle`'s, read through the replica. -/
def toMonitorChallengeOracle [DecidableEq Tweak] :
    QueryImpl (roaChallengeSpec Qq Y)
      (StateT (List Tweak × List Tweak) (Wrapped Qq Y thColl)) :=
  fun q => StateT.mk fun s =>
    if Refuses tweakOfQuery id numTargets s q then
      pure (none, s)
    else
      (liftM ((monitorChallengeSpec Qq Y).query q) : Wrapped Qq Y thColl Y) >>=
        fun y => pure (some y, (s.1 ++ [tweakOfQuery q], s.2))

/-- The collection half of the wrapper: a query at a tweak the challenge oracle has reserved is
answered `none` and not forwarded; otherwise it is forwarded and its tweak recorded.

`Qq` is explicit because it occurs only in the target monad, where it is not determined by the
arguments. -/
def toMonitorCollectionOracle [DecidableEq Tweak] (Qq : Type) :
    QueryImpl (TweakableHash.collectionSpec thColl)
      (StateT (List Tweak × List Tweak) (Wrapped Qq Y thColl)) :=
  fun q => StateT.mk fun s =>
    if TweakReserved id s.1 q.2.1 then
      pure (none, s)
    else
      (liftM ((SourceFinalValidity.collectionSpec thColl).query q) : Wrapped Qq Y thColl Y) >>=
        fun y => pure (some y, (s.1, s.2 ++ [q.2.1]))

/-- The rejection-on-arrival oracles, simulated against the source-final-validity oracles over a
replica of the two tweak histories.

Private randomness passes straight through. A query the rejection-on-arrival oracles would refuse is
answered `none` and **not forwarded**, so the monitor never sees the query that would poison it; an
accepted query is forwarded verbatim and its tweak appended to the replica. -/
def toMonitorOracles [DecidableEq Tweak] :
    QueryImpl (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl))
      (StateT (List Tweak × List Tweak) (Wrapped Qq Y thColl)) :=
  (QueryImpl.ofLift unifSpec (Wrapped Qq Y thColl)).liftTarget
      (StateT (List Tweak × List Tweak) (Wrapped Qq Y thColl)) +
    (toMonitorChallengeOracle tweakOfQuery numTargets thColl +
      toMonitorCollectionOracle thColl Qq)

/-! ## The coupling

Interpreting the wrapper's base oracles by the monitor's handler fuses the two into one handler over
the product state, at the rejection-on-arrival interface. Both handlers then speak the same oracle
spec, so the run-level agreement is a state projection gated by an invariant. -/

/-- Replica and monitor state, as carried by the fused handler. -/
abbrev JointState (Qh Tweak : Type) : Type :=
  (List Tweak × List Tweak) × SourceFinalValidity.State Qh Tweak

/-- The replica mirrors the monitor's two histories, and the monitor is unpoisoned. -/
def Coupled (tweakOfHist : Qh → Tweak) (s : JointState Qh Tweak) : Prop :=
  s.1.1 = s.2.challenges.map tweakOfHist ∧ s.1.2 = s.2.collectionTweaks ∧ s.2.valid = true

/-- The rejection-on-arrival state a joint state projects onto. -/
def project (s : JointState Qh Tweak) : List Qh × List Tweak :=
  (s.2.challenges, s.2.collectionTweaks)

/-- The wrapper and the monitor's oracles as a single handler over the joint state. -/
@[expose] def fused [DecidableEq Tweak] :
    QueryImpl (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl))
      (StateT (JointState Qh Tweak) ProbComp) :=
  ((monitorOracles tweakOfHist numTargets draw entry resp thColl pk).mapStateTBase
    (toMonitorOracles tweakOfQuery numTargets thColl)).flattenStateT

/-- One step of the fused handler: run the wrapper on the replica, then interpret the base oracles
it queried against the monitor. -/
theorem fused_run [DecidableEq Tweak]
    (t : (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl)).Domain)
    (s : JointState Qh Tweak) :
    (fused tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk t).run s =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (monitorOracles tweakOfHist numTargets draw entry resp thColl pk)
          ((toMonitorOracles tweakOfQuery numTargets thColl t).run s.1)).run s.2 :=
  rfl

/-- One step of the fused handler projects onto one step of the rejection-on-arrival handler.

`hcoh` is what makes the replica faithful: the wrapper appends `tweakOfQuery q` while the monitor
records `entry q v`, so the two agree only when a recorded entry carries its query's tweak. -/
theorem fused_project_step [DecidableEq Tweak]
    (hcoh : ∀ q v, tweakOfHist (entry q v) = tweakOfQuery q)
    (t : (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl)).Domain)
    (s : JointState Qh Tweak) (hs : Coupled tweakOfHist s) :
    Prod.map id project <$>
        (fused tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk t).run s =
      (roaOracles tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk t).run
        (project s) := by
  obtain ⟨⟨twsChal, twsColl⟩, ⟨qsChal, cs, valid⟩⟩ := s
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  cases t with
  | inl q =>
    rw [fused_run]
    simp [toMonitorOracles, monitorOracles, roaOracles, project, QueryImpl.ofLift_apply,
      Functor.map_map]
  | inr t =>
    cases t with
    | inl tm =>
      rw [fused_run]
      simp [toMonitorOracles, monitorOracles, roaOracles, project,
        toMonitorChallengeOracle, roaChallengeOracle, monitorChallengeOracle, Refuses,
        SourceFinalValidity.State.recordTarget, tweakFresh_map_iff,
        StateT.run_bind, Functor.map_map, hcoh]
      split <;> simp [Functor.map_map]
    | inr q =>
      rw [fused_run]
      simp [toMonitorOracles, monitorOracles, roaOracles, project,
        toMonitorCollectionOracle, TweakableHash.collectionOracle,
        SourceFinalValidity.collectionOracle,
        SourceFinalValidity.State.recordCollection, tweakReserved_map_iff,
        StateT.run_bind, Functor.map_map]
      split <;> simp

/-- One step of the fused handler stays coupled. The wrapper suppresses exactly the queries that
would poison the monitor, so the monitor's validity bit survives every reachable step. -/
theorem fused_preserves_coupled [DecidableEq Tweak]
    (hcoh : ∀ q v, tweakOfHist (entry q v) = tweakOfQuery q)
    (t : (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl)).Domain)
    (s : JointState Qh Tweak) (hs : Coupled tweakOfHist s) :
    ∀ z ∈ support ((fused tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk t).run s),
      Coupled tweakOfHist z.2 := by
  obtain ⟨⟨twsChal, twsColl⟩, ⟨qsChal, cs, valid⟩⟩ := s
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  cases t with
  | inl q =>
    rw [fused_run]
    simp [toMonitorOracles, monitorOracles, Coupled, QueryImpl.ofLift_apply, Functor.map_map]
  | inr t =>
    cases t with
    | inl tm =>
      rw [fused_run]
      by_cases hrej : numTargets ≤ qsChal.length ∨
          ¬ TweakFresh tweakOfHist qsChal twsColl (tweakOfQuery tm)
      · simp [toMonitorOracles, monitorOracles, toMonitorChallengeOracle, Refuses,
          tweakFresh_map_iff, Coupled, hrej]
      · rw [not_or, not_not, Nat.not_le] at hrej
        simp [toMonitorOracles, monitorOracles, toMonitorChallengeOracle,
          monitorChallengeOracle, Refuses,
          SourceFinalValidity.State.recordTarget, tweakFresh_map_iff, Coupled,
          Nat.not_le.mpr hrej.1, hrej.1, hrej.2, List.map_append, Functor.map_map, hcoh]
    | inr q =>
      rw [fused_run]
      by_cases hrej : TweakReserved tweakOfHist qsChal q.2.1 <;>
        simp [toMonitorOracles, monitorOracles, toMonitorCollectionOracle,
          SourceFinalValidity.collectionOracle,
          SourceFinalValidity.State.recordCollection, tweakReserved_map_iff, Coupled, hrej,
          Functor.map_map]

/-! ## The bridge -/

/-- Converting a whole selection phase leaves the experiment's output distribution unchanged.

The wrapper suppresses exactly the queries that would have poisoned the monitor, so the monitor is
valid on every reachable run. A game supplies its two winning conditions as `f` and `g`, together
with `hfg`: that they agree whenever the monitor is unpoisoned, at which point the monitor's two
histories *are* the rejection-on-arrival state. -/
theorem run_toMonitor_bind_eq [DecidableEq Tweak] {α β : Type}
    (hcoh : ∀ q v, tweakOfHist (entry q v) = tweakOfQuery q)
    (oa : OracleComp (unifSpec + (roaChallengeSpec Qq Y + TweakableHash.collectionSpec thColl)) α)
    (f : α → SourceFinalValidity.State Qh Tweak → ProbComp β)
    (g : α → List Qh × List Tweak → ProbComp β)
    (hfg : ∀ a (st : SourceFinalValidity.State Qh Tweak), st.valid = true →
      f a st = g a (st.challenges, st.collectionTweaks)) :
    ((simulateQ (monitorOracles tweakOfHist numTargets draw entry resp thColl pk)
        ((simulateQ (toMonitorOracles tweakOfQuery numTargets thColl) oa).run
          ([], []))).run .initial >>= fun z => f z.1.1 z.2) =
      ((simulateQ (roaOracles tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk)
        oa).run ([], []) >>= fun z => g z.1 z.2) := by
  have hinit : Coupled tweakOfHist ((([], []) : List Tweak × List Tweak),
      (SourceFinalValidity.State.initial : SourceFinalValidity.State Qh Tweak)) := by
    simp [Coupled, SourceFinalValidity.State.initial]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    show (([], []) : List Qh × List Tweak) =
      project ((([], []) : List Tweak × List Tweak),
        (SourceFinalValidity.State.initial : SourceFinalValidity.State Qh Tweak)) from rfl,
    ← map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (Coupled tweakOfHist) project
      (fused_preserves_coupled tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk hcoh)
      (fused_project_step tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk hcoh)
      oa _ hinit]
  simp only [fused, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  obtain ⟨-, -, hvalid⟩ := simulateQ_run_preserves_inv_of_query _ (Coupled tweakOfHist)
    (fused_preserves_coupled tweakOfQuery tweakOfHist numTargets draw entry resp thColl pk hcoh)
    oa _ hinit z hz
  simp only [project, Prod.map_fst, Prod.map_snd, id_eq]
  exact hfg z.1 z.2.2 hvalid

end ToFinalValidity

end TweakableHash
