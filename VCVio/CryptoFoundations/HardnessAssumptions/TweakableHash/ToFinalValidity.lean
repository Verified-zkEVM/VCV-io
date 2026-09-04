/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.ToFinalValidity.Core

/-!
# Converting rejection-on-arrival adversaries to source-final-validity adversaries

The rejection-on-arrival games and the source-final-validity games enforce the same tweak discipline
at different times: the first rejects a violating query as it arrives and leaves the state
untouched, the second answers every query and conjoins a sticky monitor into the winning condition.
The two families have distinct adversary types, so an adversary against one is not an adversary
against the other.

This file relates them in the direction a reduction needs, one conversion per game: an explicit map
sending an adversary against the rejection-on-arrival game to an adversary against the corresponding
source-final-validity game with *the same* success probability. `SM_DT_TCR_*`, `SM_DT_PRE_*`,
`SM_DT_UD_*` and `SM_DT_DSPR_*` are covered — every property this directory states in both
presentations. `SM_DT_RTCR_*` has no source-final-validity presentation and so needs no conversion.

Each game contributes `Problem.toSourceFinalValidity`, `Adversary.toSourceFinalValidity`, an
experiment equality per experiment it defines, and an advantage equality per advantage, each with a
`..._le_...` corollary.

The construction itself lives in `TweakableHash.ToFinalValidity`, stated over a challenge oracle
given by what it draws (`draw`), what it records (`entry`), what it answers (`resp`), and how the
tweak discipline reads a tweak off a query and off a recorded entry. A game appears here as a choice
of that data together with two equations identifying its own oracles with the generic ones, so the
wrapper, the coupling invariant and the run-level agreement are shared rather than repeated per
game:

|  | `V` | `draw q` | `entry q v` | `resp q v` |
|---|---|---|---|---|
| SM-DT-TCR | `Unit` | `pure ()` | `q` | `th.eval pk q.1 q.2` |
| SM-DT-PRE | `M'` | `$ᵗ M'` | `(q, v)` | `th.eval pk q (emb v)` |
| SM-DT-UD | `Y` | `response world prob pk q` | `q` | `v` |
| SM-DT-DSPR | `Unit` | `pure ()` | `q` | `th.eval pk q.1 q.2` |

The remaining parameters follow the recorded entry: `Qh` is `Tweak × M` for SM-TCR and SM-DSPR,
`Tweak × M'` for SM-PRE and `Tweak` for SM-UD, with `tweakOfHist` the matching projection, and `Qq`
is the query type of the game's own challenge spec. So SM-TCR draws nothing and records the queried
pair; SM-PRE draws its message from the subspace and records the queried tweak alongside it; SM-UD
answers with its own draw and records the tweak alone; and SM-DSPR sits at SM-TCR's row exactly, the
two games differing in their winning conditions rather than in their oracles.

The wrapper is a handler holding a replica of the two tweak histories. It evaluates the acceptance
test itself and, on a query its rejection-on-arrival counterpart would refuse, answers `none`
**without querying**. The suppressed query is exactly the one that would have poisoned the monitor,
so the monitor stays valid and the two runs couple exactly — hence an equality of advantages, with
the inequality as a corollary.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6 for the `VQS_t`
  presentation the source-final-validity games render.
-/

public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal ToFinalValidity

variable {ι PkSeed Tweak M M' Y : Type}

/-! ## SM-DT-TCR

The challenge oracle draws nothing, so the drawn-value type is `Unit`; a query is recorded verbatim
and answered with its own image. -/

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

section TCR

variable [DecidableEq Tweak] (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)

/-- The SM-TCR game is the generic rejection-on-arrival game at a challenge oracle that draws
nothing. -/
private theorem SM_DT_TCR_oracles_eq :
    SM_DT_TCR_oracles prob pk =
      roaOracles (Qq := Tweak × M) (Qh := Tweak × M) Prod.fst Prod.fst prob.numTargets
        (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
        (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk :=
  rfl

/-- Its monitor presentation is the generic one at the same data. -/
private theorem SM_DT_TCR_SourceFinalValidity_oracles_eq :
    SM_DT_TCR_SourceFinalValidity.oracles prob.toSourceFinalValidity pk =
      monitorOracles (Qq := Tweak × M) Prod.fst prob.numTargets
        (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
        (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk :=
  rfl

end TCR

/-- The converted adversary. Target selection runs against the wrapper over an initially empty
replica; the second phase is the original one, unchanged — its type is the same on both sides and
the public seed is sampled once from `prob.th.seedGen` in either experiment. -/
def SM_DT_TCR_Adversary.toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.Adversary prob.toSourceFinalValidity where
  State := adv.State × (List Tweak × List Tweak)
  choose := (simulateQ (toMonitorOracles (Qq := Tweak × M) Prod.fst prob.numTargets prob.thColl)
    adv.choose).run ([], [])
  forge state pk := adv.forge state.1 pk

/-- Converting a rejection-on-arrival adversary leaves the experiment's output distribution
unchanged: the wrapper suppresses exactly the queries that would have poisoned the monitor, so the
monitor is valid on every reachable run and the two winning conditions agree pointwise. -/
theorem SM_DT_TCR_experiment_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.Experiment adv.toSourceFinalValidity =
      SM_DT_TCR_Experiment adv := by
  simp only [SM_DT_TCR_SourceFinalValidity.Experiment, SM_DT_TCR_Experiment,
    SM_DT_TCR_Adversary.toSourceFinalValidity, SM_DT_TCR_oracles_eq,
    SM_DT_TCR_SourceFinalValidity_oracles_eq]
  refine bind_congr fun pk => ?_
  refine run_toMonitor_bind_eq (Qq := Tweak × M) Prod.fst Prod.fst prob.numTargets
    (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
    (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk (fun _ _ => rfl) adv.choose
    (fun st gameState => do
      let (j, m) ← adv.forge st pk
      match gameState.challenges[j]? with
      | none => return false
      | some (t, mj) =>
          return gameState.valid && decide (m ≠ mj ∧ prob.th.eval pk t m = prob.th.eval pk t mj))
    (fun st s => do
      let (j, m) ← adv.forge st pk
      match s.1[j]? with
      | none => return false
      | some (t, mj) => return decide (m ≠ mj ∧ prob.th.eval pk t m = prob.th.eval pk t mj))
    ?_
  intro a st hvalid
  simp [hvalid]

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

The same construction, at the game whose challenge oracle draws its own message: the drawn-value
type is the subspace `M'`, a query is a tweak alone, and the recorded entry pairs it with the draw.
The wrapper never learns the drawn message — it only ever sees the digest — which is why the replica
records tweaks alone; the projection reads the drawn messages back out of the monitor's own
history. -/

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

section PRE

variable [DecidableEq Tweak] [SampleableType M']
  (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)

/-- The SM-PRE game is the generic rejection-on-arrival game at a challenge oracle that draws from
the subspace. -/
private theorem SM_DT_PRE_oracles_eq :
    SM_DT_PRE_oracles prob pk =
      roaOracles (Qq := Tweak) (Qh := Tweak × M') id Prod.fst prob.numTargets
        (fun _ => ($ᵗ M' : ProbComp M')) (fun q v => (q, v))
        (fun q v => prob.th.eval pk q (prob.emb v)) prob.thColl pk :=
  rfl

/-- Its monitor presentation is the generic one at the same data. -/
private theorem SM_DT_PRE_SourceFinalValidity_oracles_eq :
    SM_DT_PRE_SourceFinalValidity.oracles prob.toSourceFinalValidity pk =
      monitorOracles (Qq := Tweak) Prod.fst prob.numTargets
        (fun _ => ($ᵗ M' : ProbComp M')) (fun q v => (q, v))
        (fun q v => prob.th.eval pk q (prob.emb v)) prob.thColl pk :=
  rfl

end PRE

/-- The converted adversary. -/
def SM_DT_PRE_Adversary.toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_SourceFinalValidity.Adversary prob.toSourceFinalValidity where
  State := adv.State × (List Tweak × List Tweak)
  choose := (simulateQ (toMonitorOracles (Qq := Tweak) id prob.numTargets prob.thColl)
    adv.choose).run ([], [])
  invert state pk := adv.invert state.1 pk

/-- The SM-PRE twin of `SM_DT_TCR_experiment_toSourceFinalValidity`. -/
theorem SM_DT_PRE_experiment_toSourceFinalValidity [DecidableEq Tweak] [DecidableEq Y]
    [SampleableType M'] {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_SourceFinalValidity.Experiment adv.toSourceFinalValidity =
      SM_DT_PRE_Experiment adv := by
  simp only [SM_DT_PRE_SourceFinalValidity.Experiment, SM_DT_PRE_Experiment,
    SM_DT_PRE_Adversary.toSourceFinalValidity, SM_DT_PRE_oracles_eq,
    SM_DT_PRE_SourceFinalValidity_oracles_eq]
  refine bind_congr fun pk => ?_
  refine run_toMonitor_bind_eq (Qq := Tweak) id Prod.fst prob.numTargets
    (fun _ => ($ᵗ M' : ProbComp M')) (fun q v => (q, v))
    (fun q v => prob.th.eval pk q (prob.emb v)) prob.thColl pk (fun _ _ => rfl) adv.choose
    (fun st gameState => do
      let (j, m) ← adv.invert st pk
      match gameState.challenges[j]? with
      | none => return false
      | some (t, x) =>
          return gameState.valid &&
            decide (prob.th.eval pk t (prob.emb m) = prob.th.eval pk t (prob.emb x)))
    (fun st s => do
      let (j, m) ← adv.invert st pk
      match s.1[j]? with
      | none => return false
      | some (t, x) =>
          return decide (prob.th.eval pk t (prob.emb m) = prob.th.eval pk t (prob.emb x)))
    ?_
  intro a st hvalid
  simp [hvalid]

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

/-! ## SM-DT-UD

The two-world game. Its challenge oracle answers with a sample of the queried world's response
distribution and records the queried tweak alone, so the drawn-value type is the output type `Y` and
the recorded entry is the query itself.

The world enters only through `draw`: `entry`, `resp` and both tweak projections are the same in
either world, and the wrapper does not see the world at all. So the conversion is world-independent
and one experiment equality, quantified over the world, serves both. The advantages follow from it,
which is what keeps the signed `SM_DT_UD_DirectedAdvantage`'s orientation: the two experiments are
equal as distributions, so the real and ideal success probabilities transfer separately and their
difference is not re-derived.

The two presentations declare their own two-element `World`, so the conversion carries a map between
them. -/

/-- The source-final-validity world corresponding to a rejection-on-arrival one. Exposed, so that a
consumer naming a world can see which one it converts to. -/
@[expose] def SM_DT_UD_World.toSourceFinalValidity :
    SM_DT_UD_World → SM_DT_UD_SourceFinalValidity.World
  | .real => .real
  | .ideal => .ideal

@[simp] theorem SM_DT_UD_World.toSourceFinalValidity_real :
    SM_DT_UD_World.real.toSourceFinalValidity = .real :=
  rfl

@[simp] theorem SM_DT_UD_World.toSourceFinalValidity_ideal :
    SM_DT_UD_World.ideal.toSourceFinalValidity = .ideal :=
  rfl

/-- The source-final-validity problem attacked by the converted adversary. Reducible for the same
reason as its SM-TCR counterpart. -/
@[reducible] def SM_DT_UD_Problem.toSourceFinalValidity
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) :
    SM_DT_UD_SourceFinalValidity.Problem ι PkSeed Tweak M M' Y where
  th := prob.th
  emb := prob.emb
  emb_injective := prob.emb_injective
  inputGen := prob.inputGen
  outputGen := prob.outputGen
  thColl := prob.thColl
  numTargets := prob.numTargets

section UD

variable [DecidableEq Tweak] (world : SM_DT_UD_World)
  (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)

/-- The SM-UD game is the generic rejection-on-arrival game at a challenge oracle that draws the
queried world's response and answers with it. -/
private theorem SM_DT_UD_oracles_eq :
    SM_DT_UD_oracles world prob pk =
      roaOracles (Qq := Tweak) (Qh := Tweak) id id prob.numTargets
        (SM_DT_UD_response world prob pk) (fun q _ => q) (fun _ v => v) prob.thColl pk :=
  rfl

/-- Its monitor presentation is the generic one at the same data, in the corresponding world. The
case split is on the world alone: each branch holds by `rfl`, and only the two presentations having
separate `World` types keeps the open term from reducing. -/
private theorem SM_DT_UD_SourceFinalValidity_oracles_eq :
    SM_DT_UD_SourceFinalValidity.oracles world.toSourceFinalValidity
        prob.toSourceFinalValidity pk =
      monitorOracles (Qq := Tweak) id prob.numTargets
        (SM_DT_UD_response world prob pk) (fun q _ => q) (fun _ v => v) prob.thColl pk := by
  cases world <;> rfl

end UD

/-- The converted adversary. The wrapper is built before the world is known, since the replica it
holds records tweaks and the acceptance test reads nothing else. -/
def SM_DT_UD_Adversary.toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_SourceFinalValidity.Adversary prob.toSourceFinalValidity where
  State := adv.State × (List Tweak × List Tweak)
  pick := (simulateQ (toMonitorOracles (Qq := Tweak) id prob.numTargets prob.thColl)
    adv.pick).run ([], [])
  distinguish state pk := adv.distinguish state.1 pk

/-- The SM-UD twin of `SM_DT_TCR_experiment_toSourceFinalValidity`, in either world. A refused
query draws nothing on the rejection-on-arrival side, and the wrapper suppresses exactly that query
rather than forwarding it, so neither run consumes randomness the other does not. -/
theorem SM_DT_UD_experiment_toSourceFinalValidity [DecidableEq Tweak]
    (world : SM_DT_UD_World) {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_SourceFinalValidity.Experiment world.toSourceFinalValidity
        adv.toSourceFinalValidity =
      SM_DT_UD_Experiment world adv := by
  simp only [SM_DT_UD_SourceFinalValidity.Experiment, SM_DT_UD_Experiment,
    SM_DT_UD_Adversary.toSourceFinalValidity, SM_DT_UD_oracles_eq,
    SM_DT_UD_SourceFinalValidity_oracles_eq]
  refine bind_congr fun pk => ?_
  refine run_toMonitor_bind_eq (Qq := Tweak) id id prob.numTargets
    (SM_DT_UD_response world prob pk) (fun q _ => q) (fun _ v => v) prob.thColl pk
    (fun _ _ => rfl) adv.pick
    (fun st gameState => do
      let b ← adv.distinguish st pk
      return gameState.valid && b)
    (fun st _ => adv.distinguish st pk)
    ?_
  intro a st hvalid
  simp [hvalid]

/-- The real world's success probability is preserved. -/
theorem SM_DT_UD_realSuccess_toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_RealSuccess adv =
      SM_DT_UD_SourceFinalValidity.RealSuccess adv.toSourceFinalValidity := by
  rw [SM_DT_UD_RealSuccess, SM_DT_UD_SourceFinalValidity.RealSuccess,
    ← SM_DT_UD_experiment_toSourceFinalValidity .real adv,
    SM_DT_UD_World.toSourceFinalValidity_real]

/-- The ideal world's success probability is preserved. -/
theorem SM_DT_UD_idealSuccess_toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_IdealSuccess adv =
      SM_DT_UD_SourceFinalValidity.IdealSuccess adv.toSourceFinalValidity := by
  rw [SM_DT_UD_IdealSuccess, SM_DT_UD_SourceFinalValidity.IdealSuccess,
    ← SM_DT_UD_experiment_toSourceFinalValidity .ideal adv,
    SM_DT_UD_World.toSourceFinalValidity_ideal]

/-- The conversion preserves the signed gap, orientation included: the two worlds are converted by
the same map, so neither side of the difference moves. -/
theorem SM_DT_UD_directedAdvantage_toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_DirectedAdvantage adv =
      SM_DT_UD_SourceFinalValidity.DirectedAdvantage adv.toSourceFinalValidity := by
  rw [SM_DT_UD_DirectedAdvantage, SM_DT_UD_SourceFinalValidity.DirectedAdvantage,
    SM_DT_UD_realSuccess_toSourceFinalValidity, SM_DT_UD_idealSuccess_toSourceFinalValidity]

/-- The conversion preserves the orientation-independent magnitude. -/
theorem SM_DT_UD_absoluteAdvantage_toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_AbsoluteAdvantage adv =
      SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage adv.toSourceFinalValidity := by
  rw [SM_DT_UD_AbsoluteAdvantage, SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage,
    SM_DT_UD_realSuccess_toSourceFinalValidity, SM_DT_UD_idealSuccess_toSourceFinalValidity]

/-- A rejection-on-arrival SM-UD bound follows from any source-final-validity bound on the signed
gap. -/
theorem SM_DT_UD_directedAdvantage_le_toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_DirectedAdvantage adv ≤
      SM_DT_UD_SourceFinalValidity.DirectedAdvantage adv.toSourceFinalValidity :=
  le_of_eq (SM_DT_UD_directedAdvantage_toSourceFinalValidity adv)

/-- The same, for the magnitude. -/
theorem SM_DT_UD_absoluteAdvantage_le_toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_AbsoluteAdvantage adv ≤
      SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage adv.toSourceFinalValidity :=
  le_of_eq (SM_DT_UD_absoluteAdvantage_toSourceFinalValidity adv)

/-! ## SM-DT-DSPR

The challenge oracle is SM-TCR's, so the data is SM-TCR's row unchanged; the two games differ only
in what they do with the selected target afterwards. That difference costs a second experiment
rather than a second instantiation: the advantage is a truncated difference against the `SPprob`
baseline, and both experiments run the same adversary against the same oracles, so each needs its
own equality before the advantage follows. -/

/-- The source-final-validity problem attacked by the converted adversary. Reducible for the same
reason as its SM-TCR counterpart. -/
@[reducible] def SM_DT_DSPR_Problem.toSourceFinalValidity
    (prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y) :
    SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := prob.numTargets

section DSPR

variable [DecidableEq Tweak] (prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)

/-- The SM-DSPR game is the generic rejection-on-arrival game at a challenge oracle that draws
nothing. -/
private theorem SM_DT_DSPR_oracles_eq :
    SM_DT_DSPR_oracles prob pk =
      roaOracles (Qq := Tweak × M) (Qh := Tweak × M) Prod.fst Prod.fst prob.numTargets
        (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
        (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk :=
  rfl

/-- Its monitor presentation is the generic one at the same data. -/
private theorem SM_DT_DSPR_SourceFinalValidity_oracles_eq :
    SM_DT_DSPR_SourceFinalValidity.oracles prob.toSourceFinalValidity pk =
      monitorOracles (Qq := Tweak × M) Prod.fst prob.numTargets
        (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
        (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk :=
  rfl

end DSPR

/-- The converted adversary. -/
def SM_DT_DSPR_Adversary.toSourceFinalValidity [DecidableEq Tweak]
    {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.Adversary prob.toSourceFinalValidity where
  State := adv.State × (List Tweak × List Tweak)
  choose := (simulateQ (toMonitorOracles (Qq := Tweak × M) Prod.fst prob.numTargets prob.thColl)
    adv.choose).run ([], [])
  guess state pk := adv.guess state.1 pk

/-- The SM-DSPR twin of `SM_DT_TCR_experiment_toSourceFinalValidity`, on the prediction
experiment. -/
theorem SM_DT_DSPR_experiment_toSourceFinalValidity [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.Experiment adv.toSourceFinalValidity =
      SM_DT_DSPR_Experiment adv := by
  simp only [SM_DT_DSPR_SourceFinalValidity.Experiment, SM_DT_DSPR_Experiment,
    SM_DT_DSPR_Adversary.toSourceFinalValidity, SM_DT_DSPR_oracles_eq,
    SM_DT_DSPR_SourceFinalValidity_oracles_eq]
  refine bind_congr fun pk => ?_
  refine run_toMonitor_bind_eq (Qq := Tweak × M) Prod.fst Prod.fst prob.numTargets
    (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
    (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk (fun _ _ => rfl) adv.choose
    (fun st gameState => do
      let (j, b) ← adv.guess st pk
      match gameState.challenges[j]? with
      | none => return false
      | some (t, m) =>
          return gameState.valid && decide (SecondPreimageExists prob.th pk t m ↔ b = true))
    (fun st s => do
      let (j, b) ← adv.guess st pk
      match s.1[j]? with
      | none => return false
      | some (t, m) => return decide (SecondPreimageExists prob.th pk t m ↔ b = true))
    ?_
  intro a st hvalid
  simp [hvalid]

/-- The same, on the `SPprob` baseline: the adversary and the oracles are the same, so the
conversion preserves the baseline as well as the prediction. -/
theorem SM_DT_DSPR_spExperiment_toSourceFinalValidity [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.SPExperiment adv.toSourceFinalValidity =
      SM_DT_DSPR_SPExperiment adv := by
  simp only [SM_DT_DSPR_SourceFinalValidity.SPExperiment, SM_DT_DSPR_SPExperiment,
    SM_DT_DSPR_Adversary.toSourceFinalValidity, SM_DT_DSPR_oracles_eq,
    SM_DT_DSPR_SourceFinalValidity_oracles_eq]
  refine bind_congr fun pk => ?_
  refine run_toMonitor_bind_eq (Qq := Tweak × M) Prod.fst Prod.fst prob.numTargets
    (fun _ => (pure () : ProbComp Unit)) (fun q _ => q)
    (fun q _ => prob.th.eval pk q.1 q.2) prob.thColl pk (fun _ _ => rfl) adv.choose
    (fun st gameState => do
      let (j, _) ← adv.guess st pk
      match gameState.challenges[j]? with
      | none => return false
      | some (t, m) => return gameState.valid && decide (SecondPreimageExists prob.th pk t m))
    (fun st s => do
      let (j, _) ← adv.guess st pk
      match s.1[j]? with
      | none => return false
      | some (t, m) => return decide (SecondPreimageExists prob.th pk t m))
    ?_
  intro a st hvalid
  simp [hvalid]

/-- The raw prediction success probability is preserved. -/
theorem SM_DT_DSPR_success_toSourceFinalValidity [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_Success adv =
      SM_DT_DSPR_SourceFinalValidity.Success adv.toSourceFinalValidity := by
  rw [SM_DT_DSPR_Success, SM_DT_DSPR_SourceFinalValidity.Success,
    SM_DT_DSPR_experiment_toSourceFinalValidity]

/-- The `SPprob` baseline is preserved. -/
theorem SM_DT_DSPR_spProbability_toSourceFinalValidity [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_SPProbability adv =
      SM_DT_DSPR_SourceFinalValidity.SPProbability adv.toSourceFinalValidity := by
  rw [SM_DT_DSPR_SPProbability, SM_DT_DSPR_SourceFinalValidity.SPProbability,
    SM_DT_DSPR_spExperiment_toSourceFinalValidity]

/-- The SM-DSPR conversion is advantage-preserving. Both terms of the truncated difference are
preserved, so the subtraction needs no separate argument. -/
theorem SM_DT_DSPR_advantage_toSourceFinalValidity [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_Advantage adv =
      SM_DT_DSPR_SourceFinalValidity.Advantage adv.toSourceFinalValidity := by
  rw [SM_DT_DSPR_Advantage, SM_DT_DSPR_SourceFinalValidity.Advantage,
    SM_DT_DSPR_success_toSourceFinalValidity, SM_DT_DSPR_spProbability_toSourceFinalValidity]

/-- A rejection-on-arrival SM-DSPR bound follows from any source-final-validity bound. -/
theorem SM_DT_DSPR_advantage_le_toSourceFinalValidity [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) :
    SM_DT_DSPR_Advantage adv ≤
      SM_DT_DSPR_SourceFinalValidity.Advantage adv.toSourceFinalValidity :=
  le_of_eq (SM_DT_DSPR_advantage_toSourceFinalValidity adv)

end TweakableHash
