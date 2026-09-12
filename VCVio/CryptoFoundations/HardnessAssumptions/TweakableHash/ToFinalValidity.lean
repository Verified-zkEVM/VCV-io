/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
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
source-final-validity game with *the same* success probability. `SM_DT_TCR_*` and `SM_DT_PRE_*` are
covered; the same construction applies to any further pair of games sharing this shape.

Each game contributes `Problem.toSourceFinalValidity`, `Adversary.toSourceFinalValidity`, and the
three theorems `..._experiment_toSourceFinalValidity`, `..._advantage_toSourceFinalValidity` and
`..._advantage_le_toSourceFinalValidity`.

The construction itself lives in `TweakableHash.ToFinalValidity`, stated over a challenge oracle
given by what it draws, records and answers. A game appears here as a choice of that data together
with two `rfl` equations identifying its own oracles with the generic ones, so the wrapper, the
coupling invariant and the run-level agreement are shared rather than repeated per game. SM-TCR
draws nothing and records the queried pair; SM-PRE draws its message from the subspace and records
the queried tweak alongside it.

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

end TweakableHash
