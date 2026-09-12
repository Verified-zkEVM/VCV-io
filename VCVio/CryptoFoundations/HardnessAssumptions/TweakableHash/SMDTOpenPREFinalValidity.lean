/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Source-final-validity SM-DT-OpenPRE

In SM-DT-OpenPRE the adversary commits to a list of target tweaks before seeing the public seed or
any target image. The challenger keeps only the first `numTargets` tweaks, samples one input for
each, and gives their images to the adversary. After the seed is revealed, the adversary may open
target inputs, but wins only by inverting a target it did not open.

For the collection game, collection queries are available only during `pick`. They are answered at
the hidden seed and recorded. The final-validity monitor checks distinct target tweaks and
target/collection disjointness. Taking the bounded prefix is source semantics: a longer committed
list is truncated, not rejected and not used to poison the game.

The declarations live in `TweakableHash.SM_DT_OpenPRE_SourceFinalValidity`. This explicit namespace
keeps this source-final-predicate game distinct from the rejection-on-arrival assumptions already
present in the repository.

The phase types enforce the information boundary. `pick` has no seed, images, or opening oracle;
`find` receives the seed and images and has only private randomness and the opening oracle.

## Reference

- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), and the exact executable game in
  `TweakableHashFunctions.SMDTOpenPRE` / `Collection.SMDTOpenPREC` of the accompanying EasyCrypt
  development.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

namespace SM_DT_OpenPRE_SourceFinalValidity

/-! ## The game -/

/-- The opening oracle takes a target index and returns its sampled input. -/
abbrev openSpec (M : Type) : OracleSpec ℕ := ℕ →ₒ M

/-- An SM-DT-OpenPRE problem: attacked hash, shared collection, and target cap. -/
structure Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose open-preimage resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- Distribution used to sample the hidden input of each retained target. Keeping this explicit,
  rather than fixing uniform sampling, matches the source game's abstract proper distribution and
  permits reductions to instantiate the exact distribution they embed. -/
  inputGen : ProbComp M
  /-- The rest of the collection, available while the adversary commits to target tweaks. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The number of committed tweaks retained as targets. -/
  numTargets : ℕ

/-- The property on `inputGen` required by the source DSPR/TCR quantitative reduction: every input
is sampled uniformly with full support. Keeping it separate from the game permits a more general
OpenPRE definition while making the reduction's additional hypothesis explicit. -/
def Problem.HasUniformInputs [SampleableType M]
    (prob : Problem ι PkSeed Tweak M Y) : Prop :=
  prob.inputGen = $ᵗ M

/-- The stand-alone OpenPRE problem, whose collection oracle is unqueryable. -/
def Problem.standalone (th : TweakableHash PkSeed Tweak M Y)
    (inputGen : ProbComp M) (numTargets : ℕ) :
    Problem Empty PkSeed Tweak M Y where
  th := th
  inputGen := inputGen
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- Target inputs, collection tweaks, and sticky final-validity bit. -/
abbrev State (Tweak M : Type) : Type := SourceFinalValidity.State (Tweak × M) Tweak

/-- An SM-DT-OpenPRE adversary, split at the seed-revelation boundary. -/
structure Adversary (prob : Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from target commitment to inversion. -/
  State : Type
  /-- Commit to target tweaks, with private randomness and collection access at the hidden seed. -/
  pick : OracleComp
    (unifSpec + SourceFinalValidity.collectionSpec prob.thColl) (State × List Tweak)
  /-- After the seed and target images are revealed, open targets adaptively and return a proposed
  unopened target index and preimage. -/
  find : State → PkSeed → List Y →
    OracleComp (unifSpec + openSpec M) (ℕ × M)

/-- Private randomness and collection access for the commitment phase. -/
def pickOracles [DecidableEq Tweak]
    (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (unifSpec + SourceFinalValidity.collectionSpec prob.thColl)
      (StateT (State Tweak M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (State Tweak M) ProbComp) +
    SourceFinalValidity.collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk

/-- Sample and record targets for precisely the supplied list. The experiment calls this on the
bounded prefix of the committed tweak list. -/
def initializeTargets [DecidableEq Tweak]
    (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    List Tweak → StateT (State Tweak M) ProbComp (List Y)
  | [] => pure []
  | t :: ts => do
      let x ← (prob.inputGen : StateT (State Tweak M) ProbComp M)
      let st ← get
      set (st.recordTarget prob.numTargets Prod.fst (t, x))
      let ys ← initializeTargets prob pk ts
      return prob.th.eval pk t x :: ys

/-- The opening oracle records every requested index. An out-of-range request returns the type's
fixed witness, as does EasyCrypt's `nth witness`; it cannot itself win because the final selected
index must refer to a recorded target. -/
def openOracle [Inhabited M] (targets : List (Tweak × M)) :
    QueryImpl (openSpec M) (StateT (List ℕ) ProbComp) :=
  fun j => do
    let opened ← get
    set (opened ++ [j])
    return (targets[j]?.map Prod.snd).getD default

/-- Private randomness and adaptive target opening for the inversion phase. -/
def findOracles [Inhabited M] (targets : List (Tweak × M)) :
    QueryImpl (unifSpec + openSpec M) (StateT (List ℕ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List ℕ) ProbComp) +
    openOracle targets

/-- The exact final-validity SM-DT-OpenPRE experiment. The committed tweak list is truncated before
target sampling. The selected index must exist, must never have been opened, and must name a valid
preimage of the corresponding recorded image. -/
noncomputable def Experiment [DecidableEq Tweak] [DecidableEq Y] [Inhabited M]
    {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let ((privateState, tweaks), afterPick) ←
    (simulateQ (pickOracles prob pk) adv.pick).run .initial
  let (ys, gameState) ←
    (initializeTargets prob pk (tweaks.take prob.numTargets)).run afterPick
  let ((j, m), opened) ←
    (simulateQ (findOracles gameState.challenges)
      (adv.find privateState pk ys)).run []
  match gameState.challenges[j]? with
  | none => return false
  | some (t, x) =>
      return gameState.valid && decide (j ∉ opened) &&
        decide (prob.th.eval pk t m = prob.th.eval pk t x)

/-- The SM-DT-OpenPRE success probability. -/
noncomputable def Advantage [DecidableEq Tweak] [DecidableEq Y] [Inhabited M]
    {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | Experiment adv]

/-! ## Run-level final-validity correspondence -/

section Reachable

variable [DecidableEq Tweak]

/-- Both summands of the commitment-phase oracle implementation maintain the monitor invariant:
private randomness leaves the state untouched, and the collection oracle records through
`SourceFinalValidity.State.recordCollection`. -/
theorem pickOracles_preservesInv (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl.PreservesInv (pickOracles prob pk)
      (SourceFinalValidity.Invariant prob.numTargets Prod.fst) :=
  (SourceFinalValidity.preservesInv_privateRandomness _).add
    (SourceFinalValidity.preservesInv_collectionOracle _ _ _ _)

/-- Target sampling maintains the monitor invariant: every retained tweak is recorded through
`SourceFinalValidity.State.recordTarget`, so a duplicate or collection-clashing tweak in the
committed list poisons the monitor exactly as an adversarial target query would. -/
theorem initializeTargets_preservesInv (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (ts : List Tweak) :
    StateT.PreservesInv (initializeTargets prob pk ts)
      (SourceFinalValidity.Invariant prob.numTargets Prod.fst) := by
  induction ts with
  | nil => exact StateT.preservesInv_pure _ _
  | cons t ts ih =>
      refine StateT.preservesInv_bind _ _ _ (StateT.preservesInv_monadLift _ _) fun x => ?_
      refine StateT.preservesInv_get_bind _ fun st hst => ?_
      refine StateT.preservesInv_bind _ _ _
        (StateT.preservesInv_set_of _ (hst.recordTarget prob.numTargets Prod.fst st (t, x)))
        fun _ => StateT.preservesInv_bind _ _ _ ih fun _ => StateT.preservesInv_pure _ _

/-- The sticky bit decides the final predicate on every state reachable through both monitor
phases: the commitment phase's collection queries followed by target sampling on the retained
prefix. The inversion phase carries its own opening state and never reaches the monitor, so this is
exactly the state whose `valid` field `Experiment` reads. -/
theorem valid_eq_decide_valid_of_reachable {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) (pk : PkSeed)
    {w : (adv.State × List Tweak) × State Tweak M}
    (hw : w ∈ support ((simulateQ (pickOracles prob pk) adv.pick).run .initial))
    {z : List Y × State Tweak M}
    (hz : z ∈ support ((initializeTargets prob pk (w.1.2.take prob.numTargets)).run w.2)) :
    z.2.valid = decide (SourceFinalValidity.Valid prob.numTargets Prod.fst z.2) :=
  (initializeTargets_preservesInv prob pk _ w.2
    (OracleComp.simulateQ_run_preservesInv (pickOracles prob pk) _
      (pickOracles_preservesInv prob pk) adv.pick .initial
      (SourceFinalValidity.invariant_initial _ _) w hw) z hz).eq_decide _ _ _

end Reachable

/-! ## Oracle behavior pins -/

variable [Inhabited M] {targets : List (Tweak × M)} {j : ℕ} {opened : List ℕ}

/-- Opening always records the requested index, including an out-of-range one. -/
theorem openOracle_run :
    (openOracle targets j).run opened =
      pure ((targets[j]?.map Prod.snd).getD default, opened ++ [j]) := by
  simp [openOracle]

end SM_DT_OpenPRE_SourceFinalValidity

end TweakableHash
