/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Source-final-validity SM-DT-DSPR

SM-DT-DSPR asks an adversary to predict whether one of the targets it selected has a second
preimage. The public seed is sampled by the experiment and withheld while targets are selected,
then revealed for the prediction phase. The adversary may evaluate the other members of a
tweakable-hash collection while selecting targets. All oracle queries are answered and recorded;
the experiment loses if the final-validity monitor was poisoned by exceeding the cap, repeating a
target tweak, or using a target tweak on the collection oracle. This is the source game's
final-validity semantics. The fully qualified declarations live in
`TweakableHash.SM_DT_DSPR_SourceFinalValidity`, making their semantics explicit beside the
rejection-on-arrival and source-final-validity games provided by the imported foundation.

The security quantity is **not** raw prediction success. `SPExperiment` is the source
proof's `SPprob` baseline: it runs the same adversary, including its prediction phase and target
selection, but accepts exactly when the selected target has a second preimage, independently of
the guessed bit. `Advantage` is the truncated difference
`Pr[DSPR] - Pr[SPprob]`, i.e. `max 0 (Pr[DSPR] - Pr[SPprob])` in `ℝ≥0∞`.

The message space is finite because the winning predicate decides whether a second preimage exists.
This matches the finite input type in the EasyCrypt development.

## References

- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), and its EasyCrypt theory
  `TweakableHashFunctions.SMDTDSPR` in `proofs/TweakableHashFunctions.eca`.
- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346).
- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-! ## The second-preimage predicate -/

/-- `m` has a distinct second preimage under the fixed seed and tweak. -/
def SecondPreimageExists (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak)
    (m : M) : Prop :=
  ∃ m' : M, m ≠ m' ∧ th.eval pk t m = th.eval pk t m'

instance [Fintype M] [DecidableEq M] [DecidableEq Y]
    (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) (m : M) :
    Decidable (SecondPreimageExists th pk t m) :=
  inferInstanceAs (Decidable (∃ m' : M, m ≠ m' ∧ th.eval pk t m = th.eval pk t m'))

namespace SM_DT_DSPR_SourceFinalValidity

/-! ## The game -/

/-- A DSPR challenge selects a `(tweak, message)` target and always returns its image. -/
abbrev challengeSpec (Tweak M Y : Type) : OracleSpec (Tweak × M) :=
  (Tweak × M) →ₒ Y

/-- An SM-DT-DSPR problem: attacked hash, shared collection, and target cap. -/
structure Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose second-preimage structure is being predicted. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The rest of the collection, available during target selection at the same hidden seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The maximum number of challenge queries allowed by final validity. -/
  numTargets : ℕ

/-- The stand-alone DSPR problem, whose collection oracle is unqueryable. -/
def Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (numTargets : ℕ) :
    Problem Empty PkSeed Tweak M Y where
  th := th
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- Shared histories and final-validity poison bit for the DSPR game. -/
abbrev State (Tweak M : Type) : Type := SourceFinalValidity.State (Tweak × M) Tweak

/-- An SM-DT-DSPR adversary. The seed and challenge oracles are separated by the phase types. -/
structure Adversary (prob : Problem ι PkSeed Tweak M Y) where
  /-- Private state passed from target selection to prediction. -/
  State : Type
  /-- Select targets, with private randomness and collection access but without the public seed. -/
  choose : OracleComp
    (unifSpec +
      (challengeSpec Tweak M Y + SourceFinalValidity.collectionSpec prob.thColl)) State
  /-- After the seed is revealed, select a target index and predict second-preimage existence. -/
  guess : State → PkSeed → ProbComp (ℕ × Bool)

/-- The DSPR challenge oracle. Every query is answered and recorded. A cap or tweak-discipline
violation poisons the state instead of rejecting the query. -/
def challengeOracle [DecidableEq Tweak]
    (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (challengeSpec Tweak M Y)
      (StateT (State Tweak M) ProbComp) :=
  fun tm => do
    let st ← get
    set (st.recordTarget prob.numTargets Prod.fst tm)
    return prob.th.eval pk tm.1 tm.2

/-- Challenge and collection oracles over one state and one hidden public seed. -/
def oracles [DecidableEq Tweak] (prob : Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) :
    QueryImpl (unifSpec +
      (challengeSpec Tweak M Y + SourceFinalValidity.collectionSpec prob.thColl))
      (StateT (State Tweak M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State Tweak M) ProbComp) +
    (challengeOracle prob pk +
      SourceFinalValidity.collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk)

/-- The decisional experiment. The selected target must exist and the guess must equal its actual
second-preimage-existence bit. -/
noncomputable def Experiment [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, gameState) ←
    (simulateQ (oracles prob pk) adv.choose).run .initial
  let (j, b) ← adv.guess privateState pk
  match gameState.challenges[j]? with
  | none => return false
  | some (t, m) =>
      return gameState.valid && decide (SecondPreimageExists prob.th pk t m ↔ b = true)

/-- The source proof's `SPprob` baseline. It runs exactly the same adversary and uses the same
selected index, but ignores the guessed bit and accepts iff that target has a second preimage. -/
noncomputable def SPExperiment [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, gameState) ←
    (simulateQ (oracles prob pk) adv.choose).run .initial
  let (j, _) ← adv.guess privateState pk
  match gameState.challenges[j]? with
  | none => return false
  | some (t, m) =>
      return gameState.valid && decide (SecondPreimageExists prob.th pk t m)

/-- Raw DSPR prediction success probability. Kept separate from the security advantage so the
baseline subtraction cannot be accidentally omitted at a call site. -/
noncomputable def Success [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | Experiment adv]

/-- The `SPprob` baseline success probability. -/
noncomputable def SPProbability [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SPExperiment adv]

/-- SM-DT-DSPR advantage: the ENNReal truncated difference `Pr[DSPR] - Pr[SPprob]`. -/
noncomputable def Advantage [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ℝ≥0∞ :=
  Success adv - SPProbability adv

/-! ## Oracle behavior canaries -/

variable [DecidableEq Tweak] {prob : Problem ι PkSeed Tweak M Y} {pk : PkSeed}
  {t : Tweak} {m : M} {st : State Tweak M}

/-- Every challenge query is answered and recorded, even when it poisons final validity. -/
theorem challengeOracle_run :
    (challengeOracle prob pk (t, m)).run st =
      pure (prob.th.eval pk t m, st.recordTarget prob.numTargets Prod.fst (t, m)) := by
  simp [challengeOracle]

/-! ## Run-level final-validity correspondence -/

section Reachable

/-- The target summand answers every query and records it, so it maintains the monitor invariant at
the target-recording step. -/
theorem challengeOracle_preservesInv (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl.PreservesInv (challengeOracle prob pk)
      (SourceFinalValidity.Invariant prob.numTargets Prod.fst) :=
  fun (t, m) st hst z hz => by
    rw [challengeOracle_run, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ hst.recordTarget prob.numTargets Prod.fst st (t, m)

/-- Every summand of the target-selection oracle implementation maintains the monitor invariant:
private randomness leaves the state untouched, and the challenge and collection oracles record
through `SourceFinalValidity.State.recordTarget` and
`SourceFinalValidity.State.recordCollection`. -/
theorem oracles_preservesInv (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl.PreservesInv (oracles prob pk)
      (SourceFinalValidity.Invariant prob.numTargets Prod.fst) :=
  (SourceFinalValidity.preservesInv_privateRandomness _).add
    ((challengeOracle_preservesInv prob pk).add
      (SourceFinalValidity.preservesInv_collectionOracle _ _ _ _))

/-- The sticky bit decides the final predicate on every reachable state: the run-level form of the
monitor invariant, obtained from the initial state and the two recording steps. Both `Experiment`
and `SPExperiment` read `gameState.valid`, so this is what makes their shared guard mean
`SourceFinalValidity.Valid`. -/
theorem valid_eq_decide_valid_of_reachable {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) (pk : PkSeed) {z : adv.State × State Tweak M}
    (hz : z ∈ support ((simulateQ (oracles prob pk) adv.choose).run .initial)) :
    z.2.valid = decide (SourceFinalValidity.Valid prob.numTargets Prod.fst z.2) :=
  (OracleComp.simulateQ_run_preservesInv (oracles prob pk) _ (oracles_preservesInv prob pk)
    adv.choose .initial (SourceFinalValidity.invariant_initial _ _) z hz).eq_decide _ _ _

end Reachable

end SM_DT_DSPR_SourceFinalValidity

end TweakableHash
