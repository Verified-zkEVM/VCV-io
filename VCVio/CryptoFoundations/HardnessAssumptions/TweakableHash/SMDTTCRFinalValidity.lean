/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers, Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# Source-final-validity SM-DT-TCR

This module defines the single-function, distinct-tweak, multi-target target-collision-resistance
experiment with the source final-predicate semantics used by the EasyCrypt/BDHMS development.
Every challenge and collection query is answered and recorded. The target cap, distinct target
tweaks, and target/collection disjointness are checked by a sticky final-validity monitor and enter
the final winning condition.

`TweakableHash.SM_DT_TCR_Experiment` is the live rejection-on-arrival experiment. The declarations
in `TweakableHash.SM_DT_TCR_SourceFinalValidity` name a distinct adaptive game and do not alter that
experiment's oracle result types or winning condition, with a proved bridge between the two views:
`TweakableHash.SM_DT_TCR_advantage_toSourceFinalValidity` converts an adversary against that
experiment into one against this game at the same advantage.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6.
-/

@[expose] public section

namespace TweakableHash.SM_DT_TCR_SourceFinalValidity

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-- A source-final-validity SM-DT-TCR problem: the attacked tweakable hash, the collection of other
members available to the adversary, and the final cap on challenge queries. -/
structure Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose target-collision resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The maximum number of challenge queries allowed by final validity. -/
  numTargets : ℕ

/-- The stand-alone source-final-validity problem at the empty collection. -/
def Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (numTargets : ℕ) :
    Problem Empty PkSeed Tweak M Y where
  th := th
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- Every `(tweak, message)` challenge query returns its image. -/
abbrev challengeSpec (Tweak M Y : Type) : OracleSpec (Tweak × M) :=
  (Tweak × M) →ₒ Y

/-- Challenge/collection histories and sticky source-final-validity bit. -/
abbrev State (Tweak M : Type) : Type := SourceFinalValidity.State (Tweak × M) Tweak

/-- An adversary for source-final-validity SM-DT-TCR. The seed is unavailable to `choose`; `forge`
receives it after both first-phase oracles have been removed. -/
structure Adversary (prob : Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Select targets with private randomness and collection access, without the public seed. -/
  choose : OracleComp
    (unifSpec + (challengeSpec Tweak M Y + SourceFinalValidity.collectionSpec prob.thColl)) State
  /-- Given the revealed public seed, name a target index and a colliding message. -/
  forge : State → PkSeed → ProbComp (ℕ × M)

/-- The always-answering target oracle. Every query is appended in issue order; a cap, duplicate
target tweak, or collection clash poisons final validity without changing the returned digest. -/
def challengeOracle [DecidableEq Tweak] (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (challengeSpec Tweak M Y) (StateT (State Tweak M) ProbComp) :=
  fun tm => do
    let st ← get
    set (st.recordTarget prob.numTargets Prod.fst tm)
    return prob.th.eval pk tm.1 tm.2

/-- The source-final-validity challenge and collection oracles over their shared monitor. -/
def oracles [DecidableEq Tweak] (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl
      (unifSpec + (challengeSpec Tweak M Y + SourceFinalValidity.collectionSpec prob.thColl))
      (StateT (State Tweak M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State Tweak M) ProbComp) +
    (challengeOracle prob pk +
      SourceFinalValidity.collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk)

/-- The source-final-validity SM-DT-TCR experiment. A forgery wins exactly when final validity
holds and it names a recorded target with a distinct colliding message. -/
noncomputable def Experiment [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, gameState) ← (simulateQ (oracles prob pk) adv.choose).run .initial
  let (j, m) ← adv.forge privateState pk
  match gameState.challenges[j]? with
  | none => return false
  | some (t, mj) =>
      return gameState.valid && decide (m ≠ mj ∧ prob.th.eval pk t m = prob.th.eval pk t mj)

/-- The source-final-validity SM-DT-TCR advantage. -/
noncomputable def Advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | Experiment adv]

variable [DecidableEq Tweak] {prob : Problem ι PkSeed Tweak M Y} {pk : PkSeed}
  {t : Tweak} {m : M} {st : State Tweak M}

/-- Every target query is answered and recorded, including a query that poisons final validity. -/
theorem challengeOracle_run :
    (challengeOracle prob pk (t, m)).run st =
      pure (prob.th.eval pk t m, st.recordTarget prob.numTargets Prod.fst (t, m)) := by
  simp [challengeOracle]

end TweakableHash.SM_DT_TCR_SourceFinalValidity
