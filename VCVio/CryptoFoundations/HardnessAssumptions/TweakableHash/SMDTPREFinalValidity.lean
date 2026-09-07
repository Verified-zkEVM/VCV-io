/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers, Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE

/-!
# Source-final-validity SM-DT-PRE

This module defines the single-function, distinct-tweak, multi-target preimage-resistance
experiment with source final-predicate semantics. The challenge oracle samples a message from the
declared subspace for every query, returns the corresponding image, and records the target. The
target cap and tweak-separation conditions enter the final winning condition through the shared
sticky monitor.

`TweakableHash.SM_DT_PRE_Experiment` is the live rejection-on-arrival experiment. The declarations
in `TweakableHash.SM_DT_PRE_SourceFinalValidity` name a distinct adaptive game and leave that
experiment unchanged, with a proved bridge between the two views:
`TweakableHash.SM_DT_PRE_advantage_toSourceFinalValidity` converts an adversary against that
experiment into one against this game at the same advantage.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 3 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 7, Fig. 10, and Fig. 11.
-/

@[expose] public section

namespace TweakableHash.SM_DT_PRE_SourceFinalValidity

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M M' Y : Type}

/-- A source-final-validity SM-DT-PRE problem: the attacked tweakable hash, the sampled subspace,
the collection of other members, and the final cap on challenge queries. -/
structure Problem (ι PkSeed Tweak M M' Y : Type) where
  /-- The tweakable hash whose preimage resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The map into `M` of the subspace sampled by the challenge oracle. -/
  emb : M' → M
  /-- `emb` identifies `M'` with a subset of `M`. -/
  emb_injective : Function.Injective emb
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The maximum number of challenge queries allowed by final validity. -/
  numTargets : ℕ

/-- The stand-alone source-final-validity problem at the empty collection. -/
def Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (emb : M' → M)
    (emb_injective : Function.Injective emb) (numTargets : ℕ) :
    Problem Empty PkSeed Tweak M M' Y where
  th := th
  emb := emb
  emb_injective := emb_injective
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- A source-final-validity challenge query is a tweak; the response is the sampled message's
image, never an optional rejection. -/
abbrev challengeSpec (Tweak Y : Type) : OracleSpec Tweak := Tweak →ₒ Y

/-- Challenge/collection histories and sticky source-final-validity bit. -/
abbrev State (Tweak M' : Type) : Type := SourceFinalValidity.State (Tweak × M') Tweak

/-- An adversary for source-final-validity SM-DT-PRE. The seed is unavailable to `choose`; `invert`
receives it after both first-phase oracles have been removed. -/
structure Adversary (prob : Problem ι PkSeed Tweak M M' Y) where
  /-- Private state carried from `choose` to `invert`. -/
  State : Type
  /-- Select tweaks with private randomness and collection access, without the public seed. -/
  choose : OracleComp
    (unifSpec + (challengeSpec Tweak Y + SourceFinalValidity.collectionSpec prob.thColl)) State
  /-- Given the revealed public seed, name a target index and a preimage in `M'`. -/
  invert : State → PkSeed → ProbComp (ℕ × M')

/-- The always-answering target oracle. Every query samples a message and records the target; a
cap, duplicate target tweak, or collection clash poisons final validity without suppressing the
sample or digest. -/
noncomputable def challengeOracle [DecidableEq Tweak] [SampleableType M']
    (prob : Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (challengeSpec Tweak Y) (StateT (State Tweak M') ProbComp) :=
  fun t => do
    let x ← (($ᵗ M' : ProbComp M') : StateT (State Tweak M') ProbComp M')
    let st ← get
    set (st.recordTarget prob.numTargets Prod.fst (t, x))
    return prob.th.eval pk t (prob.emb x)

/-- The source-final-validity challenge and collection oracles over their shared monitor. -/
noncomputable def oracles [DecidableEq Tweak] [SampleableType M']
    (prob : Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl
      (unifSpec + (challengeSpec Tweak Y + SourceFinalValidity.collectionSpec prob.thColl))
      (StateT (State Tweak M') ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State Tweak M') ProbComp) +
    (challengeOracle prob pk +
      SourceFinalValidity.collectionOracle (Q := Tweak × M') Prod.fst prob.thColl pk)

/-- The source-final-validity SM-DT-PRE experiment. An inversion wins exactly when final validity
holds and it names a recorded target with an agreeing preimage from `M'`. -/
noncomputable def Experiment [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {prob : Problem ι PkSeed Tweak M M' Y} (adv : Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, gameState) ← (simulateQ (oracles prob pk) adv.choose).run .initial
  let (j, m) ← adv.invert privateState pk
  match gameState.challenges[j]? with
  | none => return false
  | some (t, x) =>
      return gameState.valid &&
        decide (prob.th.eval pk t (prob.emb m) = prob.th.eval pk t (prob.emb x))

/-- The source-final-validity SM-DT-PRE advantage. -/
noncomputable def Advantage [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {prob : Problem ι PkSeed Tweak M M' Y} (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | Experiment adv]

variable [DecidableEq Tweak] [SampleableType M']
  {prob : Problem ι PkSeed Tweak M M' Y} {pk : PkSeed} {t : Tweak} {st : State Tweak M'}

/-- Every query samples, answers, and records, including a query that poisons final validity. -/
theorem challengeOracle_run :
    (challengeOracle prob pk t).run st =
      (fun x => (prob.th.eval pk t (prob.emb x),
        st.recordTarget prob.numTargets Prod.fst (t, x))) <$> ($ᵗ M') := by
  simp [challengeOracle, Functor.map_map]

end TweakableHash.SM_DT_PRE_SourceFinalValidity
