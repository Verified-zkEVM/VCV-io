/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Key Encapsulation Mechanisms

This file defines a type to represent protocols for key encapsulation mechanisms.
We also define basic correctness and security properties for these protocols.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

universe u v

/-- A key encapsulation mechanism with shared-key space `K`, public/secret key spaces `PK` and
`SK`, and ciphertext space `C`. -/
structure KEMScheme (m : Type → Type u) (K PK SK C : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  encaps : PK → m (C × K)
  decaps : SK → C → m (Option K)

namespace KEMScheme

variable {m : Type → Type v} {K PK SK C : Type}
  (kem : KEMScheme m K PK SK C)

section Correct

variable [DecidableEq K] [Monad m]

/-- Correctness experiment: decapsulation of an honestly generated encapsulation should recover the
shared key. -/
def CorrectExp : m Bool := do
  let (pk, sk) ← kem.keygen
  let (c, k) ← kem.encaps pk
  let k' ← kem.decaps sk c
  return decide (k' = some k)

/-- Perfect correctness of a KEM. -/
def PerfectlyCorrect [HasEvalSPMF m] : Prop :=
  Pr[= true | kem.exec kem.CorrectExp] = 1

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- A KEM IND-CPA adversary receives the public key, challenge ciphertext, and either the real or
random shared key, then outputs a Boolean guess. The argument order follows the upstream
proof-ladders KEM game: `(pk, k, c)`. -/
abbrev IND_CPA_Adversary (_kem : KEMScheme (OracleComp spec) K PK SK C) :=
  PK → K → C → OracleComp spec Bool

/-- Fixed-branch IND-CPA experiment for a KEM, matching the source proof-ladders formulation
`Exp.run(b)`. -/
def IND_CPA_Exp {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) (b : Bool) : ProbComp Bool :=
  kem.exec do
    let (pk, _sk) ← kem.keygen
    let (cStar, kReal) ← kem.encaps pk
    let kRand ← kem.lift_probComp ($ᵗ K)
    adversary pk (if b then kReal else kRand) cStar

/-- Single-game IND-CPA experiment obtained by sampling the challenge bit uniformly and checking
whether the adversary guessed it correctly. -/
def IND_CPA_Game {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let b' ← kem.IND_CPA_Exp adversary b
  return (b == b')

/-- IND-CPA distinguishing advantage for a KEM in the fixed-branch source formulation. -/
noncomputable def IND_CPA_Advantage {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) : ℝ :=
  (IND_CPA_Exp adversary true).boolDistAdvantage (IND_CPA_Exp adversary false)

/-- The fixed-branch source formulation and the single-game win/lose formulation induce the same
IND-CPA distinguishing advantage. -/
theorem IND_CPA_Advantage_eq_game_bias {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Advantage adversary = (kem.IND_CPA_Game adversary).boolBiasAdvantage := by
  sorry

end IND_CPA

section IND_CCA

variable {ι : Type} {spec : OracleSpec ι} [DecidableEq C] [SampleableType K]

/-- IND-CCA adversaries get access to the base oracle set `spec` plus a decapsulation oracle. -/
def IND_CCA_oracleSpec (_kem : KEMScheme (OracleComp spec) K PK SK C) :=
  spec + (C →ₒ Option K)

/-- Two-phase IND-CCA adversary for a KEM. -/
structure IND_CCA_Adversary (kem : KEMScheme (OracleComp spec) K PK SK C) where
  State : Type
  preChallenge : PK → OracleComp kem.IND_CCA_oracleSpec State
  postChallenge : State → C → K → OracleComp kem.IND_CCA_oracleSpec Bool

/-- Pre-challenge decapsulation oracle. -/
def IND_CCA_preChallengeImpl (kem : KEMScheme (OracleComp spec) K PK SK C)
    (sk : SK) : QueryImpl (IND_CCA_oracleSpec kem) (OracleComp spec) :=
  (QueryImpl.ofLift spec (OracleComp spec)) + fun c => kem.decaps sk c

/-- Post-challenge decapsulation oracle: the challenge ciphertext itself maps to `none`. -/
def IND_CCA_postChallengeImpl (kem : KEMScheme (OracleComp spec) K PK SK C)
    (sk : SK) (cStar : C) : QueryImpl (IND_CCA_oracleSpec kem) (OracleComp spec) :=
  (QueryImpl.ofLift spec (OracleComp spec)) + fun c =>
    if c = cStar then return none else kem.decaps sk c

/-- IND-CCA real-or-random experiment for a KEM. -/
def IND_CCA_Game {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CCA_Adversary) : ProbComp Bool :=
  kem.exec do
    let (pk, sk) ← kem.keygen
    let st ← simulateQ (kem.IND_CCA_preChallengeImpl sk) (adversary.preChallenge pk)
    let b ← kem.lift_probComp ($ᵗ Bool)
    let (cStar, kReal) ← kem.encaps pk
    let kRand ← kem.lift_probComp ($ᵗ K)
    let b' ← simulateQ (kem.IND_CCA_postChallengeImpl sk cStar)
      (adversary.postChallenge st cStar (if b then kReal else kRand))
    return (b == b')

/-- IND-CCA distinguishing advantage for a KEM. -/
noncomputable def IND_CCA_Advantage {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CCA_Adversary) : ℝ :=
  (IND_CCA_Game adversary).boolBiasAdvantage

/-- Any IND-CPA adversary can be viewed as an IND-CCA adversary that simply ignores the
decryption oracle and performs no pre-challenge interaction. -/
def IND_CPA_Adversary.toIND_CCA {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) : kem.IND_CCA_Adversary where
  State := PK
  preChallenge pk := pure pk
  postChallenge pk cStar kStar :=
    (liftM (adversary pk kStar cStar) : OracleComp (spec + (C →ₒ Option K)) Bool)

/-- The one-stage IND-CPA game is exactly the IND-CCA game instantiated with the trivial
CPA-to-CCA embedding that never uses the decryption oracle. -/
theorem IND_CPA_Game_eq_IND_CCA_Game_toIND_CCA
    {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Game adversary = kem.IND_CCA_Game adversary.toIND_CCA := by
  sorry

end IND_CCA

end KEMScheme
