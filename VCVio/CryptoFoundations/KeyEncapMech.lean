/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
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

end IND_CCA

end KEMScheme
