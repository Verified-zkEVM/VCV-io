/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Key Encapsulation Mechanisms

This file defines a type to represent protocols for key encapsulation mechanisms.
We also define basic correctness and security properties for these protocols.
-/


open OracleSpec OracleComp ENNReal

universe u v

/-- A key encapsulation mechanism with shared-key space `K`, public/secret key spaces `PK` and
`SK`, and ciphertext space `C`. -/
structure KEMScheme (m : Type → Type u) [Monad m] (K PK SK C : Type) where
  keygen : m (PK × SK)
  encaps : PK → m (C × K)
  decaps : SK → C → m (Option K)

namespace KEMScheme
variable {m : Type → Type v} [Monad m] {K PK SK C : Type}
  (kem : KEMScheme m K PK SK C)

section Correct

variable [DecidableEq K]

/-- Correctness experiment: decapsulation of an honestly generated encapsulation should recover the
shared key. -/
def CorrectExp (kem : KEMScheme m K PK SK C) : m Bool :=
  do
    let (pk, sk) ← kem.keygen
    let (c, k) ← kem.encaps pk
    let k' ← kem.decaps sk c
    return decide (k' = some k)

/-- Perfect correctness of a KEM. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  Pr[= true | runtime.evalDist kem.CorrectExp] = 1

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- Two-phase IND-CPA adversary for a KEM. The adversary only gets access to the base oracle
set `spec`, with no decapsulation oracle. -/
structure IND_CPA_Adversary (_kem : KEMScheme (OracleComp spec) K PK SK C) where
  State : Type
  preChallenge : PK → OracleComp spec State
  postChallenge : State → C → K → OracleComp spec Bool

/-- Fixed-branch IND-CPA experiment for a KEM, matching the source proof-ladders formulation
`Exp.run(b)`. -/
def IND_CPA_Exp {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) (b : Bool) : SPMF Bool :=
  runtime.evalDist do
    let (pk, _sk) ← kem.keygen
    let st ← adversary.preChallenge pk
    let (cStar, kReal) ← kem.encaps pk
    let kRand ← runtime.liftProbComp ($ᵗ K)
    adversary.postChallenge st cStar (if b then kReal else kRand)

/-- Single-game IND-CPA experiment obtained by sampling the challenge bit uniformly and checking
whether the adversary guessed it correctly. -/
def IND_CPA_Game {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) : SPMF Bool :=
  runtime.evalDist do
    let (pk, _sk) ← kem.keygen
    let st ← adversary.preChallenge pk
    let b ← runtime.liftProbComp ($ᵗ Bool)
    let (cStar, kReal) ← kem.encaps pk
    let kRand ← runtime.liftProbComp ($ᵗ K)
    let b' ← adversary.postChallenge st cStar (if b then kReal else kRand)
    return (b == b')

/-- IND-CPA distinguishing advantage for a KEM, defined canonically as the bias of the single
game. -/
noncomputable def IND_CPA_Advantage {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) : ℝ :=
  (IND_CPA_Game runtime adversary).boolBiasAdvantage

/-- The canonical IND-CPA advantage is definitionally the bias of the single game. -/
theorem IND_CPA_Advantage_eq_game_bias {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Advantage runtime adversary =
      (kem.IND_CPA_Game runtime adversary).boolBiasAdvantage := by
  rfl

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
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CCA_Adversary) : SPMF Bool :=
  runtime.evalDist do
    let (pk, sk) ← kem.keygen
    let st ← simulateQ (kem.IND_CCA_preChallengeImpl sk) (adversary.preChallenge pk)
    let b ← runtime.liftProbComp ($ᵗ Bool)
    let (cStar, kReal) ← kem.encaps pk
    let kRand ← runtime.liftProbComp ($ᵗ K)
    let b' ← simulateQ (kem.IND_CCA_postChallengeImpl sk cStar)
      (adversary.postChallenge st cStar (if b then kReal else kRand))
    return (b == b')

/-- IND-CCA distinguishing advantage for a KEM. -/
noncomputable def IND_CCA_Advantage {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CCA_Adversary) : ℝ :=
  (IND_CCA_Game runtime adversary).boolBiasAdvantage

/-- Any IND-CPA adversary can be viewed as an IND-CCA adversary that simply ignores the
decapsulation oracle while preserving its ordinary pre-challenge interaction with the base
oracle set `spec`. -/
def IND_CPA_Adversary.toIND_CCA {kem : KEMScheme (OracleComp spec) K PK SK C}
    (adversary : kem.IND_CPA_Adversary) : kem.IND_CCA_Adversary where
  State := adversary.State
  preChallenge pk := simulateQ
    (show QueryImpl spec (OracleComp (spec + (C →ₒ Option K))) from
      fun t => liftM (query (spec := spec) t))
    (adversary.preChallenge pk)
  postChallenge st cStar kStar := simulateQ
    (show QueryImpl spec (OracleComp (spec + (C →ₒ Option K))) from
      fun t => liftM (query (spec := spec) t))
    (adversary.postChallenge st cStar kStar)

/-- The one-stage IND-CPA game is exactly the IND-CCA game instantiated with the trivial
CPA-to-CCA embedding (`toIND_CCA`) that never uses the decryption oracle. -/
theorem IND_CPA_Game_eq_IND_CCA_Game_toIND_CCA
    {kem : KEMScheme (OracleComp spec) K PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Game runtime adversary = kem.IND_CCA_Game runtime adversary.toIND_CCA := by
  simp only [IND_CPA_Game, IND_CCA_Game, IND_CPA_Adversary.toIND_CCA,
    IND_CCA_preChallengeImpl, IND_CCA_postChallengeImpl]
  congr 1
  simp only [← QueryImpl.simulateQ_compose]
  have h : ∀ (impl₂ : QueryImpl (C →ₒ Option K) (OracleComp spec)),
      (QueryImpl.ofLift spec (OracleComp spec) + impl₂) ∘ₛ
        (fun t => liftM (query (spec := spec) t) :
          QueryImpl spec (OracleComp (spec + (C →ₒ Option K)))) =
      QueryImpl.id' spec := by
    intro impl₂
    ext t
    simp only [QueryImpl.compose, QueryImpl.id']
    change simulateQ (QueryImpl.id' spec + impl₂)
      (liftM (liftM (OracleQuery.query (spec := spec) t) :
        OracleQuery (spec + (C →ₒ Option K)) _)) = _
    simp [simulateQ_query]
  simp only [h, simulateQ_id']

end IND_CCA

end KEMScheme
