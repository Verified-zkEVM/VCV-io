/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.Defs

/-!
# Asymmetric Encryption Schemes: One-Time IND-CPA

This file contains the standard two-phase one-time IND-CPA game together with the `ProbComp`
specialization used by the generic many-query lift.
-/

open OracleSpec OracleComp

universe v

namespace AsymmEncAlg

variable {m : Type → Type v} [Monad m] {M PK SK C : Type}

section IND_CPA_TwoPhase

variable {ι : Type} {spec : OracleSpec ι}

/-- Two-phase adversary for IND-CPA security. -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg m M PK SK C) where
  State : Type
  chooseMessages : PK → m (M × M × State)
  distinguish : State → C → m Bool

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_Adv encAlg)

/-- Fixed-branch one-time IND-CPA experiment for an asymmetric encryption algorithm. -/
def IND_CPA_OneTime_Exp (b : Bool) : ProbComp Bool :=
  encAlg.exec do
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂, state) ← adv.chooseMessages pk
    let c ← encAlg.encrypt pk (if b then m₁ else m₂)
    adv.distinguish state c

/-- One-time IND-CPA experiment for an asymmetric encryption algorithm:
sample keys, let the adversary choose challenge messages, encrypt one branch, and return whether
the adversary guessed the hidden bit. -/
def IND_CPA_OneTime_Game : ProbComp Bool :=
  encAlg.exec do
    let b : Bool ← encAlg.liftProbComp ($ᵗ Bool)
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂, state) ← adv.chooseMessages pk
    let msg := if b then m₁ else m₂
    let c ← encAlg.encrypt pk msg
    let b' ← adv.distinguish state c
    return (b == b')

/-- Absolute one-time IND-CPA bias advantage for the general two-phase game. -/
noncomputable def IND_CPA_OneTime_biasAdvantage
    (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ :=
  (IND_CPA_OneTime_Game (encAlg := encAlg) adv).boolBiasAdvantage

end IND_CPA_TwoPhase

section ProbCompSpecialization

variable {encAlg : AsymmEncAlg ProbComp M PK SK C}

/-- `ProbComp` specialization of the one-time IND-CPA game. -/
abbrev IND_CPA_OneTime_Game_ProbComp (adv : IND_CPA_Adv encAlg) : ProbComp Bool :=
  do
    let b ← ($ᵗ Bool : ProbComp Bool)
    let (pk, _sk) ← encAlg.keygen
    let (m₁, m₂, state) ← adv.chooseMessages pk
    let c ← encAlg.encrypt pk (if b then m₁ else m₂)
    let b' ← adv.distinguish state c
    pure (b == b')

/-- Real-valued signed one-time IND-CPA advantage. -/
noncomputable def IND_CPA_OneTime_signedAdvantageReal
    (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ :=
  (Pr[= true | IND_CPA_OneTime_Game_ProbComp (encAlg := encAlg) adv]).toReal - 1 / 2

end ProbCompSpecialization

end AsymmEncAlg
