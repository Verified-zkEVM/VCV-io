/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Data Encapsulation Mechanisms

This file defines monadic Data Encapsulation Mechanisms (DEMs), together with their basic
correctness and IND-CPA security games.
-/

open OracleSpec OracleComp ENNReal

universe u v

/-- A data encapsulation mechanism with key space `K`, message space `M`, and ciphertext
space `C`. -/
structure DEMScheme (m : Type → Type u) (K M C : Type)
    extends ExecutionMethod m where
  keygen : m K
  encrypt : K → M → m C
  decrypt : K → C → m (Option M)

namespace DEMScheme

variable {m : Type → Type v} {K M C : Type}
  (dem : DEMScheme m K M C)

section Correct

variable [DecidableEq M] [Monad m]

/-- Correctness experiment: decrypting an honestly generated ciphertext should recover the
original message. -/
def CorrectExp (msg : M) : m Bool := do
  let k ← dem.keygen
  let c ← dem.encrypt k msg
  let msg' ← dem.decrypt k c
  return decide (msg' = some msg)

/-- Perfect correctness of a DEM. -/
def PerfectlyCorrect [HasEvalSPMF m] : Prop :=
  ∀ msg, Pr[= true | dem.exec (dem.CorrectExp msg)] = 1

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι}

/-- Two-phase IND-CPA adversary for a DEM. The adversary first chooses two challenge messages,
then distinguishes which one was encrypted. -/
structure IND_CPA_Adversary (dem : DEMScheme (OracleComp spec) K M C) where
  State : Type
  chooseMessages : OracleComp spec (M × M × State)
  distinguish : State → C → OracleComp spec Bool

/-- IND-CPA real-or-random experiment for a DEM. -/
def IND_CPA_Game {dem : DEMScheme (OracleComp spec) K M C}
    (adversary : dem.IND_CPA_Adversary) : ProbComp Bool :=
  dem.exec do
    let b ← dem.lift_probComp ($ᵗ Bool)
    let k ← dem.keygen
    let (m₀, m₁, st) ← adversary.chooseMessages
    let c ← dem.encrypt k (if b then m₀ else m₁)
    let b' ← adversary.distinguish st c
    return (b == b')

/-- IND-CPA distinguishing advantage for a DEM. -/
noncomputable def IND_CPA_Advantage {dem : DEMScheme (OracleComp spec) K M C}
    (adversary : dem.IND_CPA_Adversary) : ℝ :=
  (IND_CPA_Game adversary).boolBiasAdvantage

/-- The IND-CPA advantage is definitionally the bias of the IND-CPA game. -/
theorem IND_CPA_Advantage_eq_game_bias {dem : DEMScheme (OracleComp spec) K M C}
    (adversary : dem.IND_CPA_Adversary) :
    dem.IND_CPA_Advantage adversary = (dem.IND_CPA_Game adversary).boolBiasAdvantage := by
  rfl

end IND_CPA

end DEMScheme
