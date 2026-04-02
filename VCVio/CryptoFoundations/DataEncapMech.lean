/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.ProbComp

/-!
# Data Encapsulation Mechanisms

This file defines data encapsulation mechanisms (DEMs), their correctness notion, and the
one-time IND-CPA game used by the KEM+DEM composition theorem.
-/

universe u v

open OracleSpec OracleComp ENNReal

/-- A data encapsulation mechanism with key space `K`, message space `M`, and ciphertext space
`C`. The key is supplied externally, matching the proof-ladders DEM model. -/
structure DEMScheme (m : Type → Type u) [Monad m] (K M C : Type) where
  encrypt : K → M → m C
  decrypt : K → C → m M

namespace DEMScheme
variable {m : Type → Type v} [Monad m] {K M C : Type}
  (dem : DEMScheme m K M C)

section Correct

variable [DecidableEq M]

/-- Correctness experiment for a DEM under an externally supplied key. -/
def CorrectExp (dem : DEMScheme m K M C) (k : K) (msg : M) : m Bool :=
  do
    let c ← dem.encrypt k msg
    let msg' ← dem.decrypt k c
    return decide (msg' = msg)

/-- Perfect correctness for a DEM: every externally supplied key decrypts honest ciphertexts
correctly with probability `1`. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  ∀ k : K, ∀ msg : M, Pr[= true | runtime.evalDist (dem.CorrectExp k msg)] = 1

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- Two-phase one-time IND-CPA adversary for a DEM. The key is hidden, so the message-selection
phase receives no public input. -/
structure IND_CPA_Adversary (_dem : DEMScheme (OracleComp spec) K M C) where
  State : Type
  chooseMessages : OracleComp spec (M × M × State)
  distinguish : State → C → OracleComp spec Bool

/-- Fixed-branch one-time IND-CPA experiment for a DEM, matching the source proof-ladders
`DEM_1CPA_Exp.run(b)` presentation. -/
def IND_CPA_Exp {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_Adversary) (b : Bool) : SPMF Bool :=
  runtime.evalDist do
    let k ← runtime.liftProbComp ($ᵗ K)
    let (m₀, m₁, st) ← adversary.chooseMessages
    let c ← dem.encrypt k (if b then m₁ else m₀)
    adversary.distinguish st c

/-- Game-form one-time IND-CPA experiment for a DEM. -/
def IND_CPA_Game {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_Adversary) : SPMF Bool :=
  runtime.evalDist do
    let b ← runtime.liftProbComp ($ᵗ Bool)
    let k ← runtime.liftProbComp ($ᵗ K)
    let (m₀, m₁, st) ← adversary.chooseMessages
    let c ← dem.encrypt k (if b then m₁ else m₀)
    let b' ← adversary.distinguish st c
    return (b == b')

/-- One-time IND-CPA advantage for a DEM, defined canonically as the bias of the single game. -/
noncomputable def IND_CPA_Advantage {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_Adversary) : ℝ :=
  (IND_CPA_Game runtime adversary).boolBiasAdvantage

/-- The canonical one-time IND-CPA advantage is definitionally the bias of the single game. -/
theorem IND_CPA_Advantage_eq_game_bias {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_Adversary) :
    dem.IND_CPA_Advantage runtime adversary =
      (dem.IND_CPA_Game runtime adversary).boolBiasAdvantage := by
  rfl

end IND_CPA

end DEMScheme
