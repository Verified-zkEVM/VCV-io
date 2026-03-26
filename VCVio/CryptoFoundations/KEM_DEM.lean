/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA
import VCVio.CryptoFoundations.KeyDecapMech
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# KEM + DEM Composition

This file defines the textbook KEM+DEM public-key encryption construction and the proof-ladders A1
reduction skeleton against the repo's existing KEM and one-time IND-CPA interfaces.
-/

set_option autoImplicit false

universe u v

open OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {m : Type → Type v} {K PK SK CKEM M CDEM : Type}

/-- Textbook KEM+DEM composition. The composed scheme inherits the KEM execution method. -/
def composeWithDEM [Monad m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM) :
    AsymmEncAlg m M PK SK (CKEM × CDEM) where
  keygen := kem.keygen
  encrypt := fun pk msg => do
    let (c₁, k) ← kem.encaps pk
    let c₂ ← dem.encrypt k msg
    return (c₁, c₂)
  decrypt := fun sk c => do
    let k? ← kem.decaps sk c.1
    match k? with
    | none => return none
    | some k => return some (← dem.decrypt k c.2)
  __ := kem.toExecutionMethod

section Correct

variable [DecidableEq K] [DecidableEq M] [Monad m] [HasEvalSPMF m]

/-- Perfect correctness for the KEM+DEM composition follows from perfect correctness of both
components, provided they are interpreted under the same execution method. -/
theorem PerfectlyCorrect.composeWithDEM
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM)
    (hkem : kem.PerfectlyCorrect)
    (hdem : (dem.withExecutionMethod kem.toExecutionMethod).PerfectlyCorrect) :
    (kem.composeWithDEM dem).PerfectlyCorrect := by
  sorry

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- Left KEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. -/
def composeWithDEM_toKEMLeftReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    kem.IND_CPA_Adversary := fun pk k kc => do
      let (m₀, _m₁, st) ← adversary.chooseMessages pk
      let dc ← dem.encrypt k m₀
      adversary.distinguish st (kc, dc)

/-- Right KEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. -/
def composeWithDEM_toKEMRightReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    kem.IND_CPA_Adversary := fun pk k kc => do
      let (_m₀, m₁, st) ← adversary.chooseMessages pk
      let dc ← dem.encrypt k m₁
      adversary.distinguish st (kc, dc)

/-- DEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. It samples
the public key internally during the message-selection phase, mirroring the proof-ladders
`B_s(E_kem, A)` construction. -/
def composeWithDEM_toDEMReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    dem.IND_CPA_Adversary where
  State := PK × adversary.State
  chooseMessages := do
    let (pk, _sk) ← kem.keygen
    let (m₀, m₁, st) ← adversary.chooseMessages pk
    return (m₀, m₁, (pk, st))
  distinguish st dc := do
    let (kc, _k) ← kem.encaps st.1
    adversary.distinguish st.2 (kc, dc)

/-- Proof-ladders A1 reduction statement: the one-time IND-CPA advantage of textbook KEM+DEM is
bounded by two KEM IND-CPA advantages plus one DEM IND-CPA advantage, using the canonical
left/right and DEM reductions defined above. -/
theorem IND_CPA_OneTime_biasAdvantage_composeWithDEM_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM dem)) :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM dem) adversary ≤
      kem.IND_CPA_Advantage (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
      kem.IND_CPA_Advantage (kem.composeWithDEM_toKEMRightReduction dem adversary) +
      (dem.withExecutionMethod kem.toExecutionMethod).IND_CPA_Advantage
        (kem.composeWithDEM_toDEMReduction
          (dem.withExecutionMethod kem.toExecutionMethod) adversary) := by
  sorry

end IND_CPA

end KEMScheme
