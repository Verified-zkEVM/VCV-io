/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Fujisaki-Okamoto Shared Definitions

This file defines the shared objects used by the Fujisaki-Okamoto transform:

- deterministic PKE with explicit coins
- its randomized wrapper into `AsymmEncAlg`
- correctness and spread notions
- OW-CPA and OW-PCVA games
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

universe u v

/-- Public-key encryption with explicit coins. This is the natural source object for the
Fujisaki-Okamoto T transform. -/
structure DeterministicPKE (M PK SK R C : Type) where
  keygen : ProbComp (PK × SK)
  encrypt : PK → M → R → C
  decrypt : SK → C → Option M

namespace DeterministicPKE

variable {M PK SK R C : Type}
  (pke : DeterministicPKE M PK SK R C)

/-- Wrap a deterministic explicit-coin PKE as a randomized `AsymmEncAlg` by sampling the coins
uniformly. -/
def toRandomized [SampleableType R] : AsymmEncAlg ProbComp M PK SK C where
  keygen := pke.keygen
  encrypt := fun pk msg => do
    let r ← $ᵗ R
    return pke.encrypt pk msg r
  decrypt := fun sk c => return (pke.decrypt sk c)
  __ := ExecutionMethod.default

section Correct

variable [DecidableEq M] [SampleableType R]

/-- Correctness experiment for the deterministic scheme after sampling explicit coins. -/
def CorrectExp (msg : M) : ProbComp Bool := do
  let (pk, sk) ← pke.keygen
  let r ← $ᵗ R
  let c := pke.encrypt pk msg r
  return decide (pke.decrypt sk c = some msg)

/-- Perfect correctness of a deterministic PKE. -/
def PerfectlyCorrect : Prop :=
  ∀ msg : M, Pr[= true | pke.CorrectExp msg] = 1

/-- `delta`-correctness: correctness failure on any message occurs with probability at most
`delta`. -/
def deltaCorrect (delta : ℝ≥0∞) : Prop :=
  ∀ msg : M, Pr[= false | pke.CorrectExp msg] ≤ delta

end Correct

/-- `gamma`-spread: no ciphertext occurs with probability more than `gamma` for any fixed public
key and plaintext. -/
def gammaSpread [SampleableType R] [DecidableEq C] (gamma : ℝ≥0∞) : Prop :=
  ∀ pk msg c,
    Pr[= c | (do
      let r ← $ᵗ R
      return pke.encrypt pk msg r : ProbComp C)] ≤ gamma

section OW_CPA

variable [SampleableType M] [SampleableType R] [DecidableEq M]

/-- Oracle interface for OW-CPA adversaries: unrestricted uniform sampling plus an encryption
oracle on chosen plaintexts. -/
def OW_CPA_oracleSpec (_pke : DeterministicPKE M PK SK R C) :=
  unifSpec + (M →ₒ C)

/-- An OW-CPA adversary gets `pk`, a challenge ciphertext, and oracle access to chosen-plaintext
encryptions. -/
abbrev OW_CPA_Adversary := PK → C → OracleComp pke.OW_CPA_oracleSpec M

/-- Implementation of the OW-CPA encryption oracle. -/
def OW_CPA_queryImpl (pk : PK) : QueryImpl pke.OW_CPA_oracleSpec ProbComp :=
  let encAlg := pke.toRandomized
  (QueryImpl.ofLift unifSpec ProbComp) + fun msg => encAlg.encrypt pk msg

/-- OW-CPA experiment: sample a random message, encrypt it, and ask the adversary to recover it
given access to a chosen-plaintext encryption oracle. -/
def OW_CPA_Game (adversary : pke.OW_CPA_Adversary) : ProbComp Bool := do
  let (pk, _sk) ← pke.keygen
  let msg ← $ᵗ M
  let r ← $ᵗ R
  let c := pke.encrypt pk msg r
  let msg' ← simulateQ (pke.OW_CPA_queryImpl pk) (adversary pk c)
  return decide (msg' = msg)

/-- OW-CPA advantage is the probability of recovering the sampled challenge plaintext. -/
noncomputable def OW_CPA_Advantage (adversary : pke.OW_CPA_Adversary) : ℝ≥0∞ :=
  Pr[= true | pke.OW_CPA_Game adversary]

end OW_CPA

end DeterministicPKE

/-- Executing a lifted `ProbComp` in a public random-oracle world ignores the oracle state and
collapses back to the original probabilistic computation. -/
theorem exec_lift_probComp_withHashOracle
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α : Type} (c : ProbComp α) :
    StateT.run' (simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
      (monadLift c)) s = c := by
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)
  change StateT.run' (simulateQ (idImpl + hashImpl) (monadLift c)) s = c
  rw [show simulateQ (idImpl + hashImpl) (monadLift c) = simulateQ idImpl c by
    simpa [MonadLift.monadLift] using
      (QueryImpl.simulateQ_add_liftComp_left (impl₁' := idImpl) (impl₂' := hashImpl) c)]
  have hid : ∀ t s', (idImpl t).run' s' = query t := by
    intro t s'
    rfl
  simpa using
    (StateT_run'_simulateQ_eq_self (so := idImpl) (h := hid) (oa := c) (s := s))

section OW_PCVA

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK C : Type}

/-- OW-PCVA oracle interface: the base oracle set, a plaintext-checking oracle on arbitrary
ciphertexts, and a ciphertext-validity oracle. -/
def OW_PCVA_oracleSpec (_encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
  spec + (((C × M) →ₒ Bool) + (C →ₒ Bool))

/-- An OW-PCVA adversary gets the public key and challenge ciphertext, and outputs a plaintext
guess after querying the plaintext-checking and validity oracles. -/
abbrev OW_PCVA_Adversary (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
  PK → C → OracleComp (OW_PCVA_oracleSpec encAlg) M

/-- Oracle implementation for OW-PCVA. -/
def OW_PCVA_queryImpl (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    [DecidableEq M] (sk : SK) :
    QueryImpl (OW_PCVA_oracleSpec encAlg) (OracleComp spec) :=
  let checkImpl : QueryImpl ((C × M) →ₒ Bool) (OracleComp spec) := fun (c, msg) => do
    let msg' ← encAlg.decrypt sk c
    return decide (msg' = some msg)
  let validImpl : QueryImpl (C →ₒ Bool) (OracleComp spec) := fun c => do
    let msg' ← encAlg.decrypt sk c
    return msg'.isSome
  (QueryImpl.ofLift spec (OracleComp spec)) + (checkImpl + validImpl)

/-- OW-PCVA experiment: challenge the adversary with an honestly generated ciphertext and ask it to
recover the underlying message using plaintext-checking and validity oracles. -/
def OW_PCVA_Game {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    [SampleableType M] [DecidableEq M]
    (adversary : OW_PCVA_Adversary encAlg) : ProbComp Bool :=
  encAlg.exec do
    let (pk, sk) ← encAlg.keygen
    let msg ← encAlg.lift_probComp ($ᵗ M)
    let cStar ← encAlg.encrypt pk msg
    let msg' ← simulateQ (OW_PCVA_queryImpl encAlg sk) (adversary pk cStar)
    return decide (msg' = msg)

/-- OW-PCVA advantage is the message-recovery probability in the above game. -/
noncomputable def OW_PCVA_Advantage {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    [SampleableType M] [DecidableEq M]
    (adversary : OW_PCVA_Adversary encAlg) : ℝ≥0∞ :=
  Pr[= true | OW_PCVA_Game adversary]

end OW_PCVA
