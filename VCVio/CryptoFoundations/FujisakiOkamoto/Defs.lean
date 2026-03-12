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

- explicit-coins PKEs as a specialization of `AsymmEncAlg`
- the induced randomized `AsymmEncAlg`
- spread notions and OW-CPA games for the `ProbComp` specialization
- OW-PCVA games for the general monadic interface
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

universe u v

namespace AsymmEncAlg.ExplicitCoins

variable {M PK SK R C : Type}
  (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)

section Correct

variable [DecidableEq M] [SampleableType R]

/-- `delta`-correctness: failure in the canonical `AsymmEncAlg.CorrectExp` experiment occurs with
probability at most `delta`. -/
def deltaCorrect (delta : ℝ≥0∞) : Prop :=
  ∀ msg : M, Pr[= false | pke.toAsymmEncAlg.CorrectExp msg] ≤ delta

end Correct

/-- `gamma`-spread: no ciphertext occurs with probability more than `gamma` for any fixed public
key and plaintext. -/
def gammaSpread [SampleableType R] [DecidableEq C] (gamma : ℝ≥0∞) : Prop :=
  ∀ pk msg c, Pr[= c | pke.toAsymmEncAlg.encrypt pk msg] ≤ gamma

section OW_CPA

variable [SampleableType M] [SampleableType R] [DecidableEq M]

/-- Oracle interface for the one-way under chosen-plaintext attack (OW-CPA) game.

The sum `unifSpec + (M →ₒ C)` gives the adversary two capabilities:
- unrestricted uniform sampling from any sampleable type
- an encryption oracle on chosen plaintexts `M → C`
-/
def OW_CPA_oracleSpec (_pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) :=
  unifSpec + (M →ₒ C)

/-- An OW-CPA adversary gets `pk`, a challenge ciphertext, and oracle access to chosen-plaintext
encryptions. -/
abbrev OW_CPA_Adversary := PK → C → OracleComp pke.OW_CPA_oracleSpec M

/-- Implementation of the OW-CPA encryption oracle. -/
def OW_CPA_queryImpl (pk : PK) : QueryImpl pke.OW_CPA_oracleSpec ProbComp :=
  let encAlg := pke.toAsymmEncAlg
  (QueryImpl.ofLift unifSpec ProbComp) + fun msg => encAlg.encrypt pk msg

/-- Main one-way under chosen-plaintext attack (OW-CPA) experiment.

The game samples a fresh keypair and a uniform challenge message, forms the honest challenge
ciphertext via the induced randomized `AsymmEncAlg`, runs the adversary with oracle access
described by `OW_CPA_oracleSpec`, and returns `true` exactly when the adversary recovers the
challenge message. -/
def OW_CPA_Game (adversary : pke.OW_CPA_Adversary) : ProbComp Bool := do
  let encAlg := pke.toAsymmEncAlg
  let (pk, _sk) ← encAlg.keygen
  let msg ← $ᵗ M
  let c ← encAlg.encrypt pk msg
  let msg' ← simulateQ (pke.OW_CPA_queryImpl pk) (adversary pk c)
  return decide (msg' = msg)

/-- OW-CPA advantage is the probability of recovering the sampled challenge plaintext. -/
noncomputable def OW_CPA_Advantage (adversary : pke.OW_CPA_Adversary) : ℝ≥0∞ :=
  Pr[= true | pke.OW_CPA_Game adversary]

end OW_CPA

end AsymmEncAlg.ExplicitCoins

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

/-- Oracle interface for the one-way under plaintext-checking and validity attacks
(OW-PCVA) game.

The sum `spec + (((C × M) →ₒ Bool) + (C →ₒ Bool))` has three components:
- the ambient oracle interface `spec`
- a plaintext-checking oracle sending `(c, msg)` to whether `c` decrypts to `msg`
- a validity oracle sending `c` to whether `c` decrypts to some plaintext at all
-/
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

/-- Main one-way under plaintext-checking and validity attacks (OW-PCVA) experiment.

The game generates a keypair, samples a uniform challenge message, encrypts it honestly, and
then runs the adversary on the public key and challenge ciphertext. The adversary may query the
ambient oracle interface `spec`, the plaintext-checking oracle, and the validity oracle, and the
game returns `true` exactly when the final guess equals the hidden challenge message. -/
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
