/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.Append

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec σ M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

universe u v

open OracleSpec OracleComp ENNReal

/-- Signature algorithm with computations in the monad `m`,
where `M` is the space of messages, `PK`/`SK` are the spaces of the public/private keys,
and `S` is the type of the final signature. -/
structure SignatureAlg (m : Type → Type v) (M PK SK S : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : m S
  verify (pk : PK) (msg : M) (σ : S) : m Bool

-- namespace SignatureAlg

-- section signingOracle

-- variable {m : Type → Type v} [Monad m] {σ M PK SK S : Type}

-- def signingOracle (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) :
--     QueryImpl (M →ₒ S) (WriterT (QueryLog (M →ₒ S)) m) :=
--   QueryImpl.withLogging ⟨fun | query () msg => sigAlg.sign pk sk msg⟩

-- end signingOracle

-- section sound

-- variable {m : Type → Type v} [Monad m] {σ M PK SK S : Type}

-- /-- a `SignatureAlg` is perfectly complete if honest signatures are always verified. -/
-- def PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S) : Prop :=
--   ∀ msg : M, [= true | sigAlg.exec do
--     let (pk, sk) ← sigAlg.keygen
--     let sig ← sigAlg.sign pk sk msg
--     sigAlg.verify pk msg sig] = 1

-- end sound

-- section unforgeable

-- variable {ι : Type u} {spec : OracleSpec ι} {σ M PK SK S : Type}
--   [DecidableEq M] [DecidableEq S]

-- /-- Adversary for testing the unforgeability of a signature scheme.
-- We only define this if the monad for the protocol is `OracleComp spec`,
-- as we need to be able to give the adversary access to a signing oracle. -/
-- structure unforgeableAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
--   main (pk : PK) : OracleComp (spec ++ₒ (M →ₒ S)) (M × S)

-- /-- Unforgeability expiriment for a signature algorithm runs the adversary and checks returns
-- whether or not the adversary successfully forged a signature-/
-- def unforgeableExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
--     (adv : unforgeableAdv sigAlg) : ProbComp Bool :=
--   sigAlg.exec do
--     let (pk, sk) ← sigAlg.keygen
--     -- Simulate the adversary's signing oracle with the public / secret keys
--     let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
--       simulateQ (idOracle ++ₛₒ sigAlg.signingOracle pk sk) (adv.main pk)
--     -- Run the adversary and check that they successfully forged a signature
--     let ((m, σ), log) ← sim_adv.run
--     return !(log.wasQueried () m) && (← sigAlg.verify pk m σ)

-- /-- Advantage -/
-- noncomputable def unforgeableAdv.advantage
--     {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
--     (adv : unforgeableAdv sigAlg) : ℝ≥0∞ := [= true | unforgeableExp adv]

-- end unforgeable

-- end SignatureAlg
