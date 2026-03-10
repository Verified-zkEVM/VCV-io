/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
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

namespace SignatureAlg

section signingOracle

variable {m : Type → Type v} [Monad m] {M PK SK S : Type}

/-- In the new API, `QueryImpl (M →ₒ S)` is just `M → m S` (since `Domain = M`).
The old version used `⟨fun | query () msg => ...⟩` which matched the old struct-based API. -/
def signingOracle (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) :
    QueryImpl (M →ₒ S) (WriterT (QueryLog (M →ₒ S)) m) :=
  QueryImpl.withLogging (fun msg => sigAlg.sign pk sk msg)

end signingOracle

section sound

variable {m : Type → Type v} [Monad m] [HasEvalSPMF m] {M PK SK S : Type}

def PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S) : Prop :=
  ∀ msg : M, Pr[= true | sigAlg.exec do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig] = 1

end sound

section unforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

structure unforgeableAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (M × S)

/-- Unforgeability experiment for a signature algorithm: runs the adversary and checks whether
the adversary successfully forged a signature.

API changes from old version:
- `spec ++ₒ` → `spec +`
- `idOracle ++ₛₒ sigAlg.signingOracle pk sk` → explicit `QueryImpl.ofLift` + `liftTarget` + `+`
- `log.wasQueried () m` → `log.wasQueried msg` (Domain of `M →ₒ S` is `M`, not `Unit × M`) -/
def unforgeableExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : unforgeableAdv sigAlg) : ProbComp Bool :=
  sigAlg.exec do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (QueryImpl.ofLift spec (OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ
    return !log.wasQueried msg && verified

noncomputable def unforgeableAdv.advantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : unforgeableAdv sigAlg) : ℝ≥0∞ := Pr[= true | unforgeableExp adv]

end unforgeable

end SignatureAlg
