/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.Append
import ToMathlib.Control.Monad.Hom

/-!
# Signature Algorithms

This file defines `SignatureAlg m M PK SK S`, a type representing a digital signature scheme
with computations in the monad `m`, message space `M`, public/secret key spaces `PK`/`SK`,
and signature space `S`.
-/

universe u v

open OracleSpec OracleComp ENNReal

/-- Signature algorithm with computations in the monad `m`,
where `M` is the space of messages, `PK`/`SK` are the spaces of the public/private keys,
and `S` is the type of the final signature. -/
@[ext]
structure SignatureAlg (m : Type → Type v) [Monad m] (M PK SK S : Type) where
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

section map

variable {m : Type → Type v} [Monad m] {n : Type → Type u} [Monad n]
  {M PK SK S : Type}

/-- Transport a signature scheme across a monad morphism by mapping each algorithmic component.

This is the basic reindexing operation used by naturality theorems for generic constructions:
if a signature scheme was defined in a source monad `m`, then any monad morphism `m →ᵐ n`
induces the corresponding scheme in `n`. -/
def map (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) : SignatureAlg n M PK SK S where
  keygen := F sigAlg.keygen
  sign pk sk msg := F (sigAlg.sign pk sk msg)
  verify pk msg σ := F (sigAlg.verify pk msg σ)

@[simp]
lemma map_keygen (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) :
    (sigAlg.map F).keygen = F sigAlg.keygen := rfl

@[simp]
lemma map_sign (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S)
    (pk : PK) (sk : SK) (msg : M) :
    (sigAlg.map F).sign pk sk msg = F (sigAlg.sign pk sk msg) := rfl

@[simp]
lemma map_verify (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S)
    (pk : PK) (msg : M) (σ : S) :
    (sigAlg.map F).verify pk msg σ = F (sigAlg.verify pk msg σ) := rfl

end map

section correctness

variable {m : Type → Type v} [Monad m] {M PK SK S : Type}

/-- Completeness of a signature scheme with error `δ`: for every message, the canonical
keygen-sign-verify execution accepts with probability at least `1 - δ`.

The error `δ` captures all sources of failure, including both verification mismatches and
signing failures (e.g., abort in schemes like Fiat-Shamir with aborts).

`Complete sigAlg runtime 0` is equivalent to `PerfectlyComplete sigAlg runtime`. -/
def Complete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ msg : M, Pr[= true | runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig] ≥ 1 - δ

/-- Perfect completeness: the canonical keygen-sign-verify execution always accepts.
This is the special case of `Complete` with zero error. -/
def PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, Pr[= true | runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig] = 1

lemma perfectlyComplete_iff_complete_zero
    (sigAlg : SignatureAlg m M PK SK S) (runtime : ProbCompRuntime m) :
    sigAlg.PerfectlyComplete runtime ↔ sigAlg.Complete runtime 0 := by
  simp [PerfectlyComplete, Complete]

lemma Complete.mono {sigAlg : SignatureAlg m M PK SK S}
    {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : sigAlg.Complete runtime δ₁) (hle : δ₁ ≤ δ₂) :
    sigAlg.Complete runtime δ₂ :=
  fun msg => le_trans (tsub_le_tsub_left hle 1) (h msg)

end correctness

section unforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

structure unforgeableAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (M × S)

/-- Unforgeability experiment for a signature algorithm: runs the adversary and checks whether
the adversary successfully forged a signature. The ambient oracle family is forwarded unchanged,
the signing oracle is logged, and the final check requires both signature validity and that the
forged message was never submitted to the signing oracle. -/
noncomputable def unforgeableExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : unforgeableAdv sigAlg) : SPMF Bool :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ
    return !log.wasQueried msg && verified

/-- The success probability of a CMA adversary in the unforgeability experiment. -/
noncomputable def unforgeableAdv.advantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : unforgeableAdv sigAlg) : ℝ≥0∞ := Pr[= true | unforgeableExp runtime adv]

end unforgeable

section eufNma

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EUF-NMA (existential unforgeability under no-message attack) adversary for a
signature scheme. Unlike a CMA adversary (`unforgeableAdv`), the NMA adversary has NO
access to a signing oracle — it must forge a signature having only seen the public key.

In the random oracle model, the adversary still has access to the scheme's oracle spec
(e.g., the random oracle `H`), but never sees any legitimately generated signatures. -/
structure eufNmaAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp spec (M × S)

/-- The EUF-NMA experiment: generate a key pair, give the public key to the adversary
(with no signing oracle), and check whether the adversary produced a valid forgery. -/
def eufNmaExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : eufNmaAdv sigAlg) : SPMF Bool :=
  runtime.evalDist do
    let (pk, _) ← sigAlg.keygen
    let (msg, σ) ← adv.main pk
    sigAlg.verify pk msg σ

/-- The success probability of an EUF-NMA adversary. -/
noncomputable def eufNmaAdv.advantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : eufNmaAdv sigAlg) : ℝ≥0∞ := Pr[= true | eufNmaExp runtime adv]

end eufNma

end SignatureAlg
