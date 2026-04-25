/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.Coercions.Add
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Short Integer Solution (SIS) and SelfTargetMSIS

This file defines the Short Integer Solution (SIS) problem and its variant SelfTargetMSIS
(Self-Target Module-SIS), which is used in the security proof of ML-DSA (CRYSTALS-Dilithium).

## SIS

The (Module-)SIS problem: given a uniformly random matrix `A`, find a short nonzero vector `x`
such that `Ax = 0`. The generic interface covers both ordinary SIS over `ZMod p` and module-SIS
over a finite coefficient ring.

## SelfTargetMSIS

The SelfTargetMSIS problem (introduced in the Dilithium security proof): given a random matrix
`A` and access to a random oracle `H`, find `(c, z)` such that `Az = c*t + w` where `w` has
high bits matching a specific target, and `z` is short. The "self-target" refers to the fact
that the adversary must produce a hash preimage `c = H(...)` as part of the solution.

## References

- NIST FIPS 204 (ML-DSA security analysis)
- EasyCrypt `SelfTargetMSIS.eca` (formosa-crypto/dilithium)
- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
-/


open OracleComp OracleSpec ENNReal Matrix

namespace SIS

section Generic

variable {Sample Solution : Type}

/-- A generic SIS-style problem instance.
`Sample` is the public challenge data (e.g. a matrix), and `Solution` is the type of
short vectors the adversary must find. The predicate `isValid` checks whether a solution
is valid (short and satisfying the linear constraint). -/
structure Problem (Sample Solution : Type) where
  sampleChallenge : ProbComp Sample
  isValid : Sample → Solution → Bool

/-- A search adversary for a SIS-style problem. -/
abbrev Adversary (_problem : Problem Sample Solution) :=
  Sample → ProbComp Solution

/-- The SIS experiment: sample a random challenge, run the adversary, check validity. -/
def experiment (problem : Problem Sample Solution)
    (adv : Adversary problem) : ProbComp Bool := do
  let challenge ← problem.sampleChallenge
  let solution ← adv challenge
  return problem.isValid challenge solution

/-- Search advantage for the SIS experiment. -/
noncomputable def advantage (problem : Problem Sample Solution)
    (adv : Adversary problem) : ℝ≥0∞ :=
  Pr[= true | experiment problem adv]

end Generic

section MatrixSIS

variable {α : Type}

/-- The standard matrix-based SIS constructor.

Given matrix `A ∈ α^{n×m}`, find nonzero `x ∈ α^m` with `Ax = 0` and `‖x‖ ≤ β`.
The norm bound is encoded in `isShort`. -/
def matrixProblem (n m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (isShort : (Fin m → α) → Bool) :
    Problem (Matrix (Fin n) (Fin m) α) (Fin m → α) where
  sampleChallenge := $ᵗ Matrix (Fin n) (Fin m) α
  isValid A x := decide (x ≠ 0) && isShort x && decide (mulVec A x = 0)

end MatrixSIS

end SIS

namespace SelfTargetMSIS

/-- The SelfTargetMSIS problem for lattice-based signatures.

The adversary receives a matrix `A` and a target vector `t`, and has access to a random
oracle `H`. The adversary must produce `(hashInput, response)` such that:
1. `c = H(hashInput)` (self-targeting: the adversary must have queried the RO on `hashInput`)
2. `isValid(challenge, target, c, response)` holds (shortness bound + verification equation)

The experiment enforces RO consistency by looking up `hashInput` in the RO's query cache.
If the adversary never queried `H(hashInput)`, the check fails automatically.

This captures the core hardness assumption in the ML-DSA/Dilithium security proof. -/
structure Problem (Challenge Response Target HashInput HashOutput : Type) where
  /-- Sample the public parameters (matrix + target). -/
  sampleParams : ProbComp (Challenge × Target)
  /-- Check whether a purported solution is valid, given the hash output from the RO. -/
  isValid : Challenge → Target → HashOutput → Response → Bool

section Experiment

variable {Challenge Response Target HashInput HashOutput : Type}

/-- A SelfTargetMSIS adversary has access to a random oracle `HashInput →ₒ HashOutput`
(modeling the hash function `H`) and uniform randomness. The adversary returns a hash
preimage and a response; the experiment checks RO consistency by looking up the preimage
in the oracle's cache. -/
structure Adversary (problem : Problem Challenge Response Target HashInput HashOutput)
    where
  run (params : Challenge × Target) :
    OracleComp (unifSpec + (HashInput →ₒ HashOutput)) (HashInput × Response)

variable [DecidableEq HashInput] [SampleableType HashOutput]

/-- The SelfTargetMSIS experiment in the ROM: sample parameters, run the adversary with
uniform randomness and a lazy random oracle for `H`, then enforce:
1. The adversary actually queried `H(hashInput)` (RO consistency check via the query cache)
2. The solution passes `isValid` with the RO's cached output -/
noncomputable def experiment
    {problem : Problem Challenge Response Target HashInput HashOutput}
    (adv : Adversary problem) :
    ProbComp Bool := do
  let params ← problem.sampleParams
  let ro : QueryImpl (HashInput →ₒ HashOutput)
    (StateT ((HashInput →ₒ HashOutput).QueryCache) ProbComp) := randomOracle
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((HashInput →ₒ HashOutput).QueryCache) ProbComp)
  let ((hashInput, response), cache) ←
    StateT.run (simulateQ (idImpl + ro) (adv.run params)) ∅
  match cache hashInput with
  | some hashOutput => return problem.isValid params.1 params.2 hashOutput response
  | none => return false

/-- Advantage of a SelfTargetMSIS adversary. -/
noncomputable def advantage
    {problem : Problem Challenge Response Target HashInput HashOutput}
    (adv : Adversary problem) :
    ℝ≥0∞ :=
  Pr[= true | experiment adv]

end Experiment

end SelfTargetMSIS
