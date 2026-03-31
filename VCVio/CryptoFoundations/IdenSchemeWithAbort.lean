/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ExecutionMethod
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.TVDist

/-!
# Identification Scheme with Aborts

This file defines a structure for identification schemes with aborts, as used in ML-DSA
(CRYSTALS-Dilithium). Unlike a standard Σ-protocol (`SigmaProtocol`), the prover's response
may fail (abort), in which case the protocol is retried. This abort mechanism is essential for
the security of lattice-based schemes where masking must hide the secret.

The structure follows the EasyCrypt formalization in `IDSabort.ec` (formosa-crypto/dilithium).

## Main Definitions

- `IdenSchemeWithAbort`: identification scheme where `respond` returns `Option Z`
- `IdenSchemeWithAbort.Complete`: honest prover convinces verifier (conditioned on non-abort)
- `IdenSchemeWithAbort.HVZK`: transcript distribution is within a stated TV-distance
  of a simulator
- `IdenSchemeWithAbort.PerfectHVZK`: exact transcript distribution matching with a simulator
- `IdenSchemeWithAbort.CommitmentRecoverable`: ability to recover commitment from the transcript

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
- EasyCrypt `IDSabort.ec`
-/

set_option autoImplicit false

open OracleSpec OracleComp

/-- An identification scheme with aborts for statements in `S` and witnesses in `W`, where
`p : S → W → Bool` is the proven relation. The prover's commitment is split into a public
part `W'` (sent to the verifier) and a private state `St`. The verifier's challenge is in `C`,
and the prover's response (which may abort) is in `Z`.

Unlike `SigmaProtocol`, the `respond` function returns `Option Z` — `none` indicates an abort
and the protocol must be retried. This is the key mechanism used in Dilithium/ML-DSA to ensure
that the response distribution is independent of the secret. -/
structure IdenSchemeWithAbort
    (S W W' St C Z : Type) (p : S → W → Bool) where
  /-- Generate a commitment: returns a public commitment `W'` and private state `St`. -/
  commit (s : S) (w : W) : ProbComp (W' × St)
  /-- Respond to a challenge. Returns `none` if the response would leak information about
  the secret (abort), in which case the protocol is retried from scratch. -/
  respond (s : S) (w : W) (st : St) (c : C) : ProbComp (Option Z)
  /-- Deterministic verification: check that the response `z` is valid for the given
  statement, commitment, and challenge. -/
  verify (s : S) (w' : W') (c : C) (z : Z) : Bool

namespace IdenSchemeWithAbort

variable {S W W' St C Z : Type} {p : S → W → Bool}

section HonestExecution

variable [SampleableType C] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- A single honest execution producing an optional transcript `(W', C, Z)`. Returns `none`
if the prover aborts. -/
def honestExecution (ids : IdenSchemeWithAbort S W W' St C Z p) (s : S) (w : W) :
    ProbComp (Option (W' × C × Z)) := do
  let (w', st) ← ids.commit s w
  let c ← $ᵗ C
  let oz ← ids.respond s w st c
  return oz.map fun z => (w', c, z)

end HonestExecution

section Completeness

variable [SampleableType C] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- An identification scheme with aborts is complete if: whenever the prover does not abort,
the verifier always accepts. -/
def Complete (ids : IdenSchemeWithAbort S W W' St C Z p) : Prop :=
  ∀ s w, p s w = true →
    Pr[= true | do
      let t? ← ids.honestExecution s w
      return match t? with
        | some (w', c, z) => ids.verify s w' c z
        | none => true
    ] = 1

end Completeness

section HVZK

variable [SampleableType C] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- Approximate honest-verifier zero-knowledge for an identification scheme with aborts:
the transcript distribution produced by the honest prover is within total variation
distance `ζ_zk` of the distribution produced by the simulator.

Both distributions are over `Option (W' × C × Z)`, where `none` represents an abort.
The parameter `ζ_zk` captures both transcript mismatch and abort-probability mismatch. -/
def HVZK (ids : IdenSchemeWithAbort S W W' St C Z p)
    (sim : S → ProbComp (Option (W' × C × Z))) (ζ_zk : ℝ) : Prop :=
  ∀ s w, p s w = true →
    tvDist (ids.honestExecution s w) (sim s) ≤ ζ_zk

/-- Exact honest-verifier zero-knowledge for an identification scheme with aborts:
the transcript distribution produced by the honest prover exactly matches the
distribution produced by the simulator. -/
def PerfectHVZK (ids : IdenSchemeWithAbort S W W' St C Z p)
    (sim : S → ProbComp (Option (W' × C × Z))) : Prop :=
  ∀ s w, p s w = true →
    evalDist (ids.honestExecution s w) = evalDist (sim s)

@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    (ids : IdenSchemeWithAbort S W W' St C Z p)
    (sim : S → ProbComp (Option (W' × C × Z))) :
    ids.PerfectHVZK sim ↔ ids.HVZK sim 0 := by
  constructor
  · intro h
    dsimp [HVZK]
    intro s w hs
    have hzero : tvDist (ids.honestExecution s w) (sim s) = 0 := by
      simpa using (tvDist_eq_zero_iff (ids.honestExecution s w) (sim s)).2 (h s w hs)
    exact le_of_eq hzero
  · intro h
    dsimp [HVZK] at h
    intro s w hs
    have hzero : tvDist (ids.honestExecution s w) (sim s) = 0 := by
      exact le_antisymm (h s w hs) (by
        simpa using (tvDist_nonneg (ids.honestExecution s w) (sim s)))
    simpa using (tvDist_eq_zero_iff (ids.honestExecution s w) (sim s)).mp hzero

end HVZK

section CommitmentRecoverability

/-- Commitment recoverability: any accepting transcript determines the public commitment `W'`
from the statement, challenge, and response alone. This property is required for the
CMA-to-NMA reduction in the Fiat-Shamir with aborts security proof.

In Dilithium/ML-DSA, the commitment `w1` can be recomputed as `highBits(Az - c*t)`. -/
def CommitmentRecoverable (ids : IdenSchemeWithAbort S W W' St C Z p)
    (recover : S → C → Z → W') : Prop :=
  ∀ s w' c z,
    ids.verify s w' c z = true →
    recover s c z = w'

end CommitmentRecoverability

section Impersonation

/-- An adversary for the impersonation game against an identification scheme with aborts.
The adversary sees the public key (statement), produces a commitment together with an
internal state, and then responds to a challenge using that state. -/
structure ImpAdv (ids : IdenSchemeWithAbort S W W' St C Z p) (AdvSt : Type) where
  commit (s : S) : ProbComp (W' × AdvSt)
  respond (s : S) (c : C) (st : AdvSt) : ProbComp Z

variable [SampleableType C] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- The impersonation experiment: the adversary tries to produce a valid transcript
without knowing the witness, against a fixed statement `s`. -/
def impExp {ids : IdenSchemeWithAbort S W W' St C Z p}
    {AdvSt : Type} (adv : ImpAdv ids AdvSt) (s : S) : ProbComp Bool := do
  let (w', st) ← adv.commit s
  let c ← $ᵗ C
  let z ← adv.respond s c st
  return ids.verify s w' c z

end Impersonation

end IdenSchemeWithAbort
