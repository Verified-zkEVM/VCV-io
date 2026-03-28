/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Scheme
import VCVio.CryptoFoundations.FiatShamirWithAbort
import VCVio.CryptoFoundations.HardnessAssumptions.SIS

/-!
# ML-DSA Security

This file states the high-level security theorems for ML-DSA. The main result is that the
ML-DSA signature scheme (constructed via `FiatShamirWithAbort` applied to the ML-DSA
identification scheme) is EUF-CMA secure, reducing to:

1. The **SelfTargetMSIS** assumption on the public matrix `A`
2. The **HVZK** property of the underlying identification scheme
3. **Commitment recoverability**: `w₁` can be recomputed as `UseHint(h, Az - ct₁·2^d)`

The proof is future work and follows the structure of Theorem 4 in the CRYPTO 2023 paper
(Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts
and Dilithium").

## References

- NIST FIPS 204, Section 3.2 (security properties)
- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
- EasyCrypt `FSabort.eca`, `HVZK_FSa.ec`, `SimplifiedScheme.ec`
-/

set_option autoImplicit false

open OracleComp OracleSpec

namespace ML_DSA

variable (p : Params) (prims : Primitives p) (nttOps : NTTRingOps)
  [DecidableEq prims.High]

section Properties

variable [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [unifSpec.Fintype] [unifSpec.Inhabited]

/-- The ML-DSA identification scheme is complete: whenever the honest prover does not abort,
the verifier always accepts. This follows from the correctness of the rounding operations
and the norm bounds satisfied by honest responses. -/
theorem idsWithAbort_complete :
    (identificationScheme p prims nttOps).Complete := by
  sorry

/-- There exists a simulator for the HVZK property of the ML-DSA identification scheme.

The simulator produces transcripts by:
1. Sampling `z` uniformly from the response space (with appropriate norm bound)
2. Sampling `c̃` uniformly
3. Computing `w₁ = UseHint(h, Az - ct₁·2^d)` (the commitment recovery equation)

When the response rejection probability is sufficiently close to uniform, the simulated
transcript distribution matches the honest transcript distribution. -/
theorem idsWithAbort_hvzk :
    ∃ sim, (identificationScheme p prims nttOps).HVZK sim := by
  sorry

/-- Commitment recoverability for ML-DSA: the public commitment `w₁` can be reconstructed
from `(pk, c̃, (z, h))` alone using `UseHint(h, Az - ct₁·2^d)`. This is the key property
enabling the CMA-to-NMA reduction in the security proof.

In our formalization, this is directly enforced by the `verify` function: it checks
`UseHint(h, w'_Approx) = w₁`, so any accepted transcript necessarily satisfies
commitment recoverability. -/
theorem idsWithAbort_commitment_recoverable :
    ∃ recover, (identificationScheme p prims nttOps).CommitmentRecoverable recover := by
  sorry

end Properties

section MainTheorem

variable {M : Type} [DecidableEq M]
  [DecidableEq prims.Hint]
  [SampleableType (RqVec p.l)] [SampleableType (PublicKey p prims)]
  [SampleableType (SecretKey p)] [SampleableType (CommitHashBytes p)]
  [unifSpec.Fintype] [unifSpec.Inhabited]

/-- **Main Security Theorem (EUF-CMA).**

If the `SelfTargetMSIS` problem is hard for the ML-DSA parameters, then the ML-DSA
signature scheme (constructed via `FiatShamirWithAbort`) is existentially unforgeable
under adaptive chosen-message attack (EUF-CMA).

More precisely, for any EUF-CMA adversary `A` making at most `qH` random oracle queries
and `qS` signing queries, there exists a SelfTargetMSIS adversary `B` such that:

  `Adv^{EUF-CMA}_{ML-DSA}(A) ≤ Adv^{SelfTargetMSIS}(B)`

The reduction uses:
1. The HVZK simulator to answer signing queries (via rejection sampling)
2. Commitment recoverability to embed the SelfTargetMSIS challenge
3. The forking lemma to extract a second forgery sharing the same commitment

This theorem statement is parametric over the message type `M` and the primitive
implementations. The proof is future work following the EasyCrypt mechanization. -/
theorem euf_cma_security
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims)) :
    ∀ (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationScheme p prims nttOps)
        hr M maxAttempts)),
    ∃ (reduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage ≤ SelfTargetMSIS.advantage reduction := by
  sorry

end MainTheorem

end ML_DSA
