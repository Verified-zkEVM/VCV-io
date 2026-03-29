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

-- The algebraic core of completeness: whenever `respond` produces `some (z, h)`, the
-- `verify` function accepts. This follows from the key generation relationship
-- `A·s₁ + s₂ = t₁·2^d + t₀`, the correctness of `MakeHint`/`UseHint`, and the rounding
-- norm bounds. We isolate it as a hypothesis since the full algebraic derivation requires
-- NTT linearity and primitives laws.
variable
  (hRespondVerify : ∀ (pk : PublicKey p prims) (sk : SecretKey p),
    validKeyPair p prims pk sk = true →
    ∀ (w1 : Commitment p prims) (st : SigningState p) (cTilde : CommitHashBytes p),
    (w1, st) ∈ support ((identificationScheme p prims nttOps).commit pk sk) →
    ∀ (zh : Response p prims),
    some zh ∈ support ((identificationScheme p prims nttOps).respond pk sk st cTilde) →
    (identificationScheme p prims nttOps).verify pk w1 cTilde zh = true)

include hRespondVerify in
/-- Completeness of the ML-DSA identification scheme, conditional on `hRespondVerify`:
whenever `respond` returns `some (z, h)`, `verify` accepts. This algebraic fact follows
from the key generation identity, NTT linearity, and `Primitives.Laws`, but is isolated
here to separate the probabilistic argument from the algebraic one. -/
theorem idsWithAbort_complete' :
    (identificationScheme p prims nttOps).Complete := by
  intro pk sk hvalid
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨HasEvalPMF.probFailure_eq_zero _, ?_⟩
  intro b hb
  rw [support_bind] at hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨t?, ht?, hb⟩ := hb
  rw [support_pure] at hb
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  match t? with
  | none => rfl
  | some (w1, cTilde, zh) =>
    simp only [IdenSchemeWithAbort.honestExecution, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at ht?
    obtain ⟨⟨w1', st⟩, hw1st, cTilde', hcTilde, oz, hoz, heq⟩ := ht?
    cases oz with
    | none => simp only [Option.map, reduceCtorEq] at heq
    | some zh' =>
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hRespondVerify pk sk hvalid w1 st cTilde hw1st _ hoz

omit hRespondVerify in
/-- The ML-DSA identification scheme is complete: whenever the honest prover does not abort,
the verifier always accepts. This follows from the correctness of the rounding operations
and the norm bounds satisfied by honest responses.

The proof requires deriving the `hRespondVerify` algebraic fact from `Primitives.Laws`;
see `idsWithAbort_complete'` for the conditional version. -/
theorem idsWithAbort_complete (h_laws : Primitives.Laws prims nttOps) :
    (identificationScheme p prims nttOps).Complete := by
  sorry

omit hRespondVerify in
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

omit hRespondVerify [SampleableType (CommitHashBytes p)]
  [unifSpec.Fintype] [unifSpec.Inhabited] in
/-- Commitment recoverability for ML-DSA: the public commitment `w₁` can be reconstructed
from `(pk, c̃, (z, h))` alone using `UseHint(h, Az - ct₁·2^d)`. This is the key property
enabling the CMA-to-NMA reduction in the security proof.

In our formalization, this is directly enforced by the `verify` function: it checks
`UseHint(h, w'_Approx) = w₁`, so any accepted transcript necessarily satisfies
commitment recoverability. -/
theorem idsWithAbort_commitment_recoverable :
    ∃ recover, (identificationScheme p prims nttOps).CommitmentRecoverable recover := by
  refine ⟨fun pk cTilde (z, h) =>
    prims.useHintVec h (computeWApprox p prims nttOps (prims.expandA pk.rho)
      (prims.sampleInBall cTilde) z pk.t1), ?_⟩
  intro s w' c z hverify
  unfold identificationScheme at hverify
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hverify
  change prims.useHintVec z.2
    (computeWApprox p prims nttOps (prims.expandA s.rho) (prims.sampleInBall c) z.1 s.t1) = w'
  exact hverify.1.2

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
