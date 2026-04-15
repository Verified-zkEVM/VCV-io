/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Scheme
import VCVio.CryptoFoundations.FiatShamirWithAbort
import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
import LatticeCrypto.HardnessAssumptions.LearningWithErrors

/-!
# ML-DSA Security

This file states the high-level security theorems for ML-DSA, following the CRYPTO 2023 paper
"Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium" (Barbosa
et al., ePrint 2023/246).

The main result (Theorem 4) is that the ML-DSA signature scheme is EUF-CMA secure, reducing
to two computational assumptions plus a statistical loss from the CMA-to-NMA reduction:

  `Adv^{EUF-CMA}_{ML-DSA}(A) ≤ Adv^{MLWE}_{k,l,Sη}(B) + Adv^{SelfTargetMSIS}_{G,k,l+1,ζ}(C) + L`

The two computational assumptions are:

1. **MLWE** (Module Learning With Errors): `(A, As₁ + s₂)` is computationally indistinguishable
   from `(A, uniform)` (Definition 3).
2. **SelfTargetMSIS** (Self-Target Module-SIS): given `A` and a random oracle `H`, it is hard
   to find a short vector satisfying a self-referential hash equation (Definition 4).

The statistical loss `L` from the CMA-to-NMA reduction via Fiat-Shamir with aborts is:

  `L = 2·qS·(qH + qS + 1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk + δ`

The proof follows the structure:
1. EUF-CMA → EUF-NMA via the Fiat-Shamir with aborts CMA-to-NMA reduction (Theorem 3)
   plus `qS` extra random-oracle queries to convert standard `(w₁, z, h)` signatures into
   commitment-recoverable `(c̃, z, h)` signatures for ML-DSA.
2. EUF-NMA → MLWE + SelfTargetMSIS (Lemma 7)

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246), Theorems 3, 4 and Lemma 7, Definitions 3, 4
- NIST FIPS 204, Section 3.2 (security properties)
- EasyCrypt `FSabort.eca`, `HVZK_FSa.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
-/


open OracleComp OracleSpec ENNReal

namespace MLDSA

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

include hRespondVerify
/-- Completeness of the ML-DSA identification scheme, conditional on `hRespondVerify`:
whenever `respond` returns `some (z, h)`, `verify` accepts. This algebraic fact follows
from the key generation identity, NTT linearity, and `Primitives.Laws`, but is isolated
here to separate the probabilistic argument from the algebraic one. -/
theorem idsWithAbort_complete' :
    (identificationScheme p prims nttOps).Complete := by
  classical
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

omit hRespondVerify
/-- The ML-DSA identification scheme is complete: whenever the honest prover does not abort,
the verifier always accepts. This follows from the correctness of the rounding operations
and the norm bounds satisfied by honest responses.

The proof requires deriving the `hRespondVerify` algebraic fact from `Primitives.Laws`;
see `idsWithAbort_complete'` for the conditional version. -/
theorem idsWithAbort_complete (h_laws : Primitives.Laws prims nttOps) :
    (identificationScheme p prims nttOps).Complete := by
  classical
  sorry

/-- Placeholder quantitative HVZK theorem surface for the ML-DSA identification scheme.

THIS THEOREM STATEMENT NEEDS TO BE UPDATED ONCE WE FIGURE OUT THE CORRECT BOUND TO STATE.

The simulator produces transcripts by:
1. Sampling `z` uniformly from the response space (with appropriate norm bound)
2. Sampling `c̃` uniformly
3. Computing `w₁ = UseHint(h, Az - ct₁·2^d)` (the commitment recovery equation)

When the response rejection probability is sufficiently close to uniform, the simulated
transcript distribution is within an explicit total-variation bound `ζ_zk` of the honest
transcript distribution. The bound is nonnegative by definition of total variation
distance. -/
theorem idsWithAbort_hvzk :
    ∃ sim ζ_zk, 0 ≤ ζ_zk ∧ (identificationScheme p prims nttOps).HVZK sim ζ_zk := by
  classical
  sorry

omit [SampleableType (CommitHashBytes p)] [unifSpec.Fintype] [unifSpec.Inhabited]
/-- Commitment recoverability for ML-DSA: the public commitment `w₁` can be reconstructed
from `(pk, c̃, (z, h))` alone using `UseHint(h, Az - ct₁·2^d)`. This is the key property
enabling the CMA-to-NMA reduction in the security proof.

In our formalization, this is directly enforced by the `verify` function: it checks
`UseHint(h, w'_Approx) = w₁`, so any accepted transcript necessarily satisfies
commitment recoverability. -/
theorem idsWithAbort_commitment_recoverable :
    ∃ recover, (identificationScheme p prims nttOps).CommitmentRecoverable recover := by
  classical
  refine ⟨fun pk cTilde (z, h) =>
    prims.useHintVec h (computeWApprox p prims nttOps (prims.expandA pk.rho)
      (prims.sampleInBall cTilde) z pk.t1), ?_⟩
  rintro s w' c ⟨z, h⟩ hverify
  unfold identificationScheme at hverify
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hverify
  exact hverify.1.2

end Properties

/-! ### EUF-NMA Security (Lemma 7) -/

section NMASecurity

variable {M : Type}
  [SampleableType (RqVec p.l)] [SampleableType (PublicKey p prims)]
  [SampleableType (SecretKey p)] [SampleableType (CommitHashBytes p)]
  [unifSpec.Fintype] [unifSpec.Inhabited]

open scoped Classical in
/-- **NMA Security (Lemma 7, CRYPTO 2023).**

For every EUF-NMA adversary `A` against the ML-DSA scheme (instantiated via
`FiatShamirWithAbort`), there exist:
- An MLWE adversary `B` (against `MLWE_{k,l,Sη}`)
- A SelfTargetMSIS adversary `C` (against `SelfTargetMSIS_{G,k,l+1,ζ}`)

such that:

  `Adv^{EF-NMA}(A) ≤ Adv^{MLWE}_{k,l,Sη}(B) + Adv^{SelfTargetMSIS}_{G,k,l+1,ζ}(C)`

The proof sketch from the paper:
1. Replace `keygen` with `keygen1` (uniform `t`): the gap is exactly `Adv^{MLWE}(B)`.
2. Define `H₁(w₁, m) := G(shift_α(w₁), m)` — no loss since `shift_α` is injective.
3. Extract a SelfTargetMSIS solution from any forgery: the gap is `Adv^{SelfTargetMSIS}(C)`.

where `ζ = max(γ₁ - β, 2γ₂ + 1 + τ · 2^{d-1})` and `Time(A) ≈ Time(B) ≈ Time(C)`. -/
theorem nma_security
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims)) :
    ∀ (adv : SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort (identificationScheme p prims nttOps) hr M maxAttempts)),
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction) +
        SelfTargetMSIS.advantage stmsisReduction := by
  sorry

end NMASecurity

/-! ### CMA-to-NMA Statistical Loss (Theorem 4) -/

section CMAtoNMA

/-- The ML-DSA-specific classical ROM loss obtained by combining the abstract
Fiat-Shamir-with-aborts reduction with the commitment-recoverable signature
format used by ML-DSA.

The abstract theorem applies to the standard Fiat-Shamir signature format where
the commitment `w₁` is part of the signature, giving the loss
`FiatShamirWithAbort.cmaToNmaLoss qS qH ...`.
ML-DSA instead publishes the compressed signature `(c̃, z, h)`, and the paper's
reduction converts each signing-oracle answer back into a standard signature via
one extra random-oracle query. Across `qS` signing queries this adds `qS` to the
effective random-oracle budget, yielding:

  `L = 2·qS·(qH + qS + 1)·ε/(1-p)
     + qS·ε·(qS+1)/(2·(1-p)²)
     + qS·ζ_zk
     + δ`

This is exactly `FiatShamirWithAbort.cmaToNmaLoss qS (qH + qS) ...`. -/
noncomputable def cmaToNmaLoss
    (qS qH : ℕ) (ε p_abort ζ_zk δ : ℝ) (hp : p_abort < 1) : ℝ :=
  FiatShamirWithAbort.cmaToNmaLoss qS (qH + qS) ε p_abort ζ_zk δ hp

end CMAtoNMA

/-! ### Main Security Theorem (Theorem 4) -/

section MainTheorem

variable {M : Type}
  [SampleableType (RqVec p.l)] [SampleableType (PublicKey p prims)]
  [SampleableType (SecretKey p)] [SampleableType (CommitHashBytes p)]
  [unifSpec.Fintype] [unifSpec.Inhabited]

open scoped Classical in
/-- **Main Security Theorem (EUF-CMA, Theorem 4, CRYPTO 2023).**

THIS THEOREM STATEMENT NEEDS TO BE UPDATED ONCE WE FIGURE OUT THE CORRECT BOUND TO STATE
DIRECTLY FOR ML-DSA. For now it is parameterized by an explicit quantitative HVZK
simulator hypothesis.

For any classical EUF-CMA adversary `A` making at most `qS` signing queries and `qH` random
oracle queries, and for the adversaries `B` (against MLWE) and `C` (against SelfTargetMSIS)
constructed in the proof of Lemma 7:

  `Adv^{EUF-CMA}_{ML-DSA}(A) ≤ Adv^{MLWE}_{k,l,Sη}(B) + Adv^{SelfTargetMSIS}_{G,k,l+1,ζ}(C) + L`

where:
- `L = 2·qS·(qH+qS+1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk + δ` is
  `MLDSA.cmaToNmaLoss`
- `ε` is the commitment guessing probability
- `p` is the effective abort probability
- `sim` is an HVZK simulator for the underlying identification scheme
- `ζ_zk` is a nonnegative bound such that `HVZK sim ζ_zk`
- `δ` is the regularity failure probability
- `ζ = max(γ₁ - β, 2γ₂ + 1 + τ · 2^{d-1})`

The proof composes:
1. **CMA → NMA** (Theorem 3): the Fiat-Shamir with aborts CMA-to-NMA reduction, using the
   HVZK simulator for the ML-DSA identification scheme to answer signing queries and
   commitment recoverability to embed the challenge. Because ML-DSA compresses signatures,
   this step incurs `qS` extra random-oracle queries on top of the adversary's `qH`
   queries, yielding `MLDSA.cmaToNmaLoss`.
2. **NMA → MLWE + SelfTargetMSIS** (Lemma 7): replace `keygen` with uniform `t` (MLWE gap),
   then extract a SelfTargetMSIS solution from any forgery. -/
theorem euf_cma_security
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (_hζ : 0 ≤ ζ_zk)
    (_hhvzk : (identificationScheme p prims nttOps).HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hp : p_abort < 1) :
    ∀ (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationScheme p prims nttOps)
        hr M maxAttempts)),
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction) +
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  sorry

end MainTheorem

end MLDSA
