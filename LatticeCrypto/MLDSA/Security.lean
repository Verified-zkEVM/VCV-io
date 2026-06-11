/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Scheme
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security
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
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]

section Properties

variable [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [IsUniformSpec unifSpec]

-- The algebraic core of completeness: whenever `respond` produces `some (z, h)`, the
-- `verify` function accepts. This follows from the key generation relationship
-- `A·s₁ + s₂ = t₁·2^d + t₀`, the correctness of `MakeHint`/`UseHint`, and the rounding
-- norm bounds. We isolate it as a hypothesis since the full algebraic derivation requires
-- NTT linearity and primitives laws.
variable
  (hRespondVerify : ∀ (pk : PublicKey p prims) (sk : SecretKey p),
    validKeyPair p prims pk sk = true →
    ∀ (w1 : Commitment p prims) (st : SigningState p) (cTilde : CommitHashBytes p),
    (w1, st) ∈ support ((identificationScheme p prims).commit pk sk) →
    ∀ (zh : Response p prims),
    some zh ∈ support ((identificationScheme p prims).respond pk sk st cTilde) →
    (identificationScheme p prims).verify pk w1 cTilde zh = true)

include hRespondVerify
/-- Completeness of the ML-DSA identification scheme, conditional on `hRespondVerify`:
whenever `respond` returns `some (z, h)`, `verify` accepts. This algebraic fact follows
from the key generation identity, NTT linearity, and `Primitives.Laws`, but is isolated
here to separate the probabilistic argument from the algebraic one. -/
theorem idsWithAbort_complete' :
    (identificationScheme p prims).Complete := by
  classical
  intro pk sk hvalid
  rw [probOutput_eq_one_iff_forall]
  refine ⟨probFailure_of_liftM_PMF _, fun b hb => ?_⟩
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

omit nttOps [DecidableEq prims.High] [SampleableType (RqVec p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec] in
private lemma neg_rq_get (f : Rq) (i : Fin ringDegree) : (-f).get i = -(f.get i) := by
  change (coeffRing.neg f).get i = _
  simp [LatticeCrypto.vectorNegacyclicRing]

omit nttOps [DecidableEq prims.High] [SampleableType (RqVec p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec] in
private lemma polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  unfold polyNorm normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView]
  unfold LatticeCrypto.cInfNormOf
  apply Finset.sup_congr rfl
  intro i _
  simp only [LatticeCrypto.zmodCenteredCoeffView, polyBackend,
    LatticeCrypto.vectorNegacyclicRing, LatticeCrypto.vectorBackend]
  rw [neg_rq_get]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec] in
/-- Vector form of `useHint_makeHint`: `UseHint(MakeHint(z, r), r) = HighBits(r + z)`
componentwise, when each component of `z` is bounded by `γ₂`. -/
theorem useHintVec_makeHintVec (h_laws : Primitives.Laws prims nttOps) {k : ℕ}
    (z r : RqVec k) (hz : ∀ j : Fin k, polyNorm (z.get j) ≤ p.gamma2) :
    prims.useHintVec (prims.makeHintVec z r) r = prims.highBitsVec (r + z) := by
  apply Vector.ext; intro i hi
  simp only [Primitives.useHintVec, Primitives.makeHintVec, Primitives.highBitsVec,
    Vector.getElem_zipWith, Vector.getElem_map, Vector.getElem_add]
  exact h_laws.useHint_makeHint z[i] r[i] (by simpa using hz ⟨i, hi⟩)

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec] in
/-- Vector form of `hide_low`: a small additive perturbation does not change the high bits. -/
theorem hide_lowVec (h_laws : Primitives.Laws prims nttOps) {k : ℕ}
    (r s : RqVec k) (b : ℕ)
    (hs : ∀ j : Fin k, polyNorm (s.get j) ≤ b)
    (hr : ∀ j : Fin k, polyNorm (prims.lowBits (r.get j)) + b < p.gamma2) :
    prims.highBitsVec (r + s) = prims.highBitsVec r := by
  apply Vector.ext; intro i hi
  simp only [Primitives.highBitsVec, Vector.getElem_map, Vector.getElem_add]
  exact h_laws.hide_low r[i] s[i] b (by simpa using hs ⟨i, hi⟩) (by simpa using hr ⟨i, hi⟩)

/-- The ML-DSA identification scheme is complete: whenever the honest prover does not abort,
the verifier always accepts. This follows from the correctness of the rounding operations
and the norm bounds satisfied by honest responses.

The proof requires deriving the `hRespondVerify` algebraic fact from `Primitives.Laws`;
see `idsWithAbort_complete'` for the conditional version. -/
theorem idsWithAbort_complete (h_laws : Primitives.Laws prims nttOps) :
    (identificationScheme p prims).Complete := by
  classical
  refine idsWithAbort_complete' p prims ?_
  intro pk sk hvalid w1 st cTilde hw1st zh hzh
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims pk sk).mp hvalid
  simp only [identificationScheme, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff, Prod.mk.injEq] at hw1st
  simp only [identificationScheme] at hzh
  obtain ⟨y, -, hw1, hst⟩ := hw1st
  subst hst hw1
  split_ifs at hzh with hc1 hc2
  · rw [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hzh
    subst hzh
    dsimp only at hc1 hc2 ⊢
    obtain ⟨hz_norm, hr0_norm⟩ := hc1
    obtain ⟨hct0_norm, hweight⟩ := hc2
    -- Honest secret vectors are `η`-bounded, so the challenge product is `β`-bounded.
    have hs2_bound : polyVecBounded sk.s2 p.eta := by
      have h := congrArg Prod.snd hkeygen
      simp only [keyGenFromSeed] at h
      rw [← h]
      exact (h_laws.expandS_bound _).2
    have hcs2_norm : polyVecNorm (prims.sampleInBall cTilde • sk.s2) ≤ p.beta :=
      h_laws.sampleInBall_smul_bound cTilde sk.s2 hs2_bound
    -- Abbreviations matching the goal.
    set c := prims.sampleInBall cTilde with hc_def
    set aHat := prims.expandA pk.rho with haHat_def
    -- The challenge-times-`t₀` hint argument is `γ₂`-bounded (after negation).
    have hcond_t0 : ∀ j : Fin p.k, polyNorm ((-(c • sk.t0)).get j) ≤ p.gamma2 := by
      intro j
      rw [Vector.get_eq_getElem, Vector.getElem_neg, polyNorm_neg]
      exact le_of_lt (lt_of_le_of_lt
        (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.t0) j) hct0_norm)
    -- Vector cancellations.
    have harith1 : aHat * y - c • sk.s2 + c • sk.t0 + -(c • sk.t0) = aHat * y - c • sk.s2 := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_neg]; abel
    have harith2 : aHat * y - c • sk.s2 + c • sk.s2 = aHat * y := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_add, Vector.getElem_sub]; abel
    -- The high bits are unchanged by subtracting `c·s₂`.
    have hhide : prims.highBitsVec (aHat * y - c • sk.s2) = prims.highBitsVec (aHat * y) := by
      have h := hide_lowVec p prims h_laws (aHat * y - c • sk.s2) (c • sk.s2) p.beta
        (fun j => le_trans
          (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.s2) j) hcs2_norm)
        (fun j => by
          have hj := lt_of_le_of_lt
            (LatticeCrypto.PolyVec.component_cInfNorm_le normOps
              (prims.lowBitsVec (aHat * y - c • sk.s2)) j) hr0_norm
          simp only [Primitives.lowBitsVec, Vector.get_eq_getElem, Vector.getElem_map,
            polyNorm] at hj ⊢
          omega)
      rw [harith2] at h
      exact h.symm
    -- The key-generation identity for `wApprox`.
    have hwa := keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen c y
    -- Discharge `verify`.
    simp only [identificationScheme, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hz_norm, ?_⟩, hweight⟩
    rw [hwa, useHintVec_makeHintVec p prims h_laws (-(c • sk.t0))
        (aHat * y - c • sk.s2 + c • sk.t0) hcond_t0, harith1, hhide]
  all_goals (rw [support_pure, Set.mem_singleton_iff] at hzh; exact absurd hzh (by simp))

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
    ∃ sim ζ_zk, 0 ≤ ζ_zk ∧ (identificationScheme p prims).HVZK sim ζ_zk := by
  classical
  sorry

omit [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]
/-- Commitment recoverability for ML-DSA: the public commitment `w₁` can be reconstructed
from `(pk, c̃, (z, h))` alone using `UseHint(h, Az - ct₁·2^d)`. This is the key property
enabling the CMA-to-NMA reduction in the security proof.

In our formalization, this is directly enforced by the `verify` function: it checks
`UseHint(h, w'_Approx) = w₁`, so any accepted transcript necessarily satisfies
commitment recoverability. -/
theorem idsWithAbort_commitment_recoverable :
    ∃ recover, (identificationScheme p prims).CommitmentRecoverable recover := by
  classical
  refine ⟨fun pk cTilde (z, h) =>
    prims.useHintVec h (computeWApprox p prims (prims.expandA pk.rho)
      (prims.sampleInBall cTilde) z pk.t1), ?_⟩
  rintro s w' c ⟨z, h⟩ hverify
  unfold identificationScheme at hverify
  grind

end Properties

/-! ### EUF-NMA Security (Lemma 7)

The EUF-NMA security theorem `MLDSA.nma_security` is assembled downstream in
`LatticeCrypto.MLDSA.SecurityNMA`, where the concrete MLWE key-swap distinguisher and the
SelfTargetMSIS extractor are defined. It composes the MLWE key-swap hop with the SelfTargetMSIS
extraction bound; see that file for the statement and proof. -/

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
  [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [IsUniformSpec unifSpec]

open scoped Classical in
/-- **Main Security Theorem (EUF-CMA, Theorem 4, CRYPTO 2023).**

**WARNING: this is a placeholder statement, not the final theorem.** The current shape is
unsound as written: `ε`, `p_abort`, and `δ : ℝ` are unconstrained signed reals (only
`hp : p_abort < 1` is assumed). Inherited from
`FiatShamirWithAbort.cmaToNmaLoss`, the loss term
`2qS(qH+1)ε/(1-p) + qS·ε(qS+1)/(2(1-p)²) + qS·ζ_zk + δ` can be made arbitrarily negative
by taking `ε`, `δ` very negative; `ENNReal.ofReal` then clamps it to `0`, collapsing the
bound to `adv.advantage ≤ Adv^MLWE + Adv^SelfTargetMSIS` with no statistical slack, which
is generally false. In the final statement `ε`, `p_abort`, `δ` should be nonnegative
(e.g. `ℝ≥0` or constrained by `0 ≤ ε`, `0 ≤ p_abort`, `0 ≤ δ` hypotheses) and identified
with the concrete commitment guessing probability, abort probability, and regularity
failure probability of the ML-DSA identification scheme.

The proof is intentionally deferred. The statement also needs to be specialized to the
actual ML-DSA parameters (eliminating the explicit quantitative HVZK simulator hypothesis)
once that derivation is finalized.

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
    (_hhvzk : (identificationScheme p prims).HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hp : p_abort < 1) :
    ∀ (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationScheme p prims)
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
