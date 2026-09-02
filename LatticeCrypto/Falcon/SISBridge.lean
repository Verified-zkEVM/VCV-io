/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.Security

/-! # Falcon: PSF Collisions Yield NTRU-SIS Kernel Vectors

The kernel-vector translation of the Falcon collision problem: a valid
`ntruPSFCollisionProblem` solution — two distinct `β`-short preimages with the same image
under the Falcon PSF — maps to a valid `ntruSISProblem` solution by taking the difference
of the two preimages. Nonzeroness follows from distinctness, kernel membership from
linearity of `(s₁, s₂) ↦ s₁ + s₂·h` in the preimage, and the `4·betaSquared` norm target
from the coefficientwise bound `(a − b)² ≤ 2·a² + 2·b²` on centered representatives.

## Main results

- `centeredRepr_sub_natAbs_le`: the centered representative of a difference in `ZMod q` is
  no larger in absolute value than the difference of the centered representatives.
- `pairL2NormSq_sub_le`: the squared `ℓ₂` norm of a componentwise difference is at most
  twice the sum of the squared norms.
- `negacyclicMul_sub_left`: negacyclic multiplication is linear in its left argument.
- `ntruSISProblem_isValid_sub`: the witness-level bridge — a valid collision pair yields a
  valid NTRU-SIS kernel vector at the same public key.
- `ntruSISProblemKeyed` / `collisionToKernelAdv` / `advantage_le_ntruSISProblemKeyed`: the
  NTRU-SIS problem at Falcon's honest key distribution, the adversary transform, and the
  advantage transfer. `ntruSISProblemKeyed` differs from `ntruSISProblem` only in the
  challenge distribution (honest NTRU keys versus a uniform ring element); closing that gap
  is exactly a decisional-NTRU assumption and is not formalized here.
- `euf_cma_collision_security_ntruSIS`: the attempt-level, collision-only EUF-CMA bound of
  `euf_cma_collision_security` restated with the collision term replaced by the keyed NTRU-SIS
  advantage.
- `euf_cma_security_oneShot_ntruSIS`: the one-shot bound of `euf_cma_security_oneShot`
  restated the same way.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ## Centered-representative and norm inequalities -/

/-- The centered representative of a difference is no larger in absolute value than the
difference of the centered representatives: both are representatives of the same residue
class modulo `q`, and the centered one lands in the minimal window. -/
lemma centeredRepr_sub_natAbs_le {q : ℕ} [NeZero q] (x y : ZMod q) :
    (LatticeCrypto.centeredRepr (x - y)).natAbs ≤
      (LatticeCrypto.centeredRepr x - LatticeCrypto.centeredRepr y).natAbs := by
  have hx := LatticeCrypto.centeredRepr_abs_le x
  have hy := LatticeCrypto.centeredRepr_abs_le y
  have hxy := LatticeCrypto.centeredRepr_abs_le (x - y)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set a := LatticeCrypto.centeredRepr x
  set b := LatticeCrypto.centeredRepr y
  set c := LatticeCrypto.centeredRepr (x - y)
  have hcast : ((c : ℤ) : ZMod q) = ((a - b : ℤ) : ZMod q) := by
    push_cast
    rw [← LatticeCrypto.centeredRepr_intCast (x - y), ← LatticeCrypto.centeredRepr_intCast x,
      ← LatticeCrypto.centeredRepr_intCast y]
  have hdvd : (q : ℤ) ∣ c - (a - b) :=
    ((ZMod.intCast_eq_intCast_iff _ _ _).mp hcast).symm.dvd
  obtain ⟨k, hk⟩ := hdvd
  have habs : ((q : ℤ) * k).natAbs ≤ q / 2 + (q / 2 + q / 2) := by omega
  rw [Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hkn : k.natAbs < 2 := by
    by_contra hcon
    have h2 : q * 2 ≤ q * k.natAbs := Nat.mul_le_mul (le_refl q) (Nat.le_of_not_lt hcon)
    omega
  have hk3 : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hk3 with h | h | h <;> subst h <;> omega

/-- The squared `ℓ₂` norm of a difference of Falcon ring elements is at most twice the sum
of the individual squared norms: coefficientwise, `centeredRepr_sub_natAbs_le` bounds the
difference coefficient by the integer difference, and `(a − b)² ≤ 2·a² + 2·b²`. -/
lemma polyL2NormSq_sub_le {n : ℕ} (f g : Rq n) :
    polyL2NormSq (f - g) ≤ 2 * polyL2NormSq f + 2 * polyL2NormSq g := by
  unfold polyL2NormSq normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView,
    LatticeCrypto.l2NormSqOf, LatticeCrypto.zmodCenteredCoeffView]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [LatticeCrypto.NegacyclicRing.coeff_sub]
  set av := LatticeCrypto.centeredRepr ((polyBackend n).coeff f i) with hav
  set bv := LatticeCrypto.centeredRepr ((polyBackend n).coeff g i) with hbv
  calc (LatticeCrypto.centeredRepr
          ((polyBackend n).coeff f i - (polyBackend n).coeff g i)).natAbs ^ 2
      ≤ (av - bv).natAbs ^ 2 := by
        have hle := centeredRepr_sub_natAbs_le
          ((polyBackend n).coeff f i) ((polyBackend n).coeff g i)
        exact Nat.pow_le_pow_left hle 2
    _ ≤ (av.natAbs + bv.natAbs) ^ 2 := Nat.pow_le_pow_left (Int.natAbs_sub_le av bv) 2
    _ ≤ 2 * av.natAbs ^ 2 + 2 * bv.natAbs ^ 2 := by
        zify
        nlinarith [sq_nonneg (|av| - |bv|), abs_nonneg av, abs_nonneg bv]

/-- The pair squared `ℓ₂` norm of a componentwise difference is at most twice the sum of
the pair norms. -/
lemma pairL2NormSq_sub_le {n : ℕ} (a₁ a₂ b₁ b₂ : Rq n) :
    pairL2NormSq (a₁ - b₁) (a₂ - b₂) ≤ 2 * pairL2NormSq a₁ a₂ + 2 * pairL2NormSq b₁ b₂ := by
  have h1 := polyL2NormSq_sub_le a₁ b₁
  have h2 := polyL2NormSq_sub_le a₂ b₂
  simp only [pairL2NormSq, LatticeCrypto.NormOps.pairL2NormSq, polyL2NormSq] at h1 h2 ⊢
  omega

/-! ## Linearity of the negacyclic product in the left argument -/

/-- The negacyclic convolution is linear in its left argument, summandwise. -/
lemma negacyclicConvCoeff_sub_left {R : Type*} [CommRing R] {n : ℕ}
    (f₁ f₂ g : Fin n → R) (k : Fin n) :
    LatticeCrypto.negacyclicConvCoeff (fun i => f₁ i - f₂ i) g k =
      LatticeCrypto.negacyclicConvCoeff f₁ g k - LatticeCrypto.negacyclicConvCoeff f₂ g k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs <;> ring

/-- Coefficients of a negacyclic product are the negacyclic convolution of the
coefficient functions. -/
lemma negacyclicMul_coeff {n : ℕ} (f g : Rq n) (i : Fin (polyBackend n).degree) :
    (polyBackend n).coeff (negacyclicMul f g) i =
      LatticeCrypto.negacyclicConvCoeff
        ((polyBackend n).coeff f) ((polyBackend n).coeff g) i :=
  LatticeCrypto.negacyclicMulPure_coeff (LatticeCrypto.vectorKernel Coeff n) f g i

/-- Negacyclic multiplication is linear in its left argument. -/
lemma negacyclicMul_sub_left {n : ℕ} (f₁ f₂ g : Rq n) :
    negacyclicMul (f₁ - f₂) g = negacyclicMul f₁ g - negacyclicMul f₂ g := by
  refine LatticeCrypto.NegacyclicRing.poly_ext fun i => ?_
  rw [negacyclicMul_coeff, LatticeCrypto.NegacyclicRing.coeff_sub, negacyclicMul_coeff,
    negacyclicMul_coeff, ← negacyclicConvCoeff_sub_left]
  congr 1
  funext j
  exact LatticeCrypto.NegacyclicRing.coeff_sub _ f₁ f₂ j

/-! ## The witness-level bridge -/

/-- **Collisions yield kernel vectors.** A valid solution to `ntruPSFCollisionProblem` —
two distinct `β`-short preimages with equal image — yields a valid `ntruSISProblem`
solution at the same key: the componentwise difference is nonzero (by distinctness), lies
in the kernel of `(s₁, s₂) ↦ s₁ + s₂·h` (by linearity of the negacyclic product), and has
squared `ℓ₂` norm at most `4·betaSquared` (`pairL2NormSq_sub_le`). -/
theorem ntruSISProblem_isValid_sub
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (pk : PublicKey p) (xs : (Rq p.n × Rq p.n) × (Rq p.n × Rq p.n))
    (hxs : (ntruPSFCollisionProblem p prims hr).isValid pk xs = true) :
    (ntruSISProblem p).isValid pk.h (xs.1.1 - xs.2.1, xs.1.2 - xs.2.2) = true := by
  have hcomp : ∀ u v : Rq p.n, u - v = 0 → u = v := by
    intro u v huv
    refine LatticeCrypto.NegacyclicRing.poly_ext fun i => ?_
    have hcoeff := congrArg (fun w => (polyBackend p.n).coeff w i) huv
    simp only [LatticeCrypto.NegacyclicRing.coeff_sub,
      LatticeCrypto.NegacyclicRing.coeff_zero] at hcoeff
    exact sub_eq_zero.mp hcoeff
  simp only [ntruPSFCollisionProblem, ntruSISProblem, falconPSF, Bool.and_eq_true,
    decide_eq_true_eq] at hxs ⊢
  obtain ⟨⟨⟨hne, heval⟩, hshort₁⟩, hshort₂⟩ := hxs
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- nonzero difference, from distinctness
    intro hzero
    apply hne
    have h1 : xs.1.1 - xs.2.1 = 0 := congrArg Prod.fst hzero
    have h2 : xs.1.2 - xs.2.2 = 0 := congrArg Prod.snd hzero
    exact Prod.ext (hcomp _ _ h1) (hcomp _ _ h2)
  · -- the 4·betaSquared norm target
    calc pairL2NormSq (xs.1.1 - xs.2.1) (xs.1.2 - xs.2.2)
        ≤ 2 * pairL2NormSq xs.1.1 xs.1.2 + 2 * pairL2NormSq xs.2.1 xs.2.2 :=
          pairL2NormSq_sub_le _ _ _ _
      _ ≤ 2 * p.betaSquared + 2 * p.betaSquared := by omega
      _ = 4 * p.betaSquared := by ring
  · -- kernel membership, from linearity of the evaluation map
    rw [negacyclicMul_sub_left]
    refine LatticeCrypto.NegacyclicRing.poly_ext fun i => ?_
    have hk := congrArg (fun w => (polyBackend p.n).coeff w i) (of_decide_eq_true heval)
    simp only [LatticeCrypto.NegacyclicRing.coeff_add] at hk
    simp only [LatticeCrypto.NegacyclicRing.coeff_add, LatticeCrypto.NegacyclicRing.coeff_sub,
      LatticeCrypto.NegacyclicRing.coeff_zero]
    linear_combination hk

/-! ## The keyed NTRU-SIS problem and the advantage transfer -/

/-- The NTRU-SIS problem with its challenge drawn from Falcon's honest key distribution
rather than uniformly: the validity predicate is that of `ntruSISProblem`, read through the
public key's `h` component. Relating this to the uniform-challenge `ntruSISProblem` is
exactly a decisional-NTRU assumption on `hr.gen` and is not formalized here. -/
noncomputable def ntruSISProblemKeyed
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    SIS.Problem (PublicKey p) (Rq p.n × Rq p.n) where
  sampleChallenge := do
    let (pk, _) ← hr.gen
    pure pk
  isValid pk x := (ntruSISProblem p).isValid pk.h x

/-- The collision-to-kernel adversary transform: run the collision finder and output the
componentwise difference of the two preimages. -/
noncomputable def collisionToKernelAdv
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (B : SIS.Adversary (ntruPSFCollisionProblem p prims hr)) :
    SIS.Adversary (ntruSISProblemKeyed p hr) :=
  fun pk => (fun xs => (xs.1.1 - xs.2.1, xs.1.2 - xs.2.2)) <$> B pk

/-- **Advantage transfer.** The collision-finding advantage is bounded by the keyed
NTRU-SIS advantage of the transformed adversary: both experiments draw the same honest
key, and every accepted collision maps to an accepted kernel vector
(`ntruSISProblem_isValid_sub`). -/
theorem advantage_le_ntruSISProblemKeyed
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (B : SIS.Adversary (ntruPSFCollisionProblem p prims hr)) :
    SIS.advantage (ntruPSFCollisionProblem p prims hr) B ≤
      SIS.advantage (ntruSISProblemKeyed p hr) (collisionToKernelAdv p prims hr B) := by
  have hsamp : (ntruSISProblemKeyed p hr).sampleChallenge
      = (ntruPSFCollisionProblem p prims hr).sampleChallenge := rfl
  unfold SIS.advantage SIS.experiment collisionToKernelAdv
  rw [hsamp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun pk => ?_
  gcongr
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun xs => ?_
  gcongr
  by_cases hval : (ntruPSFCollisionProblem p prims hr).isValid pk xs = true
  · have h2 : (ntruSISProblemKeyed p hr).isValid pk (xs.1.1 - xs.2.1, xs.1.2 - xs.2.2) = true :=
      ntruSISProblem_isValid_sub p prims hr pk xs hval
    rw [hval, h2]
  · rw [Bool.not_eq_true] at hval
    rw [hval]
    simp


/-! ## The EUF-CMA bound in NTRU-SIS terms -/

/-- **EUF-CMA security of Falcon down to keyed NTRU-SIS.** The bound of
`euf_cma_security_oneShot`, with the collision term translated through
`advantage_le_ntruSISProblemKeyed` into the advantage against the kernel-vector NTRU-SIS
problem at the honest key distribution. Hypotheses are exactly those of
`euf_cma_security_oneShot`. -/
theorem euf_cma_security_oneShot_ntruSIS
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash : ℕ)
    (samplerLoss : ENNReal)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p prims Salt hr))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hReg : ∃ domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n),
      ∀ pk sk, (pk, sk) ∈ support hr.gen →
        𝒮[(do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))] =
        𝒮[(do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))])
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hTransport : ∃ adv' : SignatureAlg.unforgeableAdv
        (GPVHashAndSign idealPSF hr (List Byte) Salt),
      adv.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) ≤
          adv'.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) +
            samplerLoss ∧
        (∀ ds, GPVHashAndSign.ForgesQueriedPoint idealPSF hr (List Byte) Salt adv' ds) ∧
        (∀ pk, GPVHashAndSign.signHashQueryBound
          (M := List Byte) (Salt := Salt) (Range := Rq p.n)
          (S' := Salt × (Rq p.n × Rq p.n))
          (α := List Byte × (Salt × (Rq p.n × Rq p.n))) (oa := adv'.main pk)
          (qSign := qSign) (qHash := qHash))) :
    ∃ (sisReduction : SIS.Adversary (ntruSISProblemKeyed p hr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruSISProblemKeyed p hr) sisReduction +
        ((qSign + qHash : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound Salt qSign qHash +
        samplerLoss := by
  obtain ⟨cRed, eRed, hbound⟩ := euf_cma_security_oneShot p prims Salt hr qSign qHash samplerLoss
    adv idealPSF hEval hShort hCorrect hReg hNeverFail hTransport
  refine ⟨collisionToKernelAdv p prims hr cRed, eRed, le_trans hbound ?_⟩
  gcongr
  exact advantage_le_ntruSISProblemKeyed p prims hr cRed

/-- **Falcon EUF-CMA down to keyed NTRU-SIS, with every other branch priced.**  For an
adversary against the rejection-loop signer obeying the query bound `(qSign, qHash)`, under
the per-attempt precision budget `ε_step` (`Falcon.attemptTransport`), the idealized
per-attempt rejection probability `pRej` (`Falcon.attemptRejectBound`), the attempt budget
`maxAttempts`, and the ideal-sampler guessing bound `εpp` (`Falcon.idealSamplerGuessBound`),

  `Adv^EUF-CMA(A) ≤ Adv^NTRU-SIS_keyed(B) + (qSign + qHash + 1) · εpp`
  `                 + collisionBound Salt qSign (qHash + 1)`
  `                 + qSign · (ε_step / (1 - pRej) + pRej ^ maxAttempts)`

This is `Falcon.euf_cma_collision_security` with its one remaining
cryptographic residual — the Falcon-PSF collision problem — translated through
`advantage_le_ntruSISProblemKeyed` into a kernel-vector lattice problem.  The four terms are
the lattice assumption, the min-entropy branch at the multi-target factor, the salt birthday
bound, and the sampler loss: per-attempt precision accumulated across retries plus the
attempt-budget exhaustion mass.

The challenge of `ntruSISProblemKeyed` is drawn from Falcon's honest key distribution `hr.gen`
rather than uniformly over `Rq p.n`; closing that gap to the uniform-challenge
`ntruSISProblem` is exactly a decisional-NTRU assumption and is not formalized here. -/
theorem euf_cma_collision_security_ntruSIS
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash maxAttempts : ℕ)
    (ε_step pRej : ℝ) (hε : 0 ≤ ε_step) (hRej0 : 0 ≤ pRej) (hRej1 : pRej < 1)
    (εpp : ℝ≥0∞)
    (adv : SignatureAlg.unforgeableAdv
      (falconRetrySignatureAlg p prims Salt maxAttempts hr))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hReg : ∃ domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n),
      ∀ pk sk, (pk, sk) ∈ support hr.gen →
        𝒮[(do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))] =
        𝒮[(do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))])
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hAttempt : attemptTransport p prims hr idealAttempt ε_step)
    (hRej : attemptRejectBound p hr idealAttempt pRej)
    (hRes : idealAttemptResamples p hr idealAttempt idealPSF)
    (hQ : ∀ pk, GPVHashAndSign.signHashQueryBound
      (M := List Byte) (Salt := Salt) (Range := Rq p.n)
      (S' := Salt × (Rq p.n × Rq p.n))
      (α := List Byte × (Salt × (Rq p.n × Rq p.n))) (oa := adv.main pk)
      (qSign := qSign) (qHash := qHash))
    (hGuess : idealSamplerGuessBound p hr idealPSF εpp) :
    ∃ sisReduction : SIS.Adversary (ntruSISProblemKeyed p hr),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruSISProblemKeyed p hr) sisReduction +
        ((qSign + (qHash + 1) : ℕ) : ENNReal) * εpp +
        GPVHashAndSign.collisionBound Salt qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) := by
  obtain ⟨cRed, hbound⟩ :=
    euf_cma_collision_security p prims Salt hr qSign qHash maxAttempts
      ε_step pRej hε hRej0 hRej1 εpp adv idealAttempt idealPSF hEval hShort hCorrect hReg
      hNeverFail hAttempt hRej hRes hQ hGuess
  refine ⟨collisionToKernelAdv p prims hr cRed, le_trans hbound ?_⟩
  gcongr
  exact advantage_le_ntruSISProblemKeyed p prims hr cRed


end Falcon
