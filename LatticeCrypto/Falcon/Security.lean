/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.Scheme
public import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
public import VCVio.OracleComp.Constructions.RetryLoop
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Falcon Security

This file states the security theorems for the Falcon signature scheme in the GPV hash-and-sign
model, at two granularities of the trapdoor sampler: per signing attempt, for the rejection-loop
signer, and per trapdoor draw, for the single-draw scheme.

## Scope: an idealized Falcon/GPV model

The theorems here are about an **idealized Falcon model**, precisely:

- The schemes are `falconRetrySignatureAlg` — the generic GPV hash-and-sign scheme
  (`GPVHashAndSign`) over the rejection-loop signer `falconRetryPSF`, which repeats
  `signAttempt` up to an attempt budget — and `falconSignatureAlg`, the same scheme over a
  single trapdoor draw. Signatures carry the full `(s₁, s₂)` preimage; the compressed
  `s₂`-only wire encoding and byte-level (de)serialization of FN-DSA are not modeled.
- The trapdoor sampler enters only through an ideal preimage-sampleable abstraction
  (`idealPSF`) sharing the deterministic `eval`/`isShort` of `falconPSF`. The concrete-to-ideal
  gap is a named total-variation hypothesis — `attemptTransport` per signing attempt, or
  `samplerTransport` per trapdoor draw — and floating-point `ffSampling` with its precision
  analysis is not modeled.
- Machine-checked verification correctness (`verify` accepting honest signatures) is not
  formalized here: it requires preimage-sampleable-function correctness (`s₁ + s₂ · h = c` on
  honest keys) routed through the floating-point inverse-FFT rounding in
  `Falcon.fromFFTPreimage`.
- No cost model is attached: the reductions are constructed explicitly but their polynomial
  runtime is not machine-checked. They perform no exhaustive search and no noncomputable steps
  beyond the ambient probabilistic semantics.

## The two frontiers

Both headlines are the split GPV bound (`GPVHashAndSign.euf_cma_split_bound`): the EUF-CMA
advantage is at most the Falcon-PSF collision advantage sampled from the scheme's own key
distribution (`collisionFindingAdvantage_eq_ntruPSF`), plus an exact-match branch at an
explicit multi-target factor, plus the salt birthday bound `GPVHashAndSign.collisionBound`,
plus a sampler loss.

- `euf_cma_security` is the **attempt-level** headline, for the rejection-loop signer. Its
  sampler loss is `qSign · (ε_step / (1 − pRej) + pRej ^ maxAttempts)`
  (`tvDist_falconRetryPSF_trapdoorSample_le`): the per-attempt precision budget `ε_step`
  accumulated over the expected retry count, plus the attempt-budget exhaustion mass. The
  rejection rate `pRej` is priced separately from the precision budget, so `ε_step = 0` is
  satisfiable at any rejection rate (`attemptTransport_self_zero`) and the loss stays below
  one at Falcon's query bounds (`attemptSamplerLoss_lt_falconScale`).
  `euf_cma_collision_security` discharges its exact-match branch by the ideal sampler's
  guessing bound `idealSamplerGuessBound`.
- `euf_cma_security_oneShot` is the **one-shot** headline, for the single-draw scheme, with a
  monolithic sampler loss assumed by its `hTransport` hypothesis. Read per trapdoor draw
  (`samplerTransport`, budget `ε_step`, loss `qSign · ε_step`) that budget must absorb the
  norm check's rejection probability (`oneShot_rejection_prob_le_of_samplerTransport`), so the
  loss reaches one as soon as the signing budget reaches the inverse rejection rate
  (`oneShot_samplerLoss_one_le_of_samplerTransport`); at Falcon's parameters this frontier
  carries no quantitative content.

`LatticeCrypto.Falcon.NonVacuity` instantiates the attempt-level hypotheses at an NTRU key with
a genuinely rejecting sampler, where the attempt-level loss is below `1/2` at `qSign = 2^64`
while every per-draw budget is forced to at least `1/2`.

## Relation to the literature

[FGdG+25] Theorem 1 bounds Falcon+ by a Rényi-divergence accumulation of the per-query sampler
and random-oracle simulation gaps over all preimage-sampling calls including retries; [Jia+26]
sharpens the per-basis divergence, and [TWFalcon] measures the floating-point precision the
sampler actually achieves. The theorems here replace the Rényi accumulation by a
total-variation accumulation of a named per-attempt gap, take the salt term as the birthday
bound of GPV08 Proposition 6.2 rather than [FGdG+25]'s `Q_s · (C_s + Q_H) / 2^k`, and formalize
no concrete bit-security figure.

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769, updated 2025. First concrete security proof for Falcon+.
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Basis-specific analysis eliminating the 7-bit loss.
- [TWFalcon]: Halmans et al. "TWFalcon: Triple-Word Arithmetic for Falcon."
  ePrint 2025/1991. Shows binary64 misses the published Rényi threshold.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- [Pre17]: Prest. ASIACRYPT 2017. Rényi-based precision analysis for Klein's sampler.
-/

@[expose] public section


open OracleComp OracleSpec ENNReal

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### NTRU-SIS Hardness Assumption -/

/-- The NTRU-SIS problem: given `h ∈ R_q` (the Falcon public key), find a short nonzero
`(s₁, s₂) ∈ R_q²` satisfying `s₁ + s₂ · h = 0 mod q` with `‖(s₁, s₂)‖₂² ≤ 4·⌊β²⌋`.

This is the lattice problem underlying Falcon's security. It is an instance of
the generic SIS problem where the matrix is the single-row matrix `[I | h]`
over the cyclotomic ring `R_q = ℤ_q[x]/(x^n + 1)`.

The norm target is `4·betaSquared`, not `betaSquared`: a kernel vector produced from a
Falcon-PSF collision is the difference `x - x'` of two `β`-short preimages, so its squared
`ℓ₂` norm is at most `(‖x‖₂ + ‖x'‖₂)² ≤ (2β)² = 4·betaSquared`. The
`ntruPSFCollisionProblem → ntruSISProblem` translation realizing this target is
`Falcon.ntruSISProblem_isValid_sub` (witness level) and
`Falcon.advantage_le_ntruSISProblemKeyed` / `Falcon.euf_cma_security_oneShot_ntruSIS` (advantage
level, at the honest key distribution `ntruSISProblemKeyed`) in
`LatticeCrypto.Falcon.SISBridge`; the remaining distance between the honest key
distribution and this problem's uniform challenge is a decisional-NTRU assumption. -/
noncomputable def ntruSISProblem :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := $ᵗ (Rq p.n)
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ 4 * p.betaSquared) &&
    decide (x.1 + negacyclicMul x.2 h = 0)

/-- The direct Falcon PSF collision problem induced by the generic GPV reduction.

The challenger samples a Falcon public key from the same key distribution used by the
signature scheme, and the adversary must produce two distinct short preimages with the
same image under the Falcon PSF `(s₁, s₂) ↦ s₁ + s₂ · h`.

This is the immediate hardness target of the collision-style GPV bound before any further
translation to a kernel-vector NTRU-SIS formulation. -/
noncomputable def ntruPSFCollisionProblem
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    SIS.Problem (PublicKey p) ((Rq p.n × Rq p.n) × (Rq p.n × Rq p.n)) where
  sampleChallenge := do
    let (pk, _) ← hr.gen
    pure pk
  isValid pk xs :=
    decide (xs.1 ≠ xs.2) &&
    decide ((falconPSF p prims).eval pk xs.1 = (falconPSF p prims).eval pk xs.2) &&
    (falconPSF p prims).isShort xs.1 &&
    (falconPSF p prims).isShort xs.2

/-! ### EUF-CMA Security -/

/-- The Falcon-PSF collision experiment **is** the `ntruPSFCollisionProblem` search experiment.

For any preimage-sampleable function `psf` that shares the deterministic image map (`eval`) and
shortness predicate (`isShort`) with the concrete Falcon PSF, the keyed GPV collision-finding
advantage equals the SIS advantage against `ntruPSFCollisionProblem`: both sample a key from
`hr.gen`, run the adversary, and accept on two distinct short preimages with equal image. Only the
trapdoor sampler differs between `psf` and `falconPSF`, and the collision experiment never invokes
it, so the equality holds for any such `psf`. This bridge turns the abstract GPV collision branch
into the Falcon NTRU-SIS hardness target. -/
theorem collisionFindingAdvantage_eq_ntruPSF
    [SampleableType (Rq p.n)]
    (psf : PreimageSampleableFunction (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (hEval : ∀ pk x, psf.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, psf.isShort x = (falconPSF p prims).isShort x)
    (B : GPVHashAndSign.CollisionAdversary (PK := PublicKey p) (Domain := Rq p.n × Rq p.n)) :
    GPVHashAndSign.collisionFindingAdvantage psf hr B
      = SIS.advantage (ntruPSFCollisionProblem p prims hr) B := by
  simp only [GPVHashAndSign.collisionFindingAdvantage, GPVHashAndSign.collisionFindingExp,
    SIS.advantage, SIS.experiment, ntruPSFCollisionProblem, hEval, hShort, bind_assoc, pure_bind]

/-- **One-shot EUF-CMA security of Falcon**, generic in the salt type `Salt`: the split GPV
bound for the single-draw scheme `falconSignatureAlg`, with the sampler loss assumed
monolithically. The attempt-level headline `euf_cma_security` is the quantitatively usable
form; see the module docstring.

For any EUF-CMA adversary `A` making at most `qSign` signing queries and `qHash`
random-oracle queries against the Falcon+ signature scheme with salt type `Salt`, and
any transport bound `ε_sampler` on the concrete-to-ideal sampler swap (the
`hTransport` hypothesis), there exist:

- a collision reduction `B_coll` for the distinct-preimage branch,
- a programmed-preimage replay reduction `B_exact` for the exact-match branch,

such that:

  `Adv^{EUF-CMA}_{Falcon+}(A)`
  `  ≤ Adv^{collision}_{Falcon-PSF}(B_coll)`
  `    + (qSign + qHash) · Adv^{exact-match}_{Falcon-PSF}(B_exact)`
  `    + (qSign + qHash)² / (2 · |Salt|) + ε_sampler`

### Error terms

**Term 1: `Adv^{collision}_{Falcon-PSF}(B)`.**
The GPV reduction is tight on the distinct-preimage branch: `B` runs `A` internally with
a simulated signing oracle (sign-then-hash strategy) and extracts two distinct short
Falcon preimages for the same programmed random-oracle value. There is no `Q_hash` loss
factor in this collision-style target.

**Term 2: `(qSign + qHash) · Adv^{exact-match}_{Falcon-PSF}(B_exact)`.**
The explicit multi-target loss for the exact-match branch. The reduction guesses one of
the programmed random-oracle entries and tries to show that reproducing the simulator's
hidden short preimage there is hard.

**Term 3: `(qSign + qHash)² / (2 · |Salt|)`.**
Salt collision probability over every salt appearing in a signing query or a
random-oracle query, bounded by the birthday paradox. This is a simplified form of the
`Q_s · (C_s + Q_H) / 2^k` term from [FGdG+25] Theorem 1.

**Term 4: `ε_sampler`.**
The sampler loss, assumed by `hTransport` as the cost of swapping the concrete signing oracle
for the ideal one. It stands in for the Rényi-divergence term of [FGdG+25] Theorem 1 but is
not derived from it; read per trapdoor draw it is `qSign · ε_step` for a `samplerTransport`
budget `ε_step`, and `oneShot_samplerLoss_one_le_of_samplerTransport` shows that reading is
vacuous at Falcon's query budget.

### Proof structure

1. The generic GPV split bound (`GPVHashAndSign.euf_cma_split_bound`) which reduces EUF-CMA to
   a collision branch, an exact-match replay branch with explicit factor `qSign + qHash`,
   and a birthday collision term.
2. Reinterpret the collision branch as an adversary for the Falcon PSF collision problem
   sampled from the same key distribution (`collisionFindingAdvantage_eq_ntruPSF`).
3. Leave the exact-match branch explicit in the theorem statement until it is discharged by
   a Falcon-specific min-entropy / one-way lemma.
4. Account for finite precision via the `hTransport` sampler-transport hypothesis.

**On the GPV laws (`hCorrect`/`hReg`/`hNeverFail`).** These are taken on the support of `hr.gen`
(honestly generated keys) only, via the valid-key-restricted `GPVHashAndSign.euf_cma_split_bound`.
The universal forms would be *unsatisfiable* for the Falcon PSF — `isShort` is the norm bound
`‖·‖₂² ≤ betaSquared`, `PublicKey` is unconstrained, and a key with `h = 0` together with a
large-norm target `c` (`‖c‖² > betaSquared`) has no short preimage — so no sampler could be both
correct and total at *every* key. Restricting to `support hr.gen` (where the NTRU geometry of a
valid key guarantees short preimages — the honest-key regime in which Falcon signatures verify)
makes the hypotheses satisfiable, so this theorem is conditional, not vacuous. The ideal sampler
`idealPSF` shares the deterministic `eval`/`isShort` of `falconPSF` (`hEval`/`hShort`); `hTransport`
carries the finite-precision concrete→ideal gap as the monolithic loss `samplerLoss`, assumed here
in the same way MLWE/SIS hardness is assumed. The collision branch is discharged by
`collisionFindingAdvantage_eq_ntruPSF`. -/
theorem euf_cma_security_oneShot
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash : ℕ)
    (samplerLoss : ENNReal)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p prims Salt hr))
    -- Ideal preimage-sampleable abstraction (truncated discrete Gaussian over the NTRU coset):
    -- same deterministic `eval`/`isShort` as `falconPSF`, GPV laws on honest keys only.
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
    -- Finite-precision sampler transport ([FGdG+25] Rényi term): swapping the concrete signing
    -- oracle for the ideal one costs at most `samplerLoss` and yields a well-behaved ideal-scheme
    -- adversary. Assumed here as a single transport hypothesis; decomposing it into a
    -- per-call sampler-approximation bound with a proven adaptive accumulation is the
    -- intended refinement.
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
    ∃ (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction +
        ((qSign + qHash : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound Salt qSign qHash +
        samplerLoss := by
  obtain ⟨adv', hAdvLe, hForge', hQ'⟩ := hTransport
  obtain ⟨cRed, eRed, hsplit⟩ :=
    GPVHashAndSign.euf_cma_split_bound (psf := idealPSF) (hr := hr)
      (M := List Byte) (Salt := Salt) hCorrect hReg qSign qHash adv'
      hNeverFail hForge' hQ'
  refine ⟨cRed, eRed, ?_⟩
  have hbridge :
      GPVHashAndSign.collisionFindingAdvantage idealPSF hr cRed
        = SIS.advantage (ntruPSFCollisionProblem p prims hr) cRed :=
    collisionFindingAdvantage_eq_ntruPSF p prims idealPSF hr hEval hShort cRed
  rw [← hbridge]
  exact le_trans hAdvLe (by gcongr)

/-- Concrete instantiation of `euf_cma_security_oneShot` with the Falcon-specified 40-byte
(320-bit) salt.

The collision term specializes to `(qSign + qHash)² / (2 · 2^320)`. For the Falcon-specified
maximum of `qSign, qHash ≤ 2^64`, this is `≤ 2^{-191}`. -/
theorem euf_cma_security_oneShot_bytes40
    [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash : ℕ)
    (samplerLoss : ENNReal)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p prims (Bytes 40) hr))
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
        (GPVHashAndSign idealPSF hr (List Byte) (Bytes 40)),
      adv.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) (Bytes 40)) ≤
          adv'.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) (Bytes 40)) +
            samplerLoss ∧
        (∀ ds, GPVHashAndSign.ForgesQueriedPoint idealPSF hr (List Byte) (Bytes 40) adv' ds) ∧
        (∀ pk, GPVHashAndSign.signHashQueryBound
          (M := List Byte) (Salt := Bytes 40) (Range := Rq p.n)
          (S' := Bytes 40 × (Rq p.n × Rq p.n))
          (α := List Byte × (Bytes 40 × (Rq p.n × Rq p.n))) (oa := adv'.main pk)
          (qSign := qSign) (qHash := qHash))) :
    ∃ (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) (Bytes 40)) ≤
        SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction +
        ((qSign + qHash : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound (Bytes 40) qSign qHash +
        samplerLoss :=
  euf_cma_security_oneShot p prims (Bytes 40) hr qSign qHash samplerLoss adv
    idealPSF hEval hShort hCorrect hReg hNeverFail hTransport

/-! ### Per-call sampler transport

`euf_cma_security_oneShot` assumes the concrete-to-ideal sampler swap as the single monolithic
`hTransport` package.  `samplerTransport` names the *per-call* finite-precision
sampler-approximation bound that a decomposition of it would rest on, read against a single
trapdoor draw.

Read against a single draw the budget is not usable at Falcon's parameters: on honest keys it
dominates the whole per-attempt rejection probability of the norm check
(`oneShot_rejection_prob_le_of_samplerTransport`), so the accumulated loss `qSign · ε_step`
reaches one as soon as the signing budget reaches the inverse rejection rate
(`oneShot_samplerLoss_one_le_of_samplerTransport`).  The frontier that carries quantitative
content is the attempt-level one below, where `attemptTransport` compares whole signing
attempts and the rejection rate is priced separately. -/

/-- **Per-call sampler-approximation bound** ([FGdG+25]'s per-query Rényi term `r_p`, read
here at total-variation distance): on every honestly generated key pair and every hash
target `c`, the concrete Falcon trapdoor sampler (`ffSampling` over floating-point
arithmetic) and the ideal sampler are within total-variation distance `ε_step`.

The total-variation form is chosen because it is what the adaptive accumulation tool
(`OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_queryBoundP_mul`) consumes
per signing step; a Boolean-distinguisher formulation is interderivable but composes less
directly.  Honest-key scoping matches `hCorrect`/`hNeverFail`: the sampler geometry is
only meaningful where the NTRU basis is valid.

On honest keys every admissible `ε_step` is at least the per-draw rejection probability of
Falcon's norm check (`oneShot_rejection_prob_le_of_samplerTransport`), whatever the sampler's
precision: `hCorrect` confines the ideal side to short outputs while
`falconPSF.trapdoorSample` carries no norm check, so the two sides are conditioned
differently.  `ε_step = 1` is always admissible (`samplerTransport_one`); `ε_step = 0` would
force the concrete sampler to accept every draw (`samplerTransport_zero_forces_accept`).  The
quantitatively usable hypothesis is the attempt-level `attemptTransport` below. -/
def samplerTransport
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (ε_step : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    tvDist ((falconPSF p prims).trapdoorSample pk sk c)
      (idealPSF.trapdoorSample pk sk c) ≤ ε_step

/-- The trivial witness for the per-call sampler transport: total-variation distance never
exceeds one, so `ε_step = 1` is always admissible. -/
theorem samplerTransport_one
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n)) :
    samplerTransport p prims hr idealPSF 1 :=
  fun _pk _sk _h _c => tvDist_le_one _ _

/-! ### Ideal-sampler min-entropy

The exact-match (programmed-preimage) term of the decomposed frontier is controlled by the
*guessing probability* of the ideal trapdoor sampler
(`GPVHashAndSign.programmedPreimageAdvantage_le_of_probOutput_trapdoorSample_le`).
`idealSamplerGuessBound` names the per-call pointwise-mass bound; it is discharged into the
collision-only headline by `euf_cma_collision_security`, leaving the
NTRU-PSF collision problem as the only cryptographic residual besides the named
assumptions. -/

/-- **Per-call guessing-probability (min-entropy) bound for the ideal trapdoor sampler**: on
every honestly generated key pair and every hash target `c`, no single preimage carries more
than `εpp` of the ideal sampler's output mass — equivalently, the sampler has min-entropy at
least `log₂ (1/εpp)` at every honest key and target.

For the ideal (exact-arithmetic) discrete Gaussian over the NTRU lattice coset — the sampler
GPV08 and [FGdG+25] analyze — the literature value is `εpp = 2^(-H∞)` of the coset Gaussian
`D_{Λ+c,σ}`, and GPV08 Lemma 2.10 gives `H∞ ≥ n - 1` bits once `σ` exceeds the smoothing
parameter of the lattice, so `εpp` is negligible at Falcon parameters (`n = 512` / `1024`).
The formal discharge of a concrete numeric `εpp` awaits a discrete-Gaussian pointwise-mass
theory: `LatticeCrypto.DiscreteGaussian` currently provides the one-dimensional
`discreteGaussianPMF` with positivity and normalization but no pointwise *upper* bound.
Missing are (i) a max-mass lemma
`discreteGaussianPMF σ μ z ≤ discreteGaussianWeight σ μ ⌊μ⌉ / discreteGaussianSum σ μ`
with a quantitative lower bound on `discreteGaussianSum σ μ` (e.g. `≥ σ√(2π) - 1` by integral
comparison), and (ii) their lift to the `2n`-dimensional coset Gaussian over the NTRU lattice
via the smoothing-parameter bound (GPV08 Lemma 2.10).  Until then this remains a named
assumption with inspectable content; it is trivially satisfiable at `εpp = 1`
(`idealSamplerGuessBound_one`), since pointwise masses of any sampler are probabilities. -/
def idealSamplerGuessBound
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (εpp : ℝ≥0∞) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
    Pr[= x | idealPSF.trapdoorSample pk sk c] ≤ εpp

/-- The trivial witness for the guessing-probability bound: pointwise output masses of any
sampler never exceed one, so `εpp = 1` is always admissible. -/
theorem idealSamplerGuessBound_one
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n)) :
    idealSamplerGuessBound p hr idealPSF 1 :=
  fun _pk _sk _h _c _x => probOutput_le_one

/-! ## Falcon's rejection loop: attempt-level sampler transport

Falcon's signer is a rejection loop: `Falcon.signAttempt` draws a trapdoor preimage and returns
it only when the norm check `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` passes, retrying otherwise.  This section
prices the concrete-to-ideal sampler swap at that granularity.

`oneShot_rejection_prob_le_of_samplerTransport` records why the granularity matters: a budget
stated on a *single* trapdoor draw against a `hCorrect`/`hNeverFail` ideal sampler dominates the
whole per-attempt rejection probability, because the ideal side accepts every draw.

The attempt-level frontier separates the two costs, following [FGdG+25] Theorem 1, which
accounts over `C_s` sampling calls *including* retries and carries the per-attempt acceptance
probability explicitly:

* `attemptTransport ε_step` — the finite-precision gap between Falcon's attempt and an
  idealized attempt, both of which may reject, so `ε_step` measures precision alone;
* `attemptRejectBound pRej` — the idealized per-attempt rejection probability;
* `idealAttemptResamples` — the idealized attempt is a rejection sampler for the reject-free
  `idealPSF` that the GPV bounds consume (`ProbComp.ResamplesTo`).

`tvDist_falconRetryPSF_trapdoorSample_le` combines them into
`ε_step / (1 - pRej) + pRej ^ maxAttempts` — approximation error accumulated across retries plus
the attempt-budget exhaustion mass — and `euf_cma_security` carries that as
the sampler loss. -/

/-- **A one-shot transport budget dominates the rejection probability.**  On honest keys,
`hCorrect` and `hNeverFail` make the ideal sampler accept every draw, so total-variation
closeness to it charges `ε_step` for the entire mass on which Falcon's norm check fails. -/
theorem oneShot_rejection_prob_le_of_samplerTransport [SampleableType (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (ε_step : ℝ)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hStep : samplerTransport p prims hr idealPSF ε_step)
    (pk : PublicKey p) (sk : SecretKey p) (hmem : (pk, sk) ∈ support hr.gen)
    (c : Rq p.n) :
    1 - Pr[ fun x => (falconPSF p prims).isShort x = true
          | (falconPSF p prims).trapdoorSample pk sk c].toReal ≤ ε_step := by
  classical
  set f : Rq p.n × Rq p.n → Bool := fun x => (falconPSF p prims).isShort x with hf
  have hideal : Pr[= true | (f <$> idealPSF.trapdoorSample pk sk c : ProbComp Bool)] = 1 := by
    rw [← probEvent_eq_eq_probOutput, probEvent_map]
    refine probEvent_eq_one ⟨?_, fun x hx => ?_⟩
    · have := hNeverFail pk sk hmem c
      exact probFailure_eq_zero (mx := idealPSF.trapdoorSample pk sk c)
    · have hx' := (hCorrect pk sk hmem c x hx).2
      simpa [hf, Function.comp, ← hShort x] using hx'
  have hmap : tvDist (f <$> (falconPSF p prims).trapdoorSample pk sk c)
      (f <$> idealPSF.trapdoorSample pk sk c) ≤ ε_step :=
    le_trans (tvDist_map_le f _ _) (hStep pk sk hmem c)
  have habs := abs_probOutput_toReal_sub_le_tvDist
    (f <$> (falconPSF p prims).trapdoorSample pk sk c)
    (f <$> idealPSF.trapdoorSample pk sk c)
  rw [hideal, ENNReal.toReal_one] at habs
  have hconc : Pr[= true | (f <$> (falconPSF p prims).trapdoorSample pk sk c : ProbComp Bool)]
      = Pr[ fun x => (falconPSF p prims).isShort x = true
            | (falconPSF p prims).trapdoorSample pk sk c] := by
    rw [← probEvent_eq_eq_probOutput, probEvent_map]; rfl
  rw [hconc] at habs
  linarith [le_trans habs hmap, (abs_le.mp habs).1]

/-- **Falcon's signer as a preimage-sampleable function.**  The norm-checked attempt
`Falcon.signAttempt` retried up to `maxAttempts` times, read as a total computation by
`ProbComp.retryToDefault`.  The deterministic `eval` and `isShort` components are those of
`falconPSF`, so the collision and verification theory transfers verbatim. -/
noncomputable def falconRetryPSF [Inhabited (Rq p.n)] (maxAttempts : ℕ) :
    PreimageSampleableFunction (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval := (falconPSF p prims).eval
  trapdoorSample pk sk c := ProbComp.retryToDefault (signAttempt p prims pk sk c) maxAttempts
  isShort := (falconPSF p prims).isShort

/-- The Falcon signature scheme over the rejection-loop signer: the GPV hash-and-sign
construction at `falconRetryPSF`. -/
noncomputable def falconRetrySignatureAlg [Inhabited (Rq p.n)]
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt]
    [SampleableType (Rq p.n)] [DecidableEq (Rq p.n)]
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    SignatureAlg (OracleComp (unifSpec + (Salt × List Byte →ₒ Rq p.n)))
      (M := List Byte) (PK := PublicKey p) (SK := SecretKey p)
      (S := Salt × (Rq p.n × Rq p.n)) :=
  GPVHashAndSign (falconRetryPSF p prims maxAttempts) hr (List Byte) Salt

/-- **Per-attempt sampler approximation.**  On honestly generated keys and at every hash
target, Falcon's rejection-sampling attempt and an idealized attempt are within
total-variation distance `ε_step`.  Both sides may reject, so `ε_step` prices only the
finite-precision gap; the rejection rate itself is carried by `attemptRejectBound`. -/
def attemptTransport
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (ε_step : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    tvDist (signAttempt p prims pk sk c) (idealAttempt pk sk c) ≤ ε_step

/-- **Per-attempt rejection probability of the idealized attempt.**  This is `1 - p` for the
acceptance probability `p` of [FGdG+25] Theorem 1. -/
def attemptRejectBound
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (pRej : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    Pr[= none | idealAttempt pk sk c].toReal ≤ pRej

/-- **The idealized attempt is a rejection sampler for the ideal PSF.**  Replacing a rejection
by a fresh draw from `idealPSF.trapdoorSample` reproduces its law, so the accepted outputs of
the attempt are exactly the ideal sampler conditioned on acceptance. -/
def idealAttemptResamples
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n)) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    ProbComp.ResamplesTo (idealAttempt pk sk c) (idealPSF.trapdoorSample pk sk c)

/-- **The rejection loop transports at attempt granularity.**  Falcon's retry signer is within
`ε_step / (1 - pRej) + pRej ^ maxAttempts` of the reject-free ideal sampler: the per-attempt
precision gap accumulated geometrically across retries
(`ProbComp.tvDist_retryToDefault_le_div`), plus the attempt-budget exhaustion mass
(`ProbComp.tvDist_retryToDefault_le_pow`).

Unlike a one-shot budget (`oneShot_rejection_prob_le_of_samplerTransport`), neither summand
contains the rejection probability as an additive term: `pRej` enters only through the
retry-count factor `1 / (1 - pRej)` and the exhaustion power `pRej ^ maxAttempts`. -/
theorem tvDist_falconRetryPSF_trapdoorSample_le [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (ε_step pRej : ℝ) (maxAttempts : ℕ)
    (hStep : attemptTransport p prims hr idealAttempt ε_step)
    (hRej : attemptRejectBound p hr idealAttempt pRej)
    (hRes : idealAttemptResamples p hr idealAttempt idealPSF)
    (hRej0 : 0 ≤ pRej) (hRej1 : pRej < 1)
    (pk : PublicKey p) (sk : SecretKey p) (hmem : (pk, sk) ∈ support hr.gen)
    (c : Rq p.n) :
    tvDist ((falconRetryPSF p prims maxAttempts).trapdoorSample pk sk c)
        (idealPSF.trapdoorSample pk sk c)
      ≤ ε_step / (1 - pRej) + pRej ^ maxAttempts := by
  refine le_trans (tvDist_triangle _
    (ProbComp.retryToDefault (idealAttempt pk sk c) maxAttempts) _) (add_le_add ?_ ?_)
  · exact ProbComp.tvDist_retryToDefault_le_div _ _ (hStep pk sk hmem c) (hRej pk sk hmem c)
      hRej0 hRej1 maxAttempts
  · exact ProbComp.tvDist_retryToDefault_le_pow _ _ (hRes pk sk hmem c) (hRej pk sk hmem c)
      hRej0 maxAttempts


/-- **EUF-CMA security of the Falcon rejection-loop signer from the attempt-level frontier.**
The split GPV bound for any query-bounded adversary against `falconRetrySignatureAlg`, with the
sampler loss `qSign · (ε_step / (1 - pRej) + pRej ^ maxAttempts)` derived from the per-attempt
precision budget `ε_step`, the idealized per-attempt rejection probability `pRej`, and the
attempt budget `maxAttempts` (`tvDist_falconRetryPSF_trapdoorSample_le`).

The three cryptographic terms are those of `euf_cma_security_oneShot`:
the NTRU-PSF collision problem, the exact-match branch at the multi-target factor
`qSign + qHash + 1`, and the salt birthday bound.  The sampler loss differs in that the
per-attempt rejection probability appears only through the expected retry count
`1 / (1 - pRej)` and the exhaustion power `pRej ^ maxAttempts`, so a precision budget
`ε_step ≪ 1 / qSign` and an attempt budget with `pRej ^ maxAttempts ≪ 1 / qSign` keep the term
below one at Falcon's query bounds. -/
theorem euf_cma_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [SampleableType (Rq p.n)] [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash maxAttempts : ℕ)
    (ε_step pRej : ℝ) (hε : 0 ≤ ε_step) (hRej0 : 0 ≤ pRej) (hRej1 : pRej < 1)
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
      (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction +
        ((qSign + (qHash + 1) : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound Salt qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) := by
  obtain ⟨cRed, eRed, hsplit⟩ :=
    GPVHashAndSign.euf_cma_split_bound_of_queryBound (psf := idealPSF) (hr := hr)
      (M := List Byte) (Salt := Salt) hCorrect hReg qSign qHash ⟨adv.main⟩
      hNeverFail hQ
  refine ⟨cRed, eRed, ?_⟩
  have hbridge :
      GPVHashAndSign.collisionFindingAdvantage idealPSF hr cRed
        = SIS.advantage (ntruPSFCollisionProblem p prims hr) cRed :=
    collisionFindingAdvantage_eq_ntruPSF p prims idealPSF hr hEval hShort cRed
  rw [← hbridge]
  have hlt : (0 : ℝ) < 1 - pRej := by linarith
  have hεtot : 0 ≤ ε_step / (1 - pRej) + pRej ^ maxAttempts :=
    add_nonneg (div_nonneg hε (le_of_lt hlt)) (pow_nonneg hRej0 maxAttempts)
  have hAdvLe :
      adv.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) ≤
        (⟨adv.main⟩ : SignatureAlg.unforgeableAdv
            (GPVHashAndSign idealPSF hr (List Byte) Salt)).advantage
            (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) +
          ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) :=
    GPVHashAndSign.advantage_le_advantage_add_of_trapdoorSample_tvDist
      (falconRetryPSF p prims maxAttempts) idealPSF hr (List Byte) Salt
      (fun pk x => (hEval pk x).symm) (fun x => (hShort x).symm) hεtot
      (fun pk sk hmem c => tvDist_falconRetryPSF_trapdoorSample_le p prims hr idealAttempt
        idealPSF ε_step pRej maxAttempts hAttempt hRej hRes hRej0 hRej1 pk sk hmem c)
      qSign adv (fun pk => (hQ pk).1)
  exact le_trans hAdvLe (by gcongr)


/-! ### The precision budget is decoupled from the rejection rate

The two lemmas below isolate what the attempt-level granularity buys.  At a one-shot budget,
`ε_step = 0` forces Falcon's norm check to accept with probability one
(`samplerTransport_zero_forces_accept`), so a rejection loop is incompatible with a small
budget.  At attempt granularity, `ε_step = 0` is satisfiable at *any* rejection rate
(`attemptTransport_self_zero`), and the rejection rate is instead carried by `pRej` through the
retry-count factor and the exhaustion power. -/

/-- A vanishing one-shot transport budget forces the concrete sampler to accept every draw. -/
theorem samplerTransport_zero_forces_accept [SampleableType (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hStep : samplerTransport p prims hr idealPSF 0)
    (pk : PublicKey p) (sk : SecretKey p) (hmem : (pk, sk) ∈ support hr.gen)
    (c : Rq p.n) :
    Pr[ fun x => (falconPSF p prims).isShort x = true
      | (falconPSF p prims).trapdoorSample pk sk c] = 1 := by
  have h := oneShot_rejection_prob_le_of_samplerTransport p prims hr idealPSF 0
    hShort hCorrect hNeverFail hStep pk sk hmem c
  refine one_le_probEvent_iff.mp ?_
  rw [← ENNReal.toReal_le_toReal ENNReal.one_ne_top probEvent_ne_top, ENNReal.toReal_one]
  linarith

/-- At attempt granularity a vanishing precision budget is satisfiable whatever the norm check
rejects: Falcon's own attempt is an idealized attempt at `ε_step = 0`. -/
theorem attemptTransport_self_zero
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    attemptTransport p prims hr (signAttempt p prims) 0 :=
  fun _pk _sk _hmem _c => le_of_eq (tvDist_self _)

/-- **Collision-only EUF-CMA security of the Falcon rejection-loop signer.**
`euf_cma_security` with the exact-match branch discharged by the ideal
sampler's guessing-probability bound `hGuess`
(`GPVHashAndSign.programmedPreimageAdvantage_le_of_probOutput_trapdoorSample_le`), leaving the
NTRU-PSF collision problem as the only cryptographic residual besides the named assumptions. -/
theorem euf_cma_collision_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [SampleableType (Rq p.n)] [Inhabited (Rq p.n)]
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
    ∃ collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction +
        ((qSign + (qHash + 1) : ℕ) : ENNReal) * εpp +
        GPVHashAndSign.collisionBound Salt qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) := by
  obtain ⟨cRed, eRed, hbound⟩ :=
    euf_cma_security p prims Salt hr qSign qHash maxAttempts ε_step pRej
      hε hRej0 hRej1 adv idealAttempt idealPSF hEval hShort hCorrect hReg hNeverFail
      hAttempt hRej hRes hQ
  refine ⟨cRed, le_trans hbound ?_⟩
  gcongr
  exact GPVHashAndSign.programmedPreimageAdvantage_le_of_probOutput_trapdoorSample_le
    idealPSF hr eRed hGuess


/-! ### The two loss regimes, quantitatively

`oneShot_samplerLoss_one_le_of_samplerTransport` turns the forcing of
`oneShot_rejection_prob_le_of_samplerTransport` into a statement about the loss *term*: at a
one-shot budget the sampler loss `qSign · ε_step` reaches one as soon as the signing budget
reaches the inverse of the per-attempt rejection rate — the rate whose existence is the reason
the signer retries at all.

`attemptSamplerLoss_lt_falconScale` exhibits the attempt-level term at Falcon-scale numbers:
a signing budget of `2^64`, a per-attempt precision gap of `2^-80`, a per-attempt rejection
probability of `1/2`, and an attempt budget of `128` give a loss below `2^-14`.  The rejection
probability is deliberately taken far above any realistic Falcon value, to show that the term
is controlled by the precision gap and the attempt budget rather than by the rejection rate. -/

/-- The one-shot sampler loss reaches one once the signing budget reaches the inverse rejection
rate. -/
theorem oneShot_samplerLoss_one_le (qSign : ℕ) (rejRate ε_step : ℝ)
    (hRate : rejRate ≤ ε_step) (hq : 1 ≤ (qSign : ℝ) * rejRate) :
    (1 : ℝ) ≤ (qSign : ℝ) * ε_step :=
  le_trans hq (mul_le_mul_of_nonneg_left hRate (Nat.cast_nonneg qSign))

/-- **The one-shot sampler loss is vacuous at Falcon's query budget.**  Combining the forcing of
`oneShot_rejection_prob_le_of_samplerTransport` with `oneShot_samplerLoss_one_le`: whenever the
signing budget times the per-attempt rejection probability of Falcon's norm check reaches one,
so does the loss term `qSign · ε_step` of a one-shot transport frontier — whatever the sampler's
actual precision. -/
theorem oneShot_samplerLoss_one_le_of_samplerTransport [SampleableType (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (qSign : ℕ) (ε_step : ℝ)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hStep : samplerTransport p prims hr idealPSF ε_step)
    (pk : PublicKey p) (sk : SecretKey p) (hmem : (pk, sk) ∈ support hr.gen)
    (c : Rq p.n)
    (hq : 1 ≤ (qSign : ℝ) *
      (1 - Pr[ fun x => (falconPSF p prims).isShort x = true
             | (falconPSF p prims).trapdoorSample pk sk c].toReal)) :
    (1 : ℝ) ≤ (qSign : ℝ) * ε_step :=
  oneShot_samplerLoss_one_le qSign _ ε_step
    (oneShot_rejection_prob_le_of_samplerTransport p prims hr idealPSF ε_step
      hShort hCorrect hNeverFail hStep pk sk hmem c) hq

/-- The attempt-level sampler loss at Falcon-scale parameters: signing budget `2^64`,
per-attempt precision gap `2^-80`, per-attempt rejection probability `1/2`, attempt budget
`128`. -/
theorem attemptSamplerLoss_lt_falconScale :
    (2 ^ 64 : ℝ) * ((1 / 2 ^ 80 : ℝ) / (1 - 1 / 2) + (1 / 2 : ℝ) ^ 128) < 1 / 2 ^ 14 := by
  norm_num


end Falcon
