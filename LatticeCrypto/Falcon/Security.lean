/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Scheme
import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
import VCVio.EvalDist.RenyiDivergence

/-!
# Falcon Security

This file states the high-level security theorems for the Falcon signature scheme.

## Correctness

`verify(pk, m, sign(sk, m)) = true` whenever:
1. The key pair is valid (NTRU equation holds, `h = g · f⁻¹ mod q`).
2. Signing does not abort (norm check passes, compression succeeds).

## EUF-CMA Security

The main security theorem reduces EUF-CMA to the NTRU-SIS problem. The precise
bound follows [FGdG+25] Theorem 1 (first concrete proof for Falcon+), refined by
[Jia+26] (basis-specific Rényi analysis that eliminates the 7-bit security loss).

### The exact theorem ([FGdG+25] Theorem 1, adapted)

For adversary `A` making `Q_s` signing queries and `Q_H` RO queries, with at most
`C_s` total preimage sampling calls (including retries):

  `Adv^{UF-CMA}_{Falcon+}(A)`
  `  ≤ (r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS}(B))^{…})^{…}`
  `  + Σ C(C_s,i) · (1-p)^{C_s-i} · p^i`
  `  + Q_s · (C_s + Q_H) / 2^k`

where:
- `r_p = R_{a_p}(PreSmp ‖ D_{Λ,s,c})`: sampler Rényi divergence
- `r_u = R_{a_u}(U(R_q) ‖ Q_h)`: RO simulation Rényi divergence
- `p = Pr[‖(s₁,s₂)‖ ≤ β]`: acceptance probability per attempt
- `k = 320`: salt bits
- `a_p, a_u > 1`: Rényi orders (optimized per instance)

### Concrete security levels ([Jia+26] Table 6)

Using basis-specific analysis (Theorems 2–4 of [Jia+26]):

| Scheme | `loss_p` | `loss_u` | Bit security |
|---|---|---|---|
| Falcon+-512 | 0.093 bits | 0.093 bits | 119.81 |
| Falcon+-1024 | 0.087 bits | 0.087 bits | 277.82 (256 limited by salt term) |

The `loss_p` and `loss_u` are *maximum* over 1000 random Falcon bases ([Jia+26]
Table 5), replacing the worst-case 3.29/3.14 bits from [FGdG+25].

### Sampler precision requirements

The sampler Rényi divergence `r_p` depends on floating-point precision via:
  `δ_{RE}(PreSmp, D_{Λ,s,c}) ≤ δ_{B,s} = ∏_{i=1}^{2n} (1+ε_i)/(1-ε_i) - 1`
where `ε_i = ε^{α_i²}` and `α_i = ‖B‖_{GS}/‖b̃_i‖` ([Jia+26] Theorem 2).

The required precision `δ_c + δ_σ` for provable security:
- Required by proof: `≤ 2^{-46}` (for `λ = 256`, `Q_s = 2^{64}`)
- binary64 (53-bit): achieves only `2^{-37}` worst case ([TWFalcon]),
  provably secure for only `2^{47}` queries
- Triple-word (72-bit): achieves `2^{-57}`, fully sufficient
- Exact (infinite precision): `r_p = 1` (no loss)

### Salt collision

The salt collision term `Q_s · (C_s + Q_H) / 2^k` from [FGdG+25] Theorem 1 is slightly
tighter than the birthday bound `Q_s² / (2 · 2^k)` from GPV08 Proposition 6.2.
For `k = 320`, both are negligible.

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


open OracleComp OracleSpec ENNReal

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### Correctness -/

/-- Falcon verification correctness: if the key pair is valid and signing produces a
signature (does not abort), then verification accepts.

The proof relies on:
1. The NTRU equation ensuring `s₁ + s₂ · h = c mod q`.
2. The norm bound from `ffSampling` ensuring `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.
3. The compress/decompress roundtrip preserving `s₂`. -/
theorem verify_sign_correct (pk : PublicKey p) (sk : SecretKey p)
    (hvalid : validKeyPair p pk sk = true)
    (msg : List Byte) (sig : Signature)
    (h_laws : Primitives.Laws prims)
    (hsig : sig ∈ support (Falcon.sign p pk sk msg)) :
    Falcon.verify p prims pk msg sig = true := by
  sorry

/-! ### NTRU-SIS Hardness Assumption -/

/-- The NTRU-SIS problem: given `h ∈ R_q` (the Falcon public key), find short
`(s₁, s₂) ∈ R_q²` satisfying `s₁ + s₂ · h = 0 mod q` with
`‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.

This is the lattice problem underlying Falcon's security. It is an instance of
the generic SIS problem where the matrix is the single-row matrix `[I | h]`
over the cyclotomic ring `R_q = ℤ_q[x]/(x^n + 1)`. -/
noncomputable def ntruSISProblem [SampleableType (Rq p.n)] :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := $ᵗ (Rq p.n)
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ p.betaSquared) &&
    decide (x.1 + negacyclicMul x.2 h = 0)

/-! ### Sampler Quality Hypotheses -/

/-- The trapdoor sampler quality hypothesis: the Rényi divergence of order `a > 1`
between the concrete trapdoor sampler and an ideal sampler is bounded by `R`.

This captures the floating-point precision loss in `ffSampling` and `SamplerZ`.
The structure separates the *existence* of the bound from its *concrete value*.

### Precise bound ([Jia+26] Corollary 1, refining [Pre17] Lemma 6)

For basis `B` with Gram-Schmidt vectors `b̃_i`, let `α_i = ‖B‖_{GS} / ‖b̃_i‖` and
`ε_i = ε^{α_i²}` where `ε` is the global closeness parameter. Then:

  `R_a(PreSmp(B,s,t) ‖ D_{Λ(B),s,t}) ≲ 1 + a · δ²_{B,s} / 2`

where `δ_{B,s} = ∏_i (1+ε_i)/(1-ε_i) - 1` is the basis-specific relative error.

The previous worst-case analysis ([Pre17]) used `δ ≈ 4nε`, but the basis-specific
metric gives `δ_{B,s} ≈ 4nε / (0.87 · |ln ε|)`, which is ~21× tighter for Falcon
parameters ([Jia+26] Section 4.3).

### Optimal Rényi order ([FGdG+25] Lemma 4)

The Rényi orders `a_p, a_u` should be chosen to minimize the total security loss
`C_s · log₂(r_p) + C_s · log₂(r_u) + λ/a`, which gives much larger optimal orders
than the traditional `a = 2λ`:

| | [FGdG+25] | [Jia+26] |
|---|---|---|
| Falcon+-512 `a_p` | 72.96 | 2577.30 |
| Falcon+-512 `a_u` | 69.64 | 2573.91 |
| Falcon+-1024 `a_p` | 157.05 | 6417.73 |
| Falcon+-1024 `a_u` | 153.28 | 6413.92 |

### Precision requirements ([TWFalcon] Section 3)

The combined FP error must satisfy `10·√(2n)·(δ_c + δ_σ) ≤ 2^{-37}` for the
Rényi argument to hold with `λ = 256`, `Q_s = 2^{64}`. This requires
`δ_c + δ_σ ≤ 2^{-46}`. Measured precision:

| Arithmetic | `δ_c + δ_σ` | Provably secure queries |
|---|---|---|
| binary64 (53-bit) | ≤ 2^{-37} (worst) | 2^{47} |
| triple-word (72-bit) | ≤ 2^{-57} | 2^{68} (exceeds 2^{64}) |
| exact | 0 | ∞ |

Discharging this hypothesis requires composing per-operation FPR error bounds
(from `ApproxArith.lean` / `FPRBridge.lean`) through the `ffSampling` recursion. -/
structure SamplerQuality (pk : PublicKey p) (sk : SecretKey p) where
  /-- The Rényi divergence order. Optimal values are much larger than `2λ`:
  ~2577 for Falcon+-512, ~6418 for Falcon+-1024 ([Jia+26] Table 6). -/
  renyiOrder : ℝ
  hOrder : 1 < renyiOrder
  /-- The Rényi divergence bound `R ≥ 1`.
  By [Jia+26] Corollary 1: `R ≲ 1 + a · δ²_{B,s} / 2` where `δ_{B,s}` is the
  basis-specific relative error. For typical Falcon bases, `log₂ R < 2^{-10}`. -/
  bound : ℝ≥0∞
  /-- The ideal sampler: exact discrete Gaussian `D_{Λ^⊥, σ, c}` over the NTRU lattice
  coset. This is the target distribution that `ffSampling` approximates. -/
  idealSampler : Rq p.n → ProbComp (Rq p.n × Rq p.n)
  /-- Rényi divergence bound: for every target `c`, the Rényi divergence of order `a`
  between the concrete sampler and the ideal Gaussian is at most `R`. -/
  quality : ∀ c : Rq p.n,
    renyiDiv renyiOrder ((falconPSF p).trapdoorSample pk sk c) (idealSampler c) ≤ bound
  /-- Ideal sampler correctness: the ideal Gaussian always produces valid short preimages.
  This follows from the lattice geometry when `σ ≥ η_ε(Λ^⊥) · ‖B̃‖_GS`. -/
  idealCorrect : ∀ c : Rq p.n,
    ∀ x ∈ support (idealSampler c),
      (falconPSF p).eval pk x = c ∧ (falconPSF p).isShort x = true

/-! ### EUF-CMA Security -/

/-- **EUF-CMA security of Falcon** ([FGdG+25] Theorem 1 + [Jia+26] refined bounds),
generic in the salt type `Salt`.

For any EUF-CMA adversary `A` making at most `qSign` signing queries against the Falcon+
signature scheme with salt type `Salt`, there exists an NTRU-SIS adversary `B` such that:

  `Adv^{EUF-CMA}_{Falcon+}(A) ≤ Adv^{NTRU-SIS}(B) + qSign² / (2 · |Salt|) + ε_sampler`

### Error terms

**Term 1: `Adv^{NTRU-SIS}(B)`.**
The GPV reduction is tight: `B` runs `A` internally with a simulated signing oracle
(sign-then-hash strategy) and extracts a short NTRU preimage from any valid forgery.
There is no `Q_hash` loss factor.

**Term 2: `qSign² / (2 · |Salt|)`.**
Salt collision probability, bounded by the birthday paradox. This is a simplified form
of the `Q_s · (C_s + Q_H) / 2^k` term from [FGdG+25] Theorem 1.

**Term 3: `ε_sampler`.**
The Rényi divergence-based sampler loss. The full [FGdG+25] bound has the structure
`r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS})^{...}`, where `r_p` and `r_u` are the per-query
Rényi divergences for the sampler and RO simulation respectively.
[Jia+26] Theorems 2-4 show that with basis-specific analysis, the total loss
`C_s · (log r_p + log r_u)` is < 0.2 bits for all tested Falcon instances.
With exact arithmetic (infinite precision), `r_p = 1` and the sampler loss vanishes.

### Proof structure

1. The generic GPV reduction (`GPVHashAndSign.euf_cma_bound`) which reduces EUF-CMA to
   preimage finding with a birthday collision term.
2. A further reduction from preimage finding to NTRU-SIS (the PSF `eval` is exactly
   the SIS map `(s₁, s₂) ↦ s₁ + s₂ · h mod q`).
3. The sampler quality hypothesis to account for the finite-precision gap. -/
theorem euf_cma_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p Salt hr)) :
    ∃ (sisReduction : SIS.Adversary (ntruSISProblem p))
      (samplerLoss : ENNReal),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruSISProblem p) sisReduction +
        GPVHashAndSign.collisionBound Salt qSign +
        samplerLoss := by
  sorry

/-- Concrete instantiation of `euf_cma_security` with the Falcon-specified 40-byte
(320-bit) salt.

The collision term specializes to `qSign² / (2 · 2^320)`. For the Falcon-specified
maximum of `qSign = 2^64` signing queries, this is `≤ 2^{-193}`. -/
theorem euf_cma_security_bytes40
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p (Bytes 40) hr)) :
    ∃ (sisReduction : SIS.Adversary (ntruSISProblem p))
      (samplerLoss : ENNReal),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) (Bytes 40)) ≤
        SIS.advantage (ntruSISProblem p) sisReduction +
        GPVHashAndSign.collisionBound (Bytes 40) qSign +
        samplerLoss :=
  euf_cma_security p (Bytes 40) hr qSign adv

end Falcon
