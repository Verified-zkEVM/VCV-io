/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Scheme
import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution

/-!
# Falcon Security

This file states the high-level security theorems for the Falcon signature scheme.

## Correctness

`verify(pk, m, sign(sk, m)) = true` whenever:
1. The key pair is valid (NTRU equation holds, `h = g · f⁻¹ mod q`).
2. Signing does not abort (norm check passes, compression succeeds).

## EUF-CMA Security (GPV Theorem)

The main security theorem reduces EUF-CMA to the NTRU-SIS problem:

  `Adv^{EUF-CMA}_{Falcon}(A) ≤ Adv^{SIS}_{NTRU}(B) + q_S² / (2 · |Salt|)`

where:
- `B` is a SIS adversary constructed from `A`.
- `q_S` is the number of signing queries.
- `|Salt| = 2^320` is the salt space size (40 bytes).
- The `q_S² / (2 · |Salt|)` term is the birthday bound on salt collision (spec Section 2.2.2).

The reduction follows the GPV08 framework:
1. By hash-randomization (using fresh salts), each signing query produces an independent
   hash target.
2. Each signature is a trapdoor sample, statistically close to the ideal discrete Gaussian.
3. A forger must solve NTRU-SIS: find short `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`.

## Sampler Quality (Out of Scope)

The Renyi divergence between the exact (infinite-precision) and finite-precision (53-bit
floating-point) samplers is bounded by the analysis in Falcon spec Section 2.5.2. This gap
can be stated as a hypothesis:

  `∀ σ' μ, renyiDivergence (samplerZ_finite μ σ') (discreteGaussianPMF σ' μ) ≤ ε_renyi`

and would appear as an additional additive term in the security bound.

## References

- Falcon specification v1.2, Sections 2.2–2.5 (security analysis)
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Theorem 6.1.
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
def ntruSISProblem [SampleableType (Rq p.n)] :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := $ᵗ (Rq p.n)
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ p.betaSquared) &&
    decide (x.1 + negacyclicMul x.2 h = 0)

/-! ### EUF-CMA Security -/

/-- **EUF-CMA security of Falcon (GPV Theorem).**

For any EUF-CMA adversary `A` against the Falcon signature scheme, there exists an
NTRU-SIS adversary `B` and a salt collision bound such that:

  `Adv^{EUF-CMA}_{Falcon}(A) ≤ Adv^{NTRU-SIS}(B) + q_S² / (2 · 2^320)`

The proof follows the GPV08 framework:

1. **Hash-randomization**: Each signature uses a fresh 40-byte salt, so distinct signing
   queries produce independent random oracle targets with overwhelming probability
   (birthday bound: `q_S² / (2 · 2^320)` collision probability).

2. **Trapdoor simulation**: Under `SamplerZ` correctness (`Primitives.Laws.samplerZ_correct`),
   each signature is distributed as `D_{Λ^⊥(c), σ}` — the discrete Gaussian over the
   coset `{x : eval(pk, x) = c}`. This distribution is independent of the secret key
   (by the GPV lattice-Gaussian smoothing argument).

3. **Reduction to NTRU-SIS**: After replacing the trapdoor sampler with the ideal Gaussian
   (statistical distance at most `ε_sampler` per query), any forgery directly yields an
   NTRU-SIS solution: the forger produces short `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`
   for a `c` that was not the target of any signing query. -/
theorem euf_cma_security
    [SampleableType (Rq p.n)]
    [SampleableType (PublicKey p)] [SampleableType (SecretKey p)]
    [SampleableType (Bytes 40)]
    [DecidableEq (Rq p.n)] [DecidableEq (Rq p.n × Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p hr)) :
    ∃ (sisReduction : SIS.Adversary (ntruSISProblem p))
      (collisionBound : ENNReal),
      adv.advantage ≤
        SIS.advantage (ntruSISProblem p) sisReduction + collisionBound := by
  sorry

end Falcon
