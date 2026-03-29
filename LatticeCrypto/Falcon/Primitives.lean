/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Ring
import LatticeCrypto.DiscreteGaussian

/-!
# Falcon Primitive Interfaces

This file defines the abstract primitive interfaces for Falcon: hash-to-point, discrete
Gaussian sampler, Falcon tree, and fast Fourier sampling (ffSampling). All continuous
parameters use `ℝ` (Mathlib Real), matching the exact-arithmetic specification level.

## Design Decisions

- **`SamplerZ : ℝ → ℝ → ProbComp ℤ`** takes a real center `μ` and real standard deviation
  `σ'`, producing an integer sample from the discrete Gaussian `D_{ℤ,σ',μ}`.
- **`FalconTree`** is a binary tree with `ℝ`-valued leaves (the `σ` values from the
  normalized Gram-Schmidt basis) and `ℝ`-polynomial internal nodes.
- **`ffSampling`** operates on `ℝ`-coefficient FFT representations, producing integer outputs.

The `Float` type is intentionally avoided; see the plan for rationale.

## References

- Falcon specification v1.2, Section 3.9 (Algorithms 10–13)
- Falcon specification v1.2, Section 3.8 (Algorithm 9: ffLDL*)
-/

set_option autoImplicit false

open OracleComp

namespace Falcon

/-- A polynomial in FFT representation over `ℝ`, i.e. an element of `ℝ^{2^k}` representing
a polynomial in `ℝ[x]/(x^{2^k} + 1)` via its evaluations at the complex roots of unity.
In the exact-arithmetic specification, these are exact real (or complex) values. -/
abbrev RealFFTPoly (k : ℕ) := Vector ℝ (2 ^ k)

/-- The Falcon tree (LDL tree), a binary tree used by `ffSampling` (Algorithm 11).

- At level 0 (leaves): stores `σ > 0`, the standard deviation for `SamplerZ` at that leaf.
- At level `k + 1` (internal nodes): stores a polynomial `ℓ` in FFT representation
  (from the LDL decomposition of the Gram matrix) and two subtrees.

The tree is built by `ffLDL*` (Algorithm 9) during key generation, using exact arithmetic
over `ℝ` (or `ℚ`). The leaf values are the `σ'_i` parameters passed to `SamplerZ`. -/
inductive FalconTree : ℕ → Type where
  | leaf (σ : ℝ) : FalconTree 0
  | node {k : ℕ} (ℓ : RealFFTPoly k) (left right : FalconTree k) : FalconTree (k + 1)

/-- The primitive algorithms referenced by the Falcon specification. -/
structure Primitives (p : Params) where
  /-- `HashToPoint(salt ‖ message, q, n)` (Algorithm 2): hash a salt-message pair to a
  polynomial in `R_q` with coefficients uniform in `[0, q-1]`. This is the random oracle
  `H` in the GPV framework. -/
  hashToPoint : Bytes 40 → List Byte → Rq p.n
  /-- `SamplerZ(μ, σ')` (Algorithm 12): sample an integer `z` from the discrete Gaussian
  distribution `D_{ℤ,σ',μ}` centered at `μ ∈ ℝ` with standard deviation `σ' ∈ ℝ`. -/
  samplerZ : ℝ → ℝ → ProbComp ℤ
  /-- `Compress(s, sbytelen)` (Algorithm 17): compress an integer polynomial into a byte
  string of at most `sbytelen` bytes. Returns `none` if the polynomial cannot be compressed
  within the allotted space (triggering a signing retry). -/
  compress : IntPoly p.n → ℕ → Option (List Byte)
  /-- `Decompress(bytes, sbytelen, n)` (Algorithm 18): decompress a byte string back to
  an integer polynomial. -/
  decompress : List Byte → ℕ → Option (IntPoly p.n)
  /-- NTT operations for `R_q` with `q = 12289`. -/
  nttOps : NTTRingOps p.n

namespace Primitives

variable {p : Params} (prims : Primitives p)

/-- `ffSampling(t, T)` (Algorithm 11): the fast Fourier sampling algorithm.

Given a target vector `t = (t₀, t₁)` in FFT representation over `ℝ` and a Falcon tree `T`,
produces an integer vector `z = (z₀, z₁)` such that `(t - z)` is short (bounded by the
Gram-Schmidt norms encoded in the tree).

The algorithm recurses on the tree:
- At a leaf (n = 1): call `SamplerZ(t_i, σ_leaf)`.
- At an internal node: split, recurse on each half using the LDL factor `ℓ`, recombine.

This is the core trapdoor operation of Falcon: given the secret basis (encoded as the tree),
it samples a lattice vector close to the target. -/
noncomputable def ffSampling (κ : ℕ) (t : Vector ℝ (2 * 2 ^ κ))
    (tree : FalconTree κ) : ProbComp (Vector ℤ (2 * 2 ^ κ)) := sorry

end Primitives

/-- Algebraic and distributional laws that the Falcon primitives must satisfy. -/
structure Primitives.Laws {p : Params} (prims : Primitives p) : Prop where
  /-- The discrete Gaussian sampler produces output distributed according to the ideal
  discrete Gaussian PMF `D_{ℤ,σ',μ}`. -/
  samplerZ_correct : ∀ (μ σ' : ℝ) (hσ : 0 < σ'),
    ∀ z : ℤ, Pr[= z | prims.samplerZ μ σ'] =
      ENNReal.ofReal (LatticeCrypto.discreteGaussianPMF σ' μ hσ z)
  /-- `HashToPoint` output lies in `R_q` (coefficients in `[0, q-1]`).
  In the random oracle model, this is modeled by the random oracle itself;
  this law is a placeholder for any additional structural constraint. -/
  hashToPoint_welldefined : True
  /-- Compress/decompress roundtrip: decompressing a compressed polynomial recovers
  the original. -/
  compress_decompress : ∀ (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte),
    prims.compress s slen = some bytes →
    prims.decompress bytes slen = some s
  /-- NTT roundtrip: `NTT⁻¹(NTT(f)) = f`. -/
  ntt_invNTT : ∀ f : Rq p.n, prims.nttOps.invNTT (prims.nttOps.ntt f) = f
  /-- Inverse NTT roundtrip: `NTT(NTT⁻¹(f̂)) = f̂`. -/
  invNTT_ntt : ∀ fHat : Tq p.n, prims.nttOps.ntt (prims.nttOps.invNTT fHat) = fHat
  /-- NTT multiplication correctness. -/
  ntt_mul : ∀ f g : Rq p.n,
    prims.nttOps.multiplyNTTs (prims.nttOps.ntt f) (prims.nttOps.ntt g) =
    prims.nttOps.ntt (negacyclicMul f g)

end Falcon
