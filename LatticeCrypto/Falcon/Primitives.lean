/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Arithmetic
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
  /-- External verification-key bytes used by the raw-message FN-DSA hash-to-point path.
  In the concrete implementation this is the standard public-key encoding with its header. -/
  publicKeyBytes : Rq p.n → ByteArray
  /-- `HashToPoint(nonce, vrfy_key, message, q, n)` (FIPS 206, raw-message mode): hash a
  salt-message pair together with the external verification-key bytes to a polynomial in `R_q`
  with coefficients uniform in `[0, q-1]`. -/
  hashToPoint : Bytes 40 → ByteArray → List Byte → Rq p.n
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

/-- Hash a message using the verification-key bytes derived from `pk`. -/
@[inline] def hashToPointForPublicKey (pk : Rq p.n) (salt : Bytes 40) (msg : List Byte) :
    Rq p.n :=
  prims.hashToPoint salt (prims.publicKeyBytes pk) msg

/-- Split a vector of length `2 * 2^(k+1)` into two halves of length `2 * 2^k`
in the FFT domain. This is the ℝ-level analogue of `fpolySplitFFT`.

The split decomposes `f(x)` evaluated at `2n`-th roots of unity into even and odd
parts `f₀, f₁` evaluated at `n`-th roots of unity, such that `f = f₀ + x · f₁`. -/
noncomputable def splitFFT {k : ℕ}
    (f : Vector ℝ (2 * 2 ^ (k + 1))) :
    Vector ℝ (2 * 2 ^ k) × Vector ℝ (2 * 2 ^ k) := sorry

/-- Merge two vectors of length `2 * 2^k` into a single vector of length `2 * 2^(k+1)`
in the FFT domain. This is the ℝ-level analogue of `fpolyMergeFFT`.

Inverse of `splitFFT`: given `(f₀, f₁)` evaluated at `n`-th roots of unity, produces
`f = f₀ + x · f₁` evaluated at `2n`-th roots of unity. -/
noncomputable def mergeFFT {k : ℕ}
    (f₀ f₁ : Vector ℤ (2 * 2 ^ k)) :
    Vector ℤ (2 * 2 ^ (k + 1)) := sorry

/-- Pointwise multiplication of an ℝ-valued FFT polynomial by a difference vector
`(t₁ - z₁)`, producing an adjustment to the target for the left subtree.

This computes `ℓ · (t₁ - z₁)` in the FFT domain, which is pointwise multiplication
of the LDL factor `ℓ` with the residual `(t₁ - z₁)` cast to reals. -/
noncomputable def adjustTarget {k : ℕ}
    (ℓ : RealFFTPoly k) (t₁ : Vector ℝ (2 * 2 ^ k))
    (z₁ : Vector ℤ (2 * 2 ^ k)) :
    Vector ℝ (2 * 2 ^ k) := sorry

/-- `ffSampling(t, T)` (Algorithm 11): the fast Fourier sampling algorithm.

Given a target vector `t = (t₀, t₁)` in FFT representation over `ℝ` and a Falcon tree `T`,
produces an integer vector `z = (z₀, z₁)` such that `(t - z)` is short (bounded by the
Gram-Schmidt norms encoded in the tree).

The algorithm recurses on the tree structure:
- **Leaf** (`κ = 0`): `t` has 2 components. Sample each independently via
  `SamplerZ(tᵢ, σ_leaf)`.
- **Node** (`κ + 1`): split `t` into `(t₀, t₁)`, sample `z₁ ← ffSampling(t₁, T_right)`,
  adjust `t₀' = t₀ + ℓ · (t₁ - z₁)`, sample `z₀ ← ffSampling(t₀', T_left)`,
  return `merge(z₀, z₁)`. -/
noncomputable def ffSampling (κ : ℕ) (t : Vector ℝ (2 * 2 ^ κ))
    (tree : FalconTree κ) : ProbComp (Vector ℤ (2 * 2 ^ κ)) :=
  match κ, t, tree with
  | 0, t, .leaf σ => do
    let z₀ ← prims.samplerZ (t.get ⟨0, by omega⟩) σ
    let z₁ ← prims.samplerZ (t.get ⟨1, by omega⟩) σ
    return Vector.ofFn (Fin.cons z₀ (Fin.cons z₁ Fin.elim0))
  | k + 1, t, .node ℓ left right => do
    let (t₀, t₁) := splitFFT t
    let z₁ ← ffSampling k t₁ right
    let t₀' := t₀ + adjustTarget ℓ t₁ z₁
    let z₀ ← ffSampling k t₀' left
    return mergeFFT z₀ z₁

end Primitives

/-- Algebraic and distributional laws that the Falcon primitives must satisfy. -/
structure Primitives.Laws {p : Params} (prims : Primitives p) : Prop where
  /-- The discrete Gaussian sampler produces output distributed according to the ideal
  discrete Gaussian PMF `D_{ℤ,σ',μ}`. -/
  samplerZ_correct : ∀ (μ σ' : ℝ) (_hσ : 0 < σ'),
    ∀ z : ℤ, Pr[= z | prims.samplerZ μ σ'] =
      ENNReal.ofReal (LatticeCrypto.discreteGaussianPMF σ' μ z)
  /-- `HashToPoint` output lies in `R_q` (coefficients in `[0, q-1]`).
  In the random oracle model, this is modeled by the random oracle itself;
  this law is a placeholder for any additional structural constraint. -/
  hashToPoint_welldefined : ∀ (_salt : Bytes 40) (_vrfyKey : ByteArray) (_msg : List Byte), True
  /-- Compress/decompress roundtrip: decompressing a compressed polynomial recovers
  the original. -/
  compress_decompress : ∀ (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte),
    prims.compress s slen = some bytes →
    prims.decompress bytes slen = some s
  /-- Generic transform laws for the instantiated Falcon ring backend. -/
  transform : NTTRingLaws prims.nttOps

end Falcon
