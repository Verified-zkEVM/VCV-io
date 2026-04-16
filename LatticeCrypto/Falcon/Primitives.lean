/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Arithmetic
import LatticeCrypto.DiscreteGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
- **`ffSampling`** operates on packed FFT representations over `ℝ`, returning sampled
  vectors in the FFT domain. In coefficient space, the sampled vector is integral.
- **`fftTarget` / `fftInt` / `ifftRound`** bridge between coefficient-domain polynomials
  and the packed FFT representation used by the abstract sampler.

The `Float` type is intentionally avoided; see the plan for rationale.

## References

- Falcon specification v1.2, Section 3.9 (Algorithms 10–13)
- Falcon specification v1.2, Section 3.8 (Algorithm 9: ffLDL*)
-/


open OracleComp

namespace Falcon

/-- A single Falcon FFT polynomial in packed real form.

The first `2^k` entries are the real parts, and the last `2^k` entries are the
imaginary parts, of `2^k` complex evaluations. This matches the packed layout used by
Falcon's FFT helpers. -/
abbrev RealFFTPoly (k : ℕ) := Vector ℝ (2 * 2 ^ k)

/-- A pair `(t₀, t₁)` of same-size Falcon FFT polynomials.

This is the shape manipulated by `ffSampling`: the target vector and the sampled output
are both pairs of FFT polynomials. -/
abbrev FFTPair (k : ℕ) := RealFFTPoly k × RealFFTPoly k

namespace RealFFTPoly

/-- Real part of the `i`-th packed FFT coordinate. -/
@[inline] def re {k : ℕ} (f : RealFFTPoly k) (i : Fin (2 ^ k)) : ℝ :=
  f.get ⟨i.1, by omega⟩

/-- Imaginary part of the `i`-th packed FFT coordinate. -/
@[inline] def im {k : ℕ} (f : RealFFTPoly k) (i : Fin (2 ^ k)) : ℝ :=
  f.get ⟨i.1 + 2 ^ k, by omega⟩

/-- Pack real and imaginary parts into Falcon's FFT layout. -/
@[inline] def pack {k : ℕ}
    (rePart imPart : Vector ℝ (2 ^ k)) : RealFFTPoly k :=
  Vector.ofFn fun j =>
    if h : j.1 < 2 ^ k then
      rePart.get ⟨j.1, h⟩
    else
      imPart.get ⟨j.1 - 2 ^ k, by omega⟩

end RealFFTPoly

/-- The Falcon tree (LDL tree), a binary tree used by `ffSampling` (Algorithm 11).

- At level 0 (leaves): stores `σ > 0`, the standard deviation for `SamplerZ` at that leaf.
- At level `k + 1` (internal nodes): stores a polynomial `ℓ` in FFT representation
  (from the LDL decomposition of the Gram matrix) and two subtrees.

The tree is built by `ffLDL*` (Algorithm 9) during key generation, using exact arithmetic
over `ℝ` (or `ℚ`). The leaf values are the `σ'_i` parameters passed to `SamplerZ`. -/
inductive FalconTree : ℕ → Type where
  | leaf (σ : ℝ) : FalconTree 0
  | node {k : ℕ} (ℓ : RealFFTPoly (k + 1)) (left right : FalconTree k) : FalconTree (k + 1)

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
  /-- Convert a target polynomial in `R_q` to Falcon's packed FFT representation.

  For hash targets, coefficients are interpreted as integers in `[0, q - 1]`, matching
  the `hm` array in the reference implementation. -/
  fftTarget : Rq p.n → RealFFTPoly p.fftDepth
  /-- Convert an integer polynomial to Falcon's packed FFT representation. -/
  fftInt : IntPoly p.n → RealFFTPoly p.fftDepth
  /-- Apply the inverse packed FFT and round each coefficient to the nearest integer.

  This is the proof-level counterpart of `fpoly_iFFT` followed by coefficient rounding in
  the reference implementation. -/
  ifftRound : RealFFTPoly p.fftDepth → IntPoly p.n
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

/-- The canonical split angle for the proof-level Falcon FFT specification.

For `splitFFT` on a packed Falcon FFT polynomial of length `2 * 2^(k+1)`, we follow the
implementation order used by Falcon's `fpoly_split_fft` and `fpoly_merge_fft`: the adjacent
packed coordinates `(2i, 2i+1)` form the pair `f(ωᵢ), f(-ωᵢ)` where
`ωᵢ = exp(((2i + 1)π / 2^(k+2)) · I)`. -/
@[inline] noncomputable def splitAngle {k : ℕ} (i : Fin (2 ^ k)) : ℝ :=
  (((2 * i.1 + 1 : ℕ) : ℝ) * Real.pi) / (((2 ^ (k + 2) : ℕ) : ℝ))

/-- Hash a message using the verification-key bytes derived from `pk`. -/
@[inline] def hashToPointForPublicKey (pk : Rq p.n) (salt : Bytes 40) (msg : List Byte) :
    Rq p.n :=
  prims.hashToPoint salt (prims.publicKeyBytes pk) msg

/-- Scale a packed Falcon FFT polynomial by a real scalar. -/
@[inline] def scaleFFT {k : ℕ} (c : ℝ) (f : RealFFTPoly k) : RealFFTPoly k :=
  Vector.ofFn fun i => c * f.get i

/-- Pointwise packed-complex multiplication in Falcon's FFT representation. -/
def mulFFT {k : ℕ} (a b : RealFFTPoly k) : RealFFTPoly k :=
  let outRe : Vector ℝ (2 ^ k) := Vector.ofFn fun i =>
    RealFFTPoly.re a i * RealFFTPoly.re b i -
      RealFFTPoly.im a i * RealFFTPoly.im b i
  let outIm : Vector ℝ (2 ^ k) := Vector.ofFn fun i =>
    RealFFTPoly.re a i * RealFFTPoly.im b i +
      RealFFTPoly.im a i * RealFFTPoly.re b i
  RealFFTPoly.pack outRe outIm

/-- Split a packed Falcon FFT polynomial into its even and odd parts.

If `f = f₀(x²) + x · f₁(x²)` and the adjacent packed coordinates of `f` encode
`a = f(ωᵢ)`, `b = f(-ωᵢ)` for the canonical implementation-order roots
`ωᵢ = exp(((2i + 1)π / 2^(k+2)) · I)`, then

- `f₀(ωᵢ²) = (a + b) / 2`
- `f₁(ωᵢ²) = (a - b) / (2ωᵢ)`

This is the proof-level analogue of Falcon's `fpoly_split_fft`. -/
noncomputable def splitFFT {k : ℕ}
    (f : RealFFTPoly (k + 1)) : FFTPair k :=
  let f₀Re : Vector ℝ (2 ^ k) := Vector.ofFn fun i =>
    let aRe := RealFFTPoly.re f ⟨2 * i.1, by omega⟩
    let bRe := RealFFTPoly.re f ⟨2 * i.1 + 1, by omega⟩
    (aRe + bRe) / 2
  let f₀Im : Vector ℝ (2 ^ k) := Vector.ofFn fun i =>
    let aIm := RealFFTPoly.im f ⟨2 * i.1, by omega⟩
    let bIm := RealFFTPoly.im f ⟨2 * i.1 + 1, by omega⟩
    (aIm + bIm) / 2
  let f₁Re : Vector ℝ (2 ^ k) := Vector.ofFn fun i =>
    let aRe := RealFFTPoly.re f ⟨2 * i.1, by omega⟩
    let aIm := RealFFTPoly.im f ⟨2 * i.1, by omega⟩
    let bRe := RealFFTPoly.re f ⟨2 * i.1 + 1, by omega⟩
    let bIm := RealFFTPoly.im f ⟨2 * i.1 + 1, by omega⟩
    let uRe := (aRe - bRe) / 2
    let uIm := (aIm - bIm) / 2
    let θ := splitAngle i
    let c := Real.cos θ
    let s := Real.sin θ
    uRe * c + uIm * s
  let f₁Im : Vector ℝ (2 ^ k) := Vector.ofFn fun i =>
    let aRe := RealFFTPoly.re f ⟨2 * i.1, by omega⟩
    let aIm := RealFFTPoly.im f ⟨2 * i.1, by omega⟩
    let bRe := RealFFTPoly.re f ⟨2 * i.1 + 1, by omega⟩
    let bIm := RealFFTPoly.im f ⟨2 * i.1 + 1, by omega⟩
    let uRe := (aRe - bRe) / 2
    let uIm := (aIm - bIm) / 2
    let θ := splitAngle i
    let c := Real.cos θ
    let s := Real.sin θ
    uIm * c - uRe * s
  (RealFFTPoly.pack f₀Re f₀Im, RealFFTPoly.pack f₁Re f₁Im)

/-- Merge two half-size Falcon FFT polynomials into a full-size one.

This inverts `splitFFT`: if `f = f₀(x²) + x · f₁(x²)`, then for each implementation-order
root `ωᵢ = exp(((2i + 1)π / 2^(k+2)) · I)` we reconstruct the adjacent packed pair

- `f(ωᵢ) = f₀(ωᵢ²) + ωᵢ · f₁(ωᵢ²)`
- `f(-ωᵢ) = f₀(ωᵢ²) - ωᵢ · f₁(ωᵢ²)` -/
noncomputable def mergeFFT {k : ℕ}
    (f₀ f₁ : RealFFTPoly k) : RealFFTPoly (k + 1) :=
  let outRe : Vector ℝ (2 ^ (k + 1)) := Vector.ofFn fun i =>
    let j : Fin (2 ^ k) := ⟨i.1 / 2, by omega⟩
    let aRe := RealFFTPoly.re f₀ j
    let bRe₀ := RealFFTPoly.re f₁ j
    let bIm₀ := RealFFTPoly.im f₁ j
    let θ := splitAngle j
    let c := Real.cos θ
    let s := Real.sin θ
    let bRe := bRe₀ * c - bIm₀ * s
    if h : i.1 % 2 = 0 then aRe + bRe else aRe - bRe
  let outIm : Vector ℝ (2 ^ (k + 1)) := Vector.ofFn fun i =>
    let j : Fin (2 ^ k) := ⟨i.1 / 2, by omega⟩
    let aIm := RealFFTPoly.im f₀ j
    let bRe₀ := RealFFTPoly.re f₁ j
    let bIm₀ := RealFFTPoly.im f₁ j
    let θ := splitAngle j
    let c := Real.cos θ
    let s := Real.sin θ
    let bIm := bIm₀ * c + bRe₀ * s
    if h : i.1 % 2 = 0 then aIm + bIm else aIm - bIm
  RealFFTPoly.pack outRe outIm

/-- Pointwise packed-complex multiplication of `ℓ` with the residual `(t₁ - z₁)`.

This computes `ℓ · (t₁ - z₁)` in the FFT domain, using complex multiplication on each
packed coordinate. -/
noncomputable def adjustTarget {k : ℕ}
    (ℓ t₁ z₁ : RealFFTPoly k) : RealFFTPoly k :=
  mulFFT ℓ (t₁ - z₁)

/-- `ffSampling(t, T)` (Algorithm 11): the fast Fourier sampling algorithm.

Given a target pair `t = (t₀, t₁)` of FFT polynomials and a Falcon tree `T`, this returns
a sampled pair `z = (z₀, z₁)` in FFT representation. In coefficient space, `z` is integral
and `(t - z)` is short relative to the Gram-Schmidt data encoded by `T`.

The algorithm recurses on the tree structure:
- **Leaf** (`κ = 0`): each of `t₀` and `t₁` has one complex FFT coordinate, so we sample
  their real and imaginary parts independently via `SamplerZ`.
- **Node** (`κ + 1`): split `t₁`, recurse on the right subtree, merge to obtain `z₁`,
  compute `t_b0 = t₀ + ℓ · (t₁ - z₁)`, split `t_b0`, recurse on the left subtree, then
  merge to obtain `z₀`. -/
noncomputable def ffSampling (κ : ℕ) (t : FFTPair κ)
    (tree : FalconTree κ) : ProbComp (FFTPair κ) :=
  match κ, t, tree with
  | 0, (t₀, t₁), .leaf σ => do
    let z₀Re ← prims.samplerZ (RealFFTPoly.re t₀ ⟨0, by omega⟩) σ
    let z₀Im ← prims.samplerZ (RealFFTPoly.im t₀ ⟨0, by omega⟩) σ
    let z₁Re ← prims.samplerZ (RealFFTPoly.re t₁ ⟨0, by omega⟩) σ
    let z₁Im ← prims.samplerZ (RealFFTPoly.im t₁ ⟨0, by omega⟩) σ
    let z₀ : RealFFTPoly 0 :=
      RealFFTPoly.pack
        (Vector.ofFn fun _ => (z₀Re : ℝ))
        (Vector.ofFn fun _ => (z₀Im : ℝ))
    let z₁ : RealFFTPoly 0 :=
      RealFFTPoly.pack
        (Vector.ofFn fun _ => (z₁Re : ℝ))
        (Vector.ofFn fun _ => (z₁Im : ℝ))
    return (z₀, z₁)
  | k + 1, (t₀, t₁), .node ℓ left right => do
    let t₁Split := splitFFT t₁
    let z₁Split ← ffSampling k t₁Split right
    let z₁ := mergeFFT z₁Split.1 z₁Split.2
    let tb₀ := t₀ + adjustTarget ℓ t₁ z₁
    let tb₀Split := splitFFT tb₀
    let z₀Split ← ffSampling k tb₀Split left
    let z₀ := mergeFFT z₀Split.1 z₀Split.2
    return (z₀, z₁)

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
