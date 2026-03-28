/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Ring

/-!
# ML-DSA Primitive Interfaces

This file keeps the hash, XOF, and sampling components abstract while exposing the semantic
types the FIPS 204 pseudocode needs. A concrete primitive bundle can be supplied to make the
spec executable without committing to one implementation yet.

## Important type distinctions

- `High` — the type of `HighBits` output (commitment representatives, `w₁`). Corresponds to
  the quotient by `2γ₂` rounding. This is what the verifier reconstructs via `UseHint`.
- `Power2High` — the type of `Power2Round` output (compressed public key `t₁`). Corresponds
  to dropping the `d` least significant bits. These are distinct operations with different
  ranges and semantics.

## References

- NIST FIPS 204, Section 7 (supporting algorithms)
-/

set_option autoImplicit false

namespace ML_DSA

/-- The type of challenge polynomials: elements of `R_q` with exactly `τ` coefficients
in `{-1, +1}` and the rest zero, sampled by `SampleInBall` (Algorithm 29). -/
abbrev ChallengePoly := Rq

/-- The type of the commitment hash `c̃`, which is `λ/4` bytes long. -/
def CommitHashBytes (p : Params) := Bytes (p.lambda / 4)

/-- The primitive algorithms referenced by the ML-DSA specification. -/
structure Primitives (p : Params) where
  /-- The type of high-order representatives from `HighBits` (rounding by `2γ₂`).
  Used for commitments `w₁` and their reconstruction via `UseHint`. -/
  High : Type
  /-- The type of high-order representatives from `Power2Round` (dropping `d` bits).
  Used for the compressed public key `t₁`. Distinct from `High` because `Power2Round`
  and `HighBits` use different rounding moduli. -/
  Power2High : Type
  /-- The type of hint values produced by `MakeHint`. -/
  Hint : Type
  /-- `H(ξ || k || l, 128)`: expand a 32-byte seed into `(ρ, ρ', K)` for key generation. -/
  expandSeed : Bytes 32 → Bytes 32 × Bytes 64 × Bytes 32
  /-- `ExpandA(ρ)`: generate the public matrix Â from the public seed (Algorithm 32). -/
  expandA : Bytes 32 → TqMatrix p.k p.l
  /-- `ExpandS(ρ')`: generate the secret vectors `(s₁, s₂)` (Algorithm 33). -/
  expandS : Bytes 64 → RqVec p.l × RqVec p.k
  /-- `ExpandMask(ρ'', κ)`: generate the masking vector `y` (Algorithm 34). -/
  expandMask : Bytes 64 → ℕ → RqVec p.l
  /-- `SampleInBall(c̃)`: derive the challenge polynomial `c` with weight `τ` (Algorithm 29). -/
  sampleInBall : CommitHashBytes p → ChallengePoly
  /-- `H(tr || M', 64)`: compute the 64-byte message representative `μ`. -/
  hashMessage : Bytes 64 → List Byte → Bytes 64
  /-- `H(K || rnd || μ, 64)`: compute the private random seed `ρ''`. -/
  hashPrivateSeed : Bytes 32 → Bytes 32 → Bytes 64 → Bytes 64
  /-- `H(μ || w1Encode(w₁), λ/4)`: compute the commitment hash `c̃`. -/
  hashCommitment : Bytes 64 → List Byte → CommitHashBytes p
  /-- `H(pk, 64)`: compute the 64-byte hash `tr` of the public key.
  Internally performs `pkEncode` then hashes, but is presented here taking
  the semantic key data to keep the primitives independent of encoding. -/
  hashPublicKey : Bytes 32 → Vector Power2High p.k → Bytes 64
  /-- `HighBits(r)`: extract the high-order representative (Algorithm 37).
  Returns the quotient of `r` by `2γ₂`, with boundary correction. -/
  highBits : Rq → High
  /-- `LowBits(r)`: extract the low-order part (Algorithm 38).
  Returns `r mod± 2γ₂`. -/
  lowBits : Rq → Rq
  /-- `MakeHint(z, r)`: produce a hint (Algorithm 39).
  `MakeHint(-ct₀, w - cs₂ + ct₀)` enables recovery of `HighBits(w - cs₂)`. -/
  makeHint : Rq → Rq → Hint
  /-- `UseHint(h, r)`: use a hint to recover high bits (Algorithm 40).
  `UseHint(MakeHint(-ct₀, w-cs₂+ct₀), w'_Approx) = HighBits(w - cs₂) = w₁`. -/
  useHint : Hint → Rq → High
  /-- `Power2Round(r)`: split `r` into `(r₁, r₀)` where `r = r₁ · 2^d + r₀` (Algorithm 35).
  The high part `r₁` is the compressed value stored in the public key. -/
  power2Round : Rq → Power2High × Rq
  /-- Reconstruct the shifted value `t₁ · 2^d` from a power-2 rounded high representative.
  Used by the verifier to compute `w'_Approx = Az - c · (t₁ · 2^d)`. -/
  power2RoundShift : Power2High → Rq
  /-- `w1Encode(w₁)`: encode a vector of high-order representatives as bytes (Algorithm 28). -/
  w1Encode : Vector High p.k → List Byte
  /-- Count the number of 1's in a hint vector. -/
  hintWeight : Vector Hint p.k → ℕ

namespace Primitives

variable {p : Params} (prims : Primitives p) (nttOps : NTTRingOps)

/-- Lift `highBits` component-wise to a polynomial vector. -/
def highBitsVec {k : ℕ} (v : RqVec k) : Vector prims.High k :=
  Vector.map prims.highBits v

/-- Lift `lowBits` component-wise to a polynomial vector. -/
def lowBitsVec {k : ℕ} (v : RqVec k) : RqVec k :=
  Vector.map prims.lowBits v

/-- Lift `power2Round` component-wise to a polynomial vector. -/
def power2RoundVec {k : ℕ} (v : RqVec k) :
    Vector prims.Power2High k × RqVec k :=
  let pairs := Vector.map prims.power2Round v
  (Vector.map Prod.fst pairs, Vector.map Prod.snd pairs)

/-- Lift `power2RoundShift` component-wise to a polynomial vector.
Reconstructs `t₁ · 2^d` from the compressed public key vector `t₁`. -/
def power2RoundShiftVec {k : ℕ} (v : Vector prims.Power2High k) : RqVec k :=
  Vector.map prims.power2RoundShift v

/-- Lift `makeHint` component-wise to a polynomial vector. -/
def makeHintVec {k : ℕ} (z r : RqVec k) : Vector prims.Hint k :=
  Vector.zipWith prims.makeHint z r

/-- Lift `useHint` component-wise to a polynomial vector. -/
def useHintVec {k : ℕ} (h : Vector prims.Hint k) (r : RqVec k) :
    Vector prims.High k :=
  Vector.zipWith prims.useHint h r

end Primitives

end ML_DSA
