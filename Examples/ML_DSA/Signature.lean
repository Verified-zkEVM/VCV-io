/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Scheme
import Examples.ML_DSA.Encoding

/-!
# ML-DSA FIPS 204 Signature Algorithms

This file implements the faithful FIPS 204 signature algorithms:

- `fipsKeyGen` — Algorithm 1 / 6 (key generation with random seed sampling)
- `fipsSign` — Algorithm 2 / 7 (signing with message-dependent hashing and retry loop)
- `fipsVerify` — Algorithm 3 / 8 (verification with direct RO consistency check)

Unlike the IDS-core in `Scheme.lean`, this layer:

- Uses the FIPS signature format `(c̃, z, h)` instead of `(w₁, z, h)`
- Derives `μ = H(tr ‖ M')` from the actual message
- Derives `ρ'' = H(K ‖ rnd ‖ μ)` from the private seed, randomness, and message
- Uses `ExpandMask(ρ'', κ)` with counter `κ` incrementing by `l` each retry
- Checks RO consistency `c̃ = H(μ ‖ w1Encode(w₁'))` directly in verification

## References

- NIST FIPS 204, Algorithms 1–3 (outer API) and 6–8 (internal algorithms)
-/

set_option autoImplicit false

open OracleComp OracleSpec

namespace ML_DSA

variable (p : Params) (prims : Primitives p) (nttOps : NTTRingOps)

/-- The FIPS 204 signature format: `(c̃, z, h)`. -/
structure FIPSSignature where
  cTilde : CommitHashBytes p
  z : RqVec p.l
  h : Vector prims.Hint p.k

/-! ### Key Generation -/

/-- ML-DSA.KeyGen (Algorithm 1 / Algorithm 6): sample a random seed and generate keys. -/
noncomputable def fipsKeyGen : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  return keyGenFromSeed p prims nttOps seed

/-! ### Signing -/

/-- A single signing attempt at counter value `κ` (Algorithm 7, lines 5–30).

Deterministic given all its inputs; randomness enters through `ρ''` which was
derived from a random `rnd` by the caller. -/
def fipsSignAttempt
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    Option (FIPSSignature p prims) :=
  let y := prims.expandMask rhoDoublePrime kappa
  let w := computeW nttOps aHat y
  let w1 := prims.highBitsVec w
  let cTilde := prims.hashCommitment mu (prims.w1Encode w1)
  let c := prims.sampleInBall cTilde
  let cs1 := polyVecMul nttOps c sk.s1
  let cs2 := polyVecMul nttOps c sk.s2
  let z := y + cs1
  let r0 := prims.lowBitsVec (w - cs2)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let ct0 := polyVecMul nttOps c sk.t0
    let h := prims.makeHintVec (-ct0) (w - cs2 + ct0)
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some ⟨cTilde, z, h⟩
    else
      none
  else
    none

/-- The deterministic signing loop: try counter values `κ = 0, l, 2l, ...`
up to `maxAttempts` iterations (Algorithm 7, lines 4–31). -/
def fipsSignLoop
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ) :
    Option (FIPSSignature p prims) :=
  (List.range maxAttempts).findSome? fun i =>
    fipsSignAttempt p prims nttOps sk aHat mu rhoDoublePrime (i * p.l)

/-- ML-DSA.Sign (Algorithm 2 / Algorithm 7): sign a message.

1. Compute `μ = H(tr ‖ M')`
2. Sample `rnd` and compute `ρ'' = H(K ‖ rnd ‖ μ)`
3. Expand `Â = ExpandA(ρ)`
4. Try signing attempts with incrementing `κ`

Returns `none` if all `maxAttempts` attempts abort. In a correct implementation with
typical parameters, the probability of exhausting all attempts is negligible. -/
noncomputable def fipsSign (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) :
    ProbComp (Option (FIPSSignature p prims)) := do
  let mu := prims.hashMessage sk.tr msg
  let rnd ← $ᵗ (Bytes 32)
  let rhoDoublePrime := prims.hashPrivateSeed sk.key rnd mu
  let aHat := prims.expandA pk.rho
  return fipsSignLoop p prims nttOps sk aHat mu rhoDoublePrime maxAttempts

/-! ### Verification -/

/-- ML-DSA.Verify (Algorithm 3 / Algorithm 8): verify a signature.

1. Expand `Â = ExpandA(ρ)` from the public key
2. Compute `tr = H(pk)`, `μ = H(tr ‖ M')`
3. Derive `c = SampleInBall(c̃)` and compute `w'_Approx = Az - c·(t₁·2^d)`
4. Apply hint: `w₁' = UseHint(h, w'_Approx)`
5. Recompute `c̃' = H(μ ‖ w1Encode(w₁'))`
6. Accept iff `‖z‖∞ < γ₁ - β`, `c̃' = c̃`, and `hintWeight(h) ≤ ω` -/
def fipsVerify (pk : PublicKey p prims) (msg : List Byte)
    (sig : FIPSSignature p prims) : Bool :=
  let aHat := prims.expandA pk.rho
  let tr := prims.hashPublicKey pk.rho pk.t1
  let mu := prims.hashMessage tr msg
  let c := prims.sampleInBall sig.cTilde
  let wApprox := computeWApprox p prims nttOps aHat c sig.z pk.t1
  let w1' := prims.useHintVec sig.h wApprox
  let cTildeRecomputed := prims.hashCommitment mu (prims.w1Encode w1')
  decide (polyVecNorm sig.z < p.gamma1 - p.beta) &&
  decide (cTildeRecomputed = sig.cTilde) &&
  decide (prims.hintWeight sig.h ≤ p.omega)

/-! ### Correctness -/

/-- Correctness of FIPS ML-DSA: if a key pair was generated honestly and signing succeeds,
then verification accepts the resulting signature. -/
theorem fipsSign_fipsVerify_correct
    (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (sig : FIPSSignature p prims)
    (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (h_valid : validKeyPair p prims pk sk = true)
    (h_sign : fipsSignLoop p prims nttOps sk
      (prims.expandA pk.rho) (prims.hashMessage sk.tr msg)
      rhoDoublePrime maxAttempts = some sig) :
    fipsVerify p prims nttOps pk msg sig = true := by
  sorry

end ML_DSA
