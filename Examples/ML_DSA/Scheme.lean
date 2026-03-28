/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Primitives
import VCVio.CryptoFoundations.IdenSchemeWithAbort
import VCVio.CryptoFoundations.FiatShamirWithAbort
import VCVio.OracleComp.Constructions.SampleableType

/-!
# ML-DSA Scheme Definition

This file defines the ML-DSA digital signature scheme following FIPS 204. At the abstract
level, ML-DSA is modeled as an instance of `IdenSchemeWithAbort` (identification scheme with
aborts), which is then transformed into a signature scheme via `FiatShamirWithAbort`.

## Architecture

The `IdenSchemeWithAbort` type parameters instantiate as follows for ML-DSA:

| IdenSchemeWithAbort | ML-DSA meaning |
|---|---|
| `S` (statement) | `PublicKey` — `(ρ, t₁)` |
| `W` (witness) | `SecretKey` — `(ρ, K, tr, s₁, s₂, t₀)` |
| `W'` (commitment) | `Vector prims.High p.k` — the high-order bits `w₁ = HighBits(Ay)` |
| `St` (state) | `SigningState` — `(y, w)` retained for the respond phase |
| `C` (challenge) | `CommitHashBytes p` — the `λ/4`-byte hash `c̃` |
| `Z` (response) | `RqVec p.l × Vector prims.Hint p.k` — the pair `(z, h)` |

The `FiatShamirWithAbort` transform then produces a signature scheme with:
- Signature type = `W' × Z` = `w₁ × (z, h)`, where `w₁` is the commitment
- The random oracle maps `(M, w₁) ↦ c̃`

In the concrete FIPS 204 encoding, the signature stores `(c̃, z, h)` instead of `(w₁, z, h)`.
This is an equivalent representation via the random oracle: given `(w₁, z, h)` and the message,
`c̃` can be recomputed, and vice versa.

## Verification (Algorithm 8)

`ids.verify(pk, w₁, c̃, (z, h))` checks:
1. `‖z‖∞ < γ₁ - β` (response is short)
2. Compute `c = SampleInBall(c̃)` (derive challenge polynomial from hash)
3. Compute `w'_Approx = Az - c · (t₁ · 2^d)` (reconstruct approximate commitment)
4. Compute `w₁' = UseHint(h, w'_Approx)` (apply hint to recover high bits)
5. `w₁' = w₁` (reconstructed commitment matches)
6. Hint weight `≤ ω` (hint is valid)

The `FiatShamirWithAbort` layer additionally checks `c̃ = H(M ‖ w₁)` via the random oracle.
Together, checks 1–6 + RO consistency = full FIPS 204 Algorithm 8.

## References

- NIST FIPS 204, Algorithms 6 (KeyGen_internal), 7 (Sign_internal), 8 (Verify_internal)
- EasyCrypt `SimplifiedScheme.ec` (formosa-crypto/dilithium)
-/

set_option autoImplicit false

open OracleComp OracleSpec

namespace ML_DSA

variable (p : Params) (prims : Primitives p) (nttOps : NTTRingOps)

/-- The semantic public key: the public seed `ρ` and the power-2 rounded key vector `t₁`. -/
structure PublicKey where
  rho : Bytes 32
  t1 : Vector prims.Power2High p.k

/-- The semantic secret key: includes the expanded public key material for efficient signing. -/
structure SecretKey where
  rho : Bytes 32
  key : Bytes 32
  tr : Bytes 64
  s1 : RqVec p.l
  s2 : RqVec p.k
  t0 : RqVec p.k

/-- The signing state: commitment data retained between commit and respond phases.
Contains `y` (masking vector) and `w = Ay` (needed for rejection checks). -/
structure SigningState where
  y : RqVec p.l
  w : RqVec p.k

/-- The public commitment sent to the verifier: `w₁ = HighBits(w)`.
This is the high-order representative of `w = Ay` with respect to rounding by `2γ₂`. -/
abbrev Commitment := Vector prims.High p.k

/-- The signature response: the short vector `z` paired with the hint `h`.
- `z = y + c·s₁` with `‖z‖∞ < γ₁ - β` (response vector)
- `h = MakeHint(-c·t₀, w - c·s₂ + c·t₀)` (hint for commitment recovery) -/
abbrev Response := RqVec p.l × Vector prims.Hint p.k

/-- ML-DSA key generation (Algorithm 6), modeled as a deterministic function from seed.

Given a 32-byte seed `ξ`:
1. Expand to `(ρ, ρ', K)` via `H(ξ ‖ k ‖ l, 128)`
2. Generate matrix `Â = ExpandA(ρ)`
3. Generate secret vectors `(s₁, s₂) = ExpandS(ρ')`
4. Compute `t = A·s₁ + s₂`
5. Split `t` into `(t₁, t₀)` via `Power2Round`
6. Compute `tr = H(pkEncode(ρ, t₁), 64)` -/
def keyGenFromSeed (seed : Bytes 32) : PublicKey p prims × SecretKey p :=
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let aHat := prims.expandA rho
  let (s1, s2) := prims.expandS rhoPrime
  let s1Hat := nttOps.nttVec s1
  let t := nttOps.invNTTVec (nttOps.matVecMul aHat s1Hat) + s2
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, s1, s2, t0⟩
  (pk, sk)

/-- A key pair is valid when the public and secret keys share the same public seed `ρ`. -/
def validKeyPair [DecidableEq (Bytes 32)]
    (pk : PublicKey p prims) (sk : SecretKey p) : Bool :=
  pk.rho == sk.rho

/-- The underlying identification scheme with aborts for ML-DSA.

Maps to FIPS 204 as follows:
- **Commit** (Alg 7, lines 11–13): sample `y ← ExpandMask(ρ'', κ)`, compute
  `w = NTT⁻¹(Â · NTT(y))`, return `w₁ = HighBits(w)` and state `(y, w)`.
- **Respond** (Alg 7, lines 16–30): derive `c = SampleInBall(c̃)`, compute
  `z = y + c·s₁`, check `‖z‖∞ < γ₁ - β` and `‖LowBits(w - c·s₂)‖∞ < γ₂ - β`,
  compute hint `h = MakeHint(-c·t₀, w - c·s₂ + c·t₀)`, check `‖c·t₀‖∞ < γ₂`
  and hint weight `≤ ω`. Return `some (z, h)` on success, `none` on abort.
- **Verify** (Alg 8, lines 8–13): check `‖z‖∞ < γ₁ - β`, reconstruct
  `w'_Approx = Az - c · (t₁ · 2^d)`, compute `w₁' = UseHint(h, w'_Approx)`,
  check `w₁' = w₁` and hint weight `≤ ω`. -/
noncomputable def identificationScheme
    [DecidableEq (Bytes 32)] [DecidableEq prims.High] :
    IdenSchemeWithAbort
      (PublicKey p prims) (SecretKey p)
      (Commitment p prims) (SigningState p)
      (CommitHashBytes p) (Response p prims)
      (validKeyPair p prims) where
  commit := fun pk sk => do
    let aHat := prims.expandA pk.rho
    let mu := prims.hashMessage sk.tr []
    let rhoDoublePrime := prims.hashPrivateSeed sk.key (Vector.replicate 32 0) mu
    let y := prims.expandMask rhoDoublePrime 0
    let yHat := nttOps.nttVec y
    let w := nttOps.invNTTVec (nttOps.matVecMul aHat yHat)
    let w1 := prims.highBitsVec w
    return (w1, ⟨y, w⟩)
  respond := fun _pk sk st cTilde => do
    let c := prims.sampleInBall cTilde
    let cHat := nttOps.ntt c
    let cs1 := nttOps.invNTTVec
      (Vector.map (nttOps.multiplyNTTs cHat) (nttOps.nttVec sk.s1))
    let cs2 := nttOps.invNTTVec
      (Vector.map (nttOps.multiplyNTTs cHat) (nttOps.nttVec sk.s2))
    let z := st.y + cs1
    let r0 := prims.lowBitsVec (st.w - cs2)
    if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then do
      let ct0 := nttOps.invNTTVec
        (Vector.map (nttOps.multiplyNTTs cHat) (nttOps.nttVec sk.t0))
      let h := prims.makeHintVec (-ct0) (st.w - cs2 + ct0)
      if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
        return some (z, h)
      else
        return none
    else
      return none
  verify := fun pk w1 cTilde (z, h) =>
    let c := prims.sampleInBall cTilde
    let cHat := nttOps.ntt c
    let aHat := prims.expandA pk.rho
    let zHat := nttOps.nttVec z
    let t1Shifted := prims.power2RoundShiftVec pk.t1
    let t1ShiftedHat := nttOps.nttVec t1Shifted
    let azHat := nttOps.matVecMul aHat zHat
    let ct1Hat := Vector.map (nttOps.multiplyNTTs cHat) t1ShiftedHat
    let wApprox := nttOps.invNTTVec (Vector.zipWith (· - ·) azHat ct1Hat)
    let w1' := prims.useHintVec h wApprox
    decide (polyVecNorm z < p.gamma1 - p.beta) &&
    decide (w1' = w1) &&
    decide (prims.hintWeight h ≤ p.omega)

end ML_DSA
