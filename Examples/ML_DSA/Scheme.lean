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

The key generation, signing, and verification algorithms follow FIPS 204 Algorithms 6–8.

## Main Definitions

- `ML_DSA.identificationScheme`: the underlying identification scheme with aborts
- `ML_DSA.PublicKey` / `ML_DSA.SecretKey`: semantic key types
- `ML_DSA.signatureScheme`: the full signature scheme via Fiat-Shamir with Aborts

## References

- NIST FIPS 204, Algorithms 6 (KeyGen_internal), 7 (Sign_internal), 8 (Verify_internal)
- EasyCrypt `SimplifiedScheme.ec` (formosa-crypto/dilithium)
-/

set_option autoImplicit false

open OracleComp OracleSpec

namespace ML_DSA

variable (p : Params) (prims : Primitives p) (nttOps : NTTRingOps)

/-- The semantic public key: the public seed `ρ` and the compressed key vector `t₁`. -/
structure PublicKey where
  rho : Bytes 32
  t1 : Vector prims.High p.k

/-- The semantic secret key: includes the expanded public key material for efficient signing. -/
structure SecretKey where
  rho : Bytes 32
  key : Bytes 32
  tr : Bytes 64
  s1 : RqVec p.l
  s2 : RqVec p.k
  t0 : RqVec p.k

/-- The signing state: commitment data retained between commit and respond phases. -/
structure SigningState where
  y : RqVec p.l
  w : RqVec p.k
  w1 : Vector prims.High p.k

/-- The public commitment sent to the verifier (the high-order bits of `w = Ay`). -/
abbrev Commitment := Vector prims.High p.k

/-- The signature response: a short vector `z` such that `‖z‖∞ < γ₁ - β`. -/
abbrev Response := RqVec p.l

/-- ML-DSA key generation (Algorithm 6), modeled as a deterministic function from seed.

Given a 32-byte seed `ξ`:
1. Expand to `(ρ, ρ', K)`
2. Generate matrix `Â = ExpandA(ρ)`
3. Generate secret vectors `(s₁, s₂) = ExpandS(ρ')`
4. Compute `t = A·s₁ + s₂`
5. Split `t` into `(t₁, t₀)` via `Power2Round` -/
def keyGenFromSeed (seed : Bytes 32) : PublicKey p prims × SecretKey p :=
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let aHat := prims.expandA rho
  let (_s1, s2) := prims.expandS rhoPrime
  let s1Hat := nttOps.nttVec _s1
  let t := nttOps.invNTTVec (nttOps.matVecMul aHat s1Hat) + s2
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, _s1, s2, t0⟩
  (pk, sk)

/-- A key pair is valid when the public and secret keys share the same public seed `ρ`. -/
def validKeyPair [DecidableEq (Bytes 32)]
    (_pk : PublicKey p prims) (sk : SecretKey p) : Bool :=
  _pk.rho == sk.rho

/-- The underlying identification scheme with aborts for ML-DSA.

This captures the Fiat-Shamir structure of ML-DSA:
- **Statement** = public key, **Witness** = secret key
- **Commit**: sample masking vector `y`, compute `w₁ = HighBits(Ay)`
- **Challenge**: a hash `c̃` (modeled as `CommitHashBytes`)
- **Respond**: compute `z = y + cs₁`, reject if norms too large (return `none`)
- **Verify**: check `‖z‖∞ < γ₁ - β` and commitment consistency -/
noncomputable def identificationScheme [DecidableEq (Bytes 32)] :
    IdenSchemeWithAbort
      (PublicKey p prims) (SecretKey p)
      (Commitment p prims) (SigningState p prims)
      (CommitHashBytes p) (Response p)
      (validKeyPair p prims) where
  commit := fun _pk sk => do
    let aHat := prims.expandA _pk.rho
    let mu := prims.hashMessage sk.tr []
    let rhoDoublePrime := prims.hashPrivateSeed sk.key (Vector.replicate 32 0) mu
    let y := prims.expandMask rhoDoublePrime 0
    let yHat := nttOps.nttVec y
    let w := nttOps.invNTTVec (nttOps.matVecMul aHat yHat)
    let w1 := prims.highBitsVec w
    return (w1, ⟨y, w, w1⟩)
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
        return some z
      else
        return none
    else
      return none
  verify := fun _pk _w1 _cTilde z =>
    decide (polyVecNorm z < p.gamma1 - p.beta)

end ML_DSA
