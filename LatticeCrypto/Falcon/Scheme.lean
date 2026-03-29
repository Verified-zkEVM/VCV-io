/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Primitives
import VCVio.CryptoFoundations.GPVHashAndSign
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.Coercions.Add

/-!
# Falcon Signature Scheme

This file defines the core Falcon signature scheme algorithms: key generation, signing,
and verification. It also establishes the bridge to the generic GPV hash-and-sign framework
via a `PreimageSampleableFunction` instantiation.

## Architecture

The Falcon scheme is an instantiation of the GPV hash-and-sign framework over NTRU lattices:

- **Public key**: `h = g · f⁻¹ mod q` (a single polynomial in `R_q`).
- **Secret key**: short integer polynomials `(f, g, F, G)` satisfying the NTRU equation
  `fG - gF = q`, plus the precomputed Falcon tree for fast sampling.
- **Signing**: hash the message to a target `c ∈ R_q`, use `ffSampling` with the secret
  basis to find a short preimage `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`.
- **Verification**: recompute `c`, recover `s₁ = c - s₂ · h mod q`, check
  `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.

## References

- Falcon specification v1.2, Algorithms 1–16
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008.
-/

set_option autoImplicit false

open OracleComp OracleSpec

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### Key Types -/

/-- The Falcon public key: a single polynomial `h ∈ R_q` where `h = g · f⁻¹ mod q`. -/
structure PublicKey where
  h : Rq p.n
deriving DecidableEq

/-- The Falcon secret key: the short NTRU basis polynomials `(f, g, F, G)` over `ℤ`,
plus the precomputed Falcon tree for efficient signing.

The log-degree `logn` is `Nat.log2 p.n`. The tree encodes the normalized LDL decomposition
of the Gram matrix `[[g, -f], [G, -F]]^T · [[g, -f], [G, -F]]` in FFT representation. -/
structure SecretKey where
  f : IntPoly p.n
  g : IntPoly p.n
  capF : IntPoly p.n
  capG : IntPoly p.n
  tree : FalconTree p.logn

/-- A Falcon signature: a 40-byte random salt `r` paired with the compressed
representation of the short polynomial `s₂`. -/
structure Signature where
  salt : Bytes 40
  compressedS2 : List Byte

/-! ### NTRU Equation -/

/-- The NTRU equation over `ℤ[x]/(x^n + 1)`:
  `f · G - g · F = q`
This is the fundamental algebraic relation that the Falcon secret key must satisfy.
It ensures that `[[g, -f], [G, -F]]` forms a basis of the NTRU lattice. -/
def ntruEquation (f g capF capG : IntPoly p.n) : Prop :=
  intPolyMul f capG - intPolyMul g capF = intPolyConst (modulus : ℤ)

instance (f g capF capG : IntPoly p.n) : Decidable (ntruEquation p f g capF capG) :=
  inferInstanceAs (Decidable (_ = _))

/-- A key pair is valid when:
1. The NTRU equation holds: `fG - gF = q`.
2. The public key satisfies `h = g · f⁻¹ mod q` (i.e., `f · h = g mod q`). -/
def validKeyPair (pk : PublicKey p) (sk : SecretKey p) : Bool :=
  decide (ntruEquation p sk.f sk.g sk.capF sk.capG) &&
  decide (negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)

@[simp]
theorem validKeyPair_eq_true_iff (pk : PublicKey p) (sk : SecretKey p) :
    validKeyPair p pk sk = true ↔
      ntruEquation p sk.f sk.g sk.capF sk.capG ∧
      negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g := by
  simp [validKeyPair, Bool.and_eq_true]

/-! ### Core Algorithms -/

/-- Falcon key generation (Algorithms 4–9).

1. Generate short polynomials `(f, g)` via NTRUGen (Algorithm 5).
2. Compute `(F, G)` satisfying the NTRU equation `fG - gF = q` (Algorithm 6).
3. Compute `h = g · f⁻¹ mod q`.
4. Build the Falcon tree via `ffLDL*` and normalize (Algorithms 8–9).

This is modeled as a deterministic function from a seed. The actual NTRUGen uses
rejection sampling, but that detail is abstracted away. -/
def keyGenFromSeed (_seed : List Byte) : PublicKey p × SecretKey p := sorry

/-- Falcon signing (Algorithm 10).

Given `(pk, sk, message)`:
1. Sample a 40-byte random salt `r`.
2. Hash `c = HashToPoint(r ‖ message)` to get the target in `R_q`.
3. Compute the FFT of the target vector `t = (t₀, t₁)` where:
   `t₀ = (1/q) · FFT(c) · FFT(F)`, `t₁ = (1/q) · FFT(c) · FFT(f)`.
4. Call `ffSampling(t, tree)` to get integer vector `z = (z₀, z₁)`.
5. Compute `s₂ = t₁ - z₁` (the signature polynomial, over ℤ).
6. Check `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` where `s₁ = c - s₂ · h mod q`.
7. Compress `s₂` and return `(r, compress(s₂))`.

Steps 1–7 are retried if the norm check fails or compression fails. -/
noncomputable def sign (pk : PublicKey p) (sk : SecretKey p) (msg : List Byte) :
    ProbComp Signature := sorry

/-- Falcon verification (Algorithm 16).

Given `(pk, message, signature)`:
1. Decompress `s₂` from the signature.
2. Recompute `c = HashToPoint(r ‖ message)`.
3. Compute `s₁ = c - s₂ · h mod q`.
4. Accept iff `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`. -/
def verify (pk : PublicKey p) (msg : List Byte) (sig : Signature) : Bool :=
  match prims.decompress sig.compressedS2 p.sbytelen with
  | none => false
  | some s2Int =>
    let c := prims.hashToPoint sig.salt msg
    let s2 := IntPoly.toRq s2Int
    let s1 := c - negacyclicMul s2 pk.h
    decide (pairL2NormSq s1 s2 ≤ p.betaSquared)

/-! ### GPV Bridge -/

/-- Falcon as a `PreimageSampleableFunction`.

The PSF maps `(s₁, s₂) ↦ s₁ + s₂ · h mod q` — this is the "hash" in the hash-and-sign
paradigm. The trapdoor sampler uses `ffSampling` to find short preimages. The shortness
predicate checks the ℓ₂ norm bound.

| PSF field | Falcon instantiation |
|---|---|
| `eval pk (s₁, s₂)` | `s₁ + s₂ · h mod q` |
| `trapdoorSample pk sk c` | `ffSampling(...)` producing short `(s₁, s₂)` |
| `isShort (s₁, s₂)` | `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` | -/
def falconPSF : PreimageSampleableFunction
    (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval pk x := x.1 + negacyclicMul x.2 pk.h
  trapdoorSample _pk _sk _c := sorry
  isShort x := decide (pairL2NormSq x.1 x.2 ≤ p.betaSquared)

/-- The Falcon signature scheme as a `GPVHashAndSign` instantiation.

This connects Falcon to the generic GPV framework, enabling the generic EUF-CMA
security theorem to be applied. The message type is `List Byte`, the salt type is
`Bytes 40`, and the random oracle maps `(salt, message)` to elements of `R_q`.

Note: this requires `GenerableRelation` and various `SampleableType` instances that
are stated as hypotheses. -/
noncomputable def falconSignatureAlg
    [SampleableType (PublicKey p)] [SampleableType (SecretKey p)]
    [SampleableType (Bytes 40)] [SampleableType (Rq p.n)]
    [DecidableEq (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p)) :
    SignatureAlg (OracleComp (unifSpec + (Bytes 40 × List Byte →ₒ Rq p.n)))
      (M := List Byte) (PK := PublicKey p) (SK := SecretKey p)
      (S := Bytes 40 × (Rq p.n × Rq p.n)) :=
  GPVHashAndSign (falconPSF p) hr (List Byte) (Bytes 40)

end Falcon
