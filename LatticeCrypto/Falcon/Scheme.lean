/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.Falcon.Primitives
import VCVio.CryptoFoundations.GPVHashAndSign
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
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
- **Signing** (Falcon+): on each attempt, sample a fresh 40-byte salt `r`, hash
  `c = HashToPoint(r, pk, message)` to a target in `R_q`, use `ffSampling` with the secret
  basis to find a short preimage `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`, then check the
  norm bound and compress. Retry with a new salt on failure.
- **Verification**: recompute `c`, recover `s₁ = c - s₂ · h mod q`, check
  `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.

The signing flow follows the Falcon+ convention (fresh salt per retry, pk-bound hashing),
matching the concrete executable signer in `LatticeCrypto.Falcon.Concrete.Sign`.

## References

- Falcon specification v1.2, Algorithms 1–16
- FIPS 206 (FN-DSA) draft
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008.
-/


open OracleComp OracleSpec

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### Key Types -/

/-- The Falcon public key: a single polynomial `h ∈ R_q` where `h = g · f⁻¹ mod q`. -/
structure PublicKey where
  h : Rq p.n

noncomputable instance : DecidableEq (PublicKey p) := by
  intro a b
  cases a with
  | mk h1 =>
    cases b with
    | mk h2 =>
      simpa using (inferInstanceAs (Decidable (h1 = h2)))

/-- The Falcon secret key: the short NTRU basis polynomials `(f, g, F, G)` over `ℤ`,
plus the precomputed Falcon tree for efficient signing.

The FFT recursion depth is `p.fftDepth = p.logn - 1`. The tree encodes the normalized
LDL decomposition of the Gram matrix `[[g, -f], [G, -F]]^T · [[g, -f], [G, -F]]`
in packed FFT representation. -/
structure SecretKey where
  f : IntPoly p.n
  g : IntPoly p.n
  capF : IntPoly p.n
  capG : IntPoly p.n
  tree : FalconTree p.fftDepth

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

/-- Decidable equality reduces the Falcon NTRU equation to decidable polynomial equality. -/
instance (f g capF capG : IntPoly p.n) : Decidable (ntruEquation p f g capF capG) :=
  inferInstanceAs (Decidable (_ = _))

/-- A key pair is valid when:
1. The NTRU equation holds: `fG - gF = q`.
2. The public key satisfies `h = g · f⁻¹ mod q` (i.e., `f · h = g mod q`). -/
noncomputable def validKeyPair (pk : PublicKey p) (sk : SecretKey p) : Bool :=
  decide (ntruEquation p sk.f sk.g sk.capF sk.capG) &&
  decide (negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)

@[simp]
theorem validKeyPair_eq_true_iff (pk : PublicKey p) (sk : SecretKey p) :
    validKeyPair p pk sk = true ↔
      ntruEquation p sk.f sk.g sk.capF sk.capG ∧
      negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g := by
  simp [validKeyPair]

/-! ### Core Algorithms -/

/-- Falcon key generation (Algorithms 4–9).

1. Generate short polynomials `(f, g)` via NTRUGen (Algorithm 5).
2. Compute `(F, G)` satisfying the NTRU equation `fG - gF = q` (Algorithm 6).
3. Compute `h = g · f⁻¹ mod q`.
4. Build the Falcon tree via `ffLDL*` and normalize (Algorithms 8–9).

This is modeled as a deterministic function from a seed. The actual NTRUGen uses
rejection sampling, but that detail is abstracted away. -/
noncomputable def keyGenFromSeed (_seed : List Byte) : PublicKey p × SecretKey p := sorry

/-! ### GPV Bridge -/

/-- Convert a target `c ∈ R_q` and the secret NTRU basis to an FFT-domain target vector
for `ffSampling`.

This follows Falcon's `fpoly_apply_basis`: interpret `c` as the integer target polynomial
`hm`, take its packed FFT, and form

- `t₀ = (1/q) · FFT(hm) · FFT(-F)`
- `t₁ = (-1/q) · FFT(-f) · FFT(hm)`

where `(f, F)` come from the secret basis `[[g, -f], [G, -F]]`. -/
noncomputable def toFFTTarget (c : Rq p.n) (sk : SecretKey p) :
    FFTPair p.fftDepth :=
  let hmFFT := prims.fftTarget c
  let b01 := prims.fftInt (-sk.f)
  let b11 := prims.fftInt (-sk.capF)
  let invQ : ℝ := (1 : ℝ) / (modulus : ℝ)
  let t₀ := Primitives.scaleFFT invQ (Primitives.mulFFT hmFFT b11)
  let t₁ := Primitives.scaleFFT (-invQ) (Primitives.mulFFT b01 hmFFT)
  (t₀, t₁)

/-- Convert the ffSampling output back to a pair `(s₁, s₂) ∈ R_q × R_q`.

Given the hash target `c`, the secret basis, and the sampled FFT-domain vector `z`, this
reconstructs the lattice point `v = z · [[g, -f], [G, -F]]`, inverse-transforms and rounds
it to coefficients, then returns

- `s₁ = c - v₀`
- `s₂ = -v₁`

This matches the post-sampling basis application in Falcon's reference signing flow. -/
noncomputable def fromFFTPreimage (c : Rq p.n) (sk : SecretKey p)
    (z : FFTPair p.fftDepth) : Rq p.n × Rq p.n :=
  let v₀FFT := Primitives.mulFFT z.1 (prims.fftInt sk.g) +
    Primitives.mulFFT z.2 (prims.fftInt sk.capG)
  let v₁FFT := -(Primitives.mulFFT z.1 (prims.fftInt sk.f) +
    Primitives.mulFFT z.2 (prims.fftInt sk.capF))
  let v₀ := IntPoly.toRq (prims.ifftRound v₀FFT)
  let v₁ := IntPoly.toRq (prims.ifftRound v₁FFT)
  (c - v₀, -v₁)

/-- Falcon as a `PreimageSampleableFunction`.

The PSF maps `(s₁, s₂) ↦ s₁ + s₂ · h mod q`, the "hash" in the hash-and-sign
paradigm. The trapdoor sampler uses `ffSampling` to find short preimages. The
shortness predicate checks the `ℓ₂` norm bound.

| PSF field | Falcon instantiation |
|---|---|
| `eval pk (s₁, s₂)` | `s₁ + s₂ · h mod q` |
| `trapdoorSample pk sk c` | `ffSampling(...)` producing short `(s₁, s₂)` |
| `isShort (s₁, s₂)` | `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` |

The trapdoor sampler:
1. Converts target `c` to an FFT-domain vector using the NTRU basis (`toFFTTarget`).
2. Calls `ffSampling` with the Falcon tree to sample a nearby integer lattice point.
3. Converts the result back to `(s₁, s₂) ∈ R_q²` (`fromFFTPreimage`).

The correctness obligation is that the output distribution is close (in Rényi divergence)
to the ideal discrete Gaussian over the NTRU lattice coset. -/
noncomputable def falconPSF : PreimageSampleableFunction
    (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval pk x := x.1 + negacyclicMul x.2 pk.h
  trapdoorSample _pk sk c := do
    let t := toFFTTarget p prims c sk
    let z ← Primitives.ffSampling prims p.fftDepth t sk.tree
    return fromFFTPreimage p prims c sk z
  isShort x := decide (pairL2NormSq x.1 x.2 ≤ p.betaSquared)

/-! ### One-Shot Signing -/

/-- A single signing attempt (Falcon+, one-shot core).

Given a hash target `c ∈ R_q` (already computed from a salt and the message), uses
the trapdoor sampler (`falconPSF.trapdoorSample`) to produce a candidate short
preimage `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`. Returns the preimage if the norm
check `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` passes, or `none` to signal retry.

This separates the trapdoor-sampling obligation from retry logic: proofs about
sampling quality target `falconPSF.trapdoorSample`, while the retry loop is handled
by `sign`. -/
noncomputable def signAttempt (pk : PublicKey p) (sk : SecretKey p) (c : Rq p.n) :
    ProbComp (Option (Rq p.n × Rq p.n)) := do
  let x ← (falconPSF p prims).trapdoorSample pk sk c
  if (falconPSF p prims).isShort x then
    return some x
  else
    return none

/-- Falcon signing (Falcon+, Algorithm 10).

On each attempt:
1. Sample a fresh 40-byte salt `r`.
2. Hash `c = HashToPoint(r, pk, message)` to get the target in `R_q`.
3. Use the secret key to sample a short preimage `(s₁, s₂)` via `signAttempt`.
4. If the norm check passes and compression succeeds, return `(r, compress(s₂))`.
5. Otherwise retry with a new salt.

The fresh-salt-per-retry structure matches the Falcon+ convention and the concrete
executable signer in `LatticeCrypto.Falcon.Concrete.Sign.concreteSign`. -/
noncomputable def sign (pk : PublicKey p) (sk : SecretKey p) (msg : List Byte) :
    ProbComp Signature := sorry

/-- Falcon verification (Algorithm 16).

Given `(pk, message, signature)`:
1. Decompress `s₂` from the signature.
2. Recompute `c = HashToPoint(r, pk, message)`.
3. Compute `s₁ = c - s₂ · h mod q`.
4. Accept iff `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`. -/
noncomputable def verify (pk : PublicKey p) (msg : List Byte) (sig : Signature) : Bool :=
  match prims.decompress sig.compressedS2 p.sbytelen with
  | none => false
  | some s2Int =>
    let c := prims.hashToPointForPublicKey pk.h sig.salt msg
    let s2 := IntPoly.toRq s2Int
    let s1 := c - negacyclicMul s2 pk.h
    decide (pairL2NormSq s1 s2 ≤ p.betaSquared)

/-! ### GPV Signature Scheme -/

/-- The Falcon signature scheme as a `GPVHashAndSign` instantiation, parameterized by
a salt type `Salt`.

This connects Falcon to the generic GPV framework, enabling the generic EUF-CMA
security theorem to be applied. The message type is `List Byte` and the random oracle
maps `(salt, message)` to elements of `R_q`.

The GPV construction internally samples a fresh salt per signing query and queries
the random oracle at `(salt, message)`, matching the Falcon+ convention.

The Falcon specification uses `Salt = Bytes 40` (40 random bytes = 320 bits),
chosen as `λ + log₂(Q_s)` for `λ = 256` and `Q_s = 2^64` (Section 2.2.2). -/
noncomputable def falconSignatureAlg
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt]
    [SampleableType (Rq p.n)]
    [DecidableEq (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p)) :
    SignatureAlg (OracleComp (unifSpec + (Salt × List Byte →ₒ Rq p.n)))
      (M := List Byte) (PK := PublicKey p) (SK := SecretKey p)
      (S := Salt × (Rq p.n × Rq p.n)) :=
  GPVHashAndSign (falconPSF p prims) hr (List Byte) Salt

end Falcon
