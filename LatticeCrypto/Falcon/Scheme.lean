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
  simp [validKeyPair, Bool.and_eq_true, decide_eq_true_eq]

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

/-- Falcon as a `PreimageSampleableFunction`.

The PSF maps `(s₁, s₂) ↦ s₁ + s₂ · h mod q`, the "hash" in the hash-and-sign
paradigm. The trapdoor sampler uses `ffSampling` to find short preimages. The
shortness predicate checks the `ℓ₂` norm bound.

| PSF field | Falcon instantiation |
|---|---|
| `eval pk (s₁, s₂)` | `s₁ + s₂ · h mod q` |
| `trapdoorSample pk sk c` | `ffSampling(...)` producing short `(s₁, s₂)` |
| `isShort (s₁, s₂)` | `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` |

The trapdoor sampler abstracts the `ffSampling`-based preimage production. Its
correctness obligation is: the output distribution is close (in Rényi divergence)
to the ideal discrete Gaussian over the NTRU lattice coset. -/
noncomputable def falconPSF : PreimageSampleableFunction
    (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval pk x := x.1 + negacyclicMul x.2 pk.h
  trapdoorSample _pk _sk _c := sorry
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
  let x ← (falconPSF p).trapdoorSample pk sk c
  if (falconPSF p).isShort x then
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
  GPVHashAndSign (falconPSF p) hr (List Byte) Salt

end Falcon
