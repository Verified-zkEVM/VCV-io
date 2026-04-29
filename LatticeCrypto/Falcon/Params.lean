/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Falcon Parameters

This file collects the fixed constants and approved parameter sets from the Falcon
specification v1.2 (Section 3.13, Table 3.3). Continuous parameters (standard deviations,
sampler bounds) use `ℝ` (Mathlib Real) rather than `Float`, since the formalization targets
the exact-arithmetic specification level. See `LatticeCrypto/DiscreteGaussian.lean` for the
corresponding ideal distribution.

## References

- Falcon specification v1.2, Section 3.13 (Table 3.3: Falcon parameter sets)
- NIST FIPS 206 (FN-DSA) draft
-/


namespace Falcon

/-- Byte values used by the concrete Falcon encodings and hash inputs. -/
abbrev Byte := UInt8

/-- Fixed-length byte vectors used by the Falcon specification interfaces. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- The fixed modulus used by Falcon: `q = 12289`, the smallest prime of the form
`k · 2n + 1` with `n ≥ 512`. Specifically `12289 = 12 · 1024 + 1`. -/
def modulus : ℕ := 12289

/-- The variable parameters that distinguish the Falcon parameter sets. Continuous
parameters use `ℝ` following the exact-arithmetic specification. -/
structure Params where
  /-- Ring degree: the degree of `φ = x^n + 1`. Must be a power of 2. -/
  n : ℕ
  /-- Signature standard deviation `σ` (Falcon spec, Table 3.3).
  This is the target standard deviation for the discrete Gaussian sampler over the lattice. -/
  sigma : ℝ
  /-- Minimum sampler standard deviation `σ_min` (lower bound for SamplerZ).
  Ensures sufficient entropy in each coordinate sample. -/
  sigmaMin : ℝ
  /-- Squared ℓ₂ norm bound `⌊β²⌋` for signature verification.
  A signature `(s₁, s₂)` is accepted iff `‖(s₁, s₂)‖₂² ≤ betaSquared`. -/
  betaSquared : ℕ
  /-- Signature byte length (compressed signature encoding). -/
  sbytelen : ℕ

/-- The log₂ of the ring degree. For Falcon-512, `logn = 9`; for Falcon-1024, `logn = 10`. -/
def Params.logn (p : Params) : ℕ := Nat.log2 p.n

namespace Params

/-- The depth of Falcon's recursive FFT tree.

Falcon's packed FFT polynomials of degree `n = 2^logn` have length `n`, and the recursive
sampler stops at `logn = 1` (packed length `2`). Thus the tree depth is `logn - 1`. -/
def fftDepth (p : Params) : ℕ := p.logn - 1

/-- Size of the public key in bytes: 1 (header) + 14 · n / 8 bits per coefficient of `h`,
since `q = 12289 < 2^14`. -/
def publicKeyBytes (p : Params) : ℕ := 1 + 14 * p.n / 8

/-- Size of the encoded Falcon secret key in bytes for the supported parameter sets:
`1281` for Falcon-512 and `2305` for Falcon-1024. -/
def secretKeyBytesForDegree (n : ℕ) : ℕ :=
  match n with
  | 512 => 1281
  | 1024 => 2305
  | _ => panic! s!"Falcon secretKeyBytes is only defined for supported degrees, got n={n}"

/-- Size of the encoded Falcon secret key in bytes for the supported parameter sets:
`1281` for Falcon-512 and `2305` for Falcon-1024. -/
def secretKeyBytes (p : Params) : ℕ := secretKeyBytesForDegree p.n

/-- Maximum signature size in bytes: 1 (header) + 40 (salt) + sbytelen (compressed s₂). -/
def signatureBytes (p : Params) : ℕ := 1 + 40 + p.sbytelen

end Params

/-- The approved named parameter sets from the Falcon specification. -/
inductive ParameterSet where
  | Falcon512
  | Falcon1024
deriving Repr, DecidableEq

namespace ParameterSet

/-- Interpret a named parameter set as the corresponding parameter record.
Values from Falcon spec v1.2, Table 3.3.

Note: `sigma`, `sigmaMin` are given as `ℝ` literals. The exact rational values from the
spec are:
- Falcon-512: `σ = 165.7366171829776`, `σ_min = 1.2778336969128337`
- Falcon-1024: `σ = 168.38857144654395`, `σ_min = 1.298280334344292` -/
noncomputable def params : ParameterSet → Params
  | .Falcon512 => {
      n := 512
      sigma := (1657366171829776 : ℝ) / 10000000000000
      sigmaMin := (12778336969128337 : ℝ) / 10000000000000000
      betaSquared := 34034726
      sbytelen := 625 }
  | .Falcon1024 => {
      n := 1024
      sigma := (16838857144654395 : ℝ) / 100000000000000
      sigmaMin := (1298280334344292 : ℝ) / 1000000000000000
      betaSquared := 70265242
      sbytelen := 1239 }

end ParameterSet

/-- The approved Falcon-512 parameter record. -/
noncomputable def falcon512 : Params := ParameterSet.params .Falcon512
/-- The approved Falcon-1024 parameter record. -/
noncomputable def falcon1024 : Params := ParameterSet.params .Falcon1024

/-- Recognize the approved Falcon parameter sets. -/
noncomputable def Params.isApproved (params : Params) : Prop :=
  params = falcon512 ∨ params = falcon1024

end Falcon
