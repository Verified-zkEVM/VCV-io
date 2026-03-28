/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Primitives

/-!
# ML-DSA Encoding Interfaces

This file records the bit-packing and byte-encoding operations referenced by the FIPS 204
pseudocode (Algorithms 16–28). In this phase they are kept abstract, but their types match the
semantic objects consumed by the spec-level KeyGen, Sign, and Verify algorithms.

## References

- NIST FIPS 204, Section 7.1–7.2 (key and signature encodings)
-/

set_option autoImplicit false

namespace ML_DSA

/-- Encoding and decoding operations used by the ML-DSA pseudocode. -/
structure Encoding (p : Params) (prims : Primitives p) where
  /-- Encoded public key bytes. -/
  EncodedPK : Type
  /-- Encoded secret key bytes. -/
  EncodedSK : Type
  /-- Encoded signature bytes. -/
  EncodedSig : Type
  /-- `pkEncode(ρ, t₁)` (Algorithm 22). -/
  pkEncode : Bytes 32 → Vector prims.Power2High p.k → EncodedPK
  /-- `pkDecode(pk)` (Algorithm 23). -/
  pkDecode : EncodedPK → Bytes 32 × Vector prims.Power2High p.k
  /-- `skEncode(ρ, K, tr, s₁, s₂, t₀)` (Algorithm 24). -/
  skEncode : Bytes 32 → Bytes 32 → Bytes 64 → RqVec p.l → RqVec p.k → RqVec p.k → EncodedSK
  /-- `skDecode(sk)` (Algorithm 25). -/
  skDecode : EncodedSK → Bytes 32 × Bytes 32 × Bytes 64 × RqVec p.l × RqVec p.k × RqVec p.k
  /-- `sigEncode(c̃, z, h)` (Algorithm 26). -/
  sigEncode : CommitHashBytes p → RqVec p.l → Vector prims.Hint p.k → EncodedSig
  /-- `sigDecode(σ)` (Algorithm 27). Returns `none` if the hint is malformed. -/
  sigDecode : EncodedSig → Option (CommitHashBytes p × RqVec p.l × Vector prims.Hint p.k)

namespace Encoding

variable {p : Params} {prims : Primitives p} (enc : Encoding p prims)

/-- Roundtrip laws for the encoding operations. -/
structure Laws : Prop where
  pkDecode_pkEncode :
    ∀ (rho : Bytes 32) (t1 : Vector prims.Power2High p.k),
      enc.pkDecode (enc.pkEncode rho t1) = (rho, t1)
  skDecode_skEncode :
    ∀ (rho K : Bytes 32) (tr : Bytes 64) (s1 : RqVec p.l) (s2 t0 : RqVec p.k),
      enc.skDecode (enc.skEncode rho K tr s1 s2 t0) = (rho, K, tr, s1, s2, t0)
  sigDecode_sigEncode :
    ∀ (cTilde : CommitHashBytes p) (z : RqVec p.l) (h : Vector prims.Hint p.k),
      enc.sigDecode (enc.sigEncode cTilde z h) = some (cTilde, z, h)

end Encoding

end ML_DSA
