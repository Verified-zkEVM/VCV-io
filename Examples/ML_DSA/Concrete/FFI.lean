/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# ML-DSA FFI Bindings

Lean 4 `@[extern]` declarations for the C wrapper around
[mldsa-native](https://github.com/pq-code-package/mldsa-native),
a formally verified (CBMC) C implementation of ML-DSA / FIPS 204.

Three internal functions are exposed for ML-DSA-65:

1. `mldsa65KeypairInternal` — FIPS 204 Algorithm 6 (ML-DSA.KeyGen_internal)
2. `mldsa65SignInternal`    — FIPS 204 Algorithm 7 (ML-DSA.Sign_internal)
3. `mldsa65VerifyInternal`  — FIPS 204 Algorithm 8 (ML-DSA.Verify_internal)

The C side is compiled from `ffi/mldsa/lean_mldsa_ffi.c`, which links against
mldsa-native's monolithic `mldsa_native.c` (pinned at `v1.0.0-beta`).
-/

set_option autoImplicit false

namespace MLDSA.Concrete.FFI

/-- Deterministic internal key generation (FIPS 204 Algorithm 6).
    Input: 32-byte seed `ξ`. Output: `(pk, sk)` as serialized byte arrays. -/
@[extern "lean_mldsa_keypair_internal"]
opaque mldsa65KeypairInternal : @& ByteArray → ByteArray × ByteArray

/-- Deterministic internal signing (FIPS 204 Algorithm 7).
    Input: secret key `sk`, message `msg`, 32-byte randomness `rnd`.
    Output: signature bytes (empty on failure).
    For deterministic signing, pass `rnd = 0^32`. -/
@[extern "lean_mldsa_sign_internal"]
opaque mldsa65SignInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  ByteArray

/-- Internal verification (FIPS 204 Algorithm 8).
    Input: public key `pk`, message `msg`, signature `sig`.
    Returns `1` on success, `0` on failure. -/
@[extern "lean_mldsa_verify_internal"]
opaque mldsa65VerifyInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  UInt8

end MLDSA.Concrete.FFI
