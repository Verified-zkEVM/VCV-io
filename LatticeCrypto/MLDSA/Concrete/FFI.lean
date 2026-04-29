/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

/-!
# ML-DSA FFI Bindings

Lean 4 `@[extern]` declarations for the C wrappers around
[mldsa-native](<anonymized-repo-url>),
a formally verified (CBMC) C implementation of ML-DSA / FIPS 204.

Internal APIs (keygen, sign, verify) are exposed for all three approved
parameter sets: ML-DSA-44, ML-DSA-65, and ML-DSA-87.

The C side is compiled from `csrc/mldsa/lean_mldsa{,44,87}_ffi.c`, linking
against mldsa-native's monolithic `mldsa_native.c`.
-/


namespace MLDSA.Concrete.FFI

/-! ## ML-DSA-65 -/

/-- ML-DSA-65 key generation from the internal C reference implementation. -/
@[extern "lean_mldsa_keypair_internal"]
opaque mldsa65KeypairInternal : @& ByteArray → ByteArray × ByteArray

/-- ML-DSA-65 signing from the internal C reference implementation. -/
@[extern "lean_mldsa_sign_internal"]
opaque mldsa65SignInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  ByteArray

/-- ML-DSA-65 verification from the internal C reference implementation. -/
@[extern "lean_mldsa_verify_internal"]
opaque mldsa65VerifyInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  UInt8

/-! ## ML-DSA-44 -/

/-- ML-DSA-44 key generation from the internal C reference implementation. -/
@[extern "lean_mldsa44_keypair_internal"]
opaque mldsa44KeypairInternal : @& ByteArray → ByteArray × ByteArray

/-- ML-DSA-44 signing from the internal C reference implementation. -/
@[extern "lean_mldsa44_sign_internal"]
opaque mldsa44SignInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  ByteArray

/-- ML-DSA-44 verification from the internal C reference implementation. -/
@[extern "lean_mldsa44_verify_internal"]
opaque mldsa44VerifyInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  UInt8

/-! ## ML-DSA-87 -/

/-- ML-DSA-87 key generation from the internal C reference implementation. -/
@[extern "lean_mldsa87_keypair_internal"]
opaque mldsa87KeypairInternal : @& ByteArray → ByteArray × ByteArray

/-- ML-DSA-87 signing from the internal C reference implementation. -/
@[extern "lean_mldsa87_sign_internal"]
opaque mldsa87SignInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  ByteArray

/-- ML-DSA-87 verification from the internal C reference implementation. -/
@[extern "lean_mldsa87_verify_internal"]
opaque mldsa87VerifyInternal : @& ByteArray → @& ByteArray → @& ByteArray →
  UInt8

end MLDSA.Concrete.FFI
