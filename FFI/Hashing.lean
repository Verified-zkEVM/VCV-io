/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

/-!
# SHA-3 / FIPS 202 FFI Bindings

Lean 4 `@[extern]` declarations for SHA-3 and SHAKE hash functions, backed by the C
implementation from [mlkem-native](<anonymized-repo-url>).

These primitives are shared across ML-KEM (FIPS 203) and ML-DSA (FIPS 204).
-/


namespace FFI.Hashing

/-- SHA3-256: produces a 32-byte digest. -/
@[extern "lean_sha3_256"]
opaque sha3_256 : @& ByteArray → ByteArray

/-- SHA3-512: produces a 64-byte digest. -/
@[extern "lean_sha3_512"]
opaque sha3_512 : @& ByteArray → ByteArray

/-- SHAKE-256 XOF: produces `outLen` bytes of output. -/
@[extern "lean_shake256"]
opaque shake256 : @& ByteArray → (outLen : USize) → ByteArray

/-- SHAKE-128 XOF: produces `outLen` bytes of output. -/
@[extern "lean_shake128"]
opaque shake128 : @& ByteArray → (outLen : USize) → ByteArray

end FFI.Hashing
