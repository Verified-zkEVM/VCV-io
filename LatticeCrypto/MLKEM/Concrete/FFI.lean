/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import FFI.Hashing

/-!
# ML-KEM FFI Bindings

Lean 4 `@[extern]` declarations for the C wrapper around
[mlkem-native](https://github.com/pq-code-package/mlkem-native),
a formally verified (CBMC + HOL-Light) C90 implementation of ML-KEM / FIPS 203.

Two groups of functions are exposed:

1. **SHA-3 / FIPS 202** primitives — re-exported from `FFI.Hashing` for backward
   compatibility with existing callers.

2. **End-to-end ML-KEM** deterministic API (`mlkemKeypairDerand`, `mlkemEncDerand`,
   `mlkemDec`) — used as a reference oracle in tests.

The C side is compiled from `csrc/mlkem/lean_mlkem_ffi.c`, which `#include`s
mlkem-native's monolithic `mlkem_native.c` (pinned at `v1.1.0`).
-/

set_option autoImplicit false

namespace MLKEM.Concrete.FFI

/-! ## SHA-3 / FIPS 202 (re-exported from `FFI.Hashing`) -/

/-- Re-export of the SHA3-256 binding from `FFI.Hashing`. -/
abbrev sha3_256 := FFI.Hashing.sha3_256
/-- Re-export of the SHA3-512 binding from `FFI.Hashing`. -/
abbrev sha3_512 := FFI.Hashing.sha3_512
/-- Re-export of the SHAKE-256 binding from `FFI.Hashing`. -/
abbrev shake256 := FFI.Hashing.shake256
/-- Re-export of the SHAKE-128 binding from `FFI.Hashing`. -/
abbrev shake128 := FFI.Hashing.shake128

/-! ## ML-KEM-768 (deterministic) -/

/-- Deterministic ML-KEM-768 key generation from explicit randomness. -/
@[extern "lean_mlkem_keypair_derand"]
opaque mlkemKeypairDerand : @& ByteArray → ByteArray × ByteArray

/-- Deterministic ML-KEM-768 encapsulation from explicit message/randomness input. -/
@[extern "lean_mlkem_enc_derand"]
opaque mlkemEncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

/-- ML-KEM-768 decapsulation. -/
@[extern "lean_mlkem_dec"]
opaque mlkemDec : @& ByteArray → @& ByteArray → ByteArray

/-! ## ML-KEM-512 (deterministic) -/

/-- Deterministic ML-KEM-512 key generation from explicit randomness. -/
@[extern "lean_mlkem512_keypair_derand"]
opaque mlkem512KeypairDerand : @& ByteArray → ByteArray × ByteArray

/-- Deterministic ML-KEM-512 encapsulation from explicit message/randomness input. -/
@[extern "lean_mlkem512_enc_derand"]
opaque mlkem512EncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

/-- ML-KEM-512 decapsulation. -/
@[extern "lean_mlkem512_dec"]
opaque mlkem512Dec : @& ByteArray → @& ByteArray → ByteArray

/-! ## ML-KEM-1024 (deterministic) -/

/-- Deterministic ML-KEM-1024 key generation from explicit randomness. -/
@[extern "lean_mlkem1024_keypair_derand"]
opaque mlkem1024KeypairDerand : @& ByteArray → ByteArray × ByteArray

/-- Deterministic ML-KEM-1024 encapsulation from explicit message/randomness input. -/
@[extern "lean_mlkem1024_enc_derand"]
opaque mlkem1024EncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

/-- ML-KEM-1024 decapsulation. -/
@[extern "lean_mlkem1024_dec"]
opaque mlkem1024Dec : @& ByteArray → @& ByteArray → ByteArray

end MLKEM.Concrete.FFI
