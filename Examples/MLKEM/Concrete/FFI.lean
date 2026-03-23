/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# ML-KEM FFI Bindings

Lean 4 `@[extern]` declarations for the C wrapper around
[mlkem-native](https://github.com/pq-code-package/mlkem-native),
a formally verified (CBMC + HOL-Light) C90 implementation of ML-KEM / FIPS 203.

Two groups of functions are exposed:

1. **SHA-3 / FIPS 202** primitives (`sha3_256`, `sha3_512`, `shake128`, `shake256`) —
   used to instantiate the abstract `Primitives` interface.

2. **End-to-end ML-KEM** deterministic API (`mlkemKeypairDerand`, `mlkemEncDerand`,
   `mlkemDec`) — used as a reference oracle in tests.

The C side is compiled from `ffi/mlkem/lean_mlkem_ffi.c`, which `#include`s
mlkem-native's monolithic `mlkem_native.c` (pinned at `v1.1.0`).
-/

set_option autoImplicit false

namespace MLKEM.Concrete.FFI

/-! ## SHA-3 / FIPS 202 -/

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

/-! ## End-to-end ML-KEM (deterministic, ML-KEM-768) -/

/-- Deterministic key generation (FIPS 203 Algorithm 16).
    Input: 64 bytes of coins `d ‖ z`. Output: `(ek, dk)`. -/
@[extern "lean_mlkem_keypair_derand"]
opaque mlkemKeypairDerand : @& ByteArray → ByteArray × ByteArray

/-- Deterministic encapsulation (FIPS 203 Algorithm 17).
    Input: encapsulation key `ek`, 32-byte message `m`. Output: `(ct, ss)`. -/
@[extern "lean_mlkem_enc_derand"]
opaque mlkemEncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

/-- Decapsulation (FIPS 203 Algorithm 18/21).
    Input: decapsulation key `dk`, ciphertext `ct`. Output: shared secret `ss`. -/
@[extern "lean_mlkem_dec"]
opaque mlkemDec : @& ByteArray → @& ByteArray → ByteArray

end MLKEM.Concrete.FFI
