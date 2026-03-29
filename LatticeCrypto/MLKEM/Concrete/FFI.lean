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

abbrev sha3_256 := FFI.Hashing.sha3_256
abbrev sha3_512 := FFI.Hashing.sha3_512
abbrev shake256 := FFI.Hashing.shake256
abbrev shake128 := FFI.Hashing.shake128

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
