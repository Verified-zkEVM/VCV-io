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

/-! ## ML-KEM-768 (deterministic) -/

@[extern "lean_mlkem_keypair_derand"]
opaque mlkemKeypairDerand : @& ByteArray → ByteArray × ByteArray

@[extern "lean_mlkem_enc_derand"]
opaque mlkemEncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

@[extern "lean_mlkem_dec"]
opaque mlkemDec : @& ByteArray → @& ByteArray → ByteArray

/-! ## ML-KEM-512 (deterministic) -/

@[extern "lean_mlkem512_keypair_derand"]
opaque mlkem512KeypairDerand : @& ByteArray → ByteArray × ByteArray

@[extern "lean_mlkem512_enc_derand"]
opaque mlkem512EncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

@[extern "lean_mlkem512_dec"]
opaque mlkem512Dec : @& ByteArray → @& ByteArray → ByteArray

/-! ## ML-KEM-1024 (deterministic) -/

@[extern "lean_mlkem1024_keypair_derand"]
opaque mlkem1024KeypairDerand : @& ByteArray → ByteArray × ByteArray

@[extern "lean_mlkem1024_enc_derand"]
opaque mlkem1024EncDerand : @& ByteArray → @& ByteArray → ByteArray × ByteArray

@[extern "lean_mlkem1024_dec"]
opaque mlkem1024Dec : @& ByteArray → @& ByteArray → ByteArray

end MLKEM.Concrete.FFI
