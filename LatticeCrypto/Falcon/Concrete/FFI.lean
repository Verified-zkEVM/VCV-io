/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Falcon FFI Bindings

Lean 4 `@[extern]` declarations for the C wrapper around
[c-fn-dsa](https://github.com/pornin/c-fn-dsa), Thomas Pornin's
reference implementation of FN-DSA (FIPS 206).

Six functions are exposed covering both Falcon-512 (logn=9) and
Falcon-1024 (logn=10):

1. `falcon512KeygenSeeded` / `falcon1024KeygenSeeded` — deterministic keygen
2. `falcon512SignSeeded` / `falcon1024SignSeeded` — deterministic signing
3. `falcon512Verify` / `falcon1024Verify` — verification

The C side is compiled from `csrc/falcon/lean_falcon_ffi.c`, which links
against the c-fn-dsa SCU amalgamation (`csrc/falcon/fndsa_native.c`).
-/


namespace Falcon.Concrete.FFI

/-- Deterministic key generation for Falcon-512 (logn=9).
    Input: arbitrary-length seed. Output: `(sk, pk)` as serialized byte arrays.
    sk is 1281 bytes, pk is 897 bytes. -/
@[extern "lean_falcon512_keygen_seeded"]
opaque falcon512KeygenSeeded : @& ByteArray → ByteArray × ByteArray

/-- Deterministic signing for Falcon-512 (logn=9, raw message, no context).
    Input: signing key `sk`, message `msg`, PRNG seed.
    Output: signature bytes (empty on failure). -/
@[extern "lean_falcon512_sign_seeded"]
opaque falcon512SignSeeded : @& ByteArray → @& ByteArray → @& ByteArray →
  ByteArray

/-- Verification for Falcon-512 (logn=9, raw message, no context).
    Input: public key `pk`, message `msg`, signature `sig`.
    Returns `1` on success, `0` on failure. -/
@[extern "lean_falcon512_verify"]
opaque falcon512Verify : @& ByteArray → @& ByteArray → @& ByteArray → UInt8

/-- Deterministic key generation for Falcon-1024 (logn=10).
    Input: arbitrary-length seed. Output: `(sk, pk)` as serialized byte arrays.
    sk is 2305 bytes, pk is 1793 bytes. -/
@[extern "lean_falcon1024_keygen_seeded"]
opaque falcon1024KeygenSeeded : @& ByteArray → ByteArray × ByteArray

/-- Deterministic signing for Falcon-1024 (logn=10, raw message, no context).
    Input: signing key `sk`, message `msg`, PRNG seed.
    Output: signature bytes (empty on failure). -/
@[extern "lean_falcon1024_sign_seeded"]
opaque falcon1024SignSeeded : @& ByteArray → @& ByteArray → @& ByteArray →
  ByteArray

/-- Verification for Falcon-1024 (logn=10, raw message, no context).
    Input: public key `pk`, message `msg`, signature `sig`.
    Returns `1` on success, `0` on failure. -/
@[extern "lean_falcon1024_verify"]
opaque falcon1024Verify : @& ByteArray → @& ByteArray → @& ByteArray → UInt8

end Falcon.Concrete.FFI
