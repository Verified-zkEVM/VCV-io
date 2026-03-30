/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import FFI.Hashing
import LatticeCrypto.Falcon.Ring

/-!
# Concrete HashToPoint for Falcon

`HashToPoint(nonce, hk, msg, q, n)` (FIPS 206 / FN-DSA): SHAKE-256 based rejection
sampler that produces a polynomial in `R_q` with coefficients uniform in `[0, q)`.

For raw-message mode, the hash input is:
  `nonce(40) ‖ SHAKE-256(vrfy_key)(64) ‖ 0x00 ‖ 0x00 ‖ message`

Reads 2 bytes at a time in big-endian from the SHAKE-256 stream; accepts if
the 16-bit value is `< 61445 = 5 · 12289`, then reduces mod `q`.

## References

- FIPS 206 (FN-DSA), Section 6.2 (HashToPoint)
- c-fn-dsa: `util.c` (hash_to_point), `vrfy.c` (inner_verify)
-/

set_option autoImplicit false

namespace Falcon.Concrete

open Falcon

def hashToPoint (n : ℕ) (salt : Bytes 40) (pk : ByteArray) (msg : List Byte) :
    Rq n := Id.run do
  let hk := FFI.Hashing.shake256 pk 64
  let mut input := ByteArray.mk salt.toArray
  input := input ++ hk
  input := input ++ ByteArray.mk #[0x00, 0x00]
  input := input ++ ByteArray.mk msg.toArray
  let streamLen := 2 * (n + n)
  let stream := FFI.Hashing.shake256 input streamLen.toUSize
  let mut result : Array Coeff := #[]
  let mut j := 0
  while result.size < n do
    if j + 1 ≥ stream.size then
      result := result.push 0
    else
      let hi := stream[j]!.toNat
      let lo := stream[j + 1]!.toNat
      j := j + 2
      let w := (hi <<< 8) ||| lo
      if w < 61445 then
        result := result.push ((w % modulus) : Coeff)
  return Vector.ofFn fun ⟨i, _⟩ => result.getD i 0

end Falcon.Concrete
