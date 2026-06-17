/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny
-/
import HashSig.SLHDSA.Params

/-!
# Pure-Lean Keccak-f[1600] / keccak256 (and SHA3-256)

An executable, FFI-free Keccak-f[1600] permutation (FIPS 202) and the sponge for the EVM
`keccak256` (pad byte `0x01`) and FIPS 202 `SHA3-256` (pad byte `0x06`). `keccak256` is the
hash used by the C13 SLH-DSA variant (`keccak256` substituted for SHAKE-256, truncated to
`n = 16` bytes); `SHA3-256` is provided for completeness. The permutation is adapted from the
`sphincsminus` reference; absorb/squeeze are total `for`-loops here.

## References

- FIPS 202 (Keccak / SHA-3); Ethereum `KECCAK256` (original `0x01` padding)
-/


namespace SLHDSA.Concrete.Keccak

/-- ρ rotation offsets (lanes ordered `x + 5*y`). -/
def rhoLUT : Array ℕ :=
  #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
    41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- π permutation: `(x,y) ↦ (y, 2x+3y mod 5)`, precomputed as `oldIdx ↦ newIdx`. -/
def piLUT : Array ℕ :=
  (((List.range 5).map fun y => (List.range 5).map fun x =>
    let nx := y; let ny := (2 * x + 3 * y) % 5; nx + 5 * ny).flatten).toArray

/-- Keccak-f[1600] round constants. -/
def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Left-rotate a 64-bit word by `n` bits. -/
def rotl64 (x : UInt64) (n : ℕ) : UInt64 := (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- One Keccak-f[1600] round (θ, ρ, π, χ, ι). -/
def round (state : Array UInt64) (rc : UInt64) : Array UInt64 :=
  let C : Array UInt64 := (List.range 5).toArray.map fun x =>
    state[x]! ^^^ state[x + 5]! ^^^ state[x + 10]! ^^^ state[x + 15]! ^^^ state[x + 20]!
  let D : Array UInt64 := (List.range 5).toArray.map fun x =>
    C[(x + 4) % 5]! ^^^ rotl64 C[(x + 1) % 5]! 1
  let s1 : Array UInt64 := (List.range 25).toArray.map fun i => state[i]! ^^^ D[i % 5]!
  let B : Array UInt64 := (List.range 25).foldl
    (fun B' i => B'.set! piLUT[i]! (rotl64 s1[i]! rhoLUT[i]!)) (Array.replicate 25 0)
  let s2 : Array UInt64 := (List.range 25).toArray.map fun i =>
    let x := i % 5; let y := i / 5
    B[i]! ^^^ (~~~B[(x + 1) % 5 + 5 * y]! &&& B[(x + 2) % 5 + 5 * y]!)
  s2.set! 0 (s2[0]! ^^^ rc)

/-- The full 24-round Keccak-f[1600] permutation. -/
def f1600 (state : Array UInt64) : Array UInt64 :=
  (List.range 24).foldl (fun s r => round s roundConstants[r]!) state

/-- Sponge absorb with the given `rate` (bytes) and domain-separation pad byte. -/
def absorb (input : ByteArray) (rate : ℕ) (padByte : UInt8) : Array UInt64 := Id.run do
  let padTotal := rate - input.size % rate
  let padBytes : List UInt8 :=
    if padTotal = 1 then [padByte ||| 0x80]
    else padByte :: (List.replicate (padTotal - 2) 0 ++ [0x80])
  let padded := input ++ ByteArray.mk padBytes.toArray
  let mut s : Array UInt64 := Array.replicate 25 0
  for b in [0:padded.size / rate] do
    for i in [0:rate] do
      let bv : UInt64 := (padded[b * rate + i]!).toNat.toUInt64
      s := s.set! (i / 8) (s[i / 8]! ^^^ (bv <<< ((i % 8) * 8).toUInt64))
    s := f1600 s
  return s

/-- Squeeze `outLen ≤ rate` bytes from the state (one block; sufficient for 32-byte digests). -/
def squeeze (s : Array UInt64) (outLen : ℕ) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:outLen] do
    out := out.push (((s[i / 8]! >>> ((i % 8) * 8).toUInt64) &&& 0xFF).toUInt8)
  return out

/-- EVM `keccak256` (rate 136, pad `0x01`), 32-byte digest. -/
def keccak256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x01) 32

/-- FIPS 202 `SHA3-256` (rate 136, pad `0x06`), 32-byte digest. -/
def sha3_256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x06) 32

end SLHDSA.Concrete.Keccak
