/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Params

/-!
# Pure-Lean Keccak-f[1600], SHAKE, Keccak-256, and SHA-3

An executable, FFI-free Keccak-f[1600] permutation (FIPS 202) and distinct sponge domains for
FIPS SHAKE (`0x1f`), FIPS SHA-3 (`0x06`), and the EVM's original Keccak (`0x01`) domains.
SHAKE128 and SHAKE256 support arbitrary whole-byte output lengths by permuting between squeeze
blocks. `keccak256` remains the hash used by the separate C13 SLH-DSA variant.

## References

- FIPS 202 (Keccak / SHA-3); Ethereum `KECCAK256` (original `0x01` padding)
-/

@[expose] public section


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

/-- Squeeze the first `outLen` bytes from one state block. Callers keep `outLen ≤ rate`. -/
def squeeze (s : Array UInt64) (outLen : ℕ) : ByteArray :=
  ByteArray.mk (Array.ofFn fun i : Fin outLen =>
    ((s[i.val / 8]! >>> ((i.val % 8) * 8).toUInt64) &&& 0xFF).toUInt8)

@[simp] theorem squeeze_size (s : Array UInt64) (outLen : ℕ) :
    (squeeze s outLen).size = outLen := by
  change (Array.ofFn fun i : Fin outLen =>
    ((s[i.val / 8]! >>> ((i.val % 8) * 8).toUInt64) &&& 0xFF).toUInt8).size = outLen
  exact Array.size_ofFn

/-- Emit `blocks` complete XOF blocks and return the state for the following block. -/
def squeezeFullBlocks (initial : Array UInt64) (rate : ℕ) :
    ℕ → Array UInt64 × ByteArray
  | 0 => (initial, ByteArray.empty)
  | blocks + 1 =>
      let prior := squeezeFullBlocks initial rate blocks
      (f1600 prior.1, prior.2 ++ squeeze prior.1 rate)

@[simp] theorem squeezeFullBlocks_size (initial : Array UInt64) (rate blocks : ℕ) :
    (squeezeFullBlocks initial rate blocks).2.size = blocks * rate := by
  induction blocks with
  | zero => simp [squeezeFullBlocks]
  | succ blocks ih => simp [squeezeFullBlocks, ih, Nat.succ_mul]

/-- Multi-block XOF squeeze. Complete rate blocks are followed by the exact residual prefix.
A zero rate is outside the sponge domain and returns the empty byte array. -/
def squeezeXof (initial : Array UInt64) (rate outLen : ℕ) : ByteArray :=
  if rate = 0 then
    ByteArray.empty
  else
    let full := squeezeFullBlocks initial rate (outLen / rate)
    full.2 ++ squeeze full.1 (outLen % rate)

@[simp] theorem squeezeXof_size (initial : Array UInt64) (rate outLen : ℕ)
    (hrate : 0 < rate) :
    (squeezeXof initial rate outLen).size = outLen := by
  simp only [squeezeXof, if_neg (Nat.ne_of_gt hrate), ByteArray.size_append,
    squeezeFullBlocks_size, squeeze_size]
  simpa [Nat.mul_comm] using Nat.div_add_mod outLen rate

/-- EVM `keccak256` (rate 136, pad `0x01`), 32-byte digest. -/
def keccak256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x01) 32

/-- FIPS 202 `SHA3-256` (rate 136, pad `0x06`), 32-byte digest. -/
def sha3_256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x06) 32

/-- FIPS 202 `SHA3-224` (rate 144, pad `0x06`), 28-byte digest. -/
def sha3_224 (input : ByteArray) : ByteArray := squeeze (absorb input 144 0x06) 28

/-- FIPS 202 `SHA3-384` (rate 104, pad `0x06`), 48-byte digest. -/
def sha3_384 (input : ByteArray) : ByteArray := squeeze (absorb input 104 0x06) 48

/-- FIPS 202 `SHA3-512` (rate 72, pad `0x06`), 64-byte digest. -/
def sha3_512 (input : ByteArray) : ByteArray := squeeze (absorb input 72 0x06) 64

/-- FIPS 202 SHAKE128 with a whole-byte output length. -/
def shake128 (input : ByteArray) (outLen : ℕ) : ByteArray :=
  squeezeXof (absorb input 168 0x1f) 168 outLen

/-- FIPS 202 SHAKE256 with a whole-byte output length. The `0x1f` delimited suffix is distinct
from both SHA3's `0x06` and Ethereum Keccak's `0x01`. -/
def shake256 (input : ByteArray) (outLen : ℕ) : ByteArray :=
  squeezeXof (absorb input 136 0x1f) 136 outLen

@[simp] theorem shake128_size (input : ByteArray) (outLen : ℕ) :
    (shake128 input outLen).size = outLen := by
  simp [shake128]

@[simp] theorem shake256_size (input : ByteArray) (outLen : ℕ) :
    (shake256 input outLen).size = outLen := by
  simp [shake256]

@[simp] theorem sha3_224_size (input : ByteArray) : (sha3_224 input).size = 28 := by
  simp [sha3_224]

@[simp] theorem sha3_256_size (input : ByteArray) : (sha3_256 input).size = 32 := by
  simp [sha3_256]

@[simp] theorem sha3_384_size (input : ByteArray) : (sha3_384 input).size = 48 := by
  simp [sha3_384]

@[simp] theorem sha3_512_size (input : ByteArray) : (sha3_512 input).size = 64 := by
  simp [sha3_512]

end SLHDSA.Concrete.Keccak
