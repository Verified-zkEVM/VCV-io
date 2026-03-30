/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FPR
import FFI.Hashing

/-!
# Concrete Discrete Gaussian Sampler (SamplerZ)

Integer-only discrete Gaussian sampler for Falcon, faithfully translating
Pornin's constant-time implementation.

## Components

1. **CDT base sampler** (`gaussian0`): Cumulative Distribution Table with 18
   entries of 72-bit integers (stored as three 24-bit limbs). Samples from a
   half-Gaussian with `σ₀ = σ_min`.

2. **Bernoulli exponential** (`berExp`): Accepts with probability `ccs·exp(-x)`
   using the FACCT polynomial approximation `expm_p63`.

3. **Full sampler** (`samplerZ`): Given center `μ` and inverse standard
   deviation `1/σ` (both as `FPR`), returns an integer `z` from the discrete
   Gaussian `D_{ℤ,σ,μ}`.

## PRNG

The sampler uses SHAKE-256 as a PRNG, abstracted as a `ByteArray` state that
is squeezed to produce random bytes.

## References

- c-fn-dsa: `sign_sampler.c`
- Pornin 2019 (eprint 2019/893), Section 3.2
- FACCT (eprint 2018/1234)
-/

set_option autoImplicit false

namespace Falcon.Concrete.SamplerZ

open Falcon.Concrete.FPR

/-! ## PRNG state -/

structure PRNGState where
  buffer : ByteArray
  pos : Nat
deriving Inhabited

def PRNGState.init (seed : ByteArray) : PRNGState :=
  { buffer := FFI.Hashing.shake256 seed 4096, pos := 0 }

def PRNGState.nextByte (s : PRNGState) : UInt8 × PRNGState :=
  if s.pos < s.buffer.size then
    (s.buffer[s.pos]!, { s with pos := s.pos + 1 })
  else
    let newBuf := FFI.Hashing.shake256 s.buffer 4096
    (newBuf[0]!, { buffer := newBuf, pos := 1 })

def PRNGState.nextU64 (s : PRNGState) : UInt64 × PRNGState := Id.run do
  let mut state := s
  let mut val : UInt64 := 0
  for i in [0:8] do
    let (b, s') := state.nextByte
    state := s'
    val := val ||| (b.toUInt64 <<< (i * 8).toUInt64)
  return (val, state)

/-! ## CDT half-Gaussian base sampler -/

private def gauss0Table : Array (UInt32 × UInt32 × UInt32) := #[
  (10745844,  3068844,  3741698),
  ( 5559083,  1580863,  8248194),
  ( 2260429, 13669192,  2736639),
  (  708981,  4421575, 10046180),
  (  169348,  7122675,  4136815),
  (   30538, 13063405,  7650655),
  (    4132, 14505003,  7826148),
  (     417, 16768101, 11363290),
  (      31,  8444042,  8086568),
  (       1, 12844466,   265321),
  (       0,  1232676, 13644283),
  (       0,    38047,  9111839),
  (       0,      870,  6138264),
  (       0,       14, 12545723),
  (       0,        0,  3104126),
  (       0,        0,    28824),
  (       0,        0,      198),
  (       0,        0,        1)
]

def gaussian0 (s : PRNGState) : Int32 × PRNGState :=
  let (lo, s') := s.nextU64
  let (hiB, s'') := s'.nextByte
  let hi := hiB.toUInt32
  let v0 := lo.toUInt32 &&& 0xFFFFFF
  let v1 := (lo >>> 24).toUInt32 &&& 0xFFFFFF
  let v2 := (lo >>> 48).toUInt32 ||| (hi <<< 16)
  let z := gauss0Table.foldl (fun z entry =>
    let (g2, g1, g0) := entry
    let cc0 := (v0 - g0) >>> 31
    let cc1 := (v1 - g1 - cc0) >>> 31
    let cc2 := (v2 - g2 - cc1) >>> 31
    z + cc2.toInt32
  ) (0 : Int32)
  (z, s'')

/-! ## Bernoulli exponential sampling -/

private def log2FPR : FPR := (0x3FE62E42FEFA39EF : UInt64)
private def invLog2FPR : FPR := (0x3FF71547652B82FE : UInt64)

def berExp (s : PRNGState) (x ccs : FPR) : Bool × PRNGState := Id.run do
  let si := rint (mul x invLog2FPR)
  let r := sub x (mul (ofInt si) log2FPR)
  let mut sShift := si.toUInt64.toUInt32
  sShift := sShift ||| (((63 : UInt32) - sShift) >>> 26)
  sShift := sShift &&& 63
  let z := ((expm_p63 r ccs <<< 1) - 1) >>> sShift.toUInt64
  let mut state := s
  let mut accept := true
  for i in [0:8] do
    let w_ := (z >>> ((7 - i) * 8 : Nat).toUInt64) &&& 0xFF
    let (rndByte, s') := state.nextByte
    state := s'
    if rndByte.toUInt64 < w_ then
      accept := true
    else if rndByte.toUInt64 > w_ then
      accept := false
  return (accept, state)

/-! ## Full SamplerZ -/

private def invSqr2Sigma0 : FPR := (0x3FC2F76F031D7480 : UInt64)

def sigmaMinTable : Array FPR := #[
  (0 : UInt64),
  (0 : UInt64),
  (0x3FF0000000000000 : UInt64),
  (0x3FF0000000000000 : UInt64),
  (0x3FF0000000000000 : UInt64),
  (0x3FF0000000000000 : UInt64),
  (0x3FF0000000000000 : UInt64),
  (0x3FF0000000000000 : UInt64),
  (0x3FF4710BB39B2569 : UInt64),
  (0x3FF4710BB39B2569 : UInt64),
  (0x3FF4C4B4C1F7F6CF : UInt64)
]

def samplerZ (logn : Nat) (s : PRNGState) (mu isigma : FPR) : Int32 × PRNGState := Id.run do
  let sInt := floor_ mu
  let r := sub mu (ofInt sInt)
  let dss := mul (mul isigma isigma) half
  let sigmaMin := sigmaMinTable.getD logn (0 : UInt64)
  let ccs := mul isigma sigmaMin
  let mut state := s
  for _ in [0:1000] do
    let (z0, s') := gaussian0 state
    state := s'
    let (bByte, s'') := state.nextByte
    state := s''
    let b : Int32 := (bByte &&& 1).toUInt32.toInt32
    let z := b + ((b <<< 1) - (1 : Int32)) * z0
    let zFPR := ofInt z.toInt64
    let diff := sub zFPR r
    let x_ := mul (mul diff diff) dss
    let z0sq := ofInt (z0 * z0).toInt64
    let x := sub x_ (mul z0sq invSqr2Sigma0)
    let (accept, s''') := berExp state x ccs
    state := s'''
    if accept then
      return (sInt.toInt32 + z, state)
  return (sInt.toInt32, state)

end Falcon.Concrete.SamplerZ
