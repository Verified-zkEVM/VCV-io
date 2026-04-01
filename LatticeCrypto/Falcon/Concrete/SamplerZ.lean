/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FloatLike
import FFI.Hashing

/-!
# Concrete Discrete Gaussian Sampler (SamplerZ)

Integer-only discrete Gaussian sampler for Falcon, faithfully translating
Pornin's constant-time implementation. Generic over `FloatLike F` so it
works with both FPR (integer emulation) and Float (native hardware).

## Components

1. **CDT base sampler** (`gaussian0`): Cumulative Distribution Table with 18
   entries of 72-bit integers (stored as three 24-bit limbs). Samples from a
   half-Gaussian with `σ₀ = σ_min`.

2. **Bernoulli exponential** (`berExp`): Accepts with probability `ccs·exp(-x)`
   using `FloatLike.expm_p63`.

3. **Full sampler** (`samplerZ`): Given center `μ` and inverse standard
   deviation `1/σ` (both as `F`), returns an integer `z` from the discrete
   Gaussian `D_{ℤ,σ,μ}`.

## PRNG

The sampler uses SHAKE-256 as a PRNG, abstracted as a `ByteArray` state that
is squeezed to produce random bytes.

## References

- c-fn-dsa: `sign_sampler.c`
- Pornin 2019 (eprint 2019/893), Section 3.2
- FACCT (eprint 2018/1234)
-/


namespace Falcon.Concrete.SamplerZ

/-! ## PRNG state -/

structure PRNGState where
  seed : ByteArray
  buffer : ByteArray
  offset : Nat
  pos : Nat
deriving Inhabited

@[inline] def PRNGState.init (seed : ByteArray) : PRNGState :=
  { seed := seed, buffer := FFI.Hashing.shake256 seed 4096, offset := 0, pos := 0 }

@[inline] private def PRNGState.refill (s : PRNGState) : PRNGState :=
  let nextOffset := s.offset + s.buffer.size
  let nextEnd := nextOffset + 4096
  let full := FFI.Hashing.shake256 s.seed nextEnd.toUSize
  let nextBuf := full.extract nextOffset nextEnd
  { s with buffer := nextBuf, offset := nextOffset, pos := 0 }

@[inline] def PRNGState.nextByte (s : PRNGState) : UInt8 × PRNGState :=
  let s' := if s.pos < s.buffer.size then s else s.refill
  (s'.buffer[s'.pos]!, { s' with pos := s'.pos + 1 })

def PRNGState.nextU64 (s : PRNGState) : UInt64 × PRNGState :=
  if s.pos + 8 ≤ s.buffer.size then
    let val : UInt64 :=
      s.buffer[s.pos]!.toUInt64 |||
      (s.buffer[s.pos + 1]!.toUInt64 <<< 8) |||
      (s.buffer[s.pos + 2]!.toUInt64 <<< 16) |||
      (s.buffer[s.pos + 3]!.toUInt64 <<< 24) |||
      (s.buffer[s.pos + 4]!.toUInt64 <<< 32) |||
      (s.buffer[s.pos + 5]!.toUInt64 <<< 40) |||
      (s.buffer[s.pos + 6]!.toUInt64 <<< 48) |||
      (s.buffer[s.pos + 7]!.toUInt64 <<< 56)
    (val, { s with pos := s.pos + 8 })
  else Id.run do
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
  if s.pos + 9 ≤ s.buffer.size then
    let lo : UInt64 :=
      s.buffer[s.pos]!.toUInt64 |||
      (s.buffer[s.pos + 1]!.toUInt64 <<< 8) |||
      (s.buffer[s.pos + 2]!.toUInt64 <<< 16) |||
      (s.buffer[s.pos + 3]!.toUInt64 <<< 24) |||
      (s.buffer[s.pos + 4]!.toUInt64 <<< 32) |||
      (s.buffer[s.pos + 5]!.toUInt64 <<< 40) |||
      (s.buffer[s.pos + 6]!.toUInt64 <<< 48) |||
      (s.buffer[s.pos + 7]!.toUInt64 <<< 56)
    let hi := s.buffer[s.pos + 8]!.toUInt32
    let s' : PRNGState := { s with pos := s.pos + 9 }
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
    (z, s')
  else
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

section Generic

variable {F : Type} [FloatLike F]

instance : Inhabited F := ⟨FloatLike.zero⟩

private def log2Const : F := FloatLike.scaled (6243314768165359 : Int64) (-53 : Int32)
private def invLog2Const : F := FloatLike.scaled (6497320848556798 : Int64) (-52 : Int32)

def berExp (s : PRNGState) (x ccs : F) : Bool × PRNGState := Id.run do
  let si := FloatLike.rint (FloatLike.mul x (invLog2Const (F := F)))
  let r := FloatLike.sub x (FloatLike.mul (FloatLike.ofInt si) (log2Const (F := F)))
  let mut sShift := si.toUInt64.toUInt32
  sShift := sShift ||| (((63 : UInt32) - sShift) >>> 26)
  sShift := sShift &&& 63
  let z := ((FloatLike.expm_p63 r ccs <<< 1) - 1) >>> sShift.toUInt64
  if s.pos + 8 ≤ s.buffer.size then
    let mut decided := false
    let mut accept := false
    for i in [0:8] do
      if !decided then
        let w_ := (z >>> ((7 - i) * 8 : Nat).toUInt64) &&& 0xFF
        let rndByte := s.buffer[s.pos + i]!.toUInt64
        if rndByte < w_ then
          decided := true; accept := true
        else if rndByte > w_ then
          decided := true; accept := false
    return (accept, { s with pos := s.pos + 8 })
  else
    let mut state := s
    let mut decided := false
    let mut accept := false
    for i in [0:8] do
      let w_ := (z >>> ((7 - i) * 8 : Nat).toUInt64) &&& 0xFF
      let (rndByte, s') := state.nextByte
      state := s'
      if !decided then
        if rndByte.toUInt64 < w_ then
          decided := true; accept := true
        else if rndByte.toUInt64 > w_ then
          decided := true; accept := false
    return (accept, state)

/-! ## Full SamplerZ -/

private def invSqr2Sigma0Const : F :=
  FloatLike.scaled (5435486223186882 : Int64) (-55 : Int32)

private def sigmaMinConsts : Array F := #[
  FloatLike.zero,
  FloatLike.scaled (5028307297130123 : Int64) (-52 : Int32),
  FloatLike.scaled (5098636688852518 : Int64) (-52 : Int32),
  FloatLike.scaled (5168009084304506 : Int64) (-52 : Int32),
  FloatLike.scaled (5270355833453349 : Int64) (-52 : Int32),
  FloatLike.scaled (5370752584786614 : Int64) (-52 : Int32),
  FloatLike.scaled (5469306724145091 : Int64) (-52 : Int32),
  FloatLike.scaled (5566116128735780 : Int64) (-52 : Int32),
  FloatLike.scaled (5661270305715104 : Int64) (-52 : Int32),
  FloatLike.scaled (5754851361258101 : Int64) (-52 : Int32),
  FloatLike.scaled (5846934829975396 : Int64) (-52 : Int32)
]

@[inline] private def sigmaMinForLogn (logn : Nat) : F :=
  match (sigmaMinConsts (F := F))[logn]? with
  | some sigmaMin => sigmaMin
  | none => panic! s!"Falcon samplerZ does not support logn={logn}"

partial def samplerZLoop (state : PRNGState) (sInt : Int64)
    (r dss ccs : F) : Int32 × PRNGState :=
  let (z0, s') := gaussian0 state
  let (bByte, s'') := s'.nextByte
  let b : Int32 := (bByte &&& 1).toUInt32.toInt32
  let z := b + ((b <<< 1) - (1 : Int32)) * z0
  let zF : F := FloatLike.ofInt32 z
  let diff := FloatLike.sub zF r
  let x_ := FloatLike.mul (FloatLike.mul diff diff) dss
  let z0sq : F := FloatLike.ofInt32 (z0 * z0)
  let x := FloatLike.sub x_ (FloatLike.mul z0sq (invSqr2Sigma0Const (F := F)))
  let (accept, s''') := berExp s'' x ccs
  if accept then
    (sInt.toInt32 + z, s''')
  else
    samplerZLoop s''' sInt r dss ccs

def samplerZ (logn : Nat) (s : PRNGState) (mu isigma : F) :
    Int32 × PRNGState :=
  let sInt := FloatLike.floor_ mu
  let r := FloatLike.sub mu (FloatLike.ofInt sInt)
  let dss := FloatLike.mul (FloatLike.mul isigma isigma) (FloatLike.half (F := F))
  let sigmaMin := sigmaMinForLogn (F := F) logn
  let ccs := FloatLike.mul isigma sigmaMin
  samplerZLoop (F := F) s sInt r dss ccs

end Generic

end Falcon.Concrete.SamplerZ
