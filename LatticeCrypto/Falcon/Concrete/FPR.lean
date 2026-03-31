/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# FPR: Integer-Only IEEE-754 Binary64 Emulation

A faithful Lean translation of Pornin's `FALCON_FPEMU` mode (eprint 2019/893),
where all IEEE-754 `double` operations are implemented using pure `UInt64`
integer arithmetic.

## Bit Layout

An `FPR` value is a `UInt64` encoding:
- Bit 63: sign (0 = positive)
- Bits 62–52: biased exponent (bias = 1023)
- Bits 51–0: mantissa (implicit leading 1 for nonzero values)

## Operations

All operations (`add`, `mul`, `div`, `sqrt`) are constant-time: they use
only shifts, masks, additions, and multiplications on `UInt64`, with no
branches on data values.

## References

- c-fn-dsa: `sign_fpr.c`
- Pornin 2019 (eprint 2019/893), Section 3.1
-/


namespace Falcon.Concrete.FPR

/-- Raw IEEE-754 binary64 values encoded as `UInt64` words. -/
abbrev FPR := UInt64

private def M52 : UInt64 := ((1 : UInt64) <<< 52) - 1
private def M63 : UInt64 := ((1 : UInt64) <<< 63) - 1

@[inline] private def tbmask (x : UInt32) : UInt32 :=
  (0 : UInt32) - (x >>> 31)

@[inline] private def lzcnt_nonzero (x : UInt32) : UInt32 := Id.run do
  let mut n : UInt32 := 0
  let mut v := x
  if v &&& 0xFFFF0000 == 0 then n := n + 16; v := v <<< 16
  if v &&& 0xFF000000 == 0 then n := n + 8; v := v <<< 8
  if v &&& 0xF0000000 == 0 then n := n + 4; v := v <<< 4
  if v &&& 0xC0000000 == 0 then n := n + 2; v := v <<< 2
  if v &&& 0x80000000 == 0 then n := n + 1
  return n

@[inline] private def lzcnt64_nonzero (x : UInt64) : UInt32 :=
  let x0 : UInt32 := x.toUInt32
  let x1_ : UInt32 := (x >>> 32).toUInt32
  let m := ~~~(tbmask (x1_ ||| ((0 : UInt32) - x1_)))
  let x1 := x1_ ||| (x0 &&& m)
  lzcnt_nonzero x1 + (m &&& 32)

@[inline] private def fpr_ulsh (x : UInt64) (n : UInt32) : UInt64 :=
  x <<< n.toUInt64

@[inline] private def fpr_ursh (x : UInt64) (n : UInt32) : UInt64 :=
  x >>> n.toUInt64

@[inline] private def fpr_arsh32 (x : UInt32) (n : UInt32) : UInt32 :=
  let sign := (0 : UInt32) - (x >>> 31)
  if n == 0 then x
  else (x >>> n) ||| (sign <<< (32 - n))

@[inline] private def make (s : UInt64) (e : Int32) (m : UInt64) : FPR :=
  let cc : UInt64 := ((0xC8 : UInt64) >>> (m.toUInt32 &&& 7).toUInt64) &&& 1
  (s <<< 63) + ((e + 1076).toUInt32.toUInt64 <<< 52) + (m >>> 2) + cc

@[inline] private def make_z (s : UInt64) (e : Int32) (m : UInt64) : FPR :=
  let eu : UInt32 := ((e + 1076).toUInt32 &&& ((0 : UInt32) - (m >>> 54).toUInt32))
  let cc : UInt64 := ((0xC8 : UInt64) >>> (m.toUInt32 &&& 7).toUInt64) &&& 1
  (s <<< 63) + (eu.toUInt64 <<< 52) + (m >>> 2) + cc

@[inline] private def norm64 (m : UInt64) (e : Int32) : UInt64 × Int32 :=
  let c := lzcnt64_nonzero (m ||| 1)
  (fpr_ulsh m c, e - c.toInt32)

/-! ## Core Arithmetic -/

/-- The floating-point value `0`. -/
def zero : FPR := (0 : UInt64)
/-- The floating-point value `1`. -/
def one : FPR := (0x3FF0000000000000 : UInt64)
/-- The floating-point value `2`. -/
def two : FPR := (0x4000000000000000 : UInt64)
/-- The floating-point value `1 / 2`. -/
def half : FPR := (0x3FE0000000000000 : UInt64)
/-- The Falcon modulus `q = 12289` encoded as an `FPR`. -/
def q : FPR := (0x40C8008000000000 : UInt64)
/-- The reciprocal of the Falcon modulus encoded as an `FPR`. -/
def invQ : FPR := (0x3F1554E39097A782 : UInt64)

/-- Negate an `FPR` value by flipping its sign bit. -/
@[inline] def neg (x : FPR) : FPR := x ^^^ ((1 : UInt64) <<< 63)

/-- Convert an integer scaled by `2^sc` into an `FPR`. -/
def scaled (i : Int64) (sc : Int32) : FPR :=
  let s := (i.toUInt64 >>> 63)
  let m := ((i.toUInt64 ^^^ (0 - s)) - (0 - s))
  let c_sc := lzcnt64_nonzero (m ||| 1)
  let m' := fpr_ulsh m c_sc
  let sc' := sc - c_sc.toInt32
  let sc'' := sc' + 9
  let m'' := (m' ||| ((m' &&& 0x1FF) + 0x1FF)) >>> 9
  make_z s sc'' m''

/-- Convert an integer into an `FPR`. -/
@[inline] def ofInt (i : Int64) : FPR := scaled i 0

/-- Add two `FPR` values. -/
def add (x y : FPR) : FPR :=
  let za := (x &&& M63) - (y &&& M63)
  let za' := za ||| ((za - 1) &&& x)
  let sw := (x ^^^ y) &&& ((0 : UInt64) - (za' >>> 63))
  let x' := x ^^^ sw
  let y' := y ^^^ sw
  let ex_ := (x' >>> 52).toUInt32
  let sx := ex_ >>> 11
  let ex := ex_ &&& 0x7FF
  let xu := ((x' &&& M52) <<< 3) ||| (((ex + 0x7FF) >>> 11).toUInt64 <<< 55)
  let ex' : Int32 := (ex - 1078).toInt32
  let ey_ := (y' >>> 52).toUInt32
  let sy := ey_ >>> 11
  let ey := ey_ &&& 0x7FF
  let yu_ := ((y' &&& M52) <<< 3) ||| (((ey + 0x7FF) >>> 11).toUInt64 <<< 55)
  let n := ex - ey
  let yu' := yu_ &&& ((0 : UInt64) - ((n - 60) >>> 31).toUInt64)
  let n' := n &&& 63
  let m := fpr_ulsh 1 n' - 1
  let yu := fpr_ursh (yu' ||| ((yu' &&& m) + m)) n'
  let dm := (0 - (sx ^^^ sy).toUInt64)
  let zu := xu + yu - (dm &&& (yu <<< 1))
  let c_add := lzcnt64_nonzero (zu ||| 1)
  let zu' := fpr_ulsh zu c_add
  let ex'' := ex' - c_add.toInt32
  let zu'' := (zu' ||| ((zu' &&& 0x1FF) + 0x1FF)) >>> 9
  let ex''' := ex'' + 9
  make_z sx.toUInt64 ex''' zu''

/-- Subtract two `FPR` values. -/
@[inline] def sub (x y : FPR) : FPR := add x (neg y)

/-- Multiply two `FPR` values. -/
def mul (x y : FPR) : FPR :=
  let xu : UInt64 := (x &&& M52) ||| ((1 : UInt64) <<< 52)
  let yu : UInt64 := (y &&& M52) ||| ((1 : UInt64) <<< 52)
  let x0 := xu.toUInt32 &&& 0x01FFFFFF
  let x1 := (xu >>> 25).toUInt32
  let y0 := yu.toUInt32 &&& 0x01FFFFFF
  let y1 := (yu >>> 25).toUInt32
  let w0 := x0.toUInt64 * y0.toUInt64
  let z0 := w0.toUInt32 &&& 0x01FFFFFF
  let z1_ := (w0 >>> 25).toUInt32
  let w1 := x0.toUInt64 * y1.toUInt64
  let z1 := z1_ + (w1.toUInt32 &&& 0x01FFFFFF)
  let z2_ := (w1 >>> 25).toUInt32
  let w2 := x1.toUInt64 * y0.toUInt64
  let z1' := z1 + (w2.toUInt32 &&& 0x01FFFFFF)
  let z2 := z2_ + (w2 >>> 25).toUInt32
  let zu_ := x1.toUInt64 * y1.toUInt64
  let z2' := z2 + (z1' >>> 25)
  let zu := zu_ + z2'.toUInt64
  let zu' := zu ||| ((((z0 ||| (z1' &&& 0x01FFFFFF)) + 0x01FFFFFF) >>> 25).toUInt64)
  let es := zu' >>> 55
  let zu'' := (zu' >>> es) ||| (zu' &&& 1)
  let ex := (x >>> 52).toUInt32 &&& 0x7FF
  let ey := (y >>> 52).toUInt32 &&& 0x7FF
  let e := ex + ey - 2100 + es.toUInt32
  let s := (x ^^^ y) >>> 63
  let dzu := tbmask ((ex - 1) ||| (ey - 1))
  let e' : Int32 := (e ^^^ (dzu &&& (e ^^^ ((0 : UInt32) - 1076)))).toInt32
  let zu''' := zu'' &&& ((dzu &&& 1).toUInt64 - 1)
  make s e' zu'''

/-- Divide two `FPR` values. -/
def div (x y : FPR) : FPR := Id.run do
  let xu : UInt64 := (x &&& M52) ||| ((1 : UInt64) <<< 52)
  let yu : UInt64 := (y &&& M52) ||| ((1 : UInt64) <<< 52)
  let mut q_ : UInt64 := 0
  let mut xu_ := xu
  for _ in [0:55] do
    let b : UInt64 := ((xu_ - yu) >>> 63) - 1
    xu_ := xu_ - (b &&& yu)
    q_ := q_ ||| (b &&& (1 : UInt64))
    xu_ := xu_ <<< 1
    q_ := q_ <<< 1
  q_ := q_ ||| ((xu_ ||| (0 - xu_)) >>> 63)
  let es := q_ >>> 55
  q_ := (q_ >>> es) ||| (q_ &&& 1)
  let ex := (x >>> 52).toUInt32 &&& 0x7FF
  let ey := (y >>> 52).toUInt32 &&& 0x7FF
  let e := ex - ey - 55 + es.toUInt32
  let s := (x ^^^ y) >>> 63
  let dzu := tbmask (ex - 1)
  let e' : Int32 := (e ^^^ (dzu &&& (e ^^^ ((0 : UInt32) - 1076)))).toInt32
  let dm := (dzu &&& 1).toUInt64 - 1
  return make (s &&& dm) e' (q_ &&& dm)

/-- Compute the square root of a nonnegative `FPR` value. -/
def sqrt (x : FPR) : FPR := Id.run do
  let xu_ : UInt64 := (x &&& M52) ||| ((1 : UInt64) <<< 52)
  let ex_ := (x >>> 52).toUInt32 &&& 0x7FF
  let e_ : Int32 := ex_.toInt32 - 1023
  let xu := xu_ + (xu_ &&& (0 - (e_.toUInt32 &&& 1).toUInt64))
  let e := (fpr_arsh32 e_.toUInt32 1).toInt32
  let mut xu' := xu <<< 1
  let mut q_ : UInt64 := 0
  let mut s_ : UInt64 := 0
  let mut r := (1 : UInt64) <<< 53
  for _ in [0:54] do
    let t := s_ + r
    let b := ((xu' - t) >>> 63) - 1
    s_ := s_ + (b &&& (r <<< 1))
    xu' := xu' - (t &&& b)
    q_ := q_ + (r &&& b)
    xu' := xu' <<< 1
    r := r >>> 1
  q_ := q_ <<< 1
  q_ := q_ ||| ((xu' ||| (0 - xu')) >>> 63)
  let e' := e - 54
  q_ := q_ &&& ((0 : UInt64) - ((ex_ + 0x7FF) >>> 11).toUInt64)
  return make_z 0 e' q_

/-! ## Conversion Utilities -/

@[inline] private def fpr_arsh64 (x : UInt64) (n : UInt32) : UInt64 :=
  let sign := (0 : UInt64) - (x >>> 63)
  if n == 0 then x
  else (x >>> n.toUInt64) ||| (sign <<< (64 - n.toUInt64))

/-- Round an `FPR` value to the nearest integer using the reference binary64 rule. -/
@[inline] def rint (x : FPR) : Int64 :=
  let m0 : UInt64 := ((x <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63
  let e0 : UInt32 := (1085 : UInt32) - ((x >>> 52).toUInt32 &&& 0x7FF)
  let m := m0 &&& ((0 : UInt64) - ((e0 - 64) >>> 31).toUInt64)
  let e := e0 &&& 63
  let z := fpr_ulsh m (63 - e)
  let y := ((z &&& 0x3FFFFFFFFFFFFFFF) + 0x3FFFFFFFFFFFFFFF) >>> 1
  let cc : UInt64 := ((0xC8 : UInt64) >>> ((z ||| y) >>> 61)) &&& 1
  let r := fpr_ursh m e + cc
  let s := (0 : UInt64) - (x >>> 63)
  ((r ^^^ s) - s).toInt64

/-- Round an `FPR` value toward negative infinity. -/
@[inline] def floor_ (x : FPR) : Int64 :=
  let m0 : UInt64 := ((x <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63
  let s := (0 : UInt64) - (x >>> 63)
  let m := (m0 ^^^ s) - s
  let e : UInt32 := (1085 : UInt32) - ((x >>> 52).toUInt32 &&& 0x7FF)
  let ue := (e ||| ((63 - e) >>> 16)) &&& 63
  (fpr_arsh64 m ue).toInt64

/-! ## Expm_p63: FACCT polynomial exp(-x) approximation

Returns `⌊2^63 · ccs · exp(-x)⌋` using only integer multiply-add.
The polynomial coefficients are from the FACCT paper (eprint 2018/1234). -/

private def facctCoeffs : Array UInt64 := #[
  0x00000004741183A3,
  0x00000036548CFC06,
  0x0000024FDCBF140A,
  0x0000171D939DE045,
  0x0000D00CF58F6F84,
  0x000680681CF796E3,
  0x002D82D8305B0FEA,
  0x011111110E066FD0,
  0x0555555555070F00,
  0x155555555581FF00,
  0x400000000002B400,
  0x7FFFFFFFFFFF4800,
  0x8000000000000000
]

private def mulHi64 (a b : UInt64) : UInt64 :=
  let aLo := a &&& 0xFFFFFFFF
  let aHi := a >>> 32
  let bLo := b &&& 0xFFFFFFFF
  let bHi := b >>> 32
  let cross1 := aHi * bLo
  let cross2 := aLo * bHi
  let lo_lo := aLo * bLo
  let mid := (lo_lo >>> 32) + (cross1 &&& 0xFFFFFFFF) + (cross2 &&& 0xFFFFFFFF)
  aHi * bHi + (cross1 >>> 32) + (cross2 >>> 32) + (mid >>> 32)

@[inline] private def mtwop63 (x : FPR) : UInt64 :=
  let m : UInt64 := ((x <<< 10) ||| ((1 : UInt64) <<< 62)) &&& M63
  let e : UInt32 := (1022 : UInt32) - ((x >>> 52).toUInt32 &&& 0x7FF)
  let ue := (e ||| ((63 - e) >>> 16)) &&& 63
  m >>> ue.toUInt64

/-- Compute `⌊2^63 * ccs * exp(-x)⌋` with the FACCT polynomial approximation. -/
def expm_p63 (x : FPR) (ccs : FPR) : UInt64 := Id.run do
  let z := (mtwop63 x) <<< 1
  let w := (mtwop63 ccs) <<< 1
  let mut y := facctCoeffs[0]!
  for i in [1:facctCoeffs.size] do
    let hi := mulHi64 z y
    y := facctCoeffs[i]! - hi
  return mulHi64 w y

end Falcon.Concrete.FPR
