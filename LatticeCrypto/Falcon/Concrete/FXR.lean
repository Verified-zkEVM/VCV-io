/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Concrete.GMTable

/-!
# FXR: 64-bit Fixed-Point Arithmetic (32.32 format) for Key Generation

A faithful Lean port of the fixed-point arithmetic and FFT routines from
`c-fn-dsa/kgen_fxp.c` and `c-fn-dsa/kgen_inner.h`.

## Representation

An `FXR` value is a `UInt64` interpreted as a signed 64-bit fixed-point number
in **32.32 format**: the upper 32 bits hold the integer part and the lower 32
bits hold the fractional part. Equivalently, the real value represented is
`(v.toInt64) / 2^32`.

## Operations

Arithmetic is wrapping two's-complement, matching the C reference.
Multiplication uses the four-part decomposition (`xl*yl`, `xl*yh`, `xh*yl`,
`xh*yh`) to compute the full 128-bit product and extract the middle 64 bits.
Division uses a bit-by-bit long-division algorithm.

## References

- `c-fn-dsa/kgen_fxp.c` — fixed-point computations and GM_TAB
- `c-fn-dsa/kgen_inner.h` — inline helpers (`fxr_mul`, `fxr_sqr`, etc.)
-/

public section


namespace Falcon.Concrete.FXR

open Falcon.Concrete.GMTable

/-- Signed 32.32 fixed-point values represented by wrapping 64-bit words. -/
abbrev FXR := UInt64

-- fxr_of: convert a signed 32-bit integer to FXR (shift left by 32).
/-- Encode a signed 32-bit integer by shifting its sign-extended representation left by 32
bits. -/
def fxrOf (j : Int32) : FXR :=
  j.toInt64.toUInt64 <<< 32

-- fxr_of_scaled32: given integer t, return t/2^32 as FXR (identity on bits).
/-- Interpret a raw word as a fixed-point value scaled by `2⁻³²`. -/
def fxrOfScaled32 (t : UInt64) : FXR := t

-- fxr_add / fxr_sub: wrapping addition/subtraction.
/-- Add fixed-point values with wrapping 64-bit arithmetic. -/
def fxrAdd (x y : FXR) : FXR := x + y
/-- Subtract fixed-point values with wrapping 64-bit arithmetic. -/
def fxrSub (x y : FXR) : FXR := x - y

-- fxr_neg: two's complement negation.
/-- Negate a fixed-point value using wrapping two's-complement arithmetic. -/
def fxrNeg (x : FXR) : FXR := (0 : UInt64) - x

-- fxr_half: arithmetic right shift by 1, with rounding.
-- C: `((x + 1) >>> 1) | (x & (1 << 63))`.
/-- Halve a fixed-point value with rounding toward positive infinity at the last bit. -/
def fxrHalf (x : FXR) : FXR :=
  let y := x + 1
  (y >>> 1) ||| (y &&& ((1 : UInt64) <<< 63))

-- fxr_double: shift left by 1.
/-- Double a fixed-point value by a wrapping left shift. -/
def fxrDouble (x : FXR) : FXR := x <<< 1

-- fxr_round: round to nearest integer (add 0.5, then arithmetic right shift 32).
/-- Round a fixed-point value to a signed integer, breaking half-integer ties upward. -/
def fxrRound (x : FXR) : Int32 :=
  let y := x + 0x80000000
  (y.toInt64 >>> (32 : Int64)).toInt32

-- fxr_mul: fixed-point multiply.
-- Portable 4-part decomposition of the 128-bit product:
--   xl, xh = unsigned low / signed high 32-bit halves (the high half is an arithmetic
--   shift of the signed word, as in the reference; a logical shift would drop the sign
--   and break every product with a negative operand and a nonzero low half)
--   result = (xl*yl)>>32 + xl*(int)yh + (int)xh*yl + ((int)xh*(int)yh)<<32
/-- Multiply fixed-point values using four partial products and retain the middle 64 product
bits. -/
def fxrMul (x y : FXR) : FXR :=
  let xl : UInt64 := x &&& 0xFFFFFFFF
  let xh : Int64 := x.toInt64 >>> (32 : Int64)
  let yl : UInt64 := y &&& 0xFFFFFFFF
  let yh : Int64 := y.toInt64 >>> (32 : Int64)
  let z0 : UInt64 := (xl * yl) >>> 32
  let z1 : UInt64 := xl * yh.toUInt64
  let z2 : UInt64 := xh.toUInt64 * yl
  let z3 : UInt64 := (xh * yh).toUInt64 <<< 32
  z0 + z1 + z2 + z3

-- fxr_sqr: specialized squaring.
/-- Square a fixed-point value using the specialized partial-product decomposition. -/
def fxrSqr (x : FXR) : FXR :=
  let xl : UInt64 := x &&& 0xFFFFFFFF
  let xh : Int64 := x.toInt64 >>> (32 : Int64)
  let z0 : UInt64 := (xl * xl) >>> 32
  let z1 : UInt64 := xl * xh.toUInt64
  let z3 : UInt64 := (xh * xh).toUInt64 <<< 32
  z0 + (z1 <<< 1) + z3

-- fxr_div: bit-by-bit long division matching `inner_fxr_div`.
/-- Divide fixed-point values using the reference bit-by-bit long-division algorithm. -/
def fxrDiv (x y : FXR) : FXR := Id.run do
  let sx := x >>> 63
  let xv := (x ^^^ ((0 : UInt64) - sx)) + sx
  let sy := y >>> 63
  let yv := (y ^^^ ((0 : UInt64) - sy)) + sy

  let mut q : UInt64 := 0
  let mut num : UInt64 := xv >>> 31

  for i' in [:31] do
    let i : UInt64 := (63 : UInt64) - i'.toUInt64
    let b : UInt64 := (1 : UInt64) - ((num - yv) >>> 63)
    q := q ||| (b <<< i)
    num := num - (yv &&& ((0 : UInt64) - b))
    num := num <<< 1
    num := num ||| ((xv >>> (i - (33 : UInt64))) &&& 1)

  for i' in [:33] do
    let i : UInt64 := (32 : UInt64) - i'.toUInt64
    let b : UInt64 := (1 : UInt64) - ((num - yv) >>> 63)
    q := q ||| (b <<< i)
    num := num - (yv &&& ((0 : UInt64) - b))
    num := num <<< 1

  let b : UInt64 := (1 : UInt64) - ((num - yv) >>> 63)
  q := q + b

  let s := sx ^^^ sy
  q := (q ^^^ ((0 : UInt64) - s)) + s
  return q

-- fxr_inv: reciprocal 1/x.
/-- Compute the fixed-point reciprocal by dividing the encoding of one by the argument. -/
def fxrInv (x : FXR) : FXR :=
  fxrDiv ((1 : UInt64) <<< 32) x

-- fxr_div2e: divide by 2^e with rounding.
/-- Divide a fixed-point value by a power of two with rounding at the discarded bits. -/
def fxrDiv2e (x : FXR) (e : UInt64) : FXR :=
  let y := x + (((1 : UInt64) <<< e) >>> 1)
  (y.toInt64 >>> e.toInt64).toUInt64

-- fxr_mul2e: multiply by 2^e.
/-- Multiply a fixed-point value by a power of two using a wrapping shift. -/
def fxrMul2e (x : FXR) (e : UInt64) : FXR := x <<< e

-- fxr_lt: signed comparison.
/-- Compare fixed-point values in signed order. -/
def fxrLt (x y : FXR) : Bool := x.toInt64 < y.toInt64

/-- The fixed-point encoding of zero. -/
def fxrZero : FXR := 0
/-- The rounded 32.32 fixed-point encoding of the square root of two. -/
def fxrSqrt2 : FXR := 6074001000

/-! ## Complex fixed-point type -/

/-- A complex number with fixed-point real and imaginary components. -/
structure FXC where
  /-- Fixed-point real component. -/
  re : FXR
  /-- Fixed-point imaginary component. -/
  im : FXR
  deriving Inhabited

/-- Add complex fixed-point values componentwise. -/
def fxcAdd (x y : FXC) : FXC :=
  ⟨fxrAdd x.re y.re, fxrAdd x.im y.im⟩

/-- Subtract complex fixed-point values componentwise. -/
def fxcSub (x y : FXC) : FXC :=
  ⟨fxrSub x.re y.re, fxrSub x.im y.im⟩

/-- Halve both components with fixed-point rounding. -/
def fxcHalf (x : FXC) : FXC :=
  ⟨fxrDiv2e x.re 1, fxrDiv2e x.im 1⟩

/-- Multiply complex fixed-point values using three real multiplications. -/
def fxcMul (x y : FXC) : FXC :=
  let z0 := fxrMul x.re y.re
  let z1 := fxrMul x.im y.im
  let z2 := fxrMul (fxrAdd x.re x.im) (fxrAdd y.re y.im)
  ⟨fxrSub z0 z1, fxrSub z2 (fxrAdd z0 z1)⟩

/-- Conjugate a complex fixed-point value by negating its imaginary component. -/
def fxcConj (x : FXC) : FXC :=
  ⟨x.re, fxrNeg x.im⟩

/-! ## GM_TAB: Precomputed cos/sin table for fixed-point FFT

The table has 1024 entries of type `FXC` (re, im pairs), representing
primitive 2048-th roots of unity in proper bit-reversed order for FFT.
Each entry is a pair of `UInt64` values in 32.32 fixed-point format.

We derive the fixed-point table from the already imported floating-point
twiddle table `gmRaw` by multiplying each entry by `2^32` and rounding to
the nearest integer with the reference `FPR` arithmetic. This reproduces the
constants from `kgen_fxp.c` without storing a second 1024-entry table. -/

@[inline] private def rawFPRToFXR (x : UInt64) : FXR :=
  let scaled := Falcon.Concrete.FPR.mul x (Falcon.Concrete.FPR.scaled 1 32)
  (Falcon.Concrete.FPR.rint scaled).toUInt64

/-- Fixed-point twiddle-factor table used by the FXR FFT backend. -/
def gmTable : Array FXC :=
  (Array.range 1024).map fun i =>
    ⟨rawFPRToFXR (gmRaw.getD (2 * i) 0), rawFPRToFXR (gmRaw.getD (2 * i + 1) 0)⟩

/-! ## FFT and inverse FFT on fixed-point polynomials

The polynomial of degree n = 2^logn is stored as an array of n `FXR` values.
In FFT representation, `f[i]` (for i < n/2) holds the real part and
`f[i + n/2]` holds the imaginary part of the i-th complex coefficient. -/

/-- Transform a polynomial into the split real/imaginary fixed-point FFT representation. -/
def vectFFT (logn : Nat) (f : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := f
  let mut t := hn
  for lm in [1:logn] do
    let m := 1 <<< lm
    let ht := t >>> 1
    let mut j0 := 0
    let hm := m >>> 1
    for i in [:hm] do
      let s := gmTable[m + i]!
      for j in [j0:j0 + ht] do
        let x : FXC := ⟨arr[j]!, arr[j + hn]!⟩
        let y : FXC := ⟨arr[j + ht]!, arr[j + ht + hn]!⟩
        let y' := fxcMul s y
        let z1 := fxcAdd x y'
        arr := arr.set! j z1.re
        arr := arr.set! (j + hn) z1.im
        let z2 := fxcSub x y'
        arr := arr.set! (j + ht) z2.re
        arr := arr.set! (j + ht + hn) z2.im
      j0 := j0 + t
    t := ht
  return arr

/-- Invert the split fixed-point FFT, normalizing each butterfly by a factor of two. -/
def vectIFFT (logn : Nat) (f : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := f
  let mut ht : Nat := 1
  for lm' in [1:logn] do
    let lm := logn - lm'
    let m := 1 <<< lm
    let t := ht <<< 1
    let mut j0 := 0
    let hm := m >>> 1
    for i in [:hm] do
      let s := fxcConj (gmTable[m + i]!)
      for j in [j0:j0 + ht] do
        let x : FXC := ⟨arr[j]!, arr[j + hn]!⟩
        let y : FXC := ⟨arr[j + ht]!, arr[j + ht + hn]!⟩
        let z1 := fxcHalf (fxcAdd x y)
        arr := arr.set! j z1.re
        arr := arr.set! (j + hn) z1.im
        let z2 := fxcMul s (fxcHalf (fxcSub x y))
        arr := arr.set! (j + ht) z2.re
        arr := arr.set! (j + ht + hn) z2.im
      j0 := j0 + t
    ht := t
  return arr

/-! ## Polynomial operations -/

/-- Encode the first `2^logn` signed coefficients as fixed-point values. -/
def vectSet (logn : Nat) (f : Array Int32) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxrOf (f[i]!)

/-- Add the first `2^logn` fixed-point coefficients of two polynomials. -/
def vectAdd (logn : Nat) (a b : Array FXR) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxrAdd (a[i]!) (b[i]!)

/-- Scale the first `2^logn` fixed-point coefficients by a real constant. -/
def vectMulRealconst (logn : Nat) (a : Array FXR) (c : FXR) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxrMul (a[i]!) c

/-- Scale the first `2^logn` fixed-point coefficients by a power of two. -/
def vectMul2e (logn : Nat) (a : Array FXR) (e : UInt64) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxrMul2e (a[i]!) e

/-- Multiply two polynomials pointwise in the split complex FFT representation. -/
def vectMulFft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := a
  for i in [:hn] do
    let x : FXC := ⟨arr[i]!, arr[i + hn]!⟩
    let y : FXC := ⟨b[i]!, b[i + hn]!⟩
    let z := fxcMul x y
    arr := arr.set! i z.re
    arr := arr.set! (i + hn) z.im
  return arr

/-- Conjugate every complex coefficient of a polynomial in FFT representation. -/
def vectAdjFft (logn : Nat) (a : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let n := 1 <<< logn
  let mut arr := a
  for i in [hn:n] do
    arr := arr.set! i (fxrNeg (arr[i]!))
  return arr

/-- Multiply an FFT polynomial by a self-adjoint polynomial's real coefficients. -/
def vectMulSelfadjFft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := a
  for i in [:hn] do
    arr := arr.set! i (fxrMul (arr[i]!) (b[i]!))
    arr := arr.set! (i + hn) (fxrMul (arr[i + hn]!) (b[i]!))
  return arr

/-- Divide an FFT polynomial by a self-adjoint polynomial's real coefficients. -/
def vectDivSelfadjFft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := a
  for i in [:hn] do
    arr := arr.set! i (fxrDiv (arr[i]!) (b[i]!))
    arr := arr.set! (i + hn) (fxrDiv (arr[i + hn]!) (b[i]!))
  return arr

/-- Compute the sum of squared complex magnitudes of two FFT polynomials coefficientwise. -/
def vectNormFft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut d : Array FXR := Array.replicate hn fxrZero
  for i in [:hn] do
    let v := fxrAdd
      (fxrAdd (fxrSqr (a[i]!)) (fxrSqr (a[i + hn]!)))
      (fxrAdd (fxrSqr (b[i]!)) (fxrSqr (b[i + hn]!)))
    d := d.set! i v
  return d

/-- Compute `2^e` divided by the sum of squared magnitudes of two FFT polynomials. -/
def vectInvnormFft (logn : Nat) (a b : Array FXR) (e : UInt64) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let fe := fxrOf ((1 : Int32) <<< e.toUInt32.toInt32)
  let mut d : Array FXR := Array.replicate hn fxrZero
  for i in [:hn] do
    let z := fxrAdd
      (fxrAdd (fxrSqr (a[i]!)) (fxrSqr (a[i + hn]!)))
      (fxrAdd (fxrSqr (b[i]!)) (fxrSqr (b[i + hn]!)))
    d := d.set! i (fxrDiv fe z)
  return d

end Falcon.Concrete.FXR
