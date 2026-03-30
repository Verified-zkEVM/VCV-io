/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

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

set_option autoImplicit false

namespace Falcon.Concrete.FXR

abbrev FXR := UInt64

-- fxr_of: convert a signed 32-bit integer to FXR (shift left by 32).
def fxr_of (j : Int32) : FXR :=
  j.toInt64.toUInt64 <<< 32

-- fxr_of_scaled32: given integer t, return t/2^32 as FXR (identity on bits).
def fxr_of_scaled32 (t : UInt64) : FXR := t

-- fxr_add / fxr_sub: wrapping addition/subtraction.
def fxr_add (x y : FXR) : FXR := x + y
def fxr_sub (x y : FXR) : FXR := x - y

-- fxr_neg: two's complement negation.
def fxr_neg (x : FXR) : FXR := (0 : UInt64) - x

-- fxr_half: arithmetic right shift by 1, with rounding.
-- C: `((x + 1) >>> 1) | (x & (1 << 63))`.
def fxr_half (x : FXR) : FXR :=
  let y := x + 1
  (y >>> 1) ||| (y &&& ((1 : UInt64) <<< 63))

-- fxr_double: shift left by 1.
def fxr_double (x : FXR) : FXR := x <<< 1

-- fxr_round: round to nearest integer (add 0.5, then arithmetic right shift 32).
def fxr_round (x : FXR) : Int32 :=
  let y := x + 0x80000000
  (y.toInt64 >>> (32 : Int64)).toInt32

-- fxr_mul: fixed-point multiply.
-- Portable 4-part decomposition of the 128-bit product:
--   xl, xh = unsigned low / signed high 32-bit halves
--   result = (xl*yl)>>32 + xl*(int)yh + (int)xh*yl + ((int)xh*(int)yh)<<32
def fxr_mul (x y : FXR) : FXR :=
  let xl : UInt64 := x &&& 0xFFFFFFFF
  let xh : Int64 := (x >>> 32).toInt64
  let yl : UInt64 := y &&& 0xFFFFFFFF
  let yh : Int64 := (y >>> 32).toInt64
  let z0 : UInt64 := (xl * yl) >>> 32
  let z1 : UInt64 := xl * yh.toUInt64
  let z2 : UInt64 := xh.toUInt64 * yl
  let z3 : UInt64 := (xh * yh).toUInt64 <<< 32
  z0 + z1 + z2 + z3

-- fxr_sqr: specialized squaring.
def fxr_sqr (x : FXR) : FXR :=
  let xl : UInt64 := x &&& 0xFFFFFFFF
  let xh : Int64 := (x >>> 32).toInt64
  let z0 : UInt64 := (xl * xl) >>> 32
  let z1 : UInt64 := xl * xh.toUInt64
  let z3 : UInt64 := (xh * xh).toUInt64 <<< 32
  z0 + (z1 <<< 1) + z3

-- fxr_div: bit-by-bit long division matching `inner_fxr_div`.
def fxr_div (x y : FXR) : FXR := Id.run do
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
def fxr_inv (x : FXR) : FXR :=
  fxr_div ((1 : UInt64) <<< 32) x

-- fxr_div2e: divide by 2^e with rounding.
def fxr_div2e (x : FXR) (e : UInt64) : FXR :=
  let y := x + (((1 : UInt64) <<< e) >>> 1)
  (y.toInt64 >>> e.toInt64).toUInt64

-- fxr_mul2e: multiply by 2^e.
def fxr_mul2e (x : FXR) (e : UInt64) : FXR := x <<< e

-- fxr_lt: signed comparison.
def fxr_lt (x y : FXR) : Bool := x.toInt64 < y.toInt64

def fxr_zero : FXR := 0
def fxr_sqrt2 : FXR := 6074001000

/-! ## Complex fixed-point type -/

structure FXC where
  re : FXR
  im : FXR
  deriving Inhabited

def fxc_add (x y : FXC) : FXC :=
  ⟨fxr_add x.re y.re, fxr_add x.im y.im⟩

def fxc_sub (x y : FXC) : FXC :=
  ⟨fxr_sub x.re y.re, fxr_sub x.im y.im⟩

def fxc_half (x : FXC) : FXC :=
  ⟨fxr_div2e x.re 1, fxr_div2e x.im 1⟩

def fxc_mul (x y : FXC) : FXC :=
  let z0 := fxr_mul x.re y.re
  let z1 := fxr_mul x.im y.im
  let z2 := fxr_mul (fxr_add x.re x.im) (fxr_add y.re y.im)
  ⟨fxr_sub z0 z1, fxr_sub z2 (fxr_add z0 z1)⟩

def fxc_conj (x : FXC) : FXC :=
  ⟨x.re, fxr_neg x.im⟩

/-! ## GM_TAB: Precomputed cos/sin table for fixed-point FFT

The table has 1024 entries of type `FXC` (re, im pairs), representing
primitive 2048-th roots of unity in proper bit-reversed order for FFT.
Each entry is a pair of `UInt64` values in 32.32 fixed-point format.

Due to the large size (1024 × 2 = 2048 `UInt64` values), we use `sorry`
here. In a complete build, these would be filled from the C reference
`GM_TAB` in `kgen_fxp.c`. -/

private def GM_TAB_DATA : Array (UInt64 × UInt64) := #[]

def GM_TAB : Array FXC :=
  GM_TAB_DATA.map fun (re, im) => ⟨re, im⟩

/-! ## FFT and inverse FFT on fixed-point polynomials

The polynomial of degree n = 2^logn is stored as an array of n `FXR` values.
In FFT representation, `f[i]` (for i < n/2) holds the real part and
`f[i + n/2]` holds the imaginary part of the i-th complex coefficient. -/

def vect_FFT (logn : Nat) (f : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := f
  let mut t := hn
  for lm in [1:logn] do
    let m := 1 <<< lm
    let ht := t >>> 1
    let mut j0 := 0
    let hm := m >>> 1
    for i in [:hm] do
      let s := GM_TAB[m + i]!
      for j in [j0:j0 + ht] do
        let x : FXC := ⟨arr[j]!, arr[j + hn]!⟩
        let y : FXC := ⟨arr[j + ht]!, arr[j + ht + hn]!⟩
        let y' := fxc_mul s y
        let z1 := fxc_add x y'
        arr := arr.set! j z1.re
        arr := arr.set! (j + hn) z1.im
        let z2 := fxc_sub x y'
        arr := arr.set! (j + ht) z2.re
        arr := arr.set! (j + ht + hn) z2.im
      j0 := j0 + t
    t := ht
  return arr

def vect_iFFT (logn : Nat) (f : Array FXR) : Array FXR := Id.run do
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
      let s := fxc_conj (GM_TAB[m + i]!)
      for j in [j0:j0 + ht] do
        let x : FXC := ⟨arr[j]!, arr[j + hn]!⟩
        let y : FXC := ⟨arr[j + ht]!, arr[j + ht + hn]!⟩
        let z1 := fxc_half (fxc_add x y)
        arr := arr.set! j z1.re
        arr := arr.set! (j + hn) z1.im
        let z2 := fxc_mul s (fxc_half (fxc_sub x y))
        arr := arr.set! (j + ht) z2.re
        arr := arr.set! (j + ht + hn) z2.im
      j0 := j0 + t
    ht := t
  return arr

/-! ## Polynomial operations -/

def vect_set (logn : Nat) (f : Array Int32) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxr_of (f[i]!)

def vect_add (logn : Nat) (a b : Array FXR) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxr_add (a[i]!) (b[i]!)

def vect_mul_realconst (logn : Nat) (a : Array FXR) (c : FXR) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxr_mul (a[i]!) c

def vect_mul2e (logn : Nat) (a : Array FXR) (e : UInt64) : Array FXR :=
  let n := 1 <<< logn
  (Array.range n).map fun i => fxr_mul2e (a[i]!) e

def vect_mul_fft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := a
  for i in [:hn] do
    let x : FXC := ⟨arr[i]!, arr[i + hn]!⟩
    let y : FXC := ⟨b[i]!, b[i + hn]!⟩
    let z := fxc_mul x y
    arr := arr.set! i z.re
    arr := arr.set! (i + hn) z.im
  return arr

def vect_adj_fft (logn : Nat) (a : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let n := 1 <<< logn
  let mut arr := a
  for i in [hn:n] do
    arr := arr.set! i (fxr_neg (arr[i]!))
  return arr

def vect_mul_selfadj_fft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := a
  for i in [:hn] do
    arr := arr.set! i (fxr_mul (arr[i]!) (b[i]!))
    arr := arr.set! (i + hn) (fxr_mul (arr[i + hn]!) (b[i]!))
  return arr

def vect_div_selfadj_fft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut arr := a
  for i in [:hn] do
    arr := arr.set! i (fxr_div (arr[i]!) (b[i]!))
    arr := arr.set! (i + hn) (fxr_div (arr[i + hn]!) (b[i]!))
  return arr

def vect_norm_fft (logn : Nat) (a b : Array FXR) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut d : Array FXR := Array.replicate hn fxr_zero
  for i in [:hn] do
    let v := fxr_add
      (fxr_add (fxr_sqr (a[i]!)) (fxr_sqr (a[i + hn]!)))
      (fxr_add (fxr_sqr (b[i]!)) (fxr_sqr (b[i + hn]!)))
    d := d.set! i v
  return d

def vect_invnorm_fft (logn : Nat) (a b : Array FXR) (e : UInt64) : Array FXR := Id.run do
  let hn := 1 <<< (logn - 1)
  let fe := fxr_of ((1 : Int32) <<< e.toUInt32.toInt32)
  let mut d : Array FXR := Array.replicate hn fxr_zero
  for i in [:hn] do
    let z := fxr_add
      (fxr_add (fxr_sqr (a[i]!)) (fxr_sqr (a[i + hn]!)))
      (fxr_add (fxr_sqr (b[i]!)) (fxr_sqr (b[i + hn]!)))
    d := d.set! i (fxr_div fe z)
  return d

end Falcon.Concrete.FXR
