/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Multi-Precision Big Integer Arithmetic with 31-bit Limbs

Port of the `zint_*` functions from Pornin's `c-fn-dsa/kgen_zint31.c`.

Big integers are represented as `Array UInt32` where each limb holds a value in
`[0, 2^31 - 1]` (i.e., 31 useful bits per 32-bit word).

The original C code stores interleaved arrays with pointer strides. In this Lean
port, array elements are accessed with explicit index arithmetic:
element `i` of a logical big integer lives at `arr[offset + i * stride]`.

## Helper Functions

We also port the small modular-arithmetic helpers from `kgen_inner.h`:
`tbmask`, `mp_add`, `mp_sub`, `mp_half`, `mp_mmul`.

## Main Functions

- `zint_mul_small` — multiply a big integer by a small factor
- `zint_add_mul_small` — add `y * s` to a big integer
- `zint_mod_small_unsigned` — reduce big integer modulo a small prime (unsigned)
- `zint_add` — add two big integers
- `zint_sub` — subtract two big integers
- `zint_negate` — conditionally negate a big integer
- `zint_norm_zero` — normalize around zero (signed reduction)
- `zint_rebuild_CRT` — Chinese Remainder Theorem reconstruction
- `zint_bezout` — extended GCD / Bézout coefficients
- `zint_co_reduce` — simultaneous reduction (used in NTRU solver)
- `zint_co_reduce_mod` — modular simultaneous reduction
- `zint_add_scaled_mul_small` — scaled multiply-add
- `zint_sub_scaled` — scaled subtract
-/

set_option autoImplicit false

namespace Falcon.Concrete.BigInt31

/-! ## Bit-width constants -/

/-- The limb mask `0x7FFFFFFF = 2^31 - 1`. -/
def LIMB_MASK : UInt32 := 0x7FFFFFFF

/-! ## Low-level helpers (from `inner.h` / `kgen_inner.h`) -/

/-- Arithmetic right-shift of a `UInt32` treated as signed: expand the top bit
into a full 32-bit mask. Returns `0xFFFFFFFF` if `x ≥ 0x80000000`, else `0`. -/
@[inline] def tbmask (x : UInt32) : UInt32 :=
  (x.toInt32 >>> (31 : Int32)).toUInt32

/-- Addition modulo `p` (inputs and output in `[0, p-1]`). -/
@[inline] def mp_add (a b p : UInt32) : UInt32 :=
  let d := a + b - p
  d + (p &&& tbmask d)

/-- Subtraction modulo `p` (inputs and output in `[0, p-1]`). -/
@[inline] def mp_sub (a b p : UInt32) : UInt32 :=
  let d := a - b
  d + (p &&& tbmask d)

/-- Halving modulo `p`. -/
@[inline] def mp_half (a p : UInt32) : UInt32 :=
  (a + (p &&& (- (a &&& 1)))) >>> (1 : UInt32)

/-- Montgomery multiplication: returns `(a * b) / R mod p` where `R = 2^32`.
`p0i = -1/p mod 2^32`. -/
@[inline] def mp_mmul (a b p p0i : UInt32) : UInt32 :=
  let z : UInt64 := a.toUInt64 * b.toUInt64
  let w : UInt32 := z.toUInt32 * p0i
  let d : UInt32 := ((z + w.toUInt64 * p.toUInt64) >>> (32 : UInt64)).toUInt32 - p
  d + (p &&& tbmask d)

/-- Compute `-1/x mod 2^31` for odd `x`. -/
@[inline] def mp_ninv31 (x : UInt32) : UInt32 :=
  let y := 2 - x
  let y := y * (2 - x * y)
  let y := y * (2 - x * y)
  let y := y * (2 - x * y)
  let y := y * (2 - x * y)
  (-y) &&& LIMB_MASK

/-- Count leading zeros in a 32-bit word (portable implementation). -/
def lzcnt (x : UInt32) : UInt32 :=
  let m := tbmask ((x >>> (16 : UInt32)) - 1)
  let s := m &&& 16
  let x := (x >>> (16 : UInt32)) ^^^ (m &&& (x ^^^ (x >>> (16 : UInt32))))
  let m := tbmask ((x >>> (8 : UInt32)) - 1)
  let s := s ||| (m &&& 8)
  let x := (x >>> (8 : UInt32)) ^^^ (m &&& (x ^^^ (x >>> (8 : UInt32))))
  let m := tbmask ((x >>> (4 : UInt32)) - 1)
  let s := s ||| (m &&& 4)
  let x := (x >>> (4 : UInt32)) ^^^ (m &&& (x ^^^ (x >>> (4 : UInt32))))
  let m := tbmask ((x >>> (2 : UInt32)) - 1)
  let s := s ||| (m &&& 2)
  let x := (x >>> (2 : UInt32)) ^^^ (m &&& (x ^^^ (x >>> (2 : UInt32))))
  s + ((2 - x) &&& tbmask (x - 3))

/-! ## Array access helpers -/

/-- Read element `i` from a strided big integer starting at `offset`. -/
@[inline] def getLimb (arr : Array UInt32) (offset stride i : Nat) : UInt32 :=
  let idx := offset + i * stride
  if idx < arr.size then arr[idx]! else 0

/-- Write element `i` of a strided big integer starting at `offset`. -/
@[inline] def setLimb (arr : Array UInt32) (offset stride i : Nat) (v : UInt32) :
    Array UInt32 :=
  let idx := offset + i * stride
  if idx < arr.size then arr.set! idx v else arr

/-! ## Core big-integer operations -/

/-- Multiply a contiguous big integer `m[0..len-1]` by a small factor `x`.
Returns `(updated array, carry)`. -/
def zint_mul_small (m : Array UInt32) (len : Nat) (x : UInt32) :
    Array UInt32 × UInt32 := Id.run do
  let mut arr := m
  let mut cc : UInt32 := 0
  for i in [:len] do
    let z : UInt64 := (getLimb arr 0 1 i).toUInt64 * x.toUInt64 + cc.toUInt64
    arr := setLimb arr 0 1 i (z.toUInt32 &&& LIMB_MASK)
    cc := (z >>> (31 : UInt64)).toUInt32
  return (arr, cc)

/-- Reduce a big integer modulo a small prime `p` (unsigned result in `[0, p-1]`).
The big integer has `len` limbs starting at `offset` with the given `stride`.
`p0i = -1/p mod 2^32`, `R2 = 2^64 mod p`. -/
def zint_mod_small_unsigned (d : Array UInt32) (len : Nat) (offset stride : Nat)
    (p p0i R2 : UInt32) : UInt32 := Id.run do
  let mut x : UInt32 := 0
  let z := mp_half R2 p
  for i' in [:len] do
    let i := len - 1 - i'
    let w' := getLimb d offset stride i - p
    let w := w' + (p &&& tbmask w')
    x := mp_mmul x z p p0i
    x := mp_add x w p
  return x

/-- Add `y[0..len-1] * s` to a strided big integer `x`.
`x` has stride `xstride`; `y` is contiguous.
The final carry is written to the next limb of `x`. -/
def zint_add_mul_small (x : Array UInt32) (len : Nat)
    (xoffset xstride : Nat) (y : Array UInt32) (s : UInt32) :
    Array UInt32 := Id.run do
  let mut arr := x
  let mut cc : UInt32 := 0
  for i in [:len] do
    let xw := getLimb arr xoffset xstride i
    let yw := getLimb y 0 1 i
    let z : UInt64 := yw.toUInt64 * s.toUInt64 + xw.toUInt64 + cc.toUInt64
    arr := setLimb arr xoffset xstride i (z.toUInt32 &&& LIMB_MASK)
    cc := (z >>> (31 : UInt64)).toUInt32
  arr := setLimb arr xoffset xstride len cc
  return arr

/-- Normalize a big integer around zero: if `x > (m-1)/2` then replace `x`
with `x - m`. Both `x` (strided) and `m` (contiguous) have `len` limbs. -/
def zint_norm_zero (x : Array UInt32) (len : Nat)
    (xoffset xstride : Nat) (m : Array UInt32) : Array UInt32 := Id.run do
  let mut r : UInt32 := 0
  let mut bb : UInt32 := 0
  for i' in [:len] do
    let i := len - 1 - i'
    let wx := getLimb x xoffset xstride i
    let wp := (getLimb m 0 1 i >>> (1 : UInt32)) ||| (bb <<< (30 : UInt32))
    bb := getLimb m 0 1 i &&& 1
    let cc := wp - wx
    let cc' := ((- cc) >>> (31 : UInt32)) ||| (- (cc >>> (31 : UInt32)))
    r := r ||| (cc' &&& ((r &&& 1) - 1))
  let s := tbmask r
  let mut arr := x
  let mut cc : UInt32 := 0
  for j in [:len] do
    let xw := getLimb arr xoffset xstride j
    let w := xw - getLimb m 0 1 j - cc
    cc := w >>> (31 : UInt32)
    let xw' := xw ^^^ (((w &&& LIMB_MASK) ^^^ xw) &&& s)
    arr := setLimb arr xoffset xstride j xw'
  return arr

/-- Conditionally negate a contiguous big integer of `len` limbs.
If `ctl = 0xFFFFFFFF` the value is negated; if `ctl = 0` it is unchanged. -/
def zint_negate (a : Array UInt32) (len : Nat) (ctl : UInt32) :
    Array UInt32 := Id.run do
  let mut arr := a
  let mut cc : UInt32 := - ctl
  let m := ctl >>> (1 : UInt32)
  for i in [:len] do
    let aw := getLimb arr 0 1 i
    let aw' := (aw ^^^ m) + cc
    arr := setLimb arr 0 1 i (aw' &&& LIMB_MASK)
    cc := aw' >>> (31 : UInt32)
  return arr

/-- Add two contiguous big integers of `len` limbs. Returns `(result, carry)`. -/
def zint_add (a b : Array UInt32) (len : Nat) : Array UInt32 × UInt32 := Id.run do
  let mut arr := a
  let mut cc : UInt32 := 0
  for i in [:len] do
    let w := getLimb arr 0 1 i + getLimb b 0 1 i + cc
    arr := setLimb arr 0 1 i (w &&& LIMB_MASK)
    cc := w >>> (31 : UInt32)
  return (arr, cc)

/-- Subtract two contiguous big integers of `len` limbs: `a := a - b`.
Returns `(result, borrow)`. -/
def zint_sub (a b : Array UInt32) (len : Nat) : Array UInt32 × UInt32 := Id.run do
  let mut arr := a
  let mut cc : UInt32 := 0
  for i in [:len] do
    let w := getLimb arr 0 1 i - getLimb b 0 1 i - cc
    arr := setLimb arr 0 1 i (w &&& LIMB_MASK)
    cc := w >>> (31 : UInt32)
  return (arr, cc)

/-! ## Simultaneous reduction (`zint_co_reduce`)

Replace `a` with `(a*xa + b*xb) / 2^31` and `b` with `(a*ya + b*yb) / 2^31`.
The low bits are dropped (the caller ensures they are zero). Negative results
are negated; the return value encodes which were negated (bit 0 = a, bit 1 = b).
-/

/-- Simultaneous reduction. Returns `(a', b', negation_flags)`.
Coefficients `xa, xb, ya, yb` may use the full signed 32-bit range. -/
def zint_co_reduce (a b : Array UInt32) (len : Nat)
    (xa xb ya yb : Int64) : Array UInt32 × Array UInt32 × UInt32 := Id.run do
  let mut a' := a
  let mut b' := b
  let mut cca : Int64 := 0
  let mut ccb : Int64 := 0
  for i in [:len] do
    let wa := (getLimb a' 0 1 i).toUInt64.toInt64
    let wb := (getLimb b' 0 1 i).toUInt64.toInt64
    let za : Int64 := wa * xa + wb * xb + cca
    let zb : Int64 := wa * ya + wb * yb + ccb
    if i > 0 then
      a' := setLimb a' 0 1 (i - 1) (za.toUInt64.toUInt32 &&& LIMB_MASK)
      b' := setLimb b' 0 1 (i - 1) (zb.toUInt64.toUInt32 &&& LIMB_MASK)
    cca := za >>> (31 : Int64)
    ccb := zb >>> (31 : Int64)
  if len > 0 then
    a' := setLimb a' 0 1 (len - 1) (cca.toUInt64.toUInt32 &&& LIMB_MASK)
    b' := setLimb b' 0 1 (len - 1) (ccb.toUInt64.toUInt32 &&& LIMB_MASK)
  let nega : UInt32 := (cca >>> (63 : Int64)).toUInt64.toUInt32
  let negb : UInt32 := (ccb >>> (63 : Int64)).toUInt64.toUInt32
  a' := zint_negate a' len nega
  b' := zint_negate b' len negb
  return (a', b', (- nega) ||| ((- negb) <<< (1 : UInt32)))

/-! ## Modular finish and `zint_co_reduce_mod` -/

/-- Finish modular reduction: ensure `a ∈ [0, m-1]`.
If `neg = 1` then `-m ≤ a < 0`; if `neg = 0` then `0 ≤ a < 2m`. -/
def zint_finish_mod (a m : Array UInt32) (len : Nat) (neg : UInt32) :
    Array UInt32 := Id.run do
  let mut cc : UInt32 := 0
  for i in [:len] do
    cc := (getLimb a 0 1 i - getLimb m 0 1 i - cc) >>> (31 : UInt32)
  let xm := (- neg) >>> (1 : UInt32)
  let ym := - (neg ||| (1 - cc))
  let mut arr := a
  cc := neg
  for i in [:len] do
    let mw := (getLimb m 0 1 i ^^^ xm) &&& ym
    let aw := getLimb arr 0 1 i - mw - cc
    arr := setLimb arr 0 1 i (aw &&& LIMB_MASK)
    cc := aw >>> (31 : UInt32)
  return arr

/-- Modular simultaneous reduction. Replace:
  `a := (a*xa + b*xb) / 2^31 mod m`
  `b := (a*ya + b*yb) / 2^31 mod m`
`m0i = -1/m[0] mod 2^31`. -/
def zint_co_reduce_mod (a b m : Array UInt32) (len : Nat)
    (m0i : UInt32) (xa xb ya yb : Int64) :
    Array UInt32 × Array UInt32 := Id.run do
  let mut a' := a
  let mut b' := b
  let mut cca : Int64 := 0
  let mut ccb : Int64 := 0
  let a0 := (getLimb a 0 1 0).toUInt64
  let b0 := (getLimb b 0 1 0).toUInt64
  let fa : UInt32 :=
    ((a0.toUInt32 * xa.toUInt64.toUInt32 +
      b0.toUInt32 * xb.toUInt64.toUInt32) * m0i) &&& LIMB_MASK
  let fb : UInt32 :=
    ((a0.toUInt32 * ya.toUInt64.toUInt32 +
      b0.toUInt32 * yb.toUInt64.toUInt32) * m0i) &&& LIMB_MASK
  for i in [:len] do
    let wa := (getLimb a' 0 1 i).toUInt64.toInt64
    let wb := (getLimb b' 0 1 i).toUInt64.toInt64
    let mi := (getLimb m 0 1 i).toUInt64.toInt64
    let za : Int64 := wa * xa + wb * xb + mi * fa.toUInt64.toInt64 + cca
    let zb : Int64 := wa * ya + wb * yb + mi * fb.toUInt64.toInt64 + ccb
    if i > 0 then
      a' := setLimb a' 0 1 (i - 1) (za.toUInt64.toUInt32 &&& LIMB_MASK)
      b' := setLimb b' 0 1 (i - 1) (zb.toUInt64.toUInt32 &&& LIMB_MASK)
    cca := za >>> (31 : Int64)
    ccb := zb >>> (31 : Int64)
  if len > 0 then
    a' := setLimb a' 0 1 (len - 1) cca.toUInt64.toUInt32
    b' := setLimb b' 0 1 (len - 1) ccb.toUInt64.toUInt32
  let negA := (cca.toUInt64 >>> (63 : UInt64)).toUInt32
  let negB := (ccb.toUInt64 >>> (63 : UInt64)).toUInt32
  a' := zint_finish_mod a' m len negA
  b' := zint_finish_mod b' m len negB
  return (a', b')

/-! ## CRT reconstruction

`zint_rebuild_CRT` reconstructs big integers from their residues modulo a
sequence of small primes, using the Chinese Remainder Theorem. The function
operates on an interleaved array `xx` containing `num_sets` groups of `n`
big integers, each with `xlen` limbs (stride = `n`).
-/

/-- A small-prime record, matching the C `PRIMES[]` table entries. -/
structure SmallPrime where
  p : UInt32
  p0i : UInt32
  R2 : UInt32
  s : UInt32
  deriving Repr, Inhabited

/-- CRT reconstruction. `primes` supplies the moduli (in order).
If `normalizeSigned` is true, results are centered around 0. -/
def zint_rebuild_CRT (xx : Array UInt32) (xlen n numSets : Nat)
    (primes : Array SmallPrime) (normalizeSigned : Bool)
    (tmp : Array UInt32) : Array UInt32 × Array UInt32 := Id.run do
  let mut xx' := xx
  let mut tmp' := tmp
  if xlen == 0 then return (xx', tmp')
  if 0 < primes.size then
    tmp' := setLimb tmp' 0 1 0 primes[0]!.p
  let mut uu : Nat := 0
  for i in [1:xlen] do
    if i < primes.size then
      let pr := primes[i]!
      uu := uu + n
      let mut kk : Nat := 0
      for _ in [:numSets] do
        for j in [:n] do
          let xp := getLimb xx' (kk + j + uu) 1 0
          let xq := zint_mod_small_unsigned xx' i (kk + j) n pr.p pr.p0i pr.R2
          let xr := mp_mmul pr.s (mp_sub xp xq pr.p) pr.p pr.p0i
          xx' := zint_add_mul_small xx' i (kk + j) n tmp' xr
        kk := kk + n * xlen
      let (newTmp, carry) := zint_mul_small tmp' i pr.p
      tmp' := newTmp
      tmp' := setLimb tmp' 0 1 i carry
  if normalizeSigned then
    let mut kk : Nat := 0
    for _ in [:numSets] do
      for j in [:n] do
        xx' := zint_norm_zero xx' xlen (kk + j) n tmp'
      kk := kk + n * xlen
  return (xx', tmp')

/-! ## Extended GCD / Bézout coefficients

`zint_bezout` computes `u, v` such that `x*u - y*v = gcd(x, y)`.
Uses the optimized binary GCD from <https://eprint.iacr.org/2020/972>.
Returns 1 on success (GCD = 1), 0 on failure.
-/

/-- Extended GCD. Returns `(u, v, success)` where `x*u - y*v = gcd(x,y)`,
and `success = 1` iff `gcd(x,y) = 1` and both `x, y` are odd. -/
def zint_bezout (x y : Array UInt32) (len : Nat) :
    Array UInt32 × Array UInt32 × UInt32 := Id.run do
  if len == 0 then return (#[], #[], 0)
  let x0i := mp_ninv31 (getLimb x 0 1 0)
  let y0i := mp_ninv31 (getLimb y 0 1 0)
  let mut a := x.extract 0 len
  let mut b := y.extract 0 len
  let mut u0 : Array UInt32 := Array.replicate len 0
  u0 := setLimb u0 0 1 0 1
  let mut v0 : Array UInt32 := Array.replicate len 0
  let mut u1 := y.extract 0 len
  let mut v1 := x.extract 0 len
  v1 := setLimb v1 0 1 0 (getLimb v1 0 1 0 - 1)

  let numIter := 62 * len + 31
  for iter in [:numIter] do
    let num := numIter - iter
    if num < 31 then
      break

    let mut c0 : UInt32 := 0xFFFFFFFF
    let mut c1 : UInt32 := 0xFFFFFFFF
    let mut cp : UInt32 := 0xFFFFFFFF
    let mut a0 : UInt32 := 0
    let mut a1 : UInt32 := 0
    let mut b0 : UInt32 := 0
    let mut b1 : UInt32 := 0
    for j' in [:len] do
      let j := len - 1 - j'
      let aw := getLimb a 0 1 j
      let bw := getLimb b 0 1 j
      a1 := a1 ^^^ (c1 &&& (a1 ^^^ aw))
      a0 := a0 ^^^ (c0 &&& (a0 ^^^ aw))
      b1 := b1 ^^^ (c1 &&& (b1 ^^^ bw))
      b0 := b0 ^^^ (c0 &&& (b0 ^^^ bw))
      cp := c0
      c0 := c1
      c1 := c1 &&& ((((aw ||| bw) + LIMB_MASK) >>> (31 : UInt32)) - 1)

    let s := lzcnt (a1 ||| b1 ||| ((cp &&& c0) >>> (1 : UInt32)))
    let ha_raw := (a1 <<< s) ||| (a0 >>> (31 - s))
    let hb_raw := (b1 <<< s) ||| (b0 >>> (31 - s))
    let ha_adj := ha_raw ^^^ (cp &&& (ha_raw ^^^ a1))
    let hb_adj := hb_raw ^^^ (cp &&& (hb_raw ^^^ b1))
    let ha := ha_adj &&& (~~~ c0)
    let hb := hb_adj &&& (~~~ c0)

    let xa_init : UInt64 := (ha.toUInt64 <<< (31 : UInt64)) ||| (getLimb a 0 1 0).toUInt64
    let xb_init : UInt64 := (hb.toUInt64 <<< (31 : UInt64)) ||| (getLimb b 0 1 0).toUInt64

    let mut xa := xa_init
    let mut xb := xb_init
    let mut fg0 : UInt64 := 1
    let mut fg1 : UInt64 := (1 : UInt64) <<< (32 : UInt64)
    for _ in [:31] do
      let a_odd : UInt64 := - (xa &&& 1)
      let dx := xa - xb
      let dxSign : UInt64 := dx.toInt64.toUInt64 >>> (63 : UInt64)
      let swap := a_odd &&& dxSign
      let t1 := swap &&& (xa ^^^ xb)
      xa := xa ^^^ t1
      xb := xb ^^^ t1
      let t2 := swap &&& (fg0 ^^^ fg1)
      fg0 := fg0 ^^^ t2
      fg1 := fg1 ^^^ t2
      xa := xa - (a_odd &&& xb)
      fg0 := fg0 - (a_odd &&& fg1)
      xa := xa >>> (1 : UInt64)
      fg1 := fg1 <<< (1 : UInt64)

    fg0 := fg0 + 0x7FFFFFFF7FFFFFFF
    fg1 := fg1 + 0x7FFFFFFF7FFFFFFF
    let f0 : Int64 := (fg0 &&& 0xFFFFFFFF).toInt64 - 0x7FFFFFFF
    let g0 : Int64 := (fg0 >>> (32 : UInt64)).toInt64 - 0x7FFFFFFF
    let f1 : Int64 := (fg1 &&& 0xFFFFFFFF).toInt64 - 0x7FFFFFFF
    let g1 : Int64 := (fg1 >>> (32 : UInt64)).toInt64 - 0x7FFFFFFF

    let (a'', b'', negab) := zint_co_reduce a b len f0 g0 f1 g1
    a := a''
    b := b''
    let negA_mask : Int64 := - (negab &&& 1).toUInt64.toInt64
    let negB_mask : Int64 := - (negab >>> (1 : UInt32)).toUInt64.toInt64
    let f0' := f0 - ((f0 + f0) &&& negA_mask)
    let g0' := g0 - ((g0 + g0) &&& negA_mask)
    let f1' := f1 - ((f1 + f1) &&& negB_mask)
    let g1' := g1 - ((g1 + g1) &&& negB_mask)
    let (u0'', u1'') :=
      zint_co_reduce_mod u0 u1 (y.extract 0 len) len y0i f0' g0' f1' g1'
    u0 := u0''
    u1 := u1''
    let (v0'', v1'') :=
      zint_co_reduce_mod v0 v1 (x.extract 0 len) len x0i f0' g0' f1' g1'
    v0 := v0''
    v1 := v1''

  let mut r := getLimb b 0 1 0 ^^^ 1
  for j in [1:len] do
    r := r ||| getLimb b 0 1 j
  r := r ||| ((getLimb x 0 1 0 &&& getLimb y 0 1 0 &&& 1) ^^^ 1)
  let success := 1 - ((r ||| (- r)) >>> (31 : UInt32))
  return (u1, v1, success)

/-! ## Scaled operations (used in NTRU key generation) -/

/-- Add `(2^(31*sch + scl)) * k * y` to a strided big integer `x`.
`y` is strided with stride `stride`; `x` is strided with the same stride.
`k` is a signed 32-bit factor. -/
def zint_add_scaled_mul_small (x : Array UInt32) (xlen : Nat)
    (y : Array UInt32) (ylen : Nat) (stride : Nat)
    (k : Int32) (sch scl : UInt32) : Array UInt32 := Id.run do
  if ylen == 0 then return x
  let ysign := (- (getLimb y 0 stride (ylen - 1) >>> (30 : UInt32))) >>> (1 : UInt32)
  let mut tw : UInt32 := 0
  let mut cc : Int32 := 0
  let mut arr := x
  let mut yrem := ylen
  let mut yidx : Nat := 0
  for i in [sch.toNat:xlen] do
    let mut wy : UInt32 := ysign
    if yrem > 0 then
      wy := getLimb y 0 stride yidx
      yidx := yidx + 1
      yrem := yrem - 1
    let wys := ((wy <<< scl) &&& LIMB_MASK) ||| tw
    tw := wy >>> (31 - scl)
    let xw := getLimb arr 0 stride i
    let wysI : Int64 := wys.toUInt64.toInt64
    let kI : Int64 := k.toInt64
    let xwI : Int64 := xw.toUInt64.toInt64
    let ccI : Int64 := cc.toInt64
    let prod : Int64 := wysI * kI + xwI + ccI
    arr := setLimb arr 0 stride i (prod.toUInt64.toUInt32 &&& LIMB_MASK)
    let carry := (prod.toUInt64 >>> (31 : UInt64)).toUInt32
    cc := carry.toInt32
  return arr

/-- Subtract `(2^(31*sch + scl)) * y` from a strided big integer `x`. -/
def zint_sub_scaled (x : Array UInt32) (xlen : Nat)
    (y : Array UInt32) (ylen : Nat) (stride : Nat)
    (sch scl : UInt32) : Array UInt32 := Id.run do
  if ylen == 0 then return x
  let ysign := (- (getLimb y 0 stride (ylen - 1) >>> (30 : UInt32))) >>> (1 : UInt32)
  let mut tw : UInt32 := 0
  let mut cc : UInt32 := 0
  let mut arr := x
  let mut yrem := ylen
  let mut yidx : Nat := 0
  for i in [sch.toNat:xlen] do
    let mut wy : UInt32 := ysign
    if yrem > 0 then
      wy := getLimb y 0 stride yidx
      yidx := yidx + 1
      yrem := yrem - 1
    let wys := ((wy <<< scl) &&& LIMB_MASK) ||| tw
    tw := wy >>> (31 - scl)
    let xw := getLimb arr 0 stride i
    let w := xw - wys - cc
    arr := setLimb arr 0 stride i (w &&& LIMB_MASK)
    cc := w >>> (31 : UInt32)
  return arr

end Falcon.Concrete.BigInt31
