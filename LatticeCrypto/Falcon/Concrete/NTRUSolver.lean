/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.BigInt31
import LatticeCrypto.Falcon.Concrete.SmallPrimeNTT

/-!
# NTRU Equation Solver for Falcon Key Generation

Port of the NTRU equation solver from Pornin's `c-fn-dsa/kgen_ntru.c`.

Given short polynomials `f, g ∈ ℤ[x]/(x^n + 1)`, the NTRU equation solver
finds short polynomials `F, G` satisfying `fG - gF = q` where `q = 12289`.

## Algorithm Overview

1. **Descent**: Compute field norms `N(f), N(g)` recursively to reduce
   the polynomial degree from `n = 2^logn` down to 1 (scalar).
2. **Base case**: Solve `f₀ · G₀ - g₀ · F₀ = q` via extended binary GCD.
3. **Ascent**: Lift `(F, G)` through each level using NTT-based polynomial
   multiplication, then apply Babai's nearest-plane reduction.

## Representation

- Big integers use 31-bit limbs in multi-word interleaved format (stride `n`).
- Small-prime RNS + NTT for fast polynomial multiplication.
- Fixed-point 32.32 arithmetic (FXR) for the Babai rounding step.

## References

- Pornin 2025, eprint 2025/1239
- `c-fn-dsa/kgen_ntru.c`, `c-fn-dsa/kgen_inner.h`
-/


namespace Falcon.Concrete.NTRUSolver

/-! ## Constants -/

/-- The Falcon modulus `q = 12289`. -/
def Q : UInt32 := 12289

/-- Maximum big-integer word count for `(f, g)` at each depth. -/
def MAX_BL_SMALL : Array Nat := #[1, 1, 2, 3, 4, 8, 14, 27, 53, 104, 207]

/-- Maximum big-integer word count for unreduced `(F, G)` at each depth. -/
def MAX_BL_LARGE : Array Nat := #[1, 2, 3, 6, 11, 21, 40, 78, 155, 308]

/-- Number of top words used for fixed-point approximation at each depth. -/
def WORD_WIN : Array Nat := #[1, 1, 2, 2, 2, 3, 3, 4, 5, 7]

/-- Minimum depth at which intermediate `(f, g)` are saved during descent. -/
def MIN_SAVE_FG : Array Nat := #[0, 0, 1, 2, 2, 2, 2, 2, 2, 3, 3]

/-! ## FXR (Fixed-point Real) type stubs

The FXR type is a 32.32 fixed-point number stored as `UInt64`.
Full implementation will come from a dedicated FXR module
(port of `kgen_fxp.c`). -/

abbrev FXR := UInt64

namespace FXR

@[inline] def zero : FXR := 0

@[inline] def ofInt (j : Int32) : FXR := j.toUInt32.toUInt64 <<< 32

@[inline] def add (x y : FXR) : FXR := x + y

@[inline] def sqr (_x : FXR) : FXR := sorry

@[inline] def lt (x y : FXR) : Bool := x.toInt64 < y.toInt64

@[inline] def ofScaled32 (x : UInt64) : FXR := x

end FXR

/-! ## Stub operations for modules not yet ported

These functions will be provided by `PolyBigInt` and `FXR` modules once
they are ported from `kgen_fxp.c` and `kgen_poly.c`. -/

private def poly_big_to_small (_logn : Nat) (_s : Array UInt32) (_off : Nat)
    (_lim : Int32) : Option (Array Int8) := sorry

private def vect_set (_logn : Nat) (_f : Array Int8) : Array FXR := sorry
private def vect_FFT (_logn : Nat) (_f : Array FXR) : Array FXR := sorry
private def vect_iFFT (_logn : Nat) (_f : Array FXR) : Array FXR := sorry
private def vect_invnorm_fft (_logn : Nat) (_a _b : Array FXR) (_e : Nat) :
    Array FXR := sorry
private def vect_adj_fft (_logn : Nat) (_a : Array FXR) : Array FXR := sorry
private def vect_mul_realconst (_logn : Nat) (_a : Array FXR) (_c : FXR) :
    Array FXR := sorry
private def vect_mul_selfadj_fft (_logn : Nat) (_a _b : Array FXR) :
    Array FXR := sorry

/-! ## Helper types and conversions -/

/-- Convert from `SmallPrimeNTT.SmallPrime` to `BigInt31.SmallPrime`
(dropping the `g` and `ig` fields which are only needed for NTT). -/
@[inline] def toBigInt31Prime (sp : SmallPrimeNTT.SmallPrime) :
    BigInt31.SmallPrime :=
  ⟨sp.p, sp.p0i, sp.R2, sp.s⟩

/-- The PRIMES table converted to `BigInt31.SmallPrime` format
(used by CRT reconstruction). -/
def PRIMES_BI : Array BigInt31.SmallPrime :=
  SmallPrimeNTT.PRIMES.map toBigInt31Prime

/-! ## Buffer manipulation helpers -/

@[inline] private def getU32 (arr : Array UInt32) (i : Nat) : UInt32 :=
  arr.getD i 0

/-- Extract `len` words from `arr` starting at offset `off`. -/
private def extractRange (arr : Array UInt32) (off len : Nat) : Array UInt32 :=
  arr.extract off (off + len)

/-- Overwrite `src.size` words into `arr` starting at offset `off`. -/
private def writeRange (arr : Array UInt32) (off : Nat) (src : Array UInt32) :
    Array UInt32 := Id.run do
  let mut arr := arr
  for i in [:src.size] do
    if off + i < arr.size then
      arr := arr.set! (off + i) (src.getD i 0)
  return arr

/-- Ensure array has at least `sz` elements, zero-extending if needed. -/
private def ensureSize (arr : Array UInt32) (sz : Nat) : Array UInt32 :=
  if arr.size >= sz then arr
  else arr ++ Array.replicate (sz - arr.size) (0 : UInt32)

/-- Construct inverse-NTT twiddle factors for prime `pr` at degree `2^logn`.
Uses `mp_mkgmigm` and returns only the `igm` component. -/
private def mkigm (logn : Nat) (pr : SmallPrimeNTT.SmallPrime) : Array UInt32 :=
  (SmallPrimeNTT.mp_mkgmigm logn pr.g pr.ig pr.p pr.p0i).2

/-- Reduce a big integer modulo a small prime using signed convention.
Port of the inline `zint_mod_small_signed` from `kgen_inner.h`.
The big integer has `len` limbs starting at `offset` with stride `stride`.
`Rx = 2^(31*len) mod p`. -/
private def zint_mod_small_signed (d : Array UInt32) (len : Nat)
    (offset stride : Nat) (p p0i R2 Rx : UInt32) : UInt32 :=
  if len == 0 then 0
  else
    let z := BigInt31.zint_mod_small_unsigned d len offset stride p p0i R2
    let topWord := BigInt31.getLimb d offset stride (len - 1)
    SmallPrimeNTT.mp_sub z (Rx &&& (0 - (topWord >>> (30 : UInt32)))) p

/-! ## make_fg_zero

Convert source `f` and `g` into RNS+NTT (one word per coefficient) using
the first small prime. Returns `ft ++ gt` (each `n = 2^logn` words). -/

def make_fg_zero (logn : Nat) (f g : Array Int8) : Array UInt32 :=
  let pr := SmallPrimeNTT.PRIMES.getD 0 default
  let p := pr.p
  let p0i := pr.p0i
  let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i
  let ft := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn f p) gm p p0i
  let gt := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn g p) gm p p0i
  ft ++ gt

/-! ## make_fg_step

One step of field-norm computation. Given `(f, g)` at depth `d` with degree
`n = 2^(logn_top - d)` and `slen = MAX_BL_SMALL[d]` RNS words per coefficient,
compute `(f', g')` at depth `d + 1` with degree `n/2` and
`tlen = MAX_BL_SMALL[d + 1]` words.

In NTT representation, the field norm satisfies:
  `N(f)[j] = f[2j] · f[2j+1] · R²` (Montgomery form)

**Phase 1** (primes `0..slen-1`): compute norms from existing NTT data,
then inverse-NTT the source to recover `(f, g)` in RNS (non-NTT).

**Phase 2**: CRT-reconstruct `(f, g)` from RNS to plain integers.

**Phase 3** (primes `slen..tlen-1`): reduce plain-integer coefficients
modulo each new prime, forward-NTT, compute norms. -/

def make_fg_step (logn_top depth : Nat) (buf : Array UInt32) :
    Array UInt32 := Id.run do
  let logn := logn_top - depth
  let n := 1 <<< logn
  let hn := n >>> 1
  let slen := MAX_BL_SMALL.getD depth 1
  let tlen := MAX_BL_SMALL.getD (depth + 1) 1

  let mut fs := extractRange buf 0 (n * slen)
  let mut gs := extractRange buf (n * slen) (n * slen)
  let mut fd : Array UInt32 := Array.replicate (hn * tlen) 0
  let mut gd : Array UInt32 := Array.replicate (hn * tlen) 0

  -- Phase 1: first slen primes — compute norms from NTT, then iNTT source
  for i in [:slen] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let p := pr.p
    let p0i := pr.p0i
    let r2 := pr.R2

    for j in [:hn] do
      let xf0 := getU32 fs (i * n + 2 * j)
      let xf1 := getU32 fs (i * n + 2 * j + 1)
      let xg0 := getU32 gs (i * n + 2 * j)
      let xg1 := getU32 gs (i * n + 2 * j + 1)
      fd := fd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul xf0 xf1 p p0i) r2 p p0i)
      gd := gd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul xg0 xg1 p p0i) r2 p p0i)

    let igm := mkigm logn pr
    let fSlice := SmallPrimeNTT.mp_iNTT logn
      (extractRange fs (i * n) n) igm p p0i
    fs := writeRange fs (i * n) fSlice
    let gSlice := SmallPrimeNTT.mp_iNTT logn
      (extractRange gs (i * n) n) igm p p0i
    gs := writeRange gs (i * n) gSlice

  -- Phase 2: CRT-reconstruct source (f, g) → plain signed integers
  let combined := fs ++ gs
  let crtTmp := Array.replicate slen (0 : UInt32)
  let (combined', _) :=
    BigInt31.zint_rebuild_CRT combined slen n 2 PRIMES_BI true crtTmp
  fs := extractRange combined' 0 (n * slen)
  gs := extractRange combined' (n * slen) (n * slen)

  -- Phase 3: primes slen..tlen-1 — reduce, NTT, compute norms
  for i in [slen:tlen] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let p := pr.p
    let p0i := pr.p0i
    let r2 := pr.R2
    let rx := SmallPrimeNTT.mp_Rx31 slen p p0i r2
    let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i

    let mut t2 : Array UInt32 := Array.replicate n 0
    for j in [:n] do
      t2 := t2.set! j (zint_mod_small_signed fs slen j n p p0i r2 rx)
    t2 := SmallPrimeNTT.mp_NTT logn t2 gm p p0i
    for j in [:hn] do
      fd := fd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul (getU32 t2 (2 * j))
            (getU32 t2 (2 * j + 1)) p p0i) r2 p p0i)

    for j in [:n] do
      t2 := t2.set! j (zint_mod_small_signed gs slen j n p p0i r2 rx)
    t2 := SmallPrimeNTT.mp_NTT logn t2 gm p p0i
    for j in [:hn] do
      gd := gd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul (getU32 t2 (2 * j))
            (getU32 t2 (2 * j + 1)) p p0i) r2 p p0i)

  return fd ++ gd

/-! ## make_fg_intermediate

Compute `(f, g)` at a specified depth by starting from the original
polynomials and applying `depth` field-norm steps. -/

def make_fg_intermediate (logn_top : Nat) (f g : Array Int8)
    (depth : Nat) : Array UInt32 := Id.run do
  let mut buf := make_fg_zero logn_top f g
  for d in [:depth] do
    buf := make_fg_step logn_top d buf
  return buf

/-! ## make_fg_deepest

Compute `(f, g)` at the deepest level (degree 1 = resultants). Also checks
that `f` is invertible modulo the first prime (all NTT coefficients nonzero).
Intermediate `(f, g)` values above the save threshold are stored near the
end of the 6n-word buffer for reuse during the lifting phase.

Returns `(buffer, f_is_invertible)`. -/

def make_fg_deepest (logn_top : Nat) (f g : Array Int8) :
    Array UInt32 × Bool := Id.run do
  let n := 1 <<< logn_top
  let bufSize := 6 * n
  let mut buf := ensureSize (make_fg_zero logn_top f g) bufSize

  -- Invertibility: all NTT coefficients of f must be nonzero (mod p₀)
  let mut b : UInt32 := 0
  for i in [:n] do
    b := b ||| (getU32 buf i - 1)
  let invertible := (b >>> (31 : UInt32)) == 0

  -- Descend through all depths, saving intermediates for the ascent
  let mut savOff := bufSize
  for d in [:logn_top] do
    let result := make_fg_step logn_top d buf
    buf := writeRange buf 0 result
    let d2 := d + 1
    let minSave := MIN_SAVE_FG.getD logn_top 0
    if d2 < logn_top && d2 >= minSave then
      let slen := MAX_BL_SMALL.getD d2 1
      let fglen := slen <<< (logn_top + 1 - d2)
      savOff := savOff - fglen
      let saved := extractRange buf 0 fglen
      buf := writeRange buf savOff saved

  return (buf, invertible)

/-! ## solve_NTRU_deepest

Base case of the NTRU solver. The deepest level reduces to scalar integers:
the resultants `f₀ = Res(f, x^n + 1)` and `g₀ = Res(g, x^n + 1)`.

1. Compute resultants via iterated field norms (`make_fg_deepest`)
2. CRT-reconstruct from RNS to plain big integers
3. Extended binary GCD: `f₀ · G₀ - g₀ · F₀ = 1`
4. Scale: `F₀ ← q · F₀`, `G₀ ← q · G₀`

On success, `F₀` is at `buf[0..len)` and `G₀` at `buf[len..2·len)`. -/

def solve_NTRU_deepest (logn_top : Nat) (f g : Array Int8) :
    Option (Array UInt32) := Id.run do
  let (buf, ok) := make_fg_deepest logn_top f g
  if !ok then return none

  let len := MAX_BL_SMALL.getD logn_top 1

  -- Resultants are at buf[0..2*len) in RNS (n = 1, stride = 1, 2 sets)
  let combined := extractRange buf 0 (2 * len)
  let crtTmp := Array.replicate len (0 : UInt32)
  let (combined', _) :=
    BigInt31.zint_rebuild_CRT combined len 1 2 PRIMES_BI false crtTmp

  let fp := extractRange combined' 0 len
  let gp := extractRange combined' len len

  -- Extended GCD: fp · u - gp · v = 1 ⟹ u = G₀, v = F₀
  let (capG, capF, success) := BigInt31.zint_bezout fp gp len
  if success == 0 then return none

  -- Scale by q to get fp · G₀ - gp · F₀ = q
  let (capF, carryF) := BigInt31.zint_mul_small capF len Q
  if carryF != 0 then return none
  let (capG, carryG) := BigInt31.zint_mul_small capG len Q
  if carryG != 0 then return none

  -- Write F₀, G₀ into the buffer (preserving saved intermediates)
  let mut result := buf
  result := writeRange result 0 capF
  result := writeRange result len capG
  return some result

/-! ## solve_NTRU_intermediate

Lift `(F, G)` from depth `depth + 1` (degree `n/2`) to depth `depth`
(degree `n`).

Given `(F_deep, G_deep)` from the deeper level, compute `(F, G)` at this
level by:

1. **Retrieve (f, g)**: either from saved values in the buffer or by
   recomputing via `make_fg_intermediate`.

2. **Convert to RNS**: Reduce `(F_deep, G_deep)` modulo `llen` small
   primes.

3. **NTT lifting**: For each prime `pᵢ`, compute unreduced `(F, G)`:
   ```
   F[2j]   = g[2j+1] · F_deep[j]
   F[2j+1] = g[2j]   · F_deep[j]
   G[2j]   = f[2j+1] · G_deep[j]
   G[2j+1] = f[2j]   · G_deep[j]
   ```
   with Montgomery correction factors.

4. **CRT reconstruct**: Rebuild unreduced `(F, G)` as plain integers.

5. **Babai reduction** (iterative):
   ```
   k ← round((F·adj(f) + G·adj(g)) / (f·adj(f) + g·adj(g)))
   (F, G) ← (F - k·f, G - k·g)
   ```
   Uses fixed-point (FXR) FFT for the division step, and either
   `poly_sub_scaled` or `poly_sub_scaled_ntt` for the subtraction.
   Iterates until `|F|, |G|` are reduced to the size of `|f|, |g|`.

6. **Verification**: Check `f·G - g·F ≡ q (mod p₀)` in NTT form. -/

def solve_NTRU_intermediate (_logn_top : Nat) (_f _g : Array Int8)
    (_depth : Nat) (_buf : Array UInt32) : Option (Array UInt32) := sorry

/-! ## solve_NTRU_depth0

Specialized top-level solver for depth 0. At this depth all polynomial
coefficients fit in a single 31-bit word, so a single prime modulus
suffices for all modular arithmetic.

1. Load `f, g` into RNS+NTT; load deeper-level `(F, G)` and NTT them.
2. Compute unreduced `(F, G)` at degree `n` via NTT lifting.
3. Compute adjoint products `F·adj(f) + G·adj(g)` and
   `f·adj(f) + g·adj(g)` using NTT, then convert to FFT domain.
4. Divide and round: `k = round(quotient)`, convert `k` to NTT+Montgomery.
5. Subtract: `F ← F - k·f`, `G ← G - k·g` in NTT form.
6. Verify `f·G - g·F ≡ q·R (mod p)` for all NTT slots.
7. Convert back via inverse NTT and normalize. -/

def solve_NTRU_depth0 (_logn : Nat) (_f _g : Array Int8)
    (_buf : Array UInt32) : Option (Array UInt32) := sorry

/-! ## Lifting loop helper -/

/-- Lift `(F, G)` from the deepest level through intermediate depths
`logn - 1` down to depth 1. Returns `none` if any step fails. -/
private def liftIntermediateLevels (logn : Nat) (f g : Array Int8)
    (buf : Array UInt32) : Option (Array UInt32) := Id.run do
  let mut buf := buf
  for d in [1:logn] do
    let depth := logn - d
    match solve_NTRU_intermediate logn f g depth buf with
    | none => return none
    | some buf' => buf := buf'
  return some buf

/-! ## solve_NTRU — Main entry point

Solve the NTRU equation: given `f, g ∈ ℤ[x]/(x^n + 1)` with `n = 2^logn`,
find `F, G` satisfying `f · G - g · F = q`.

The algorithm proceeds in three phases:

1. **Descent + base case**: Iteratively compute field norms to reduce
   `(f, g)` to scalar resultants, then solve the scalar NTRU equation
   `f₀ · G₀ - g₀ · F₀ = q` via extended binary GCD.

2. **Ascent (intermediate)**: Lift `(F, G)` from depth `logn - 1` to
   depth 1. At each level, the degree doubles and Babai's nearest-plane
   reduction keeps `(F, G)` small.

3. **Top level (depth 0)**: Apply the specialized single-prime solver.
   Convert the result from 31-bit limbs to `Int8` representation and
   verify that coefficients are within `[-127, 127]`.

Returns `some (F, G)` on success, or `none` on failure. -/

def solve_NTRU (logn : Nat) (f g : Array Int8) :
    Option (Array Int8 × Array Int8) := do
  let n := 1 <<< logn
  let buf ← solve_NTRU_deepest logn f g
  let buf ← liftIntermediateLevels logn f g buf
  let buf ← solve_NTRU_depth0 logn f g buf
  let capF ← poly_big_to_small logn buf 0 127
  let capG ← poly_big_to_small logn buf n 127
  pure (capF, capG)

/-! ## check_ortho_norm

Verify that the Gram-Schmidt norm `‖b̃₁‖²` of the NTRU lattice basis
`B = [[g, -f], [G, -F]]` is below the Falcon acceptance threshold.

The second Gram-Schmidt vector satisfies (in FFT representation):
```
b̃₁ = q · [adj(f), adj(g)] / (f · adj(f) + g · adj(g))
```

Its squared norm is computed and compared against the threshold constant
`72251709809335` (a 32.32 fixed-point value from Section 3.8.2 of the
Falcon specification). -/

def check_ortho_norm (logn : Nat) (f g : Array Int8) : Bool := Id.run do
  let n := 1 <<< logn
  let mut rt1 := vect_FFT logn (vect_set logn f)
  let mut rt2 := vect_FFT logn (vect_set logn g)
  let rt3 := vect_invnorm_fft logn rt1 rt2 0
  rt1 := vect_adj_fft logn rt1
  rt2 := vect_adj_fft logn rt2
  rt1 := vect_mul_realconst logn rt1 (FXR.ofInt 12289)
  rt2 := vect_mul_realconst logn rt2 (FXR.ofInt 12289)
  rt1 := vect_mul_selfadj_fft logn rt1 rt3
  rt2 := vect_mul_selfadj_fft logn rt2 rt3
  rt1 := vect_iFFT logn rt1
  rt2 := vect_iFFT logn rt2
  let mut sn : FXR := FXR.zero
  for i in [:n] do
    sn := FXR.add sn
      (FXR.add (FXR.sqr (rt1.getD i 0)) (FXR.sqr (rt2.getD i 0)))
  return FXR.lt sn (FXR.ofScaled32 72251709809335)

end Falcon.Concrete.NTRUSolver
