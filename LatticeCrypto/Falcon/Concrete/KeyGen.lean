/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.Falcon.Concrete.NTRUSolver
import LatticeCrypto.Falcon.Concrete.FFT
import LatticeCrypto.Falcon.Concrete.NTT
import LatticeCrypto.Falcon.Concrete.SamplerZ

/-!
# Concrete Falcon Key Generation

NTRU polynomial generation and full Falcon key pair construction,
ported from Pornin's `c-fn-dsa` (`kgen.c`, `kgen_gauss.c`, `mq.c`).

## Overview

1. **Gaussian CDT sampling** (`sample_f`): Sample short polynomials `f, g`
   from a discrete Gaussian distribution using cumulative distribution tables.
   The tables are parameter-specific: `gauss_256` for small degrees,
   `gauss_512` for `n = 512`, and `gauss_1024` for `n = 1024`.

2. **Invertibility check** (`isInvertibleModQ`): Verify that `f` is invertible
   in `ℤ_q[x]/(x^n + 1)` by checking that all NTT coefficients are nonzero.

3. **Public key computation** (`computeH`): Compute `h = g · f⁻¹ mod q`
   using NTT-domain pointwise division.

4. **NTRU generation** (`ntruGen`): Loop: sample `(f, g)`, verify invertibility,
   verify norm bound, return valid pair.

5. **Key generation** (`keyGen`): Orchestrate `ntruGen`, NTRU equation solving
   (`solve_NTRU`), orthogonalized norm check, public key computation, and
   Gram matrix construction for the signing tree.

## References

- c-fn-dsa: `kgen.c`, `kgen_gauss.c`, `mq.c`
- Pornin 2025 (eprint 2025/1239)
- Falcon specification v1.2, Algorithms 4–9
-/


namespace Falcon.Concrete.KeyGen

open Falcon.Concrete.SamplerZ
open Falcon.Concrete.FFTOps
open Falcon.Concrete.FPR

/-! ## PRNG helper: 16-bit extraction -/

def PRNGState.nextU16 (s : PRNGState) : UInt32 × PRNGState :=
  let (b0, s') := s.nextByte
  let (b1, s'') := s'.nextByte
  (b0.toUInt32 ||| (b1.toUInt32 <<< 8), s'')

/-! ## Gaussian CDT tables

Cumulative distribution tables for sampling short polynomial coefficients.
Each table entry is a threshold: a random 16-bit value is compared against
all entries to determine the sample magnitude. The tables define symmetric
distributions centered at 0.

Port of `gauss_256`, `gauss_512`, `gauss_1024` from `kgen_gauss.c`. -/

private def gauss256 : Array UInt32 := #[
      1,     3,     6,    11,    22,    40,    73,   129,
    222,   371,   602,   950,  1460,  2183,  3179,  4509,
   6231,  8395, 11032, 14150, 17726, 21703, 25995, 30487,
  35048, 39540, 43832, 47809, 51385, 54503, 57140, 59304,
  61026, 62356, 63352, 64075, 64585, 64933, 65164, 65313,
  65406, 65462, 65495, 65513, 65524, 65529, 65532, 65534
]

private def gauss512 : Array UInt32 := #[
      1,     4,    11,    28,    65,   146,   308,   615,
   1164,  2083,  3535,  5692,  8706, 12669, 17574, 23285,
  29542, 35993, 42250, 47961, 52866, 56829, 59843, 62000,
  63452, 64371, 64920, 65227, 65389, 65470, 65507, 65524,
  65531, 65534
]

private def gauss1024 : Array UInt32 := #[
      2,     8,    28,    94,   280,   742,  1761,  3753,
   7197, 12472, 19623, 28206, 37329, 45912, 53063, 58338,
  61782, 63774, 64793, 65255, 65441, 65507, 65527, 65533
]

private structure GaussParams where
  tab : Array UInt32
  tabLen : Nat
  zz : Nat

private def getGaussParams? (logn : Nat) : Option GaussParams :=
  match logn with
  | 9  => some ⟨gauss512, 34, 1⟩
  | 10 => some ⟨gauss1024, 24, 1⟩
  | _  =>
    if logn ≤ 8 then
      some ⟨gauss256, 48, 1 <<< (8 - logn)⟩
    else
      none

/-! ## Gaussian CDT coefficient sampling

For each coefficient, we draw a random 16-bit value `y` and count how many
CDT entries are strictly less than `y`. The count is centered by subtracting
`tabLen / 2`, giving a sample from the discrete Gaussian.

For `logn < 8`, multiple CDT samples are summed (`zz > 1`) to increase
the variance to match the target distribution for degree-256 parameters. -/

private def sampleOneCoeff (gp : GaussParams) (state : PRNGState) :
    Int32 × UInt32 × PRNGState := Id.run do
  let kmax : UInt32 := (gp.tabLen >>> 1).toUInt32 <<< 16
  let mut v : UInt32 := 0
  let mut st := state
  for _ in [0:gp.zz] do
    let (y, st') := PRNGState.nextU16 st
    st := st'
    v := v - kmax
    for k in [0:gp.tabLen] do
      let entry := gp.tab.getD k 0
      v := v - ((entry - y) &&& ~~~(0xFFFF : UInt32))
  let top := v >>> 16
  let s : Int32 :=
    if top.toNat < 32768 then top.toInt32
    else top.toInt32 - (65536 : Int32)
  (s, v, st)

/-- Sample a short polynomial from the discrete Gaussian distribution.
Coefficients are sampled via the CDT method, and the polynomial is
rejected unless it has odd parity (the sum of coefficients is odd).

Port of `sample_f` from `kgen_gauss.c`. -/
def sample_f (logn : Nat) (prng : PRNGState) : Array Int8 × PRNGState := Id.run do
  let some gp := getGaussParams? logn
    | panic! s!"Falcon keygen does not support logn={logn}"
  let n := 1 <<< logn
  let mut state := prng
  for _ in [0:10000] do
    let mut f : Array Int8 := Array.mkEmpty n
    let mut parity : UInt32 := 0
    let mut i := 0
    while i < n do
      let (s, v, st') := sampleOneCoeff gp state
      state := st'
      if s < (-127 : Int32) || s > (127 : Int32) then
        continue
      f := f.push s.toInt8
      parity := parity ^^^ v
      i := i + 1
    if ((parity >>> 16) &&& 1) != 0 then
      return (f, state)
  return (Array.replicate n (0 : Int8), state)

/-! ## Type conversions between Int8 arrays and NTT-domain types

The abstract NTT from `NTT.lean` operates on `Rq (2^logn) = Vector (ZMod 12289) (2^logn)`.
These helpers convert between the concrete `Array Int8` representation used by the
Gaussian sampler and the abstract polynomial types. -/

private def int8ToInt (x : Int8) : Int :=
  let n := x.toUInt8.toNat
  if n < 128 then (n : Int) else (n : Int) - 256

private def int8ToCoeff (x : Int8) : Falcon.Coeff :=
  (int8ToInt x : Falcon.Coeff)

private def int8ArrayToRq (logn : Nat) (f : Array Int8) : Falcon.Rq (2 ^ logn) :=
  Vector.ofFn fun ⟨i, _⟩ => int8ToCoeff (f.getD i 0)

private def coeffToUInt16 (x : Falcon.Coeff) : UInt16 :=
  x.val.toUInt32.toUInt16

private def rqToUInt16Array (logn : Nat) (p : Falcon.Rq (2 ^ logn)) : Array UInt16 :=
  (Array.range (2 ^ logn)).map fun i => coeffToUInt16 (p.getD i 0)

/-- Modular inverse via Fermat's little theorem: `x⁻¹ = x^(q-2) mod q`.
Valid because `q = 12289` is prime. Returns 0 for input 0. -/
private def coeffInv (x : Falcon.Coeff) : Falcon.Coeff :=
  x ^ (Falcon.modulus - 2)

/-! ## NTT-based invertibility check

A polynomial `f` is invertible in `ℤ_q[x]/(x^n + 1)` if and only if all its
NTT coefficients are nonzero. This is checked by performing a forward NTT and
testing each coefficient.

Port of `mqpoly_is_invertible` from `mq.c`. -/

/-- Check whether a small polynomial `f` (given as `Array Int8`) is invertible
mod `q = 12289` in the ring `ℤ_q[x]/(x^n + 1)` with `n = 2^logn`. -/
def isInvertibleModQ (logn : Nat) (f : Array Int8) : Bool := Id.run do
  let fRq := int8ArrayToRq logn f
  let fHat := Falcon.Concrete.ntt logn fRq
  let mut allNonzero := true
  for i in [0:2 ^ logn] do
    if fHat.coeffs.getD i 0 = 0 then
      allNonzero := false
      break
  return allNonzero

/-! ## Public key computation: h = g / f mod q

Compute the public key polynomial `h = g · f⁻¹` in the NTT domain, then
convert back to coefficient representation. Returns `none` if `f` is not
invertible (some NTT coefficient is zero).

Port of `mqpoly_div_small` from `mq.c`. -/

/-- Compute `h = g · f⁻¹ mod q` in `ℤ_q[x]/(x^n + 1)`, returning the
result as an array of `UInt16` values in `[0, q)`. Returns `none` if `f`
is not invertible. -/
def computeH (logn : Nat) (f g : Array Int8) : Option (Array UInt16) := Id.run do
  let fRq := int8ArrayToRq logn f
  let gRq := int8ArrayToRq logn g
  let fHat := Falcon.Concrete.ntt logn fRq
  let gHat := Falcon.Concrete.ntt logn gRq
  let n := 2 ^ logn
  let mut hHat : Array Falcon.Coeff := Array.replicate n 0
  for i in [0:n] do
    let fi := fHat.coeffs.getD i 0
    if fi = 0 then return none
    let gi := gHat.coeffs.getD i 0
    hHat := hHat.set! i (gi * coeffInv fi)
  let hHatTq : Falcon.Tq n := ⟨Vector.ofFn fun ⟨i, _⟩ => hHat.getD i 0⟩
  let hRq := Falcon.Concrete.invNTT logn hHatTq
  return some (rqToUInt16Array logn hRq)

/-! ## Squared norm bound

The Falcon specification requires `‖(g, -f)‖² < 1.17² · q ≈ 16822.4`.
We use the integer threshold `16823` (following the C reference). -/

private def SQ_NORM_BOUND : Int32 := 16823

/-- Compute `‖f‖² + ‖g‖² = Σᵢ (fᵢ² + gᵢ²)` for short polynomials. -/
def sqNorm (f g : Array Int8) (n : Nat) : Int32 := Id.run do
  let mut sn : Int32 := 0
  for i in [0:n] do
    let xf : Int32 := (f.getD i 0).toInt32
    let xg : Int32 := (g.getD i 0).toInt32
    sn := sn + xf * xf + xg * xg
  return sn

/-! ## NTRU polynomial generation

Sample `(f, g)` from the discrete Gaussian, then validate:
1. Squared norm bound: `‖(g, -f)‖² < 16823`
2. Invertibility: `f` is invertible mod `q`
3. (Optionally) `g` invertibility is not required by the spec but
   helps catch degenerate cases.

The loop retries until a valid pair is found.

Port of the inner loop of `keygen_inner` from `kgen.c`. -/

/-- Generate a valid NTRU polynomial pair `(f, g)` by repeated Gaussian
sampling with validation. Returns `none` if the retry budget is exhausted. -/
def ntruGen (logn : Nat) (prng : PRNGState) :
    Option (Array Int8 × Array Int8) × PRNGState := Id.run do
  let n := 1 <<< logn
  let mut state := prng
  for _ in [0:10000] do
    let (f, st1) := sample_f logn state
    let (g, st2) := sample_f logn st1
    state := st2
    if sqNorm f g n >= SQ_NORM_BOUND then continue
    if !isInvertibleModQ logn f then continue
    return (some (f, g), state)
  return (none, state)

/-! ## Raw key pair structure -/

/-- A raw Falcon key pair containing all components needed for signing.

- `f, g`: Short secret polynomials sampled from the discrete Gaussian.
- `capF, capG`: Solution to the NTRU equation `f·G - g·F = q`.
- `h`: Public key `h = g·f⁻¹ mod q` in external representation.
- `gramData`: Precomputed Gram matrix of the NTRU basis in FPR format,
  used as input to `ffSampling` during signing. Stored as a flat
  `UInt64` buffer encoding the LDL tree. -/
structure RawKeyPair where
  f : Array Int8
  g : Array Int8
  capF : Array Int8
  capG : Array Int8
  h : Array UInt16
  gramData : Array UInt64

/-! ## Gram matrix computation

Build the Gram matrix of the NTRU basis `B = [[g, -f], [G, -F]]` in the
FFT domain, then flatten it into a `UInt64` buffer for `ffSampling`.

The basis vectors in FFT domain are:
- Row 0: `(g, -f)` → `b00 = FFT(g)`, `b01 = FFT(-f)`
- Row 1: `(G, -F)` → `b10 = FFT(G)`, `b11 = FFT(-F)`

The Gram matrix `G = B · B*` has entries:
- `g00 = b00·adj(b00) + b01·adj(b01)` (self-adjoint)
- `g01 = b00·adj(b10) + b01·adj(b11)` (complex)
- `g11 = b10·adj(b10) + b11·adj(b11)` (self-adjoint)

These are computed by `fpolyGramFFT` from `FFT.lean`.
-/

private def int8ToInt32 (x : Int8) : Int32 := x.toInt32

/-- Convert an `Array Int8` to `Array Int32` for the FFT pipeline. -/
private def int8ArrayToInt32 (f : Array Int8) : Array Int32 :=
  f.map int8ToInt32

/-- Compute the Gram matrix data for the Falcon signing tree.
Takes the NTRU basis polynomials `(f, g, F, G)` and returns the
flattened Gram matrix entries `(g00, g01, g11)` as `Array UInt64`. -/
def computeGramData (logn : Nat) (f g capF capG : Array Int8) :
    Array UInt64 := Id.run do
  let b00 := fpolyFFT (F := FPR) logn
    (fpolySetSmall (F := FPR) logn (int8ArrayToInt32 g))
  let b01 := fpolyFFT (F := FPR) logn
    (fpolyNeg (F := FPR) logn (fpolySetSmall (F := FPR) logn (int8ArrayToInt32 f)))
  let b10 := fpolyFFT (F := FPR) logn
    (fpolySetSmall (F := FPR) logn (int8ArrayToInt32 capG))
  let b11 := fpolyFFT (F := FPR) logn
    (fpolyNeg (F := FPR) logn (fpolySetSmall (F := FPR) logn (int8ArrayToInt32 capF)))
  let (g00, g01, g11) := fpolyGramFFT (F := FPR) logn b00 b01 b10 b11
  return g00 ++ g01 ++ g11

/-! ## Full key generation -/

/-- Generate a complete Falcon key pair from a seed.

1. Initialize PRNG from `seed`.
2. Loop:
   - Sample `(f, g)` via `ntruGen` (Gaussian CDT + validation).
   - Check orthogonalized norm of the NTRU basis.
   - Solve the NTRU equation for `(F, G)`.
   - Compute public key `h = g · f⁻¹ mod q`.
   - Compute Gram matrix data for the signing tree.
3. Return the `RawKeyPair`.

Returns `none` if key generation fails (exhausts retry budget). -/
def keyGen (logn : Nat) (seed : ByteArray) : Option RawKeyPair := Id.run do
  let mut state := PRNGState.init seed
  for _ in [0:100] do
    let (fg?, st1) := ntruGen logn state
    state := st1
    let some (f, g) := fg? | continue
    if !NTRUSolver.check_ortho_norm logn f g then continue
    match NTRUSolver.solve_NTRU logn f g with
    | none => continue
    | some (capF, capG) =>
      match computeH logn f g with
      | none => continue
      | some h =>
        let gramData := computeGramData logn f g capF capG
        return some {
          f := f
          g := g
          capF := capF
          capG := capG
          h := h
          gramData := gramData
        }
  return none

end Falcon.Concrete.KeyGen
