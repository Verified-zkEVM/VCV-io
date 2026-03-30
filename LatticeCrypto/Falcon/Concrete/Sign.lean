/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FFT
import LatticeCrypto.Falcon.Concrete.Sampling
import LatticeCrypto.Falcon.Concrete.Encoding
import LatticeCrypto.Falcon.Concrete.NTT
import LatticeCrypto.Falcon.Params

/-!
# Falcon Signing Core

Port of c-fn-dsa's `sign_core.c` and `sign.c`: the Falcon signature generation pipeline,
generic over `FloatLike F`.

## Pipeline

1. **Basis construction** (`basisToFFT`): convert `(f, g, F, G)` to the lattice basis
   `B = [[g, -f], [G, -F]]` in FFT domain.
2. **Gram matrix** (`fpolyGramFFT`): compute `G = B · adj(B)` for the LDL tree.
3. **Hash-to-point**: SHAKE-256 rejection sampling to obtain `c ∈ R_q`.
4. **Target vector** (`fpolyApplyBasis`): compute `(t₀, t₁) = (1/q) · B · [0, c]`.
5. **ffSampling**: discrete Gaussian sampling in the FFT tree to obtain lattice point `z`.
6. **Signature extraction**: `s₁ = c - (g·z₀ + G·z₁)`, `s₂ = f·z₀ + F·z₁`.
7. **Norm check**: accept iff `‖(s₁, s₂)‖² ≤ β²`.
8. **Compression**: Golomb-Rice encoding of `s₂`.

## References

- c-fn-dsa: `sign_core.c`, `sign.c`
- Falcon specification v1.2, Section 3.8 (Sign algorithm)
- FIPS 206 (FN-DSA) draft
-/

set_option autoImplicit false

namespace Falcon.Concrete.Sign

open Falcon
open Falcon.Concrete
open Falcon.Concrete.FFTOps
open Falcon.Concrete.SamplerZ

/-! ## Constants -/

/-- Squared norm bound `β²` by `logn`. Falcon-512 (`logn = 9`) and Falcon-1024 (`logn = 10`)
are the approved production parameter sets; smaller values are for testing. -/
def betaSquaredForLogn (logn : Nat) : Nat :=
  match logn with
  | 2  => 101498
  | 3  => 208714
  | 4  => 428865
  | 5  => 892039
  | 6  => 1852696
  | 7  => 3842630
  | 8  => 7959734
  | 9  => 34034726
  | 10 => 70265242
  | _  => 0

/-- Compressed signature data length (bytes) by `logn`. -/
def sbytelenForLogn (logn : Nat) : Nat :=
  match logn with
  | 2  => 44
  | 3  => 47
  | 4  => 52
  | 5  => 63
  | 6  => 82
  | 7  => 122
  | 8  => 200
  | 9  => 625
  | 10 => 1239
  | _  => 0

/-! ## PRNG helpers -/

/-- Generate `len` random bytes from the PRNG state. -/
def prngNextBytes (s : PRNGState) (len : Nat) : ByteArray × PRNGState := Id.run do
  let mut st := s
  let mut bytes := ByteArray.empty
  for _ in [0:len] do
    let (b, s') := st.nextByte
    bytes := bytes.push b
    st := s'
  return (bytes, st)

/-- Generate a 40-byte salt (nonce) from the PRNG state. -/
def prngNextSalt (s : PRNGState) : Bytes 40 × PRNGState := Id.run do
  let mut st := s
  let mut bytes : Array UInt8 := Array.mkEmpty 40
  for _ in [0:40] do
    let (b, s') := st.nextByte
    bytes := bytes.push b
    st := s'
  return (Vector.ofFn fun ⟨i, _⟩ => bytes.getD i 0, st)

/-! ## Type conversions -/

/-- Sign-extend an `Int8` to `Int32`. -/
private def int8ToInt32 (x : Int8) : Int32 :=
  let u32 : UInt32 := x.toUInt8.toUInt32
  if u32 < 128 then u32.toInt32
  else (u32 ||| 0xFFFFFF00).toInt32

/-- Convert an array of `Int8` to `Int32` (sign-extending). -/
def int8ArrayToInt32 (a : Array Int8) : Array Int32 :=
  a.map int8ToInt32

/-- Convert `Rq n` (coefficients mod q) to `Array UInt16`. -/
def rqToUInt16Array {n : ℕ} (h : Rq n) : Array UInt16 :=
  h.toArray.map fun c => c.val.toUInt32.toUInt16

/-- Convert a signed `Int64` to `Int` for squared norm computation. -/
@[inline] private def int64ToInt (x : Int64) : Int :=
  let v := x.toUInt64.toNat
  if v ≥ 9223372036854775808 then (v : Int) - 18446744073709551616 else ↑v

/-! ## Generic over FloatLike F -/

section Generic

variable {F : Type} [FloatLike F]

instance : Inhabited F := ⟨FloatLike.zero⟩

/-! ### Basis construction in FFT domain -/

/-- Build the lattice basis `B = [[g, -f], [G, -F]]` in FFT domain.
Returns `(b₀₀, b₀₁, b₁₀, b₁₁)` where:
- `b₀₀ = FFT(g)`, `b₀₁ = -FFT(f)` (first row)
- `b₁₀ = FFT(G)`, `b₁₁ = -FFT(F)` (second row) -/
def basisToFFT (logn : Nat) (f g capF capG : Array Int32) :
    Array F × Array F × Array F × Array F :=
  let b00 := fpolyFFT logn (fpolySetSmall (F := F) logn g)
  let b01 := fpolyNeg logn (fpolyFFT logn (fpolySetSmall (F := F) logn f))
  let b10 := fpolyFFT logn (fpolySetSmall (F := F) logn capG)
  let b11 := fpolyNeg logn (fpolyFFT logn (fpolySetSmall (F := F) logn capF))
  (b00, b01, b10, b11)

/-! ### Gram matrix packing -/

/-- Extract the self-adjoint (real-only, half-size) representation from a Gram diagonal.
Self-adjoint FFT polynomials have zero imaginary parts; only the first `n/2` entries are stored.
Matches the C reference's compact layout for `g₀₀` and `g₁₁`. -/
def selfAdjointCompress (logn : Nat) (g : Array F) : Array F :=
  let hn := 1 <<< (logn - 1)
  (Array.range hn).map fun i => g.getD i FloatLike.zero

/-- Pack the target vector `(t₀, t₁)` and Gram matrix data `(g₀₁, g₀₀, g₁₁)` into the
flat buffer layout expected by `ffSampling`.

Layout (in units of `qn = n/4`):
- `[0, 4qn)` = `t₀`, `[4qn, 8qn)` = `t₁`
- `[8qn, 12qn)` = `g₀₁` (full), `[12qn, 14qn)` = `g₀₀` (half), `[14qn, 16qn)` = `g₁₁` (half)
- `[16qn, 28qn)` = working space for recursive LDL decomposition -/
def packFFSampBuffer (logn : Nat) (t0 t1 g01 g00sa g11sa : Array F) : Array F := Id.run do
  let n := 1 <<< logn
  let hn := n >>> 1
  let fz : F := FloatLike.zero
  let mut buf : Array F := Array.replicate (7 * n) fz
  for i in [0:n] do
    buf := buf.set! i (t0.getD i fz)
  for i in [0:n] do
    buf := buf.set! (n + i) (t1.getD i fz)
  for i in [0:n] do
    buf := buf.set! (2 * n + i) (g01.getD i fz)
  for i in [0:hn] do
    buf := buf.set! (3 * n + i) (g00sa.getD i fz)
  for i in [0:hn] do
    buf := buf.set! (3 * n + hn + i) (g11sa.getD i fz)
  return buf

/-! ### Post-sampling: lattice point and signature extraction -/

/-- Apply the lattice basis to the sampled FFT vector `(z₀, z₁)` to obtain the
time-domain lattice point `(v₀, v₁)`:
- `v₀ = IFFT(b₀₀ · z₀ + b₁₀ · z₁)` = `g · z₀ + G · z₁`
- `v₁ = IFFT(b₀₁ · z₀ + b₁₁ · z₁)` = `-(f · z₀ + F · z₁)` -/
def applyBasisToSampled (logn : Nat) (z0fft z1fft : Array F)
    (b00 b01 b10 b11 : Array F) : Array F × Array F :=
  let v0fft := fpolyAdd logn (fpolyMulFFT logn b00 z0fft) (fpolyMulFFT logn b10 z1fft)
  let v1fft := fpolyAdd logn (fpolyMulFFT logn b01 z0fft) (fpolyMulFFT logn b11 z1fft)
  (fpolyIFFT logn v0fft, fpolyIFFT logn v1fft)

/-- Compute signature polynomials from the hash point `hm` and lattice point `(v₀, v₁)`:
- `s₁[i] = hm[i] - round(v₀[i])`
- `s₂[i] = -round(v₁[i])` = `round(f · z₀ + F · z₁)[i]`

Returns `(‖(s₁, s₂)‖², s₂)`. -/
def computeSignature (logn : Nat) (hm : Array UInt16) (v0 v1 : Array F) :
    Nat × Array ℤ := Id.run do
  let n := 1 <<< logn
  let fz : F := FloatLike.zero
  let mut sqn : UInt64 := 0
  let mut s2arr : Array ℤ := Array.replicate n 0
  for i in [0:n] do
    let v0i := FloatLike.rint (v0.getD i fz)
    let s1 : Int64 := (hm.getD i 0).toUInt32.toUInt64.toInt64 - v0i
    sqn := sqn + (s1 * s1).toUInt64
  for i in [0:n] do
    let v1i := FloatLike.rint (v1.getD i fz)
    let s2i : Int64 := (0 : Int64) - v1i
    sqn := sqn + (s2i * s2i).toUInt64
    s2arr := s2arr.set! i (int64ToInt s2i)
  return (sqn.toNat, s2arr)

/-! ### Single signing attempt -/

/-- A single signing attempt. Builds the FFT-domain basis, computes the Gram matrix,
derives the target vector from the hash point, runs `ffSampling`, applies the basis to the
sampled vector, and checks the squared norm.

Returns `some s₂` if the norm `‖(s₁, s₂)‖² ≤ β²`, or `none` to signal retry. -/
def signAttempt (logn : Nat) (f g capF capG : Array Int32)
    (hm : Array UInt16) (prng : PRNGState) :
    Option (Array ℤ) × PRNGState := Id.run do
  let n := 1 <<< logn
  let (b00, b01, b10, b11) := basisToFFT (F := F) logn f g capF capG
  let (g00, g01, g11) := fpolyGramFFT logn b00 b01 b10 b11
  let g00sa := selfAdjointCompress logn g00
  let g11sa := selfAdjointCompress logn g11
  let (t0, t1) := fpolyApplyBasis logn b01 b11 hm
  let buf := packFFSampBuffer logn t0 t1 g01 g00sa g11sa
  let (buf', prng') := ffSampling logn prng buf
  let z0fft : Array F := (Array.range n).map fun i => buf'.getD i FloatLike.zero
  let z1fft : Array F := (Array.range n).map fun i => buf'.getD (n + i) FloatLike.zero
  let (v0, v1) := applyBasisToSampled logn z0fft z1fft b00 b01 b10 b11
  let (sqn, s2) := computeSignature logn hm v0 v1
  if sqn ≤ betaSquaredForLogn logn then
    return (some s2, prng')
  else
    return (none, prng')

/-! ### Full signing function -/

/-- Full Falcon signing. On each iteration: generate a fresh salt and sampler seed, hash
the message to a polynomial in `R_q`, attempt signing, and compress/encode on success.
Retries up to 1000 times (expected: ~1–2 iterations for production parameters).

Takes the secret key polynomials as `Array Int32`; use `int8ArrayToInt32` to convert from
`Array Int8`. Returns the encoded signature: `header(1) ‖ salt(40) ‖ compressed_s₂`. -/
def concreteSign (logn : Nat) (f g capF capG : Array Int32)
    (pk : ByteArray) (msg : List Byte) (seed : ByteArray) : Option ByteArray := Id.run do
  let n := 1 <<< logn
  let dlen := sbytelenForLogn logn
  if dlen == 0 then return none
  let mut masterPRNG := PRNGState.init seed
  for _ in [0:1000] do
    let (salt, prng1) := prngNextSalt masterPRNG
    let (subSeedBA, prng2) := prngNextBytes prng1 56
    masterPRNG := prng2
    let samplerPRNG := PRNGState.init subSeedBA
    let hm := hashToPoint n salt pk msg
    let hmArr := rqToUInt16Array hm
    let (result, _) := signAttempt (F := F) logn f g capF capG hmArr samplerPRNG
    if let some s2 := result then
      let s2Poly : IntPoly n := Vector.ofFn fun ⟨i, _⟩ => s2.getD i 0
      if let some compSig := compress n s2Poly dlen then
        return some (sigEncode salt compSig logn)
  return none

end Generic

end Falcon.Concrete.Sign
