/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Ring

/-!
# Concrete NTT for ML-KEM

Pure-Lean executable implementation of FIPS 203 Algorithms 9–11 (NTT, NTT⁻¹, MultiplyNTTs)
specialised to `q = 3329`, `n = 256`, `ζ = 17`.

## Coefficient ordering in `MultiplyNTTs`

FIPS 203 Section 4.3 defines `γᵢ = ζ^(2 · BitRev₇(i) + 1)` for `i = 0, …, 127` and
Algorithm 11 assigns twiddle factors to coefficient pairs as:

    pair (2i, 2i+1)       → γ_{2i}       for i = 0, …, 63
    pair (2(i+64), 2(i+64)+1) → −γ_{2i}

This places all positive-gamma pairs in positions 0–127 and all negated pairs in 128–255.

However, Algorithm 9 (the Cooley-Tukey NTT) produces output in a **different physical
ordering**. At the last butterfly layer (`len = 2`), each group `g` of 4 coefficients
uses `zetaArray[64 + g]`, giving:

    pair (4g, 4g+1)   → +zetaArray[64 + g]
    pair (4g+2, 4g+3) → −zetaArray[64 + g]

Positive and negative pairs are **interleaved in groups of 4**, not segregated into halves.
Concretely, the pair at positions `(2, 3)` gets `γ₁ = ζ^129 = −ζ` (matching the NTT
butterfly), whereas Algorithm 11's indexing would assign `γ₂ = ζ^65` to that position.

Both orderings describe the same 128 quotient rings `ℤ_q[X]/(X² − γᵢ)`; they differ
only in which physical array positions are mapped to which ring. This implementation follows
the butterfly-natural ordering produced by Algorithm 9, matching the
[pqcrystals reference](https://github.com/pq-crystals/kyber/blob/main/ref/poly.c)
and [mlkem-native](https://github.com/pq-code-package/mlkem-native). Correctness is
verified byte-for-byte against mlkem-native for multiple key pairs, encapsulations, and
decapsulations (see `MLKEMTest.lean`).
-/

set_option autoImplicit false

namespace MLKEM.Concrete

open MLKEM

/-! ## Bit reversal and zeta table -/

/-- Reverse the low 7 bits of `i`. -/
def bitRev7 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 6) ||| (b 1 <<< 5) ||| (b 2 <<< 4) ||| (b 3 <<< 3) |||
  (b 4 <<< 2) ||| (b 5 <<< 1) ||| b 6

/-- Precomputed twiddle factors `ζ^{BitRev₇(i)}` for `i = 0 … 127`. -/
def zetaArray : Array Coeff :=
  (Array.range 128).map fun i => zeta ^ bitRev7 i

/-- `128⁻¹ mod 3329 = 3303`. Applied after the inverse NTT. -/
private def nInv : Coeff := 3303

/-- Safe array access with fallback to zero. -/
private def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

/-! ## Forward NTT (Algorithm 9) -/

private def nttLayer (a : Array Coeff) (len : Nat) (k : Nat) : Array Coeff × Nat := Id.run do
  let mut arr := a
  let mut ki := k
  let numGroups := 256 / (2 * len)
  for s in [0:numGroups] do
    let start := s * 2 * len
    let z := getZ zetaArray ki
    ki := ki + 1
    for jj in [0:len] do
      let j := start + jj
      let t := z * getZ arr (j + len)
      let fj := getZ arr j
      arr := arr.set! (j + len) (fj - t)
      arr := arr.set! j (fj + t)
  return (arr, ki)

/-- FIPS 203 Algorithm 9: Number-Theoretic Transform. -/
def ntt (f : Rq) : Tq :=
  let (a, _) := [128, 64, 32, 16, 8, 4, 2].foldl
    (fun (a, k) len => nttLayer a len k) (f.toArray, 1)
  Vector.ofFn fun i => getZ a i.val

/-! ## Inverse NTT (Algorithm 10) -/

private def invNttLayer (a : Array Coeff) (len : Nat) (k : Nat) :
    Array Coeff × Nat := Id.run do
  let mut arr := a
  let mut ki := k
  let numGroups := 256 / (2 * len)
  for s in [0:numGroups] do
    let start := s * 2 * len
    let z := getZ zetaArray ki
    ki := ki - 1
    for jj in [0:len] do
      let j := start + jj
      let t := getZ arr j
      let u := getZ arr (j + len)
      arr := arr.set! j (t + u)
      arr := arr.set! (j + len) (z * (u - t))
  return (arr, ki)

/-- FIPS 203 Algorithm 10: Inverse Number-Theoretic Transform. -/
def invNTT (fHat : Tq) : Rq :=
  let (a, _) := [2, 4, 8, 16, 32, 64, 128].foldl
    (fun (a, k) len => invNttLayer a len k) (fHat.toArray, 127)
  Vector.ofFn fun i => nInv * getZ a i.val

/-! ## Base-case multiplication and MultiplyNTTs (Algorithm 11) -/

/-- FIPS 203 Algorithm 11 (MultiplyNTTs), using the butterfly-natural coefficient ordering
    from Algorithm 9 rather than Algorithm 11's stated indexing convention (see module
    docstring for details). Within each group `g` of 4 coefficients, the pair at `(4g, 4g+1)`
    uses twiddle factor `zetaArray[64+g]` and the pair at `(4g+2, 4g+3)` uses its negation. -/
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  let fa := fHat.toArray
  let ga := gHat.toArray
  Vector.ofFn fun idx =>
    let pos := idx.val
    let group := pos / 4
    let z := getZ zetaArray (64 + group)
    let gamma := if (pos / 2) % 2 == 0 then z else -z
    let base := (pos / 2) * 2
    let a0 := getZ fa base
    let a1 := getZ fa (base + 1)
    let b0 := getZ ga base
    let b1 := getZ ga (base + 1)
    if pos % 2 == 0 then
      a0 * b0 + a1 * b1 * gamma
    else
      a0 * b1 + a1 * b0

/-- Concrete `NTTRingOps` instance for ML-KEM. -/
def concreteNTTRingOps : NTTRingOps where
  ntt := ntt
  invNTT := invNTT
  multiplyNTTs := multiplyNTTs

end MLKEM.Concrete
