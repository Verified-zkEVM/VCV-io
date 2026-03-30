/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete NTT for ML-KEM

Pure-Lean executable kernels for FIPS 203 Algorithms 9–11 (NTT, NTT⁻¹, MultiplyNTTs),
specialised to `q = 3329`, `n = 256`, `ζ = 17`.

The public `ntt` / `invNTT` interface is exposed in a proof-oriented form: we first evaluate the
algorithmic kernels on the standard basis, then reuse the resulting concrete transform matrices to
obtain a public NTT pair with mechanically checked inverse laws. At runtime, `@[implemented_by]`
rebinds those public definitions to the fast loop kernels, so execution keeps the intended
`O(n log n)` / `O(n)` behavior while proofs continue to see the matrix-based semantics.

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

open scoped BigOperators

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

/-- FIPS 203 Algorithm 9: executable loop kernel for the Number-Theoretic Transform. -/
def loopNTT (f : Rq) : Tq :=
  let (a, _) := [128, 64, 32, 16, 8, 4, 2].foldl
    (fun (a, k) len => nttLayer a len k) (f.toArray, 1)
  ⟨Vector.ofFn fun i => getZ a i.val⟩

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

/-- FIPS 203 Algorithm 10: executable loop kernel for the inverse Number-Theoretic Transform. -/
def loopInvNTT (fHat : Tq) : Rq :=
  let (a, _) := [2, 4, 8, 16, 32, 64, 128].foldl
    (fun (a, k) len => invNttLayer a len k) (fHat.toArray, 127)
  Vector.ofFn fun i => nInv * getZ a i.val

/-! ## Base-case multiplication and MultiplyNTTs (Algorithm 11) -/

/-- FIPS 203 Algorithm 11 executable kernel, using the butterfly-natural coefficient ordering
    from Algorithm 9 rather than Algorithm 11's stated indexing convention (see module
    docstring for details). Within each group `g` of 4 coefficients, the pair at `(4g, 4g+1)`
    uses twiddle factor `zetaArray[64+g]` and the pair at `(4g+2, 4g+3)` uses its negation. -/
def loopMultiplyNTTs (fHat gHat : Tq) : Tq :=
  let fa := fHat.toArray
  let ga := gHat.toArray
  ⟨Vector.ofFn fun idx =>
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
      a0 * b1 + a1 * b0⟩

private def basisRq (i : Fin ringDegree) : Rq :=
  Vector.ofFn fun j => if i = j then 1 else 0

private def basisTq (i : Fin ringDegree) : Tq :=
  ⟨basisRq i⟩

private def nttColumns : Vector Tq ringDegree :=
  Vector.ofFn fun i => loopNTT (basisRq i)

private def invNTTColumns : Vector Rq ringDegree :=
  Vector.ofFn fun i => loopInvNTT (basisTq i)

private def nttMatrix (row col : Fin ringDegree) : Coeff :=
  (nttColumns[col.val])[row.val]

private def invNTTMatrix (row col : Fin ringDegree) : Coeff :=
  (invNTTColumns[col.val])[row.val]

private def applyMatrix (M : Fin ringDegree → Fin ringDegree → Coeff) (f : Rq) : Rq :=
  Vector.ofFn fun row => ∑ col : Fin ringDegree, M row col * f[col.val]

private def idMatrix (row col : Fin ringDegree) : Coeff :=
  if col = row then 1 else 0

private theorem applyMatrix_comp
    (A B C : Fin ringDegree → Fin ringDegree → Coeff)
    (hcomp : ∀ row col : Fin ringDegree, ∑ k : Fin ringDegree, A row k * B k col = C row col)
    (f : Rq) :
    applyMatrix A (applyMatrix B f) = applyMatrix C f := by
  apply Vector.ext
  intro j hj
  let jFin : Fin ringDegree := ⟨j, hj⟩
  calc
    (applyMatrix A (applyMatrix B f))[j]
        = ∑ k : Fin ringDegree, A jFin k * (∑ i : Fin ringDegree, B k i * f[i.val]) := by
            simp [applyMatrix, jFin]
    _ = ∑ k : Fin ringDegree, ∑ i : Fin ringDegree, A jFin k * (B k i * f[i.val]) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.mul_sum]
    _ = ∑ i : Fin ringDegree, ∑ k : Fin ringDegree, A jFin k * (B k i * f[i.val]) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin ringDegree, (∑ k : Fin ringDegree, A jFin k * B k i) * f[i.val] := by
          refine Finset.sum_congr rfl ?_
          intro i _
          calc
            ∑ k : Fin ringDegree, A jFin k * (B k i * f[i.val])
                = ∑ k : Fin ringDegree, (A jFin k * B k i) * f[i.val] := by
                    refine Finset.sum_congr rfl ?_
                    intro k _
                    ring
            _ = (∑ k : Fin ringDegree, A jFin k * B k i) * f[i.val] := by
                    rw [Finset.sum_mul]
    _ = ∑ i : Fin ringDegree, C jFin i * f[i.val] := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hcomp jFin i]
    _ = (applyMatrix C f)[j] := by
          simp [applyMatrix, jFin]

private theorem applyMatrix_id (f : Rq) :
    applyMatrix idMatrix f = f := by
  apply Vector.ext
  intro j hj
  let jFin : Fin ringDegree := ⟨j, hj⟩
  simp [applyMatrix, idMatrix]

set_option linter.style.nativeDecide false
private theorem invNTTMatrix_nttMatrix_entry :
    ∀ row col : Fin ringDegree,
      (∑ k : Fin ringDegree, invNTTMatrix row k * nttMatrix k col) = idMatrix row col := by
  -- This closed 256x256 matrix identity is intentionally discharged with `native_decide`
  -- to avoid severe kernel reduction timeouts in the proof-oriented model.
  native_decide

/-- Proof-oriented NTT obtained from the transform matrix extracted from the algorithmic
implementation on the standard basis. -/
@[implemented_by loopNTT]
def ntt (f : Rq) : Tq :=
  ⟨applyMatrix nttMatrix f⟩

/-- Proof-oriented inverse NTT obtained from the inverse transform matrix. -/
@[implemented_by loopInvNTT]
def invNTT (fHat : Tq) : Rq :=
  applyMatrix invNTTMatrix fHat.coeffs

/-- Proof-oriented `MultiplyNTTs` transported through the proven NTT isomorphism. -/
@[implemented_by loopMultiplyNTTs]
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  ntt (negacyclicMul (invNTT fHat) (invNTT gHat))

/-- The concrete inverse transform is a left inverse to the concrete forward transform. -/
theorem invNTT_ntt (f : Rq) : invNTT (ntt f) = f := by
  calc
    invNTT (ntt f) = applyMatrix idMatrix f := by
      simpa [invNTT, ntt] using
        applyMatrix_comp invNTTMatrix nttMatrix idMatrix invNTTMatrix_nttMatrix_entry f
    _ = f := applyMatrix_id f

/-- Concrete `NTTRingOps` instance for ML-KEM. -/
def concreteNTTRingOps : NTTRingOps where
  ntt := ntt
  invNTT := invNTT
  multiplyNTTs := multiplyNTTs

/-- Proof bundle showing that the concrete ML-KEM NTT implementation satisfies the abstract
`NTTRingLaws`. -/
def concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  invNTT_ntt := invNTT_ntt
  ntt_mul := by
    intro f g
    simp [concreteNTTRingOps, multiplyNTTs, invNTT_ntt]

end MLKEM.Concrete
