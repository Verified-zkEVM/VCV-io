/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete NTT for ML-DSA

Pure-Lean executable kernels for FIPS 204 Algorithms 41, 42, and 47, specialized to
`q = 8380417`, `n = 256`, and `ζ = 1753`.

As in the ML-KEM concrete development, the public `ntt` / `invNTT` / `multiplyNTTs`
interface is proof-oriented: we extract the transform matrices by evaluating the executable
kernels on the standard basis, prove the matrices are inverse, and then expose matrix-based
definitions marked with `@[implemented_by]`. Runtime execution still uses the fast loop
kernels, while proofs reason about the checked matrix semantics.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MLDSA.Concrete

open MLDSA

private local instance instAddRqNTT : Add Rq := Vector.instAdd
private local instance instZeroRqNTT : Zero Rq := Vector.instZero
private local instance instSubRqNTT : Sub Rq := Vector.instSub
private local instance instNegRqNTT : Neg Rq := Vector.instNeg

/-- Reverse the low 8 bits of `i` (FIPS 204: `brv(k)`). -/
def bitRev8 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 7) ||| (b 1 <<< 6) ||| (b 2 <<< 5) ||| (b 3 <<< 4) |||
  (b 4 <<< 3) ||| (b 5 <<< 2) ||| (b 6 <<< 1) ||| b 7

/-- Precomputed twiddle table: `zetas[k] = ζ^(brv(k))` for `k = 0 .. 255`,
where `brv` is 8-bit reversal per FIPS 204 §4.5.
The forward NTT uses indices `1 .. 255`; the inverse NTT uses the same indices
(negated) in reverse order `255 .. 1`. -/
def zetaTable : Array Coeff :=
  (Array.range 256).map fun i => zeta ^ bitRev8 i

/-- `256⁻¹ mod q`. -/
def nInv : Coeff := ((modulus - (modulus - 1) / ringDegree : ℕ) : Coeff)

/-- Safe array access with fallback to zero. -/
private def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

/-- FIPS 204 Algorithm 41: executable loop kernel for the forward NTT. -/
def loopNTT (f : Rq) : Tq := Id.run do
  let mut a := f.toArray
  let mut k := 1
  let mut len := 128
  while len ≥ 1 do
    let mut start := 0
    while start < ringDegree do
      let z := getZ zetaTable k
      k := k + 1
      for j in [start : start + len] do
        let u := getZ a j
        let v := getZ a (j + len)
        let t := z * v
        a := a.set! (j + len) (u - t)
        a := a.set! j (u + t)
      start := start + 2 * len
    len := len / 2
  return ⟨Vector.ofFn fun i => getZ a i.val⟩

/-- FIPS 204 Algorithm 42: executable loop kernel for the inverse NTT. -/
def loopInvNTT (fHat : Tq) : Rq := Id.run do
  let mut a := fHat.toArray
  let mut k := 255
  let mut len := 1
  while len ≤ 128 do
    let mut start := 0
    while start < ringDegree do
      let z := -(getZ zetaTable k)
      k := k - 1
      for j in [start : start + len] do
        let u := getZ a j
        let v := getZ a (j + len)
        a := a.set! j (u + v)
        a := a.set! (j + len) (z * (u - v))
      start := start + 2 * len
    len := len * 2
  for j in [0 : ringDegree] do
    a := a.set! j (nInv * getZ a j)
  return Vector.ofFn fun i => getZ a i.val

/-- Executable pointwise multiplication in the ML-DSA NTT domain (Algorithm 47). -/
def loopMultiplyNTTs (fHat gHat : Tq) : Tq :=
  ⟨Vector.ofFn fun i => fHat[i.val] * gHat[i.val]⟩

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

private theorem applyMatrix_get
    (M : Fin ringDegree → Fin ringDegree → Coeff) (f : Rq) {j : Nat} (hj : j < ringDegree) :
    (applyMatrix M f)[j] = ∑ col : Fin ringDegree, M ⟨j, hj⟩ col * f[col.val] := by
  rw [applyMatrix]
  simp

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
  rw [applyMatrix_get]
  simp [idMatrix]

private theorem applyMatrix_add
    (M : Fin ringDegree → Fin ringDegree → Coeff) (f g : Rq) :
    applyMatrix M (f + g) = applyMatrix M f + applyMatrix M g := by
  apply Vector.ext
  intro j hj
  let jFin : Fin ringDegree := ⟨j, hj⟩
  have hsum_add := applyMatrix_get M (f + g) hj
  have hsum_f := applyMatrix_get M f hj
  have hsum_g := applyMatrix_get M g hj
  calc
    (applyMatrix M (f + g))[j]
        = ∑ col : Fin ringDegree, M jFin col * ((f + g)[col.val]) := hsum_add
    _ = ∑ col : Fin ringDegree, M jFin col * (f[col.val] + g[col.val]) := by
          refine Finset.sum_congr rfl ?_
          intro col _
          exact congrArg (fun x => M jFin col * x) (Vector.getElem_add f g col.val col.isLt)
    _ = ∑ col : Fin ringDegree, (M jFin col * f[col.val] + M jFin col * g[col.val]) := by
          refine Finset.sum_congr rfl ?_
          intro col _
          ring
    _ = (∑ col : Fin ringDegree, M jFin col * f[col.val]) +
          (∑ col : Fin ringDegree, M jFin col * g[col.val]) := by
            rw [Finset.sum_add_distrib]
    _ = (applyMatrix M f)[j] + (applyMatrix M g)[j] := by
          rw [← hsum_f, ← hsum_g]
    _ = (applyMatrix M f + applyMatrix M g)[j] := by
          symm
          exact Vector.getElem_add (applyMatrix M f) (applyMatrix M g) j hj

private theorem applyMatrix_neg
    (M : Fin ringDegree → Fin ringDegree → Coeff) (f : Rq) :
    applyMatrix M (-f) = -applyMatrix M f := by
  apply Vector.ext
  intro j hj
  let jFin : Fin ringDegree := ⟨j, hj⟩
  have hsum_neg := applyMatrix_get M (-f) hj
  have hsum_f := applyMatrix_get M f hj
  calc
    (applyMatrix M (-f))[j]
        = ∑ col : Fin ringDegree, M jFin col * ((-f)[col.val]) := hsum_neg
    _ = ∑ col : Fin ringDegree, -(M jFin col * f[col.val]) := by
          refine Finset.sum_congr rfl ?_
          intro col _
          calc
            M jFin col * ((-f)[col.val]) = M jFin col * (-f[col.val]) := by
              exact congrArg (fun x => M jFin col * x) (Vector.getElem_neg f col.val col.isLt)
            _ = -(M jFin col * f[col.val]) := by
              ring
    _ = -(∑ col : Fin ringDegree, M jFin col * f[col.val]) := by
          rw [← Finset.sum_neg_distrib]
    _ = -((applyMatrix M f)[j]) := by
          rw [← hsum_f]
    _ = (-applyMatrix M f)[j] := by
          symm
          exact Vector.getElem_neg (applyMatrix M f) j hj

private theorem applyMatrix_sub
    (M : Fin ringDegree → Fin ringDegree → Coeff) (f g : Rq) :
    applyMatrix M (f - g) = applyMatrix M f - applyMatrix M g := by
  apply Vector.ext
  intro j hj
  let jFin : Fin ringDegree := ⟨j, hj⟩
  have hsum_sub := applyMatrix_get M (f - g) hj
  have hsum_f := applyMatrix_get M f hj
  have hsum_g := applyMatrix_get M g hj
  calc
    (applyMatrix M (f - g))[j]
        = ∑ col : Fin ringDegree, M jFin col * ((f - g)[col.val]) := hsum_sub
    _ = ∑ col : Fin ringDegree, M jFin col * (f[col.val] - g[col.val]) := by
          refine Finset.sum_congr rfl ?_
          intro col _
          exact congrArg (fun x => M jFin col * x) (Vector.getElem_sub f g col.val col.isLt)
    _ = ∑ col : Fin ringDegree, (M jFin col * f[col.val] - M jFin col * g[col.val]) := by
          refine Finset.sum_congr rfl ?_
          intro col _
          ring
    _ = (∑ col : Fin ringDegree, M jFin col * f[col.val]) -
          (∑ col : Fin ringDegree, M jFin col * g[col.val]) := by
            rw [Finset.sum_sub_distrib]
    _ = (applyMatrix M f)[j] - (applyMatrix M g)[j] := by
          rw [← hsum_f, ← hsum_g]
    _ = (applyMatrix M f - applyMatrix M g)[j] := by
          symm
          exact Vector.getElem_sub (applyMatrix M f) (applyMatrix M g) j hj

set_option linter.style.nativeDecide false
private theorem invNTTMatrix_nttMatrix_entry :
    ∀ row col : Fin ringDegree,
      (∑ k : Fin ringDegree, invNTTMatrix row k * nttMatrix k col) = idMatrix row col := by
  native_decide

private theorem nttMatrix_invNTTMatrix_entry :
    ∀ row col : Fin ringDegree,
      (∑ k : Fin ringDegree, nttMatrix row k * invNTTMatrix k col) = idMatrix row col := by
  native_decide

/-- Proof-oriented forward NTT obtained from the transform matrix extracted from the
algorithmic kernel. -/
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

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  apply Tq.ext
  calc
    (ntt (invNTT fHat)).coeffs = applyMatrix idMatrix fHat.coeffs := by
      simpa [invNTT, ntt] using
        applyMatrix_comp nttMatrix invNTTMatrix idMatrix nttMatrix_invNTTMatrix_entry fHat.coeffs
    _ = fHat.coeffs := applyMatrix_id fHat.coeffs

/-- The concrete NTT is additive on the coefficient-vector carrier of `T_q`. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) := by
  exact applyMatrix_add nttMatrix f g

/-- The concrete NTT preserves subtraction on the coefficient-vector carrier of `T_q`. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) := by
  exact applyMatrix_sub nttMatrix f g

/-- Concrete `NTTRingOps` instance for ML-DSA. -/
def concreteNTTRingOps : NTTRingOps where
  ntt := ntt
  invNTT := invNTT
  multiplyNTTs := multiplyNTTs

/-- Proof-oriented algebraic laws for the ML-DSA concrete NTT. -/
def concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  invNTT_ntt := invNTT_ntt
  ntt_mul := by
    intro f g
    simp [concreteNTTRingOps, multiplyNTTs, invNTT_ntt]

end MLDSA.Concrete
