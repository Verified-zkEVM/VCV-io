/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.MLDSA.Arithmetic
import LatticeCrypto.Ring.NTTCert
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


open scoped BigOperators

namespace MLDSA.Concrete

open MLDSA


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
  LatticeCrypto.NTTCert.basis polyBackend i

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
  LatticeCrypto.NTTCert.applyMatrix polyBackend M f

private def idMatrix (row col : Fin ringDegree) : Coeff :=
  LatticeCrypto.NTTCert.idMatrix ringDegree row col

-- The extracted 256×256 transform matrices expand to a large closed `ZMod` expression for
-- each entry. At the moment, `native_decide` is the only practical way we have to discharge
-- this fully concrete certificate inside Lean without a separate proof-oriented certificate
-- artifact. Plain kernel reduction (`decide`/`rfl`) gets stuck on the resulting arithmetic.
--
-- To move off `native_decide`, we likely need one of:
-- 1. generated row/entry certificates for the matrix product `M⁻¹ · M = I`, checked by small
--    kernel proofs, or
-- 2. a more algebraic NTT correctness development showing the loop kernels implement the
--    canonical transform and deriving inversion abstractly.
--
-- Both are larger refactors than a small warning-cleanup pass. Until then, we scope off
-- Mathlib's `nativeDecide` style linter for this certificate lemma only. The reverse
-- roundtrip law below is derived from this one using finiteness of the concrete carriers.
set_option maxHeartbeats 800000 in
-- The concrete matrix certificate currently needs a larger heartbeat budget.
set_option linter.style.nativeDecide false in
private theorem invNTTMatrix_nttMatrix_entry :
    ∀ row col : Fin ringDegree,
      (∑ k : Fin ringDegree, invNTTMatrix row k * nttMatrix k col) = idMatrix row col := by
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
        LatticeCrypto.NTTCert.applyMatrix_comp (backend := polyBackend)
          invNTTMatrix nttMatrix idMatrix invNTTMatrix_nttMatrix_entry f
    _ = f := LatticeCrypto.NTTCert.applyMatrix_id (backend := polyBackend) f

private def rqEquivCoeffFun : Rq ≃ (Fin ringDegree → Coeff) where
  toFun f i := f.get i
  invFun f := Vector.ofFn f
  left_inv f := by
    apply Vector.ext
    intro i hi
    exact Vector.getElem_ofFn (f := fun i => f.get i) hi
  right_inv f := by
    funext i
    exact Vector.get_ofFn f i

private def rqEquivTq : Rq ≃ Tq where
  toFun f := ⟨f⟩
  invFun fHat := fHat.coeffs
  left_inv _ := rfl
  right_inv fHat := by cases fHat; rfl

private theorem ntt_injective : Function.Injective ntt := by
  intro f g h
  have hInv := congrArg invNTT h
  simpa [invNTT_ntt] using hInv

private theorem ntt_surjective : Function.Surjective ntt := by
  letI : NeZero modulus := ⟨by norm_num [modulus]⟩
  letI : Fintype Coeff := by
    dsimp [Coeff]
    exact ZMod.fintype modulus
  letI : Finite Rq := Finite.of_equiv (Fin ringDegree → Coeff) rqEquivCoeffFun.symm
  exact ntt_injective.surjective_of_finite rqEquivTq

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

private theorem hadd_rq (f g : Rq) :
    polyBackend.coeff (f + g) = fun i => polyBackend.coeff f i + polyBackend.coeff g i := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).add f g).get i = f.get i + g.get i
  simp

private theorem hsub_rq (f g : Rq) :
    polyBackend.coeff (f - g) = fun i => polyBackend.coeff f i - polyBackend.coeff g i := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).sub f g).get i = f.get i - g.get i
  simp

private theorem hzero_rq (i : Fin polyBackend.degree) :
    polyBackend.coeff (0 : Rq) i = 0 :=
  LatticeCrypto.vectorRing_zero_get i

/-- The concrete NTT is additive. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) :=
  LatticeCrypto.NTTCert.applyMatrix_add (backend := polyBackend) nttMatrix hadd_rq f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  simpa using ntt_add_toRq f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) :=
  LatticeCrypto.NTTCert.applyMatrix_sub (backend := polyBackend) nttMatrix hsub_rq f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub (f g : Rq) : ntt (f - g) = ntt f - ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  simpa using ntt_sub_toRq f g

/-- Concrete `NTTRingOps` instance for ML-DSA. -/
def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  zeroHat := 0
  addHat := (· + ·)
  subHat := (· - ·)
  mulHat := multiplyNTTs

/-- Proof-oriented algebraic laws for the ML-DSA concrete NTT. -/
noncomputable def concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    apply LatticeCrypto.TransformPoly.ext
    exact LatticeCrypto.NTTCert.applyMatrix_zero (backend := polyBackend) nttMatrix hzero_rq
  toHat_mul := by
    intro f g
    simp [concreteNTTRingOps, multiplyNTTs, invNTT_ntt]
  toHat_add := by
    intro f g; exact ntt_add f g
  toHat_sub := by
    intro f g; exact ntt_sub f g

end MLDSA.Concrete
