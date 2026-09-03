/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import all Init.Data.Array.Basic
import all Init.Data.Vector.Algebra
import all LatticeCrypto.MLDSA.Arithmetic
public meta import LatticeCrypto.MLDSA.Arithmetic
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Data.ZMod.Defs
public import LatticeCrypto.MLDSA.Arithmetic
public import LatticeCrypto.Ring.NTTCert
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete NTT for ML-DSA

Pure-Lean executable kernels for FIPS 204 Algorithms 41, 42, and 47, specialized to
`q = 8380417`, `n = 256`, and `ζ = 1753`.

The proof-oriented `ntt` / `invNTT` interface composes eight blocked butterfly stages.
Complementary bit-reversed twiddles make the inverse stages cancel the forward stages up to
`2^8`, and `nInv` removes that factor. Runtime execution remains rebound to the existing
imperative kernels through `@[implemented_by]`. This remains the executable refinement boundary:
the structural formulas mirror the loops, but this module does not yet prove the imperative
`Array` programs extensionally equal to them.
-/

public section



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

private theorem bitRev8_layer_partner :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      bitRev8 (2 ^ s.val + g.val) +
          bitRev8 (2 ^ (s.val + 1) - 1 - g.val) = 256 := by
  decide

private theorem layer_twiddle_index_bounds :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      2 ^ s.val + g.val < 256 ∧
        2 ^ (s.val + 1) - 1 - g.val < 256 := by
  decide

private theorem getZ_zetaTable (i : Nat) (hi : i < 256) :
    getZ zetaTable i = zeta ^ bitRev8 i := by
  simp [getZ, zetaTable, hi]

private theorem square_mod (a b : Nat) (h : a ^ 2 % modulus = b) (hb : b < modulus) :
    (a : Coeff) ^ 2 = b := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
  simpa [Nat.mod_eq_of_lt hb] using h

private theorem zeta_pow_256 : (zeta : Coeff) ^ 256 = -1 := by
  have h2 : (zeta : Coeff) ^ 2 = 3073009 := by
    change (1753 : Coeff) ^ 2 = 3073009
    exact square_mod 1753 3073009 (by norm_num [modulus]) (by norm_num [modulus])
  have h4 : (zeta : Coeff) ^ 4 = 3602218 := by
    calc
      zeta ^ 4 = (zeta ^ 2) ^ 2 := by ring
      _ = (3073009 : Coeff) ^ 2 := by rw [h2]
      _ = 3602218 := square_mod 3073009 3602218
        (by norm_num [modulus]) (by norm_num [modulus])
  have h8 : (zeta : Coeff) ^ 8 = 5010068 := by
    calc
      zeta ^ 8 = (zeta ^ 4) ^ 2 := by ring
      _ = (3602218 : Coeff) ^ 2 := by rw [h4]
      _ = 5010068 := square_mod 3602218 5010068
        (by norm_num [modulus]) (by norm_num [modulus])
  have h16 : (zeta : Coeff) ^ 16 = 7778734 := by
    calc
      zeta ^ 16 = (zeta ^ 8) ^ 2 := by ring
      _ = (5010068 : Coeff) ^ 2 := by rw [h8]
      _ = 7778734 := square_mod 5010068 7778734
        (by norm_num [modulus]) (by norm_num [modulus])
  have h32 : (zeta : Coeff) ^ 32 = 5178923 := by
    calc
      zeta ^ 32 = (zeta ^ 16) ^ 2 := by ring
      _ = (7778734 : Coeff) ^ 2 := by rw [h16]
      _ = 5178923 := square_mod 7778734 5178923
        (by norm_num [modulus]) (by norm_num [modulus])
  have h64 : (zeta : Coeff) ^ 64 = 3765607 := by
    calc
      zeta ^ 64 = (zeta ^ 32) ^ 2 := by ring
      _ = (5178923 : Coeff) ^ 2 := by rw [h32]
      _ = 3765607 := square_mod 5178923 3765607
        (by norm_num [modulus]) (by norm_num [modulus])
  have h128 : (zeta : Coeff) ^ 128 = 4808194 := by
    calc
      zeta ^ 128 = (zeta ^ 64) ^ 2 := by ring
      _ = (3765607 : Coeff) ^ 2 := by rw [h64]
      _ = 4808194 := square_mod 3765607 4808194
        (by norm_num [modulus]) (by norm_num [modulus])
  calc
    zeta ^ 256 = (zeta ^ 128) ^ 2 := by ring
    _ = (4808194 : Coeff) ^ 2 := by rw [h128]
    _ = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      change (((4808194 ^ 2 + 1 : Nat) : ZMod modulus)) = 0
      rw [ZMod.natCast_eq_zero_iff]
      norm_num [modulus]

/-- Forward and complementary inverse-table twiddles in one layer multiply to `-1`. -/
private theorem zetaTable_layer_partner :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      getZ zetaTable (2 ^ s.val + g.val) *
          getZ zetaTable (2 ^ (s.val + 1) - 1 - g.val) = -1 := by
  intro s g
  obtain ⟨hforward, hinverse⟩ := layer_twiddle_index_bounds s g
  rw [getZ_zetaTable _ hforward, getZ_zetaTable _ hinverse, ← pow_add]
  rw [bitRev8_layer_partner s g, zeta_pow_256]

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

private theorem layer_shape :
    ∀ s : Fin 8, 2 ^ s.val * (2 * (128 / 2 ^ s.val)) = polyBackend.degree := by
  decide

private abbrev NTTCoord := Fin polyBackend.degree

private def layerLayout (s : Fin 8) :
    LatticeCrypto.NTTCert.ButterflyLayout
      (Fin (2 ^ s.val) × Fin (128 / 2 ^ s.val)) NTTCoord where
  equiv := (LatticeCrypto.NTTCert.blockLayout (2 ^ s.val) (128 / 2 ^ s.val)).equiv.trans
    (finCongr (layer_shape s))

private def nttStage (s : Fin 8) :
    LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.butterflyStage (layerLayout s)
    (fun pair => getZ zetaTable (2 ^ s.val + pair.1.val))
    (fun pair => -getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val))
    (by
      intro pair
      have h := zetaTable_layer_partner s pair.1
      calc
        -getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val) *
            getZ zetaTable (2 ^ s.val + pair.1.val) =
          -(getZ zetaTable (2 ^ s.val + pair.1.val) *
            getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val)) := by ring
        _ = -(-1) := by rw [h]
        _ = 1 := by ring)

private def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3,
    nttStage 4, nttStage 5, nttStage 6, nttStage 7]

private theorem nInv_stageScalar :
    nInv * LatticeCrypto.NTTCert.stageScalar nttStages = 1 := by
  change ((8347681 * 256 : Nat) : ZMod 8380417) = ((1 : Nat) : ZMod 8380417)
  rw [ZMod.natCast_eq_natCast_iff']

private def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

private def invNTTCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.scaleCoeffs nInv
    (LatticeCrypto.NTTCert.inverseStages nttStages input)

private theorem invNTTCoeffs_nttCoeffs (input : NTTCoord → Coeff) :
    invNTTCoeffs (nttCoeffs input) = input := by
  unfold invNTTCoeffs nttCoeffs
  exact LatticeCrypto.NTTCert.scale_inverseStages_forwardStages
    nttStages nInv nInv_stageScalar input

private theorem nttCoeffs_add (left right : NTTCoord → Coeff) :
    nttCoeffs (left + right) = nttCoeffs left + nttCoeffs right := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_add nttStages left right

private theorem nttCoeffs_sub (left right : NTTCoord → Coeff) :
    nttCoeffs (left - right) = nttCoeffs left - nttCoeffs right := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_sub nttStages left right

private theorem nttCoeffs_zero : nttCoeffs 0 = 0 := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_zero nttStages

/-- Proof-oriented forward NTT assembled from eight certified butterfly stages. -/
@[implemented_by loopNTT]
def ntt (f : Rq) : Tq :=
  ⟨LatticeCrypto.NTTCert.applyCoeffTransform polyBackend nttCoeffs f⟩

/-- Proof-oriented inverse NTT assembled from the matching reverse stages and scaling. -/
@[implemented_by loopInvNTT]
def invNTT (fHat : Tq) : Rq :=
  LatticeCrypto.NTTCert.applyCoeffTransform polyBackend invNTTCoeffs fHat.coeffs

/-- Proof-oriented `MultiplyNTTs` transported through the proven NTT isomorphism. -/
@[implemented_by loopMultiplyNTTs]
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  ntt (negacyclicMul (invNTT fHat) (invNTT gHat))

/-- The concrete inverse transform is a left inverse to the concrete forward transform. -/
theorem invNTT_ntt (f : Rq) : invNTT (ntt f) = f := by
  exact LatticeCrypto.NTTCert.applyCoeffTransform_comp
    nttCoeffs invNTTCoeffs invNTTCoeffs_nttCoeffs f

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
  let : NeZero modulus := ⟨by norm_num [modulus]⟩
  let : Fintype Coeff := by
    dsimp [Coeff]
    exact ZMod.fintype modulus
  let : Finite Rq := Finite.of_equiv (Fin ringDegree → Coeff) rqEquivCoeffFun.symm
  exact ntt_injective.surjective_of_finite rqEquivTq

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

private theorem hadd_rq (f g : Rq) :
    polyBackend.coeff (f + g) = polyBackend.coeff f + polyBackend.coeff g := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).add f g).get i = f.get i + g.get i
  simp

private theorem hsub_rq (f g : Rq) :
    polyBackend.coeff (f - g) = polyBackend.coeff f - polyBackend.coeff g := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).sub f g).get i = f.get i - g.get i
  simp

private theorem hzero_rq : polyBackend.coeff (0 : Rq) = 0 := by
  funext i
  exact LatticeCrypto.vectorRing_zero_get i

/-- The concrete NTT is additive. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) :=
  LatticeCrypto.NTTCert.applyCoeffTransform_add nttCoeffs hadd_rq nttCoeffs_add f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq)
  exact ntt_add_toRq f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) :=
  LatticeCrypto.NTTCert.applyCoeffTransform_sub nttCoeffs hsub_rq nttCoeffs_sub f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub (f g : Rq) : ntt (f - g) = ntt f - ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq)
  exact ntt_sub_toRq f g

private theorem invNTT_add (g h : Tq) : invNTT (g + h) = invNTT g + invNTT h := by
  apply ntt_injective
  rw [ntt_invNTT, ntt_add, ntt_invNTT, ntt_invNTT]

private theorem invNTT_sub (g h : Tq) : invNTT (g - h) = invNTT g - invNTT h := by
  apply ntt_injective
  rw [ntt_invNTT, ntt_sub, ntt_invNTT, ntt_invNTT]

private theorem negacyclicMul_coeff (a b : Rq) (k : Fin ringDegree) :
    polyBackend.coeff (negacyclicMul a b) k =
      LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff a) (polyBackend.coeff b) k :=
  LatticeCrypto.negacyclicMulPure_coeff polyKernel a b k

/-- Concrete `NTTRingOps` instance for ML-DSA. -/
@[reducible] def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  mulHat := multiplyNTTs

/-- Proof-oriented algebraic laws for the ML-DSA concrete NTT. -/
theorem concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    apply LatticeCrypto.TransformPoly.ext
    exact LatticeCrypto.NTTCert.applyCoeffTransform_zero nttCoeffs hzero_rq nttCoeffs_zero
  toHat_mul f g := by
    change ntt (negacyclicMul f g) = multiplyNTTs (ntt f) (ntt g)
    simp only [multiplyNTTs, invNTT_ntt]
  toHat_add f g := ntt_add f g
  toHat_sub f g := ntt_sub f g
  mul_add f g h := by
    change multiplyNTTs f (g + h) = multiplyNTTs f g + multiplyNTTs f h
    simp only [multiplyNTTs, invNTT_add]
    rw [← ntt_add]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_add_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_sub f g h := by
    change multiplyNTTs f (g - h) = multiplyNTTs f g - multiplyNTTs f h
    simp only [multiplyNTTs, invNTT_sub]
    rw [← ntt_sub]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_sub_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_comm f g := by
    change multiplyNTTs f g = multiplyNTTs g f
    simp only [multiplyNTTs, LatticeCrypto.vectorRing_mul_comm]
  mul_assoc f g h := by
    change multiplyNTTs (multiplyNTTs f g) h = multiplyNTTs f (multiplyNTTs g h)
    simp only [multiplyNTTs, invNTT_ntt]
    exact congrArg ntt (mul_assoc (invNTT f) (invNTT g) (invNTT h))

end MLDSA.Concrete
