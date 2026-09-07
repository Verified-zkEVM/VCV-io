/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import all Init.Data.Array.Basic
import all Init.Data.Vector.Algebra
import all LatticeCrypto.MLKEM.Arithmetic
public meta import LatticeCrypto.MLKEM.Arithmetic
public meta import LatticeCrypto.MLKEM.Params
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Data.ZMod.Defs
public import LatticeCrypto.MLKEM.Arithmetic
public import LatticeCrypto.Ring.NTTCert
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete NTT for ML-KEM

Pure-Lean executable kernels for FIPS 203 Algorithms 9–11 (NTT, NTT⁻¹, MultiplyNTTs),
specialised to `q = 3329`, `n = 256`, `ζ = 17`.

The public `ntt` / `invNTT` interface is exposed in a proof-oriented form assembled from the seven
butterfly layers of Algorithms 9 and 10. Each layer carries its exact blocked coordinate layout and
complementary twiddle law; their structural composition proves the inverse laws after the final
normalization. At runtime, `@[implemented_by]` rebinds those public definitions to the original fast
loop kernels, so execution keeps the intended `O(n log n)` / `O(n)` behavior. That compiler
substitution remains the executable refinement boundary: the structural formulas mirror the loops,
but this module does not yet prove the imperative `Array` programs extensionally equal to them.

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

public section



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

private theorem bitRev7_layer_partner :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      bitRev7 (2 ^ s.val + g.val) +
          bitRev7 (2 ^ (s.val + 1) - 1 - g.val) = 128 := by
  decide

private theorem layer_twiddle_index_bounds :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      2 ^ s.val + g.val < 128 ∧
        2 ^ (s.val + 1) - 1 - g.val < 128 := by
  decide

private theorem getZ_zetaArray (i : Nat) (hi : i < 128) :
    getZ zetaArray i = zeta ^ bitRev7 i := by
  simp [getZ, zetaArray, hi]

private theorem zeta_pow_128 : (zeta : Coeff) ^ 128 = -1 := by
  have h2 : (zeta : Coeff) ^ 2 = 289 := by
    norm_num [MLKEM.zeta, MLKEM.modulus]
  have h4 : (zeta : Coeff) ^ 4 = 296 := by
    calc
      zeta ^ 4 = (zeta ^ 2) ^ 2 := by ring
      _ = (289 : Coeff) ^ 2 := by rw [h2]
      _ = 296 := by
        change ((289 ^ 2 : Nat) : ZMod 3329) = ((296 : Nat) : ZMod 3329)
        rw [ZMod.natCast_eq_natCast_iff']
        norm_num
  have h8 : (zeta : Coeff) ^ 8 = 1062 := by
    calc
      zeta ^ 8 = (zeta ^ 4) ^ 2 := by ring
      _ = (296 : Coeff) ^ 2 := by rw [h4]
      _ = 1062 := by
        change ((296 ^ 2 : Nat) : ZMod 3329) = ((1062 : Nat) : ZMod 3329)
        rw [ZMod.natCast_eq_natCast_iff']
        norm_num
  have h16 : (zeta : Coeff) ^ 16 = 2642 := by
    calc
      zeta ^ 16 = (zeta ^ 8) ^ 2 := by ring
      _ = (1062 : Coeff) ^ 2 := by rw [h8]
      _ = 2642 := by
        change ((1062 ^ 2 : Nat) : ZMod 3329) = ((2642 : Nat) : ZMod 3329)
        rw [ZMod.natCast_eq_natCast_iff']
        norm_num
  have h32 : (zeta : Coeff) ^ 32 = 2580 := by
    calc
      zeta ^ 32 = (zeta ^ 16) ^ 2 := by ring
      _ = (2642 : Coeff) ^ 2 := by rw [h16]
      _ = 2580 := by
        change ((2642 ^ 2 : Nat) : ZMod 3329) = ((2580 : Nat) : ZMod 3329)
        rw [ZMod.natCast_eq_natCast_iff']
        norm_num
  have h64 : (zeta : Coeff) ^ 64 = 1729 := by
    calc
      zeta ^ 64 = (zeta ^ 32) ^ 2 := by ring
      _ = (2580 : Coeff) ^ 2 := by rw [h32]
      _ = 1729 := by
        change ((2580 ^ 2 : Nat) : ZMod 3329) = ((1729 : Nat) : ZMod 3329)
        rw [ZMod.natCast_eq_natCast_iff']
        norm_num
  calc
    zeta ^ 128 = (zeta ^ 64) ^ 2 := by ring
    _ = (1729 : Coeff) ^ 2 := by rw [h64]
    _ = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      change (((1729 ^ 2 + 1 : Nat) : ZMod 3329)) = 0
      rw [ZMod.natCast_eq_zero_iff]
      norm_num

/-- The twiddle used by a forward butterfly and the complementary twiddle
used by its matching inverse butterfly multiply to `-1`. -/
private theorem zetaArray_layer_partner :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      getZ zetaArray (2 ^ s.val + g.val) *
          getZ zetaArray (2 ^ (s.val + 1) - 1 - g.val) = -1 := by
  intro s g
  obtain ⟨hforward, hinverse⟩ := layer_twiddle_index_bounds s g
  rw [getZ_zetaArray _ hforward, getZ_zetaArray _ hinverse, ← pow_add]
  rw [bitRev7_layer_partner s g, zeta_pow_128]

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

private theorem layer_shape :
    ∀ s : Fin 7, 2 ^ s.val * (2 * (128 / 2 ^ s.val)) = polyBackend.degree := by
  decide

private abbrev NTTCoord := Fin polyBackend.degree

/-- The blocked coordinate layout used by layer `s` of Algorithms 9 and 10. -/
private def layerLayout (s : Fin 7) :
    LatticeCrypto.NTTCert.ButterflyLayout
      (Fin (2 ^ s.val) × Fin (128 / 2 ^ s.val)) NTTCoord where
  equiv := (LatticeCrypto.NTTCert.blockLayout (2 ^ s.val) (128 / 2 ^ s.val)).equiv.trans
    (finCongr (layer_shape s))

/-- One structurally certified ML-KEM butterfly layer. The group coordinate chooses the
twiddle; the within-group coordinate selects one of the independent butterflies. -/
private def nttStage (s : Fin 7) :
    LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.butterflyStageRev (layerLayout s)
    (fun pair => getZ zetaArray (2 ^ s.val + pair.1.val))
    (fun pair => getZ zetaArray (2 ^ (s.val + 1) - 1 - pair.1.val))
    (by
      intro pair
      have h := zetaArray_layer_partner s pair.1
      calc
        -getZ zetaArray (2 ^ (s.val + 1) - 1 - pair.1.val) *
            getZ zetaArray (2 ^ s.val + pair.1.val) =
          -(getZ zetaArray (2 ^ s.val + pair.1.val) *
            getZ zetaArray (2 ^ (s.val + 1) - 1 - pair.1.val)) := by ring
        _ = -(-1) := by rw [h]
        _ = 1 := by ring)

/-- The seven forward layers, ordered as Algorithm 9 executes them. -/
private def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3, nttStage 4, nttStage 5, nttStage 6]

private theorem nInv_stageScalar :
    nInv * LatticeCrypto.NTTCert.stageScalar nttStages = 1 := by
  change ((3303 * 128 : Nat) : ZMod 3329) = ((1 : Nat) : ZMod 3329)
  rw [ZMod.natCast_eq_natCast_iff']

/-- Named proof-facing coefficient transform. Keeping the assembled stage list behind this
boundary lets downstream algebraic proofs use focused interface lemmas. -/
private def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

/-- Named proof-facing inverse coefficient transform, including the final normalization. -/
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

/-- Proof-oriented NTT assembled from the seven certified butterfly layers. -/
@[implemented_by loopNTT]
def ntt (f : Rq) : Tq :=
  ⟨LatticeCrypto.NTTCert.applyCoeffTransform polyBackend nttCoeffs f⟩

/-- Proof-oriented inverse NTT assembled from the matching reverse layers and final scaling. -/
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

private theorem hadd_rq (f g : Rq) :
    polyBackend.coeff (f + g) = polyBackend.coeff f + polyBackend.coeff g := by
  funext i
  change (f + g).get i = f.get i + g.get i
  exact coeffRing.add_coeff f g i

private theorem hsub_rq (f g : Rq) :
    polyBackend.coeff (f - g) = polyBackend.coeff f - polyBackend.coeff g := by
  funext i
  change (f - g).get i = f.get i - g.get i
  exact coeffRing.sub_coeff f g i

private theorem hzero_rq : polyBackend.coeff (0 : Rq) = 0 := by
  funext i
  change (0 : Rq).get i = 0
  exact LatticeCrypto.vectorRing_zero_get i

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

/-- The concrete NTT is additive on the coefficient-vector carrier of `T_q`. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) := by
  exact LatticeCrypto.NTTCert.applyCoeffTransform_add nttCoeffs hadd_rq
    nttCoeffs_add f g

/-- The concrete NTT preserves subtraction on the coefficient-vector carrier of `T_q`. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) := by
  exact LatticeCrypto.NTTCert.applyCoeffTransform_sub nttCoeffs hsub_rq
    nttCoeffs_sub f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq)
  exact ntt_add_toRq f g

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

private theorem hinvadd_tq (fHat gHat : Tq) :
    polyBackend.coeff (fHat + gHat).coeffs =
      fun i => polyBackend.coeff fHat.coeffs i + polyBackend.coeff gHat.coeffs i := by
  funext i; exact coeffRing.add_coeff fHat.coeffs gHat.coeffs i

private theorem negacyclicMul_coeff (a b : Rq) (k : Fin ringDegree) :
    polyBackend.coeff (negacyclicMul a b) k =
      LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff a) (polyBackend.coeff b) k :=
  LatticeCrypto.negacyclicMulPure_coeff polyKernel a b k

/-- Concrete `NTTRingOps` instance for ML-KEM. -/
@[reducible] def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  mulHat := multiplyNTTs

/-- Proof bundle showing that the concrete ML-KEM NTT implementation satisfies the abstract
`NTTRingLaws`. -/
theorem concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    apply LatticeCrypto.TransformPoly.ext
    exact LatticeCrypto.NTTCert.applyCoeffTransform_zero nttCoeffs hzero_rq nttCoeffs_zero
  toHat_mul f g := by
    change ntt (negacyclicMul f g) = multiplyNTTs (ntt f) (ntt g)
    simp only [multiplyNTTs, invNTT_ntt]
  toHat_add f g := by
    change ntt (f + g) = ntt f + ntt g
    exact ntt_add f g
  toHat_sub f g := by
    change ntt (f - g) = ntt f - ntt g
    exact ntt_sub f g
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

end MLKEM.Concrete
