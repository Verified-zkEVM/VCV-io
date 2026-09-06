/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.Primitives

/-!
# The exact packed FFT

`Primitives.mergeFFT` and `Primitives.splitFFT` recurse on the packed FFT layout of the Falcon
specification. This file identifies the recursion with an evaluation map: `RealFFTPoly.ofCoeffs`
builds the packed representation of a real polynomial by merging the representations of its
even and odd parts, and `coord_ofCoeffs` shows that coordinate `j` at level `k` is the value of
the polynomial at `exp(rootAngle k j · I)`. Everything else follows from that description:

- `ofCoeffs_negacyclic`: the packed FFT turns negacyclic multiplication into the pointwise
  complex multiplication `Primitives.mulFFT`, because each root angle is a root of
  `X^n + 1` (`exp_rootAngle`);
- `toCoeffs_ofCoeffs`: the split recursion `RealFFTPoly.toCoeffs` inverts `ofCoeffs`;
- `Primitives.ffSampling_support_ofCoeffs`: every output of `ffSampling` is the packed FFT of a
  pair of integer polynomials, because the leaves sample integers and the nodes merge.
-/

@[expose] public section

open OracleComp OracleSpec Complex

namespace Falcon

/-! ## Coordinates of a packed FFT polynomial -/

namespace RealFFTPoly

variable {k : ℕ}

/-- The `j`-th packed coordinate as a complex number. -/
noncomputable def coord (f : RealFFTPoly k) (j : Fin (2 ^ k)) : ℂ := ⟨f.re j, f.im j⟩

@[simp] theorem coord_re (f : RealFFTPoly k) (j : Fin (2 ^ k)) : (coord f j).re = f.re j := rfl

@[simp] theorem coord_im (f : RealFFTPoly k) (j : Fin (2 ^ k)) : (coord f j).im = f.im j := rfl

@[simp] theorem re_pack (a b : Vector ℝ (2 ^ k)) (i : Fin (2 ^ k)) : (pack a b).re i = a.get i := by
  simp [pack, re, i.isLt]

@[simp] theorem im_pack (a b : Vector ℝ (2 ^ k)) (i : Fin (2 ^ k)) : (pack a b).im i = b.get i := by
  simp only [pack, im, LatticeCrypto.Poly.get_vectorOfFn]
  rw [dif_neg (by omega)]
  congr 1
  ext
  simp

theorem coord_pack (a b : Vector ℝ (2 ^ k)) (i : Fin (2 ^ k)) :
    coord (pack a b) i = ⟨a.get i, b.get i⟩ := by
  simp [coord]

theorem get_eq_getElem {n : ℕ} (v : Vector ℝ n) (i : Fin n) : v.get i = v[i.1] := rfl

/-- Two packed FFT polynomials with the same coordinates are equal. -/
theorem ext_coord {a b : RealFFTPoly k} (h : ∀ j, coord a j = coord b j) : a = b := by
  apply Vector.ext
  intro m hm
  by_cases hlt : m < 2 ^ k
  · have := congrArg Complex.re (h ⟨m, hlt⟩)
    simp only [coord_re, re, get_eq_getElem] at this
    exact this
  · have := congrArg Complex.im (h ⟨m - 2 ^ k, by omega⟩)
    simp only [coord_im, im, get_eq_getElem] at this
    have hmk : m - 2 ^ k + 2 ^ k = m := by omega
    simp only [hmk] at this
    exact this

theorem coord_add (a b : RealFFTPoly k) (j : Fin (2 ^ k)) :
    coord (a + b) j = coord a j + coord b j := by
  apply Complex.ext
  · simp only [coord_re, add_re]
    exact LatticeCrypto.Poly.get_add (Coeff := ℝ) a b _
  · simp only [coord_im, add_im]
    exact LatticeCrypto.Poly.get_add (Coeff := ℝ) a b _

theorem coord_neg (a : RealFFTPoly k) (j : Fin (2 ^ k)) : coord (-a) j = -coord a j := by
  apply Complex.ext
  · simp only [coord_re, neg_re]
    exact LatticeCrypto.Poly.get_neg (Coeff := ℝ) a _
  · simp only [coord_im, neg_im]
    exact LatticeCrypto.Poly.get_neg (Coeff := ℝ) a _

theorem coord_mulFFT (a b : RealFFTPoly k) (j : Fin (2 ^ k)) :
    coord (Primitives.mulFFT a b) j = coord a j * coord b j := by
  apply Complex.ext <;> simp [coord, Primitives.mulFFT]

theorem two_pow_succ_eq (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by ring

/-- Half of a coordinate index, as an index one level down. -/
abbrev half (j : Fin (2 ^ (k + 1))) : Fin (2 ^ k) :=
  ⟨j.1 / 2, by have := j.2; have := two_pow_succ_eq k; omega⟩

theorem coord_mergeFFT_even (f₀ f₁ : RealFFTPoly k) (i : ℕ) (hi : i < 2 ^ k) :
    coord (Primitives.mergeFFT f₀ f₁) ⟨2 * i, by have := two_pow_succ_eq k; omega⟩ =
      coord f₀ ⟨i, hi⟩ +
        Complex.exp ((Primitives.splitAngle ⟨i, hi⟩ : ℝ) * I) * coord f₁ ⟨i, hi⟩ := by
  apply Complex.ext <;>
    simp [coord, Primitives.mergeFFT, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] <;> ring

theorem coord_mergeFFT_odd (f₀ f₁ : RealFFTPoly k) (i : ℕ) (hi : i < 2 ^ k) :
    coord (Primitives.mergeFFT f₀ f₁) ⟨2 * i + 1, by have := two_pow_succ_eq k; omega⟩ =
      coord f₀ ⟨i, hi⟩ -
        Complex.exp ((Primitives.splitAngle ⟨i, hi⟩ : ℝ) * I) * coord f₁ ⟨i, hi⟩ := by
  apply Complex.ext <;>
    simp [coord, Primitives.mergeFFT, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      Nat.mul_add_div] <;> ring

end RealFFTPoly

/-! ## Evaluation of a real polynomial on the unit circle -/

/-- The value at `exp(θ · I)` of the real polynomial with coefficient function `f`. -/
noncomputable def evalAngle {n : ℕ} (f : Fin n → ℝ) (θ : ℝ) : ℂ :=
  ∑ m : Fin n, (f m : ℂ) * Complex.exp (((m.1 : ℝ) * θ : ℝ) * I)

theorem sum_univ_two_mul {M : Type*} [AddCommMonoid M] {n N : ℕ} (h : n = 2 * N)
    (g : Fin n → M) :
    ∑ m, g m = ∑ i : Fin N, (g ⟨2 * i.1, by omega⟩ + g ⟨2 * i.1 + 1, by omega⟩) := by
  subst h
  let g' : ℕ → M := fun m => if hm : m < 2 * N then g ⟨m, hm⟩ else 0
  have h1 : ∑ m : Fin (2 * N), g m = ∑ m ∈ Finset.range (2 * N), g' m := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m _
    simp [g', m.2]
  have h2 : ∀ K, ∑ m ∈ Finset.range (2 * K), g' m =
      ∑ i ∈ Finset.range K, (g' (2 * i) + g' (2 * i + 1)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, add_assoc]
  rw [h1, h2, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : 2 * i.1 < 2 * N := by omega
  have h2 : 2 * i.1 + 1 < 2 * N := by omega
  simp [g', h1, h2]

theorem evalAngle_two_mul {n N : ℕ} (h : n = 2 * N) (f : Fin n → ℝ) (θ : ℝ) :
    evalAngle f θ = evalAngle (fun i : Fin N => f ⟨2 * i.1, by omega⟩) (2 * θ) +
      Complex.exp ((θ : ℂ) * I) *
        evalAngle (fun i : Fin N => f ⟨2 * i.1 + 1, by omega⟩) (2 * θ) := by
  unfold evalAngle
  rw [sum_univ_two_mul h, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 2
    push_cast
    ring
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem evalAngle_add {n : ℕ} (f g : Fin n → ℝ) (θ : ℝ) :
    evalAngle (fun i => f i + g i) θ = evalAngle f θ + evalAngle g θ := by
  unfold evalAngle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem evalAngle_neg {n : ℕ} (f : Fin n → ℝ) (θ : ℝ) :
    evalAngle (fun i => -f i) θ = -evalAngle f θ := by
  unfold evalAngle
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem evalAngle_add_two_pi {n : ℕ} (f : Fin n → ℝ) (θ : ℝ) :
    evalAngle f (θ + 2 * Real.pi) = evalAngle f θ := by
  unfold evalAngle
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [show ((((i.1 : ℝ) * (θ + 2 * Real.pi) : ℝ)) : ℂ) * I =
      (((i.1 : ℝ) * θ : ℝ) : ℂ) * I + (i.1 : ℂ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-! ## Root angles are roots of `X^n + 1` -/

theorem exp_rootAngle : ∀ (k j : ℕ),
    Complex.exp ((((2 * 2 ^ k : ℕ) : ℝ) * rootAngle k j : ℝ) * I) = -1
  | 0, j => by
    have h : (((2 * 2 ^ 0 : ℕ) : ℝ) * rootAngle 0 j : ℝ) = Real.pi := by
      simp only [rootAngle_zero]
      push_cast
      ring
    rw [h]
    exact Complex.exp_pi_mul_I
  | k + 1, j => by
    have h : (((2 * 2 ^ (k + 1) : ℕ) : ℝ) * rootAngle (k + 1) j : ℝ) =
        (((2 * 2 ^ k : ℕ) : ℝ) * rootAngle k (j / 2) : ℝ) +
          (((2 ^ (k + 1) * (j % 2) : ℕ) : ℝ) * (2 * Real.pi) : ℝ) := by
      simp only [rootAngle]
      push_cast
      ring
    rw [h, Complex.ofReal_add, add_mul, Complex.exp_add, exp_rootAngle k (j / 2)]
    rw [show (((((2 ^ (k + 1) * (j % 2) : ℕ) : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * I =
        ((2 ^ (k + 1) * (j % 2) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_nat_mul_two_pi_mul_I]
    ring

/-! ## Evaluation is a ring homomorphism on the roots of `X^n + 1` -/

theorem evalAngle_negacyclicConvCoeff {n : ℕ} (a b : Fin n → ℝ) (θ : ℝ)
    (hθ : Complex.exp ((((n : ℕ) : ℝ) * θ : ℝ) * I) = -1) :
    evalAngle (fun m => LatticeCrypto.negacyclicConvCoeff a b m) θ =
      evalAngle a θ * evalAngle b θ := by
  unfold evalAngle
  set E : ℕ → ℂ := fun m => Complex.exp (((m : ℝ) * θ : ℝ) * I) with hE
  have hEmul : ∀ i j : ℕ, E (i + j) = E i * E j := by
    intro i j
    simp only [hE]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEn : E n = -1 := hθ
  change ∑ m : Fin n, ((LatticeCrypto.negacyclicConvCoeff a b m : ℝ) : ℂ) * E m.1 =
    (∑ m : Fin n, (a m : ℂ) * E m.1) * ∑ m : Fin n, (b m : ℂ) * E m.1
  rw [Finset.sum_mul_sum]
  simp only [LatticeCrypto.negacyclicConvCoeff, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hn : 0 < n := Fin.pos i
  set t : Fin n := ⟨(i.1 + j.1) % n, Nat.mod_lt _ hn⟩ with ht
  set s : ℝ := if i.1 + j.1 < n then a i * b j else -(a i * b j) with hs
  have hterm : ∀ m : Fin n,
      ((if (i.1 + j.1) % n = m.1 then s else 0 : ℝ) : ℂ) * E m.1 =
        if m = t then (s : ℂ) * E t.1 else 0 := by
    intro m
    by_cases hm : m = t
    · subst hm
      simp [ht]
    · have : (i.1 + j.1) % n ≠ m.1 := fun h => hm (Fin.ext h.symm)
      simp [this, hm]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hlt : i.1 + j.1 < n
  · have ht' : t.1 = i.1 + j.1 := Nat.mod_eq_of_lt hlt
    rw [ht', hEmul]
    simp only [hs, if_pos hlt]
    push_cast
    ring
  · rw [not_lt] at hlt
    have ht' : t.1 = i.1 + j.1 - n := by
      change (i.1 + j.1) % n = _
      rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt (by omega)]
    have hsplit : (a i : ℂ) * E i.1 * ((b j : ℂ) * E j.1) =
        ((a i * b j : ℝ) : ℂ) * (E (i.1 + j.1 - n) * E n) := by
      rw [← hEmul, Nat.sub_add_cancel hlt, hEmul]
      push_cast
      ring
    rw [ht', hsplit, hEn]
    simp only [hs, if_neg (not_lt.mpr hlt)]
    push_cast
    ring

/-! ## The packed FFT of a real polynomial -/

namespace RealFFTPoly

variable {k : ℕ}

/-- The packed FFT representation of the real polynomial with coefficient function `f`, built by
the merge recursion of the specification. -/
noncomputable def ofCoeffs : (k : ℕ) → (Fin (2 * 2 ^ k) → ℝ) → RealFFTPoly k
  | 0, f =>
      pack (Vector.ofFn fun _ => f ⟨0, by norm_num⟩) (Vector.ofFn fun _ => f ⟨1, by norm_num⟩)
  | k + 1, f =>
      Primitives.mergeFFT
        (ofCoeffs k fun i => f ⟨2 * i.1, by have := i.2; have := two_pow_succ_eq k; omega⟩)
        (ofCoeffs k fun i => f ⟨2 * i.1 + 1, by have := i.2; have := two_pow_succ_eq k; omega⟩)

/-- The coefficients recovered from a packed FFT representation by the split recursion of the
specification. -/
noncomputable def toCoeffs : (k : ℕ) → RealFFTPoly k → (Fin (2 * 2 ^ k) → ℝ)
  | 0, v => fun i => v.get i
  | k + 1, v => fun i =>
      if i.1 % 2 = 0 then
        toCoeffs k (Primitives.splitFFT v).1
          ⟨i.1 / 2, by have := i.2; have := two_pow_succ_eq k; omega⟩
      else
        toCoeffs k (Primitives.splitFFT v).2
          ⟨i.1 / 2, by have := i.2; have := two_pow_succ_eq k; omega⟩

/-- **The packed FFT is an evaluation map.** Coordinate `j` at level `k` is the value of the
polynomial at `exp(rootAngle k j · I)`. -/
theorem coord_ofCoeffs : ∀ (k : ℕ) (f : Fin (2 * 2 ^ k) → ℝ) (j : Fin (2 ^ k)),
    coord (ofCoeffs k f) j = evalAngle f (rootAngle k j.1)
  | 0, f, j => by
    have hj : j = ⟨0, by norm_num⟩ := Fin.ext (by have := j.2; simp at this; omega)
    subst hj
    rw [ofCoeffs, coord_pack]
    unfold evalAngle
    rw [sum_univ_two_mul (N := 1) (by norm_num), Fin.sum_univ_one]
    apply Complex.ext
    · simp
    · simp
  | k + 1, f, j => by
    rcases Nat.even_or_odd' j.1 with ⟨i, hi | hi⟩
    · have hi' : i < 2 ^ k := by have := j.2; have := two_pow_succ_eq k; omega
      have hj : j = ⟨2 * i, by have := two_pow_succ_eq k; omega⟩ := Fin.ext hi
      rw [hj, ofCoeffs, coord_mergeFFT_even _ _ i hi', coord_ofCoeffs k, coord_ofCoeffs k,
        evalAngle_two_mul (n := 2 * 2 ^ (k + 1)) (N := 2 * 2 ^ k) (by ring)]
      simp only [rootAngle_two_mul, Primitives.splitAngle]
      rw [show 2 * (rootAngle k i / 2) = rootAngle k i by ring]
    · have hi' : i < 2 ^ k := by have := j.2; have := two_pow_succ_eq k; omega
      have hj : j = ⟨2 * i + 1, by have := two_pow_succ_eq k; omega⟩ := Fin.ext hi
      rw [hj, ofCoeffs, coord_mergeFFT_odd _ _ i hi', coord_ofCoeffs k, coord_ofCoeffs k,
        evalAngle_two_mul (n := 2 * 2 ^ (k + 1)) (N := 2 * 2 ^ k) (by ring)]
      simp only [rootAngle_two_mul_add_one, Primitives.splitAngle]
      rw [show 2 * (rootAngle k i / 2 + Real.pi) = rootAngle k i + 2 * Real.pi by ring,
        evalAngle_add_two_pi, evalAngle_add_two_pi, Complex.ofReal_add, add_mul, Complex.exp_add,
        Complex.exp_pi_mul_I]
      ring

/-- **The packed FFT is multiplicative.** Negacyclic multiplication of coefficient functions
becomes the pointwise complex multiplication `Primitives.mulFFT`. -/
theorem ofCoeffs_negacyclic (k : ℕ) (a b : Fin (2 * 2 ^ k) → ℝ) :
    ofCoeffs k (fun m => LatticeCrypto.negacyclicConvCoeff a b m) =
      Primitives.mulFFT (ofCoeffs k a) (ofCoeffs k b) := by
  apply ext_coord
  intro j
  rw [coord_mulFFT, coord_ofCoeffs, coord_ofCoeffs, coord_ofCoeffs,
    evalAngle_negacyclicConvCoeff a b _ (exp_rootAngle k j.1)]

theorem ofCoeffs_add (k : ℕ) (a b : Fin (2 * 2 ^ k) → ℝ) :
    ofCoeffs k (fun m => a m + b m) = ofCoeffs k a + ofCoeffs k b := by
  apply ext_coord
  intro j
  rw [coord_add, coord_ofCoeffs, coord_ofCoeffs, coord_ofCoeffs, evalAngle_add]

theorem ofCoeffs_neg (k : ℕ) (a : Fin (2 * 2 ^ k) → ℝ) :
    ofCoeffs k (fun m => -a m) = -ofCoeffs k a := by
  apply ext_coord
  intro j
  rw [coord_neg, coord_ofCoeffs, coord_ofCoeffs, evalAngle_neg]

/-! ## The split recursion inverts the merge recursion -/

theorem splitFFT_mergeFFT (f₀ f₁ : RealFFTPoly k) :
    Primitives.splitFFT (Primitives.mergeFFT f₀ f₁) = (f₀, f₁) := by
  refine Prod.ext (ext_coord fun i => ?_) (ext_coord fun i => ?_)
  · apply Complex.ext <;>
      simp [coord, Primitives.splitFFT, Primitives.mergeFFT, Nat.mul_add_div]
  · apply Complex.ext
    · simp only [coord, Primitives.splitFFT, Primitives.mergeFFT, dite_eq_ite, re_pack,
        Vector.get_ofFn, Nat.mul_mod_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, Fin.eta, Nat.mul_add_mod_self_left, Nat.mod_succ,
        one_ne_zero, gt_iff_lt, Order.lt_two_iff, zero_le, Nat.mul_add_div, Nat.reduceDiv, add_zero,
        add_add_sub_cancel, add_self_div_two, im_pack, add_sub_sub_cancel]
      linear_combination f₁.re i * Real.cos_sq_add_sin_sq (Primitives.splitAngle i)
    · simp only [coord, Primitives.splitFFT, Primitives.mergeFFT, dite_eq_ite, re_pack,
        Vector.get_ofFn, Nat.mul_mod_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, Fin.eta, Nat.mul_add_mod_self_left, Nat.mod_succ,
        one_ne_zero, gt_iff_lt, Order.lt_two_iff, zero_le, Nat.mul_add_div, Nat.reduceDiv, add_zero,
        add_add_sub_cancel, add_self_div_two, im_pack, add_sub_sub_cancel]
      linear_combination f₁.im i * Real.cos_sq_add_sin_sq (Primitives.splitAngle i)

theorem toCoeffs_ofCoeffs : ∀ (k : ℕ) (f : Fin (2 * 2 ^ k) → ℝ), toCoeffs k (ofCoeffs k f) = f
  | 0, f => by
    funext i
    rcases i with ⟨m, hm⟩
    have hm' : m = 0 ∨ m = 1 := by norm_num at hm; omega
    rcases hm' with rfl | rfl
    · change (pack _ _).re ⟨0, by norm_num⟩ = _
      rw [re_pack]
      simp
    · change (pack _ _).im ⟨0, by norm_num⟩ = _
      rw [im_pack]
      simp
  | k + 1, f => by
    funext i
    simp only [toCoeffs, ofCoeffs, splitFFT_mergeFFT, toCoeffs_ofCoeffs k]
    split_ifs with h
    · congr 1
      ext
      simp only
      omega
    · congr 1
      ext
      simp only
      omega

/-! ## Interleaving even and odd coefficients -/

/-- The coefficient function whose even coefficients are `a` and odd coefficients are `b`. -/
def interleave {α : Type*} (k : ℕ) (a b : Fin (2 * 2 ^ k) → α) : Fin (2 * 2 ^ (k + 1)) → α :=
  fun i =>
    if i.1 % 2 = 0 then a ⟨i.1 / 2, by have := i.2; have := two_pow_succ_eq k; omega⟩
    else b ⟨i.1 / 2, by have := i.2; have := two_pow_succ_eq k; omega⟩

theorem interleave_cast (k : ℕ) (a b : Fin (2 * 2 ^ k) → ℤ) :
    (fun i => ((interleave k a b i : ℤ) : ℝ)) =
      interleave k (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) := by
  funext i
  simp only [interleave]
  split_ifs <;> rfl

theorem ofCoeffs_interleave (k : ℕ) (a b : Fin (2 * 2 ^ k) → ℝ) :
    ofCoeffs (k + 1) (interleave k a b) = Primitives.mergeFFT (ofCoeffs k a) (ofCoeffs k b) := by
  simp only [ofCoeffs]
  congr 1
  · congr 1
    funext i
    simp [interleave]
  · congr 1
    funext i
    simp [interleave, Nat.mul_add_div]

end RealFFTPoly

/-! ## The sampler outputs packed FFTs of integer polynomials -/

/-- **Every `ffSampling` output is the packed FFT of a pair of integer polynomials.** The leaves
sample integers into both coordinates and the nodes merge. -/
theorem Primitives.ffSampling_support_ofCoeffs {p : Params} (prims : Primitives p) :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ) (z : FFTPair κ),
      z ∈ support (prims.ffSampling κ t tree) →
        ∃ a b : Fin (2 * 2 ^ κ) → ℤ,
          z.1 = RealFFTPoly.ofCoeffs κ (fun i => (a i : ℝ)) ∧
          z.2 = RealFFTPoly.ofCoeffs κ (fun i => (b i : ℝ))
  | 0, (t₀, t₁), .leaf σ, z, hz => by
    simp only [Primitives.ffSampling, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨z₀Re, -, z₀Im, -, z₁Re, -, z₁Im, -, rfl⟩ := hz
    refine ⟨fun i => if i.1 = 0 then z₀Re else z₀Im, fun i => if i.1 = 0 then z₁Re else z₁Im,
      ?_, ?_⟩ <;> simp [RealFFTPoly.ofCoeffs]
  | k + 1, (t₀, t₁), .node ℓ left right, z, hz => by
    simp only [Primitives.ffSampling, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨z₁Split, hz₁, z₀Split, hz₀, rfl⟩ := hz
    obtain ⟨a₁, b₁, ha₁, hb₁⟩ := ffSampling_support_ofCoeffs prims k _ right z₁Split hz₁
    obtain ⟨a₀, b₀, ha₀, hb₀⟩ := ffSampling_support_ofCoeffs prims k _ left z₀Split hz₀
    refine ⟨RealFFTPoly.interleave k a₀ b₀, RealFFTPoly.interleave k a₁ b₁, ?_, ?_⟩
    · rw [RealFFTPoly.interleave_cast, RealFFTPoly.ofCoeffs_interleave, ← ha₀, ← hb₀]
    · rw [RealFFTPoly.interleave_cast, RealFFTPoly.ofCoeffs_interleave, ← ha₁, ← hb₁]

/-! ## Specification-level FFT primitives -/

namespace Primitives

variable (p : Params)

/-- The exact `fftTarget`: the packed FFT of the hash target, coefficients read as the integers
in `[0, q)` of the reference `hm` array. Degenerate parameters with `p.n ≠ 2 * 2 ^ p.fftDepth`
map to `0`. -/
noncomputable def exactFftTarget (c : Rq p.n) : RealFFTPoly p.fftDepth :=
  if h : 2 * 2 ^ p.fftDepth = p.n then
    RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast h i)).val : ℕ) : ℝ)
  else 0

/-- The exact `fftInt`: the packed FFT of an integer polynomial. -/
noncomputable def exactFftInt (f : IntPoly p.n) : RealFFTPoly p.fftDepth :=
  if h : 2 * 2 ^ p.fftDepth = p.n then
    RealFFTPoly.ofCoeffs p.fftDepth fun i => (f.get (Fin.cast h i) : ℝ)
  else 0

/-- The exact `ifftRound`: the coefficients recovered by the split recursion, rounded to the
nearest integer. -/
noncomputable def exactIfftRound (v : RealFFTPoly p.fftDepth) : IntPoly p.n :=
  if h : 2 * 2 ^ p.fftDepth = p.n then
    LatticeCrypto.Poly.ofPi fun i =>
      round (RealFFTPoly.toCoeffs p.fftDepth v (Fin.cast h.symm i))
  else 0

/-- A primitive bundle whose `fftInt` and `ifftRound` are the exact packed FFT of the
specification. `hn` identifies the ring degree with the packed length. -/
structure ExactFFT {p : Params} (prims : Primitives p) (hn : 2 * 2 ^ p.fftDepth = p.n) :
    Prop where
  fftInt_eq : ∀ f : IntPoly p.n,
    prims.fftInt f = RealFFTPoly.ofCoeffs p.fftDepth fun i => (f.get (Fin.cast hn i) : ℝ)
  ifftRound_eq : ∀ v : RealFFTPoly p.fftDepth,
    prims.ifftRound v =
      LatticeCrypto.Poly.ofPi fun i =>
        round (RealFFTPoly.toCoeffs p.fftDepth v (Fin.cast hn.symm i))

theorem exactFftInt_eq (hn : 2 * 2 ^ p.fftDepth = p.n) (f : IntPoly p.n) :
    exactFftInt p f = RealFFTPoly.ofCoeffs p.fftDepth fun i => (f.get (Fin.cast hn i) : ℝ) := by
  simp [exactFftInt, hn]

theorem exactIfftRound_eq (hn : 2 * 2 ^ p.fftDepth = p.n) (v : RealFFTPoly p.fftDepth) :
    exactIfftRound p v =
      LatticeCrypto.Poly.ofPi fun i =>
        round (RealFFTPoly.toCoeffs p.fftDepth v (Fin.cast hn.symm i)) := by
  simp [exactIfftRound, hn]

/-- Any bundle built from the exact fields satisfies `ExactFFT`. -/
theorem exactFFT_of_eq {p : Params} (prims : Primitives p) (hn : 2 * 2 ^ p.fftDepth = p.n)
    (hfft : prims.fftInt = exactFftInt p) (hifft : prims.ifftRound = exactIfftRound p) :
    prims.ExactFFT hn :=
  ⟨fun f => by rw [hfft, exactFftInt_eq p hn], fun v => by rw [hifft, exactIfftRound_eq p hn]⟩

end Primitives

end Falcon

end
