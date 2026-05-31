/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Arithmetic
import LatticeCrypto.Ring.VectorCommRing

/-!
# Ajtai Gadget Matrices

The main object is `Ajtai.gadgetMatrix ring base rows digits`, the block diagonal
gadget matrix `I_rows ⊗ [1, base, base^2, ..., base^(digits - 1)]`. It maps
`rows * digits` ring elements to `rows` ring elements and is used by the
inner-outer Hachi commitment layer. `Ajtai.IsLawfulGadgetDecomposition` records
when a decomposition is inverted by gadget multiplication.

The final section provides the canonical **base-two** gadget decomposition over
`vectorNegacyclicRing (ZMod q) d` — the binary digit expansion of each
coefficient — and proves it is lawful for `gadgetMatrix … (2 : ZMod q)` whenever
the number of digits covers the modulus (`q ≤ 2 ^ digits`). This is the gadget
`G_n := I_n ⊗ [1, 2, 4, ..., 2^(δ-1)]` of the Hachi paper (Nguyen, O'Rourke,
Zhang) together with its decomposition `G_n⁻¹`.
-/

open scoped BigOperators

universe u

namespace LatticeCrypto
namespace Ajtai

variable {Coeff : Type u} [CommRing Coeff]

/-- Entry of the base-`base` gadget matrix `I_rows ⊗ [1, base, ..., base^(digits-1)]`. -/
def gadgetEntry (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat} (i : Fin rows) (j : Fin (rows * digits)) : ring.Poly :=
  if j.val / digits = i.val then
    ring.scalarPoly (base ^ (j.val % digits))
  else
    ring.zero

/-- The base-`base` gadget matrix `I_rows ⊗ [1, base, ..., base^(digits-1)]`. -/
def gadgetMatrix (ring : NegacyclicRing Coeff) (base : Coeff)
    (rows digits : Nat) : PolyMatrix ring.Poly rows (rows * digits) :=
  Vector.ofFn fun i => Vector.ofFn fun j => gadgetEntry ring base i j

/-- Apply the gadget matrix to a decomposed vector. -/
def gadgetMul (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat} (v : PolyVec ring.Poly (rows * digits)) : PolyVec ring.Poly rows :=
  ring.matVecMul (gadgetMatrix ring base rows digits) v

/-- A gadget decomposition is lawful when gadget multiplication reconstructs its input. -/
def IsLawfulGadgetDecomposition (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat}
    (decompose : PolyVec ring.Poly rows → PolyVec ring.Poly (rows * digits)) : Prop :=
  ∀ x, gadgetMul ring base (decompose x) = x

/-! ## Base-two gadget decomposition over `vectorNegacyclicRing (ZMod q) d`

We give the canonical base-two decomposition `binaryDecompose` and prove it is
lawful for `gadgetMatrix … (2 : ZMod q)` whenever `q ≤ 2 ^ digits`. The proof
reduces gadget multiplication to a per-coefficient binary reconstruction.
-/

section Base2

open Finset

variable {q : ℕ} {n : ℕ}

/-- Coefficient-level reading of ring multiplication on the vector backend. -/
theorem vectorRing_mul_get {Coeff : Type u} [CommRing Coeff]
    (f g : (vectorNegacyclicRing Coeff n).Poly) (k : Fin n) :
    ((vectorNegacyclicRing Coeff n).mul f g).get k
      = negacyclicConvCoeff (fun t => f.get t) (fun t => g.get t) k := by
  change Vector.get (negacyclicMulPure (vectorKernel Coeff n) f g) k = _
  unfold negacyclicMulPure
  simp only [vectorBackend, Vector.get_ofFn]

/-- Multiplying by `scalarPoly c` scales each coefficient by `c`. -/
theorem scalarPoly_mul_get {Coeff : Type u} [CommRing Coeff] [NeZero n]
    (c : Coeff) (p : (vectorNegacyclicRing Coeff n).Poly) (k : Fin n) :
    ((vectorNegacyclicRing Coeff n).mul ((vectorNegacyclicRing Coeff n).scalarPoly c) p).get k
      = c * p.get k := by
  rw [vectorRing_mul_get]
  unfold negacyclicConvCoeff
  rw [Fintype.sum_eq_single (⟨⟨0, NeZero.pos n⟩, k⟩ : Fin n × Fin n)]
  · have h0 : ((vectorNegacyclicRing Coeff n).scalarPoly c).get ⟨0, NeZero.pos n⟩ = c := by
      rw [get_scalarPoly]; simp
    simp only [h0]
    rw [Nat.zero_add, Nat.mod_eq_of_lt k.isLt, if_pos rfl, if_pos k.isLt]
  · rintro ⟨a, b⟩ hab
    by_cases ha : a.val = 0
    · have hbk : b ≠ k := by
        rintro rfl
        exact hab (by ext <;> simp [ha])
      have : (a.val + b.val) % n ≠ k.val := by
        rw [ha, Nat.zero_add, Nat.mod_eq_of_lt b.isLt]
        exact fun h => hbk (Fin.ext h)
      simp [this]
    · have hzero : ((vectorNegacyclicRing Coeff n).scalarPoly c).get a = 0 := by
        rw [get_scalarPoly]; simp [ha]
      by_cases hcond : (a.val + b.val) % n = k.val <;>
        simp [hcond, hzero]

/-- Base-`a` carry/remainder split of a modulus. -/
private theorem nat_mod_mul (m a b : ℕ) :
    m % (a * b) = m % a + a * (m / a % b) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    rw [Nat.mul_zero, Nat.mod_zero, Nat.mod_zero]
    exact (Nat.mod_add_div m a).symm
  have hrb : m / a % b < b := Nat.mod_lt _ hb
  have hm : m = (m % a + a * (m / a % b)) + a * b * (m / a / b) := by
    conv_lhs => rw [← Nat.div_add_mod m a, ← Nat.div_add_mod (m / a) b]
    ring
  have hlt : m % a + a * (m / a % b) < a * b := by
    have h1 : m / a % b + 1 ≤ b := hrb
    calc m % a + a * (m / a % b) < a + a * (m / a % b) := by
            have := Nat.mod_lt m ha; omega
      _ = a * (m / a % b + 1) := by ring
      _ ≤ a * b := Nat.mul_le_mul (le_refl a) h1
  have hsplit : m % (a * b) = (m % a + a * (m / a % b)) % (a * b) := by
    conv_lhs => rw [hm]
    rw [Nat.add_mul_mod_self_left]
  rw [hsplit, Nat.mod_eq_of_lt hlt]

/-- Binary reconstruction of a natural number from its first `D` bits. -/
private theorem sum_two_pow_digit (D m : ℕ) :
    ∑ e ∈ range D, 2 ^ e * (m / 2 ^ e % 2) = m % 2 ^ D := by
  induction D with
  | zero => simp [Nat.mod_one]
  | succ D ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, nat_mod_mul]

/-- Binary reconstruction of a `ZMod q` element when `q ≤ 2 ^ D`. -/
theorem zmod_sum_two_pow_digit [NeZero q] (D : ℕ) (hq : q ≤ 2 ^ D) (x : ZMod q) :
    ∑ e ∈ range D, (2 : ZMod q) ^ e * ((x.val / 2 ^ e % 2 : ℕ) : ZMod q) = x := by
  have hlt : x.val < 2 ^ D := lt_of_lt_of_le (ZMod.val_lt x) hq
  have hnat := sum_two_pow_digit D x.val
  rw [Nat.mod_eq_of_lt hlt] at hnat
  have hcast : ((∑ e ∈ range D, 2 ^ e * (x.val / 2 ^ e % 2) : ℕ) : ZMod q)
      = ∑ e ∈ range D, (2 : ZMod q) ^ e * ((x.val / 2 ^ e % 2 : ℕ) : ZMod q) := by
    push_cast
    rfl
  rw [← hcast, hnat, ZMod.natCast_rightInverse x]

/-- `* `-form of `scalarPoly_mul_get` (the `CommRing` product is `ring.mul`). -/
theorem scalarPoly_hmul_get [NeZero n] [Fact (1 < q)] (c : ZMod q)
    (p : (vectorNegacyclicRing (ZMod q) n).Poly) (k : Fin n) :
    ((vectorNegacyclicRing (ZMod q) n).scalarPoly c * p).get k = c * p.get k :=
  scalarPoly_mul_get c p k

/-- Coefficient read-off as an additive hom, used to push `.get` through finite sums. -/
def getAddHom (k : Fin n) : (vectorNegacyclicRing (ZMod q) n).Poly →+ ZMod q where
  toFun p := p.get k
  map_zero' := Poly.get_zero k
  map_add' p p' := vectorRing_add_get p p' k

/-- `.get k` commutes with finite sums of polynomials. -/
theorem get_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → (vectorNegacyclicRing (ZMod q) n).Poly) (k : Fin n) :
    (∑ i ∈ s, f i).get k = ∑ i ∈ s, (f i).get k :=
  map_sum (getAddHom k) f s

/-- The row index `j / digits` of a gadget column `j` is a valid row. -/
theorem div_lt_rows {rows digits : ℕ} (j : Fin (rows * digits)) :
    j.val / digits < rows := by
  have hpos : 0 < digits :=
    Nat.pos_of_ne_zero (by rintro rfl; exact absurd j.isLt (by simp))
  exact (Nat.div_lt_iff_lt_mul hpos).mpr j.isLt

/-- Reindexing the gadget-row dot product: the only contributing columns of row
`r` are `r * digits + e` for `e < digits`, giving the per-digit sum. -/
theorem gadget_index_sum {rows digits : ℕ} (hdigits : 0 < digits)
    (r : ℕ) (hr : r < rows) (G : ℕ → ZMod q) :
    (∑ j : Fin (rows * digits),
        (if j.val / digits = r then G (j.val % digits) else 0))
      = ∑ e ∈ range digits, G e := by
  rw [← Equiv.sum_comp finProdFinEquiv
        (fun j : Fin (rows * digits) =>
          if j.val / digits = r then G (j.val % digits) else 0),
    Fintype.sum_prod_type]
  have hbody : ∀ (i : Fin rows) (e : Fin digits),
      (if (finProdFinEquiv (i, e)).val / digits = r
          then G ((finProdFinEquiv (i, e)).val % digits) else 0)
        = (if i.val = r then G e.val else 0) := by
    intro i e
    have hv : (finProdFinEquiv (i, e)).val = e.val + digits * i.val := rfl
    rw [hv, Nat.add_mul_div_left _ _ hdigits, Nat.add_mul_mod_self_left,
      Nat.div_eq_of_lt e.isLt, Nat.zero_add, Nat.mod_eq_of_lt e.isLt]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun e _ => hbody i e))]
  rw [Finset.sum_eq_single (⟨r, hr⟩ : Fin rows)]
  · rw [show (∑ e : Fin digits, (if (⟨r, hr⟩ : Fin rows).val = r then G e.val else 0))
          = ∑ e : Fin digits, G e.val from
        Finset.sum_congr rfl (fun e _ => if_pos rfl)]
    exact Fin.sum_univ_eq_sum_range (fun e => G e) digits
  · intro i _ hir
    have hne : i.val ≠ r := fun h => hir (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The `e`-th binary digit-plane of `p`: its `k`-th coefficient is the `e`-th bit
of the `k`-th coefficient of `p`. -/
def binaryDigitPlane (p : (vectorNegacyclicRing (ZMod q) n).Poly) (e : ℕ) :
    (vectorNegacyclicRing (ZMod q) n).Poly :=
  Vector.ofFn fun k => (((p.get k).val / 2 ^ e % 2 : ℕ) : ZMod q)

@[simp]
theorem binaryDigitPlane_get (p : (vectorNegacyclicRing (ZMod q) n).Poly) (e : ℕ) (k : Fin n) :
    (binaryDigitPlane p e).get k = (((p.get k).val / 2 ^ e % 2 : ℕ) : ZMod q) :=
  Vector.get_ofFn _ k

/-- The canonical base-two gadget decomposition: column `r * digits + e` holds the
`e`-th binary digit-plane of row `r`. -/
def binaryDecompose (rows digits : ℕ)
    (x : PolyVec (vectorNegacyclicRing (ZMod q) n).Poly rows) :
    PolyVec (vectorNegacyclicRing (ZMod q) n).Poly (rows * digits) :=
  Vector.ofFn fun j =>
    binaryDigitPlane (x.get ⟨j.val / digits, div_lt_rows j⟩) (j.val % digits)

/-- The base-two binary decomposition inverts the base-two gadget matrix, i.e. it is
a lawful gadget decomposition for `gadgetMatrix … (2 : ZMod q)`, provided the number
of digits covers the modulus (`q ≤ 2 ^ digits`). This is `G_n⁻¹` of the Hachi paper. -/
theorem binaryDecompose_lawful [NeZero q] [Fact (1 < q)] [NeZero n]
    (rows digits : ℕ) (hdigits : 0 < digits) (hq : q ≤ 2 ^ digits) :
    IsLawfulGadgetDecomposition (vectorNegacyclicRing (ZMod q) n) (2 : ZMod q)
      (binaryDecompose (q := q) (n := n) rows digits) := by
  intro x
  refine Vector.ext (fun r hr => ?_)
  refine Poly.ext_get_eq (fun k => ?_)
  unfold gadgetMul
  rw [matVecMul_getElem _ _ hr, dot_eq_sum, get_finsetSum]
  have hsummand : ∀ j : Fin (rows * digits),
      (((gadgetMatrix (vectorNegacyclicRing (ZMod q) n) (2 : ZMod q) rows digits)[r]'hr).get j
          * (binaryDecompose (q := q) (n := n) rows digits x).get j).get k
        = (if j.val / digits = r
            then (2 : ZMod q) ^ (j.val % digits)
              * ((((x[r]'hr).get k).val / 2 ^ (j.val % digits) % 2 : ℕ) : ZMod q)
            else 0) := by
    intro j
    have hentry :
        ((gadgetMatrix (vectorNegacyclicRing (ZMod q) n) (2 : ZMod q) rows digits)[r]'hr).get j
          = gadgetEntry (vectorNegacyclicRing (ZMod q) n) (2 : ZMod q) (⟨r, hr⟩ : Fin rows) j := by
      simp only [gadgetMatrix, Vector.getElem_ofFn, Vector.get_ofFn]
    have hdec :
        (binaryDecompose (q := q) (n := n) rows digits x).get j
          = binaryDigitPlane (x.get ⟨j.val / digits, div_lt_rows j⟩) (j.val % digits) := by
      simp only [binaryDecompose, Vector.get_ofFn]
    rw [hentry, hdec, gadgetEntry]
    by_cases hj : j.val / digits = r
    · rw [if_pos hj, if_pos hj, scalarPoly_hmul_get, binaryDigitPlane_get]
      have hidx : (⟨j.val / digits, div_lt_rows j⟩ : Fin rows) = ⟨r, hr⟩ := Fin.ext hj
      rw [hidx]
      rfl
    · rw [if_neg hj, if_neg hj]
      change ((vectorNegacyclicRing (ZMod q) n).mul (vectorNegacyclicRing (ZMod q) n).zero
          (binaryDigitPlane (x.get ⟨j.val / digits, div_lt_rows j⟩) (j.val % digits))).get k = 0
      rw [vectorRing_mul_get, negacyclicConvCoeff]
      simp
  rw [Finset.sum_congr rfl (fun j _ => hsummand j),
    gadget_index_sum hdigits r hr
      (fun e => (2 : ZMod q) ^ e * ((((x[r]'hr).get k).val / 2 ^ e % 2 : ℕ) : ZMod q))]
  exact zmod_sum_two_pow_digit digits hq ((x[r]'hr).get k)

end Base2

end Ajtai
end LatticeCrypto
