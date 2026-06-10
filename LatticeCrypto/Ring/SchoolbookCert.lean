/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Ring.VectorBackend
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Schoolbook Negacyclic Multiplication Soundness

Proves that `negacyclicMulPure` computes polynomial multiplication in the
quotient ring `R[X] / (X^n + 1)`. The proof decomposes into:

1. **Negacyclic quotient algebra**: `X^n ≡ -1` and derived monomial reduction.
2. **Product expansion**: the product of two monomial sums equals a double sum
   of monomial products.
3. **Negacyclic reduction**: relating the double sum to `negacyclicConvCoeff`.
4. **Assembly**: connecting the above to the `NegacyclicRingSemantics` obligation.
-/

open scoped BigOperators
open Polynomial

namespace LatticeCrypto

variable {R : Type*} [CommRing R] {n : Nat}

/-- Private alias for the canonical quotient map onto `R[X] / (X^n + 1)`. Reducible
so that proofs treat `mkQ R n p` and `Ideal.Quotient.mk (Ideal.span …) p` as the same
expression, while keeping local theorem statements compact. -/
private noncomputable abbrev mkQ (R : Type*) [CommRing R] (n : Nat) :
    Polynomial R →+* NegacyclicQuotient R n :=
  Ideal.Quotient.mk _

/-! ## Section 1: Negacyclic Quotient Algebra -/

/-- The negacyclic modulus `X^n + 1` maps to zero in the quotient. -/
theorem mk_negacyclicModulus_eq_zero :
    mkQ R n (negacyclicModulus R n) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- In `R[X]/(X^n + 1)`, `X^n = -1`. -/
theorem mk_X_pow_n : mkQ R n ((X : Polynomial R) ^ n) = -1 := by
  have h := mk_negacyclicModulus_eq_zero (R := R) (n := n)
  have h' : mkQ R n ((X : Polynomial R) ^ n) + 1 = 0 := by
    simpa [negacyclicModulus, map_add, map_one] using h
  exact (add_eq_zero_iff_eq_neg.mp h')

/-- In `R[X]/(X^n + 1)`, `X^(k + n) = -X^k`. -/
theorem mk_X_pow_add_n (k : Nat) :
    mkQ R n ((X : Polynomial R) ^ (k + n)) = -(mkQ R n (X ^ k)) := by
  rw [pow_add, map_mul, mk_X_pow_n]; ring

/-- In `R[X]/(X^n + 1)`, `monomial (k + n) c = -monomial k c`. -/
theorem mk_monomial_add_n (k : Nat) (c : R) :
    mkQ R n (Polynomial.monomial (k + n) c) =
      -(mkQ R n (Polynomial.monomial k c)) := by
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_mul,
    mk_X_pow_add_n]
  ring

/-! ## Section 2: Product Expansion -/

/-- The product of two `toPolynomial` sums equals a double sum of monomial products. -/
theorem toPolynomial_mul_eq_double_sum (backend : PolyBackend R) (f g : backend.Poly) :
    backend.toPolynomial f * backend.toPolynomial g =
      ∑ i : Fin backend.degree, ∑ j : Fin backend.degree,
        Polynomial.monomial (i.val + j.val) (backend.coeff f i * backend.coeff g j) := by
  simp only [PolyBackend.toPolynomial, Finset.sum_mul_sum, Polynomial.monomial_mul_monomial]

/-! ## Section 3: Negacyclic Reduction -/

/-- The key algebraic step: the double sum of monomial products maps to the
same quotient element as the negacyclic convolution polynomial. -/
theorem mk_double_sum_eq_mk_negacyclicConv (hn : 0 < n) (f g : Fin n → R) :
    mkQ R n (∑ i : Fin n, ∑ j : Fin n,
        Polynomial.monomial (i.val + j.val) (f i * g j)) =
    mkQ R n (∑ k : Fin n, Polynomial.monomial k.val (negacyclicConvCoeff f g k)) := by
  have h_reduction : ∀ i j : Fin n,
      mkQ R n (Polynomial.monomial (i.val + j.val) (f i * g j)) =
      mkQ R n (Polynomial.monomial ((i.val + j.val) % n)
          (if i.val + j.val < n then f i * g j else -(f i * g j))) := by
    intro i j
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · have h_neg : mkQ R n (Polynomial.monomial (n + (i.val + j.val - n)) (f i * g j)) =
          mkQ R n (-Polynomial.monomial ((i.val + j.val - n)) (f i * g j)) := by
        simpa [Nat.add_comm] using
          mk_monomial_add_n (i.val + j.val - n) (f i * g j)
      have hle : n ≤ i.val + j.val := le_of_not_gt h
      have hlt : i.val + j.val - n < n := by
        rw [tsub_lt_iff_left hle]
        linarith [Fin.is_lt i, Fin.is_lt j]
      have hmod : (i.val + j.val) % n = i.val + j.val - n := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt]
      simpa [Nat.add_sub_of_le hle, h, hmod] using h_neg
  calc
    mkQ R n (∑ i : Fin n, ∑ j : Fin n,
          Polynomial.monomial (i.val + j.val) (f i * g j)) =
      ∑ i : Fin n, ∑ j : Fin n,
        mkQ R n (Polynomial.monomial (i.val + j.val) (f i * g j)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sum]
    _ =
      ∑ i : Fin n, ∑ j : Fin n,
        mkQ R n (Polynomial.monomial ((i.val + j.val) % n)
            (if i.val + j.val < n then f i * g j else -(f i * g j))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          exact h_reduction i j
    _ =
      ∑ x ∈ Finset.univ ×ˢ Finset.univ,
        mkQ R n (Polynomial.monomial ((x.1.val + x.2.val) % n)
            (if x.1.val + x.2.val < n then f x.1 * g x.2 else -(f x.1 * g x.2))) := by
          rw [← Finset.sum_product']
    _ =
      ∑ x ∈ Finset.univ ×ˢ Finset.univ,
        ∑ k : Fin n,
          mkQ R n (Polynomial.monomial k.val
              (if (x.1.val + x.2.val) % n = k.val then
                if x.1.val + x.2.val < n then f x.1 * g x.2 else -(f x.1 * g x.2)
              else 0)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_eq_single ⟨(x.1.val + x.2.val) % n, Nat.mod_lt _ hn⟩]
          · simp
          · intro y hy hne
            have hne' : (x.1.val + x.2.val) % n ≠ y.val := by
              intro hEq
              apply hne
              exact Fin.ext hEq.symm
            simp [hne']
          · intro hnot
            exact (hnot (Finset.mem_univ _)).elim
    _ =
      ∑ k : Fin n,
        ∑ x ∈ Finset.univ ×ˢ Finset.univ,
          mkQ R n (Polynomial.monomial k.val
              (if (x.1.val + x.2.val) % n = k.val then
                if x.1.val + x.2.val < n then f x.1 * g x.2 else -(f x.1 * g x.2)
              else 0)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ k : Fin n,
        mkQ R n (∑ x ∈ Finset.univ ×ˢ Finset.univ,
            Polynomial.monomial k.val
              (if (x.1.val + x.2.val) % n = k.val then
                if x.1.val + x.2.val < n then f x.1 * g x.2 else -(f x.1 * g x.2)
              else 0)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_sum]
    _ =
      ∑ k : Fin n,
        mkQ R n (Polynomial.monomial k.val (negacyclicConvCoeff f g k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          let coeffTerm : Fin n × Fin n → R := fun x =>
            if (x.1.val + x.2.val) % n = k.val then
              if x.1.val + x.2.val < n then f x.1 * g x.2 else -(f x.1 * g x.2)
            else 0
          have h_monomial_sum :
              Polynomial.monomial k.val (∑ x : Fin n × Fin n, coeffTerm x) =
                ∑ x : Fin n × Fin n, Polynomial.monomial k.val (coeffTerm x) := by
            rw [← map_sum]
          exact congrArg (mkQ R n) h_monomial_sum.symm
    _ = mkQ R n (∑ k : Fin n, Polynomial.monomial k.val (negacyclicConvCoeff f g k)) := by
          rw [← map_sum]

/-! ## Section 4: Assembly -/

/-- `toPolynomial` of the pure negacyclic multiplication equals the
negacyclic convolution polynomial. -/
theorem negacyclicMulPure_toPolynomial (backend : PolyBackend R)
    (kernel : PolyKernel R backend) (f g : backend.Poly) :
    backend.toPolynomial (negacyclicMulPure kernel f g) =
      ∑ k : Fin backend.degree,
        Polynomial.monomial k.val
          (negacyclicConvCoeff (backend.coeff f) (backend.coeff g) k) := by
  simp [negacyclicMulPure, PolyBackend.toPolynomial]

/-- Soundness of `negacyclicMulPure`: its image in `R[X]/(X^n + 1)` equals the
product of the images. -/
theorem negacyclicMulPure_sound
    (backend : PolyBackend R) (kernel : PolyKernel R backend)
    (f g : backend.Poly) :
    NegacyclicQuotient.ofBackend backend (negacyclicMulPure kernel f g) =
      NegacyclicQuotient.ofBackend backend f *
        NegacyclicQuotient.ofBackend backend g := by
  simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial]
  rw [negacyclicMulPure_toPolynomial, ← map_mul, toPolynomial_mul_eq_double_sum]
  by_cases hn : 0 < backend.degree
  · exact (mk_double_sum_eq_mk_negacyclicConv hn _ _).symm
  · -- n = 0: both sums are over Fin 0, hence empty
    push Not at hn
    have hd : backend.degree = 0 := by omega
    haveI : IsEmpty (Fin backend.degree) := hd ▸ inferInstance
    simp [Finset.univ_eq_empty]

/-! ### `one_sound` for the vector backend -/

/-- The constant-`1` vector maps to `1` in `R[X] / (X^n + 1)` for `n > 0`.
For `n = 0`, `X^0 + 1 = 2` and `mk(0) = 1` fails for general `CommRing`
(e.g. `ℤ[X] / (2)`), so this theorem requires positivity. -/
private theorem vectorNegacyclicSemantics_one_sound
    (Coeff : Type*) [CommRing Coeff] {n : Nat} (hn : 0 < n) :
    NegacyclicQuotient.ofBackend (vectorBackend Coeff n)
        (vectorNegacyclicRing Coeff n).one = 1 := by
  simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial,
             PolyBackend.toPolynomial]
  have hcoeff : ∀ i : Fin n, (vectorBackend Coeff n).coeff (vectorNegacyclicRing Coeff n).one i =
      if i.val = 0 then 1 else 0 := fun i => by
    change (vectorNegacyclicRing Coeff n).one.get i = if i.val = 0 then 1 else 0
    simp [vectorNegacyclicRing, Vector.get, Array.getElem_ofFn]
  simp only [hcoeff, map_sum]
  rw [Finset.sum_eq_single_of_mem ⟨0, hn⟩ (Finset.mem_univ _)]
  · simp [Polynomial.monomial_zero_left, map_one]
  · intro ⟨j, hj⟩ _ hne
    simp only [Fin.mk.injEq, ne_eq] at hne
    simp [hne, map_zero]

/-- Proof-facing quotient interpretation for the canonical vector backend.

Maps each executable operation to its counterpart in the quotient ring
`R[X] / (X^n + 1)` and asserts soundness of the mapping.
Requires `0 < n` because `one_sound` fails for `n = 0` in general `CommRing`s. -/
noncomputable def vectorNegacyclicSemantics (Coeff : Type*) [CommRing Coeff]
    {n : Nat} (hn : 0 < n) :
    NegacyclicRingSemantics (vectorNegacyclicRing Coeff n) where
  quotientOf := NegacyclicQuotient.ofBackend (vectorBackend Coeff n)
  zero_sound := by
    unfold NegacyclicQuotient.ofBackend NegacyclicQuotient.ofPolynomial PolyBackend.toPolynomial
    simp [vectorBackend_coeff, Finset.sum_const_zero, map_zero]
    rfl
  one_sound := vectorNegacyclicSemantics_one_sound Coeff hn
  add_sound f g := by
    have hpoly : (vectorBackend Coeff n).toPolynomial ((vectorNegacyclicRing Coeff n).add f g) =
        (vectorBackend Coeff n).toPolynomial f + (vectorBackend Coeff n).toPolynomial g := by
      simp [PolyBackend.toPolynomial, vectorNegacyclicRing, vectorBackend,
            Vector.get, Finset.sum_add_distrib]
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, hpoly]
    exact map_add (Ideal.Quotient.mk _) _ _
  sub_sound f g := by
    have hpoly : (vectorBackend Coeff n).toPolynomial ((vectorNegacyclicRing Coeff n).sub f g) =
        (vectorBackend Coeff n).toPolynomial f - (vectorBackend Coeff n).toPolynomial g := by
      simp [PolyBackend.toPolynomial, vectorNegacyclicRing, vectorBackend,
            Vector.get, map_sub, Finset.sum_sub_distrib]
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, hpoly]
    exact map_sub (Ideal.Quotient.mk _) _ _
  neg_sound f := by
    have hpoly : (vectorBackend Coeff n).toPolynomial ((vectorNegacyclicRing Coeff n).neg f) =
        -(vectorBackend Coeff n).toPolynomial f := by
      simp [PolyBackend.toPolynomial, vectorNegacyclicRing, vectorBackend,
            Vector.get, map_neg, Finset.sum_neg_distrib]
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, hpoly]
    exact map_neg (Ideal.Quotient.mk _) _
  mul_sound f g := negacyclicMulPure_sound (vectorBackend Coeff n) (vectorKernel Coeff n) f g

/-! ### `CommRing` instance for the vector backend -/

/-- The vector-backed negacyclic ring carrier is a `CommRing`.

Each ring axiom is lifted from `NegacyclicQuotient` (a `CommRing`) via the injective
homomorphism `quotientOf = NegacyclicQuotient.ofBackend`. -/
noncomputable instance vectorNegacyclicRing_instCommRing (Coeff : Type*) [CommRing Coeff]
    (n : Nat) : CommRing (vectorNegacyclicRing Coeff n).Poly := by
  cases n with
  | zero =>
    haveI hss : Subsingleton (vectorNegacyclicRing Coeff 0).Poly :=
      ⟨fun a b => PolyBackend.ext_coeff fun i => i.elim0⟩
    exact { mul := (vectorNegacyclicRing Coeff 0).mul
            one := (vectorNegacyclicRing Coeff 0).one
            mul_assoc a b c:= hss.elim _ _
            one_mul a := hss.elim _ _
            mul_one a := hss.elim _ _
            mul_comm a b := hss.elim _ _
            left_distrib a b c:= hss.elim _ _
            right_distrib a b c:= hss.elim _ _
            zero_mul a := hss.elim _ _
            mul_zero a := hss.elim _ _
            npow k _ := if k = 0 then (vectorNegacyclicRing Coeff 0).one else 0
            npow_zero _ := rfl
            npow_succ k a := hss.elim _ _
            natCast _ := 0
            natCast_zero := rfl
            natCast_succ k := hss.elim _ _
            intCast _ := 0
            intCast_ofNat k := hss.elim _ _
            intCast_negSucc k := hss.elim _ _ }
  | succ m =>
    let vRing := vectorNegacyclicRing Coeff (m + 1)
    let vs := vectorNegacyclicSemantics Coeff (Nat.succ_pos m)
    have lift : ∀ a b : vRing.Poly, vs.quotientOf a = vs.quotientOf b → a = b :=
      NegacyclicQuotient.ofBackend_injective (vectorBackend Coeff (m + 1))
    have hmul : ∀ a b : vRing.Poly,
        vs.quotientOf (a * b) = vs.quotientOf a * vs.quotientOf b := fun a b =>
      vs.mul_sound a b
    have hone : vs.quotientOf 1 = 1 := vs.one_sound
    have hadd : ∀ a b : vRing.Poly,
        vs.quotientOf (a + b) = vs.quotientOf a + vs.quotientOf b := fun a b =>
      vs.add_sound a b
    have hzero : vs.quotientOf 0 = 0 := vs.zero_sound
    exact { mul := vRing.mul
            one := vRing.one
            mul_assoc a b c := lift _ _ (by simp only [hmul]; ring)
            one_mul a := lift _ _ (by simp only [hmul, hone]; ring)
            mul_one a := lift _ _ (by simp only [hmul, hone]; ring)
            mul_comm a b := lift _ _ (by simp only [hmul]; ring)
            left_distrib a b c := lift _ _ (by simp only [hmul, hadd]; ring)
            right_distrib a b c := lift _ _ (by simp only [hmul, hadd]; ring)
            zero_mul a := lift _ _ (by simp only [hmul, hzero]; ring)
            mul_zero a := lift _ _ (by simp only [hmul, hzero]; ring) }

end LatticeCrypto
