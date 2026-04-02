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

/-! ## Section 1: Negacyclic Quotient Algebra -/

/-- The negacyclic modulus `X^n + 1` maps to zero in the quotient. -/
theorem mk_negacyclicModulus_eq_zero :
    (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
      (negacyclicModulus R n) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- In `R[X]/(X^n + 1)`, `X^n = -1`. -/
theorem mk_X_pow_n :
    (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
      ((X : Polynomial R) ^ n) = -1 := by
  have h := mk_negacyclicModulus_eq_zero (R := R) (n := n)
  simp only [negacyclicModulus] at h
  rwa [map_add, map_one, add_eq_zero_iff_eq_neg] at h

/-- In `R[X]/(X^n + 1)`, `X^(k + n) = -X^k`. -/
theorem mk_X_pow_add_n (hn : 0 < n) (k : Nat) :
    (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
      ((X : Polynomial R) ^ (k + n)) =
    -(Ideal.Quotient.mk _ (X ^ k)) := by
  rw [pow_add, map_mul, mk_X_pow_n hn]; ring

/-- In `R[X]/(X^n + 1)`, `monomial (k + n) c = -monomial k c`. -/
theorem mk_monomial_add_n (hn : 0 < n) (k : Nat) (c : R) :
    (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
      (Polynomial.monomial (k + n) c) =
    -(Ideal.Quotient.mk _ (Polynomial.monomial k c)) := by
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_mul,
    mk_X_pow_add_n hn]
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
    (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
      (∑ i : Fin n, ∑ j : Fin n,
        Polynomial.monomial (i.val + j.val) (f i * g j)) =
    (Ideal.Quotient.mk _)
      (∑ k : Fin n, Polynomial.monomial k.val (negacyclicConvCoeff f g k)) := by
  have h_reduction : ∀ i j : Fin n,
      (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
        (Polynomial.monomial (i.val + j.val) (f i * g j)) =
      (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
        (Polynomial.monomial ((i.val + j.val) % n)
          (if i.val + j.val < n then f i * g j else -(f i * g j))) := by
    intro i j
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · have h_neg : (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
          (Polynomial.monomial (n + (i.val + j.val - n)) (f i * g j)) =
        (Ideal.Quotient.mk (Ideal.span ({negacyclicModulus R n} : Set (Polynomial R))))
          (-Polynomial.monomial ((i.val + j.val - n)) (f i * g j)) := by
        grind +suggestions
      have hle : n ≤ i.val + j.val := le_of_not_gt h
      have hlt : i.val + j.val - n < n := by
        rw [tsub_lt_iff_left hle]
        linarith [Fin.is_lt i, Fin.is_lt j]
      have hmod : (i.val + j.val) % n = i.val + j.val - n := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt]
      simpa [Nat.add_sub_of_le hle, h, hmod] using h_neg
      rw [Nat.mod_eq_of_lt (by rw [tsub_lt_iff_left h]; linarith [Fin.is_lt i, Fin.is_lt j])]
  simp only [negacyclicConvCoeff]
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_eq_single ⟨(x.1 + x.2) % n, Nat.mod_lt _ hn⟩] <;> aesop

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
    push_neg at hn
    have hd : backend.degree = 0 := by omega
    have : IsEmpty (Fin backend.degree) := by rw [hd]; exact Fin.isEmpty
    simp [Finset.univ_eq_empty]

/-- Proof-facing quotient interpretation for the canonical vector backend.

Maps each executable operation to its counterpart in the quotient ring
`R[X] / (X^n + 1)` and asserts soundness of the mapping.
Requires `0 < n` for the negacyclic reduction in `mul_sound`. -/
noncomputable def vectorNegacyclicSemantics (Coeff : Type*) [CommRing Coeff] (n : Nat) :
    NegacyclicRingSemantics (vectorNegacyclicRing Coeff n) :=
  vectorNegacyclicSemantics_additive Coeff n
    (fun f g => negacyclicMulPure_sound (vectorBackend Coeff n) (vectorKernel Coeff n) f g)

end LatticeCrypto
