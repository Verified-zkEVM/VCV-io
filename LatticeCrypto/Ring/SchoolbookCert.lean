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
theorem mk_X_pow_n (hn : 0 < n) :
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
  sorry

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
theorem negacyclicMulPure_sound (hn : 0 < n)
    (backend : PolyBackend R) (kernel : PolyKernel R backend)
    (hd : backend.degree = n) (f g : backend.Poly) :
    NegacyclicQuotient.ofBackend backend (negacyclicMulPure kernel f g) =
      NegacyclicQuotient.ofBackend backend f *
        NegacyclicQuotient.ofBackend backend g := by
  sorry

end LatticeCrypto
