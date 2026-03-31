/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import LatticeCrypto.Ring.VectorBackend

/-!
# Shared Matrix Certification Scaffolding For Concrete NTTs

Centralizes the standard-basis evaluation and matrix-application reasoning
shared by the concrete ML-DSA and ML-KEM NTT developments.

The concrete NTT certification strategy works as follows:
1. Evaluate the executable NTT loop kernel on each standard-basis vector to
   extract the transform matrix `M` as a `Fin n → Fin n → Coeff` function.
2. Define the public `ntt` / `invNTT` as `applyMatrix M` / `applyMatrix M⁻¹`,
   then mark them `@[implemented_by]` to rebind to the fast loop kernels at
   runtime.
3. Prove that `M · M⁻¹ = I` (via `applyMatrix_comp` and `applyMatrix_id`) to
   obtain the roundtrip laws.

This module provides `basis`, `applyMatrix`, `idMatrix`, and the composition /
identity / additivity lemmas that the scheme-specific `Concrete/NTT.lean` files
use.
-/


open scoped BigOperators

namespace LatticeCrypto.NTTCert

universe u

variable {Coeff : Type u} [Ring Coeff] {backend : LatticeCrypto.PolyBackend Coeff}

/-- Standard basis vector `eᵢ` in the backend carrier, with `1` at position `i`
and `0` elsewhere. Used to extract transform matrices by evaluating NTT kernels
on each basis element. -/
def basis (backend : LatticeCrypto.PolyBackend Coeff) (i : Fin backend.degree) : backend.Poly :=
  backend.build fun j => if i = j then 1 else 0

/-- Apply a coefficient matrix `M` to a backend polynomial, computing
`(M · f)[row] = Σ_col M[row][col] · f[col]`. The proof-oriented NTT
definitions are stated in terms of `applyMatrix`. -/
def applyMatrix (backend : LatticeCrypto.PolyBackend Coeff)
    (M : Fin backend.degree → Fin backend.degree → Coeff) (f : backend.Poly) : backend.Poly :=
  backend.build fun row => ∑ col : Fin backend.degree, M row col * backend.coeff f col

/-- Identity matrix in row/column form. -/
def idMatrix (n : Nat) (row col : Fin n) : Coeff :=
  if col = row then 1 else 0

theorem applyMatrix_get (M : Fin backend.degree → Fin backend.degree → Coeff)
    (f : backend.Poly) (j : Fin backend.degree) :
    backend.coeff (applyMatrix backend M f) j =
      ∑ col : Fin backend.degree, M j col * backend.coeff f col := by
  simp [applyMatrix]

theorem applyMatrix_comp
    (A B C : Fin backend.degree → Fin backend.degree → Coeff)
    (hcomp : ∀ row col : Fin backend.degree,
      ∑ k : Fin backend.degree, A row k * B k col = C row col)
    (f : backend.Poly) :
    applyMatrix backend A (applyMatrix backend B f) = applyMatrix backend C f := by
  suffices h : ∀ row : Fin backend.degree,
      ∑ col, A row col * backend.coeff (applyMatrix backend B f) col =
      ∑ col, C row col * backend.coeff f col by
    unfold applyMatrix; congr 1; funext row; exact h row
  intro row
  simp_rw [applyMatrix_get B f]
  simp_rw [Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  congr 1; funext col; congr 1; exact hcomp row col

theorem applyMatrix_id (f : backend.Poly) :
    applyMatrix backend (idMatrix backend.degree) f = f := by
  unfold applyMatrix
  have h : ∀ row : Fin backend.degree,
      (∑ col : Fin backend.degree,
        idMatrix backend.degree row col * backend.coeff f col) =
      backend.coeff f row := by
    intro row
    rw [Finset.sum_eq_single_of_mem row (Finset.mem_univ _)]
    · simp [idMatrix]
    · intro b _ hne; simp [idMatrix, hne]
  simp_rw [h]
  exact backend.build_coeff f

theorem applyMatrix_add
    (M : Fin backend.degree → Fin backend.degree → Coeff)
    [Add backend.Poly] (hadd : ∀ f g : backend.Poly,
      backend.coeff (f + g) = fun i => backend.coeff f i + backend.coeff g i)
    (f g : backend.Poly) :
    applyMatrix backend M (f + g) =
      backend.build (fun row =>
        ∑ col : Fin backend.degree, M row col * backend.coeff f col) +
      backend.build (fun row =>
        ∑ col : Fin backend.degree, M row col * backend.coeff g col) := by
  simp only [applyMatrix]
  have hfg : ∀ col, backend.coeff (f + g) col = backend.coeff f col + backend.coeff g col :=
    fun col => congr_fun (hadd f g) col
  simp_rw [hfg, mul_add, Finset.sum_add_distrib]
  rw [← backend.build_coeff (_ + _)]
  congr 1; funext row
  rw [congr_fun (hadd _ _) row, backend.coeff_build, backend.coeff_build]

theorem applyMatrix_zero
    (M : Fin backend.degree → Fin backend.degree → Coeff)
    [Zero backend.Poly] (hzero : ∀ i, backend.coeff (0 : backend.Poly) i = 0) :
    applyMatrix backend M 0 = 0 := by
  simp only [applyMatrix, hzero, mul_zero, Finset.sum_const_zero]
  conv_rhs => rw [← backend.build_coeff (0 : backend.Poly)]
  congr 1; funext row; exact (hzero row).symm

theorem applyMatrix_sub
    (M : Fin backend.degree → Fin backend.degree → Coeff)
    [Sub backend.Poly] (hsub : ∀ f g : backend.Poly,
      backend.coeff (f - g) = fun i => backend.coeff f i - backend.coeff g i)
    (f g : backend.Poly) :
    applyMatrix backend M (f - g) =
      backend.build (fun row =>
        ∑ col : Fin backend.degree, M row col * backend.coeff f col) -
      backend.build (fun row =>
        ∑ col : Fin backend.degree, M row col * backend.coeff g col) := by
  simp only [applyMatrix]
  have hfg : ∀ col, backend.coeff (f - g) col = backend.coeff f col - backend.coeff g col :=
    fun col => congr_fun (hsub f g) col
  simp_rw [hfg, mul_sub, Finset.sum_sub_distrib]
  rw [← backend.build_coeff (_ - _)]
  congr 1; funext row
  rw [congr_fun (hsub _ _) row, backend.coeff_build, backend.coeff_build]

end LatticeCrypto.NTTCert
