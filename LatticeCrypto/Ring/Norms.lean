/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Ring.VectorBackend
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Norms For Negacyclic Ring Backends

Backend-generic norm infrastructure for the lattice ring layer. Defines:

- `CenteredCoeffView`: an integer-valued centered representative map for
  coefficients, used to define norms generically over any backend.
- `NormOps`: a norm bundle (`cInfNorm`, `l1Norm`, `l2NormSq`) parameterized
  by a `PolyBackend`, with a `pairL2NormSq` helper for Falcon-style signature
  norm bounds.
- `centeredRepr` and associated lemmas: the canonical centered representative
  for `ZMod q`, mapping each element to `[-(q-1)/2, (q-1)/2]`.
- Generic norm constructors (`cInfNormOf`, `l1NormOf`, `l2NormSqOf`) and their
  specialized vector-backend versions (`cInfNorm`, `l1Norm`, `l2NormSq`).
- `PolyVec` norm lifts and `zmodPolyNormOps`.

`MLDSA.Arithmetic` and `Falcon.Arithmetic` assemble scheme-local norm aliases
from `zmodPolyNormOps`.
-/


open scoped BigOperators

namespace LatticeCrypto

/-- A centered integer view of coefficients.

Maps each coefficient to a representative integer, enabling backend-generic
norm definitions. The canonical instance for `ZMod q` is `zmodCenteredCoeffView`,
which uses `centeredRepr`. -/
structure CenteredCoeffView (Coeff : Type*) where
  repr : Coeff → ℤ

/-- Norm bundle layered over a `PolyBackend`.

Bundles the three standard polynomial norms used across ML-DSA and Falcon:
centered `ℓ∞`, `ℓ₁`, and squared `ℓ₂`. Constructed generically via
`normOpsOfCenteredView`, or directly via `zmodPolyNormOps` for `ZMod q`
coefficients. -/
structure NormOps {Coeff : Type*} (backend : PolyBackend Coeff) where
  cInfNorm : backend.Poly → ℕ
  l1Norm : backend.Poly → ℕ
  l2NormSq : backend.Poly → ℕ

namespace NormOps

variable {Coeff : Type*} {backend : PolyBackend Coeff}

/-- The squared `ℓ₂` norm of a pair of polynomials. -/
def pairL2NormSq (ops : NormOps backend) (p₁ p₂ : backend.Poly) : ℕ :=
  ops.l2NormSq p₁ + ops.l2NormSq p₂

end NormOps

section CenteredRepr

variable {q : ℕ} [NeZero q]

/-- The centered representative of `x : ZMod q`, mapping to the unique integer in
`[-(q-1)/2, (q-1)/2]` congruent to `x` mod `q`. -/
def centeredRepr (x : ZMod q) : ℤ :=
  if (x.val : ℤ) ≤ (q : ℤ) / 2 then (x.val : ℤ) else (x.val : ℤ) - q

omit [NeZero q] in
@[simp] theorem centeredRepr_of_le {x : ZMod q} (h : (x.val : ℤ) ≤ (q : ℤ) / 2) :
    centeredRepr x = x.val := by
  unfold centeredRepr
  exact if_pos h

omit [NeZero q] in
@[simp] theorem centeredRepr_of_gt {x : ZMod q} (h : (q : ℤ) / 2 < (x.val : ℤ)) :
    centeredRepr x = (x.val : ℤ) - q := by
  unfold centeredRepr
  exact if_neg (not_le.mpr h)

/-- The centered representative is always at most `q / 2`. -/
theorem centeredRepr_upper_bound (x : ZMod q) : centeredRepr x ≤ (q : ℤ) / 2 := by
  simp only [centeredRepr]
  split_ifs with h
  · exact h
  · push_neg at h
    have hval := ZMod.val_lt x
    omega

/-- The centered representative has absolute value at most `q / 2`. -/
theorem centeredRepr_abs_le (x : ZMod q) : (centeredRepr x).natAbs ≤ q / 2 := by
  simp only [centeredRepr]
  have hval := ZMod.val_lt x
  split_ifs with h <;> omega

/-- Negation preserves the absolute value of the centered representative. -/
theorem centeredRepr_natAbs_neg (x : ZMod q) :
    (centeredRepr (-x)).natAbs = (centeredRepr x).natAbs := by
  by_cases hx : x = 0
  · simp [hx]
  · haveI : NeZero x := ⟨hx⟩
    simp only [centeredRepr, ZMod.val_neg_of_ne_zero]
    have hval := ZMod.val_lt x
    have hpos : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx)
    split_ifs <;> omega

/-- Casting the centered representative back into `ZMod q` recovers the original element. -/
theorem centeredRepr_intCast (x : ZMod q) :
    (x : ZMod q) = ((centeredRepr x : ℤ) : ZMod q) := by
  by_cases h : (x.val : ℤ) ≤ (q : ℤ) / 2
  · rw [centeredRepr_of_le h, Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hgt : (q : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [centeredRepr_of_gt hgt, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self]
    simp

/-- Twice the centered representative lies in the interval used by `ZMod.valMinAbs`. -/
theorem centeredRepr_mem_Ioc (x : ZMod q) :
    centeredRepr x * 2 ∈ Set.Ioc (-(q : ℤ)) q := by
  by_cases h : (x.val : ℤ) ≤ (q : ℤ) / 2
  · rw [centeredRepr_of_le h]
    have hx : 0 ≤ (x.val : ℤ) := by positivity
    have hmod : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
    constructor <;> omega
  · have hgt : (q : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [centeredRepr_of_gt hgt]
    have hval := ZMod.val_lt x
    constructor <;> omega

/-- The centered representative agrees with `ZMod.valMinAbs`. -/
theorem centeredRepr_eq_valMinAbs (x : ZMod q) :
    centeredRepr x = x.valMinAbs := by
  simpa using ((ZMod.valMinAbs_spec x (centeredRepr x)).2
    ⟨centeredRepr_intCast x, centeredRepr_mem_Ioc x⟩).symm

/-- Casting an integer already in the centered interval preserves that integer. -/
theorem centeredRepr_intCast_eq (z : ℤ)
    (hzlo : -(q : ℤ) < z * 2) (hzhi : z * 2 ≤ q) :
    centeredRepr ((z : ZMod q)) = z := by
  rw [centeredRepr_eq_valMinAbs]
  exact (ZMod.valMinAbs_spec ((z : ZMod q)) z).2 ⟨rfl, ⟨hzlo, hzhi⟩⟩

/-- A small-enough integer is unchanged by casting into `ZMod q` and taking `centeredRepr`. -/
theorem centeredRepr_intCast_eq_of_natAbs_le (z : ℤ) {b : ℕ}
    (hbound : z.natAbs ≤ b) (hbq : 2 * b < q) :
    centeredRepr ((z : ZMod q)) = z := by
  apply centeredRepr_intCast_eq
  · have : -(b : ℤ) ≤ z := by omega
    omega
  · have : z ≤ b := by omega
    omega

/-- A `natAbs` bound yields both lower and upper integer bounds. -/
theorem neg_le_and_le_of_natAbs_le {z : ℤ} {b : ℕ}
    (hbound : z.natAbs ≤ b) : -(b : ℤ) ≤ z ∧ z ≤ b := by
  constructor <;> omega

/-- The canonical centered coefficient view for `ZMod q`. -/
def zmodCenteredCoeffView (q : ℕ) [NeZero q] : CenteredCoeffView (ZMod q) where
  repr := centeredRepr

end CenteredRepr

section GenericNorms

variable {Coeff : Type*} (backend : PolyBackend Coeff) (view : CenteredCoeffView Coeff)

/-- Backend-generic centered infinity norm. -/
def cInfNormOf (p : backend.Poly) : ℕ :=
  Finset.sup Finset.univ fun i : Fin backend.degree => (view.repr (backend.coeff p i)).natAbs

/-- Backend-generic `ℓ₁` norm. -/
def l1NormOf (p : backend.Poly) : ℕ :=
  ∑ i : Fin backend.degree, (view.repr (backend.coeff p i)).natAbs

/-- Backend-generic squared `ℓ₂` norm. -/
def l2NormSqOf (p : backend.Poly) : ℕ :=
  ∑ i : Fin backend.degree, (view.repr (backend.coeff p i)).natAbs ^ 2

/-- Construct a generic norm bundle from a centered coefficient view. -/
def normOpsOfCenteredView : NormOps backend where
  cInfNorm := cInfNormOf backend view
  l1Norm := l1NormOf backend view
  l2NormSq := l2NormSqOf backend view

end GenericNorms

section SpecializedVectorNorms

variable {q : ℕ} [NeZero q] {n : Nat}

/-- The centered infinity norm on the canonical vector backend. -/
def cInfNorm (p : Poly (ZMod q) n) : ℕ :=
  cInfNormOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The `ℓ₁` norm on the canonical vector backend. -/
def l1Norm (p : Poly (ZMod q) n) : ℕ :=
  l1NormOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The squared `ℓ₂` norm on the canonical vector backend. -/
def l2NormSq (p : Poly (ZMod q) n) : ℕ :=
  l2NormSqOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The squared `ℓ₂` norm of a pair of vector-backed polynomials. -/
def pairL2NormSq (p₁ p₂ : Poly (ZMod q) n) : ℕ :=
  l2NormSq p₁ + l2NormSq p₂

theorem cInfNorm_le_iff {p : Poly (ZMod q) n} {b : ℕ} :
    cInfNorm p ≤ b ↔ ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b := by
  simp [cInfNorm, cInfNormOf, vectorBackend, zmodCenteredCoeffView, Finset.sup_le_iff]

theorem cInfNorm_le_of_coeff_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b) : cInfNorm p ≤ b :=
  cInfNorm_le_iff.mpr h

theorem coeff_le_cInfNorm (p : Poly (ZMod q) n) (i : Fin n) :
    (centeredRepr (p.get i)).natAbs ≤ cInfNorm p := by
  exact Finset.le_sup (f := fun i => (centeredRepr (p.get i)).natAbs) (Finset.mem_univ i)

/-- Every polynomial has centered infinity norm at most `q / 2`. -/
theorem cInfNorm_le_halfq (p : Poly (ZMod q) n) : cInfNorm p ≤ q / 2 :=
  cInfNorm_le_iff.mpr (fun i => centeredRepr_abs_le (p.get i))

/-- Negation preserves the centered infinity norm. -/
@[simp] theorem cInfNorm_neg (f : Poly (ZMod q) n) : cInfNorm (-f) = cInfNorm f := by
  simp only [cInfNorm, cInfNormOf, vectorBackend, zmodCenteredCoeffView]
  congr 1
  ext i
  have hneg : (-f).get i = -(f.get i) := Vector.getElem_map (- ·) i.isLt
  rw [hneg, centeredRepr_natAbs_neg]

theorem l1Norm_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l1Norm p ≤ n * b := by
  unfold l1Norm l1NormOf
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs
      ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => (cInfNorm_le_iff.mp h) i
    _ = n * b := by simp [Finset.sum_const]

theorem l2NormSq_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l2NormSq p ≤ n * b ^ 2 := by
  unfold l2NormSq l2NormSqOf
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2
      ≤ ∑ _i : Fin n, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (cInfNorm_le_iff.mp h i) 2
    _ = n * b ^ 2 := by simp [Finset.sum_const]

end SpecializedVectorNorms

namespace PolyVec

variable {Coeff : Type*} {backend : PolyBackend Coeff} (ops : NormOps backend) {k : Nat}

/-- The centered infinity norm of a polynomial vector. -/
def cInfNorm (v : PolyVec backend.Poly k) : ℕ :=
  Finset.sup Finset.univ fun j : Fin k => ops.cInfNorm (v.get j)

/-- A polynomial vector has centered infinity norm at most `b` exactly when each component
polynomial does. -/
theorem cInfNorm_le_iff {v : PolyVec backend.Poly k} {b : ℕ} :
    PolyVec.cInfNorm ops v ≤ b ↔ ∀ j : Fin k, ops.cInfNorm (v.get j) ≤ b := by
  simp [PolyVec.cInfNorm, Finset.sup_le_iff]

/-- Each component polynomial is bounded by the centered infinity norm of the whole vector. -/
theorem component_cInfNorm_le (v : PolyVec backend.Poly k) (j : Fin k) :
    ops.cInfNorm (v.get j) ≤ PolyVec.cInfNorm ops v :=
  Finset.le_sup (f := fun j => ops.cInfNorm (v.get j)) (Finset.mem_univ j)

/-- The `ℓ₁` norm of a polynomial vector. -/
def l1Norm (v : PolyVec backend.Poly k) : ℕ :=
  Finset.sup Finset.univ fun j : Fin k => ops.l1Norm (v.get j)

/-- The squared `ℓ₂` norm of a polynomial vector. -/
def l2NormSq (v : PolyVec backend.Poly k) : ℕ :=
  ∑ j : Fin k, ops.l2NormSq (v.get j)

end PolyVec

/-- The canonical backend-generic norm bundle for `ZMod q` coefficients. -/
def zmodPolyNormOps (q : ℕ) [NeZero q] (backend : PolyBackend (ZMod q)) : NormOps backend :=
  normOpsOfCenteredView backend (zmodCenteredCoeffView q)

end LatticeCrypto
