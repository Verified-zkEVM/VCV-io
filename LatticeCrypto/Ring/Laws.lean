/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.Norms

/-!
# Proof-Facing Laws For Negacyclic Rings

`NegacyclicRing` is the executable ring bundle.  This file contains optional
law-carrying certificates used by security proofs that need algebraic facts
beyond the executable interface.
-/

universe u

namespace LatticeCrypto
namespace NegacyclicRing

variable {Coeff : Type u} [CommRing Coeff]

/-- Proof-facing scalar/matrix-vector laws for a bundled negacyclic ring. -/
structure ScalarMulLaws (ring : NegacyclicRing Coeff) where
  /-- Executable unit-like test used by protocols. -/
  isUnitLike : ring.Poly → Bool
  /-- Multiplication is commutative for protocol scalars. -/
  mul_comm : ∀ c d : ring.Poly, ring.mul c d = ring.mul d c
  /-- The product of two unit-like elements is unit-like. -/
  isUnitLike_mul :
    ∀ c d : ring.Poly, isUnitLike c = true → isUnitLike d = true →
      isUnitLike (ring.mul c d) = true
  /-- Multiplication by a unit-like scalar is injective on vectors. -/
  scalarVecMul_injective_of_isUnitLike :
    ∀ {cols : Nat} (c : ring.Poly), isUnitLike c = true →
      Function.Injective (scalarVecMul ring (cols := cols) c)
  /-- Matrix-vector multiplication commutes with left scalar multiplication. -/
  matVecMul_scalarVecMul :
    ∀ {rows cols : Nat} (A : PolyMatrix ring.Poly rows cols) (c : ring.Poly)
      (v : PolyVec ring.Poly cols),
      matVecMul ring A (scalarVecMul ring c v) =
        scalarVecMul ring c (matVecMul ring A v)

namespace ScalarMulLaws

variable {ring : NegacyclicRing Coeff} (laws : ScalarMulLaws ring)

/-- Scaling by the product of two unit-like scalars preserves vector inequality. -/
theorem scalarVecMul_mul_ne_of_ne {cols : Nat} {c d : ring.Poly}
    {v w : PolyVec ring.Poly cols}
    (hc : laws.isUnitLike c = true) (hd : laws.isUnitLike d = true)
    (hvw : v ≠ w) :
    scalarVecMul ring (ring.mul c d) v ≠
      scalarVecMul ring (ring.mul d c) w := by
  intro h
  apply hvw
  have hcomm : ring.mul d c = ring.mul c d := laws.mul_comm d c
  have hinj :=
    laws.scalarVecMul_injective_of_isUnitLike (cols := cols) (ring.mul c d)
      (laws.isUnitLike_mul c d hc hd)
  exact hinj (by simpa [hcomm] using h)

/-- Equality of matrix products is preserved by scalar multiplication. -/
theorem matVecMul_scalarVecMul_eq_of_eq {rows cols : Nat}
    (laws : ScalarMulLaws ring) (A : PolyMatrix ring.Poly rows cols) (c : ring.Poly)
    {v w : PolyVec ring.Poly cols}
    (h : matVecMul ring A v = matVecMul ring A w) :
    matVecMul ring A (scalarVecMul ring c v) =
      matVecMul ring A (scalarVecMul ring c w) := by
  rw [laws.matVecMul_scalarVecMul A c v, laws.matVecMul_scalarVecMul A c w, h]

/-- Equality of matrix products is preserved by scaling with a product of two scalars. -/
theorem matVecMul_scalarVecMul_mul_eq_of_eq {rows cols : Nat}
    (laws : ScalarMulLaws ring) (A : PolyMatrix ring.Poly rows cols) (c d : ring.Poly)
    {v w : PolyVec ring.Poly cols}
    (h : matVecMul ring A v = matVecMul ring A w) :
    matVecMul ring A (scalarVecMul ring (ring.mul c d) v) =
      matVecMul ring A (scalarVecMul ring (ring.mul d c) w) := by
  rw [laws.matVecMul_scalarVecMul A (ring.mul c d) v,
    laws.matVecMul_scalarVecMul A (ring.mul d c) w, laws.mul_comm d c, h]

end ScalarMulLaws

/-- Proof-facing norm growth law for executable scalar multiplication. -/
structure ScalarNormLaws (ring : NegacyclicRing Coeff) (normOps : NormOps ring.backend) where
  /-- Executable bound for multiplying an already scaled vector by one more bounded scalar. -/
  scalarVecMulMulL2NormSqBound : Nat → Nat → Nat
  /-- Multiplication by a scalar with bounded `ℓ₁` norm preserves the configured `ℓ₂` bound. -/
  scalarVecMul_mul_l2NormSq_le :
    ∀ {cols : Nat} (c d : ring.Poly) (v : PolyVec ring.Poly cols) {kappa betaSq : Nat},
      normOps.l1Norm d ≤ kappa →
      PolyVec.l2NormSq normOps (scalarVecMul ring c v) ≤ betaSq →
      PolyVec.l2NormSq normOps (scalarVecMul ring (ring.mul c d) v) ≤
        scalarVecMulMulL2NormSqBound kappa betaSq

end NegacyclicRing
end LatticeCrypto
