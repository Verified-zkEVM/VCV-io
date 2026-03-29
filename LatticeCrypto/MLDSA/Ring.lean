/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Params
import LatticeCrypto.Ring
import LatticeCrypto.Norm
import LatticeCrypto.Rounding

/-!
# ML-DSA Ring Layer

This file specializes the generic lattice ring layer from `VCVio.LatticeCrypto.Ring` to the
fixed modulus `q = 8380417` and degree `n = 256` used by FIPS 204. It also lifts the norm
and rounding abstractions to the concrete ML-DSA types.

## References

- NIST FIPS 204, Sections 2.3–2.5 and 7.4–7.6
-/

set_option autoImplicit false

namespace MLDSA

/-- Coefficients in the ML-DSA base ring. -/
abbrev Coeff := ZMod modulus

/-- Coefficient-vector representation of a polynomial in `R_q = Z_q[X]/(X^256 + 1)`. -/
abbrev Rq := LatticeCrypto.Poly Coeff ringDegree

/-- NTT-domain polynomials are kept distinct from coefficient-domain polynomials. -/
@[ext] structure Tq where
  coeffs : LatticeCrypto.Poly Coeff ringDegree
deriving Repr, DecidableEq

namespace Tq

def toRq (fHat : Tq) : Rq := fHat.coeffs

instance : Coe Tq Rq := ⟨Tq.toRq⟩
instance : Zero Tq := ⟨⟨0⟩⟩
instance : Add Tq := ⟨fun fHat gHat => ⟨fHat.coeffs + gHat.coeffs⟩⟩
instance : Sub Tq := ⟨fun fHat gHat => ⟨fHat.coeffs - gHat.coeffs⟩⟩
instance : Neg Tq := ⟨fun fHat => ⟨-fHat.coeffs⟩⟩

instance : GetElem Tq Nat Coeff (fun _ i => i < ringDegree) where
  getElem fHat i hi := fHat.coeffs[i]'hi

@[simp] theorem getElem_eq_coeffs_getElem (fHat : Tq) {i : Nat} (hi : i < ringDegree) :
    fHat[i] = fHat.coeffs[i] := rfl

end Tq

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.PolyVec Coeff ringDegree k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := Vector Tq k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := Vector (TqVec cols) rows

/-- The NTT-domain operations needed by the FIPS 204 pseudocode. -/
abbrev NTTRingOps := LatticeCrypto.NTTRingOps Rq Tq

section Norms

/-- The centered infinity norm of an ML-DSA polynomial. -/
abbrev polyNorm (f : Rq) : ℕ := LatticeCrypto.cInfNorm f

/-- The centered infinity norm of an ML-DSA polynomial vector. -/
abbrev polyVecNorm {k : ℕ} (v : RqVec k) : ℕ :=
  LatticeCrypto.PolyVec.cInfNorm v

/-- Whether all coefficients of a polynomial are in `[-b, b]`. -/
def polyBounded (f : Rq) (b : ℕ) : Prop := polyNorm f ≤ b

/-- Whether all coefficients of every component of a polynomial vector are in `[-b, b]`. -/
def polyVecBounded {k : ℕ} (v : RqVec k) (b : ℕ) : Prop :=
  polyVecNorm v ≤ b

end Norms

section Rounding

/-- Abstract rounding operations for ML-DSA, parameterized by `2 * γ₂`. -/
abbrev RoundingOps (alpha : ℕ) := LatticeCrypto.RoundingOps Rq alpha

/-- Abstract power-2 rounding operations for ML-DSA, parameterized by `d = 13`. -/
abbrev Power2RoundOps := LatticeCrypto.Power2RoundOps Rq droppedBits

end Rounding

/-- Schoolbook negacyclic multiplication in `R_q = Z_q[X]/(X^256 + 1)`. -/
def negacyclicMul (f g : Rq) : Rq := Id.run do
  let fa := f.toArray
  let ga := g.toArray
  let mut h : Array Coeff := Array.replicate ringDegree 0
  for i in [0:ringDegree] do
    for j in [0:ringDegree] do
      let fi := fa.getD i 0
      let gj := ga.getD j 0
      let k := (i + j) % ringDegree
      if i + j < ringDegree then
        h := h.set! k ((h.getD k 0) + fi * gj)
      else
        h := h.set! k ((h.getD k 0) - fi * gj)
  return Vector.ofFn fun ⟨i, _⟩ => h.getD i 0

namespace NTTRingOps

variable (ops : NTTRingOps)

abbrev transpose (_ops : NTTRingOps) {rows cols : ℕ} (A : TqMatrix rows cols) :
    TqMatrix cols rows := LatticeCrypto.NTTRingOps.transpose A

abbrev nttVec {k : ℕ} (v : RqVec k) : TqVec k :=
  LatticeCrypto.NTTRingOps.nttVec ops v

abbrev invNTTVec {k : ℕ} (v : TqVec k) : RqVec k :=
  LatticeCrypto.NTTRingOps.invNTTVec ops v

abbrev dot {k : ℕ} (u v : TqVec k) : Tq :=
  LatticeCrypto.NTTRingOps.dot ops u v

abbrev matVecMul {rows cols : ℕ} (A : TqMatrix rows cols) (v : TqVec cols) :
    TqVec rows :=
  LatticeCrypto.NTTRingOps.matVecMul ops A v

end NTTRingOps

end MLDSA
