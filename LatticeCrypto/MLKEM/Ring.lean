/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Params
import LatticeCrypto.Ring

/-!
# ML-KEM Ring Layer

This file specializes the generic vector-backed lattice ring layer from
`VCVio.LatticeCrypto.Ring` to the fixed modulus and degree used by FIPS 203.
-/

set_option autoImplicit false

namespace MLKEM

/-- Coefficients in the ML-KEM base ring. -/
abbrev Coeff := ZMod modulus

/-- Coefficient-vector representation of a polynomial in `R_q`. -/
abbrev Rq := LatticeCrypto.Poly Coeff ringDegree

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

/-- NTT-domain polynomials are kept distinct from coefficient-domain polynomials. -/
@[ext] structure Tq where
  coeffs : LatticeCrypto.Poly Coeff ringDegree
deriving Repr, DecidableEq

namespace Tq

/-- Rewrap a coefficient vector as an NTT-domain polynomial. -/
def ofRq (f : Rq) : Tq := ⟨f⟩

/-- Forget the NTT-domain tag. -/
def toRq (fHat : Tq) : Rq := fHat.coeffs

/-- Access the underlying coefficient array. -/
def toArray (fHat : Tq) : Array Coeff := fHat.coeffs.toArray

/-- Coercion from `Tq` to the underlying polynomial representation. -/
instance : Coe Tq Rq := ⟨Tq.toRq⟩

/-- The zero NTT-domain polynomial. -/
instance : Zero Tq := ⟨⟨0⟩⟩
/-- Pointwise addition on NTT-domain polynomials. -/
instance : Add Tq := ⟨fun fHat gHat => ⟨fHat.coeffs + gHat.coeffs⟩⟩
/-- Pointwise subtraction on NTT-domain polynomials. -/
instance : Sub Tq := ⟨fun fHat gHat => ⟨fHat.coeffs - gHat.coeffs⟩⟩
/-- Pointwise negation on NTT-domain polynomials. -/
instance : Neg Tq := ⟨fun fHat => ⟨-fHat.coeffs⟩⟩

/-- Indexing into an NTT-domain polynomial by coefficient position. -/
instance : GetElem Tq Nat Coeff (fun _ i => i < ringDegree) where
  getElem fHat i hi := fHat.coeffs[i]'hi

/-- Indexing through `Tq` agrees with indexing the underlying polynomial. -/
@[simp] theorem getElem_eq_coeffs_getElem (fHat : Tq) {i : Nat} (hi : i < ringDegree) :
    fHat[i] = fHat.coeffs[i] := rfl

@[simp] theorem toArray_getElem (fHat : Tq) {i : Nat} (hi : i < ringDegree) :
    fHat.toArray[i]'(by simpa [Tq.toArray] using hi) = fHat.coeffs[i] := rfl

end Tq

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.PolyVec Coeff ringDegree k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := Vector Tq k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := Vector (TqVec cols) rows

/-- The NTT-domain operations needed by the FIPS 203 pseudocode. -/
abbrev NTTRingOps := LatticeCrypto.NTTRingOps Rq Tq

/-- Proof-oriented algebraic laws for an ML-KEM NTT implementation. -/
abbrev NTTRingLaws (ops : NTTRingOps) := LatticeCrypto.NTTRingOps.Laws ops negacyclicMul

namespace NTTRingOps

variable (ops : NTTRingOps)

/-- Transpose a row-major matrix over `T_q`. -/
abbrev transpose (_ops : NTTRingOps) {rows cols : ℕ} (A : TqMatrix rows cols) :
    TqMatrix cols rows := LatticeCrypto.NTTRingOps.transpose A

/-- Apply NTT coordinate-wise to a vector over `R_q`. -/
abbrev nttVec {k : ℕ} (v : RqVec k) : TqVec k :=
  LatticeCrypto.NTTRingOps.nttVec ops v

/-- Apply inverse NTT coordinate-wise to a vector over `T_q`. -/
abbrev invNTTVec {k : ℕ} (v : TqVec k) : RqVec k :=
  LatticeCrypto.NTTRingOps.invNTTVec ops v

/-- Dot product in the NTT domain, using `multiplyNTTs` as the base multiplication. -/
abbrev dot {k : ℕ} (u v : TqVec k) : Tq :=
  LatticeCrypto.NTTRingOps.dot ops u v

/-- Matrix-vector multiplication in the NTT domain. -/
abbrev matVecMul {rows cols : ℕ} (A : TqMatrix rows cols) (v : TqVec cols) : TqVec rows :=
  LatticeCrypto.NTTRingOps.matVecMul ops A v

/-- Transposed matrix-vector multiplication in the NTT domain. -/
abbrev matTransposeVecMul {rows cols : ℕ} (A : TqMatrix rows cols) (v : TqVec rows) :
    TqVec cols :=
  LatticeCrypto.NTTRingOps.matTransposeVecMul ops A v

end NTTRingOps

end MLKEM
