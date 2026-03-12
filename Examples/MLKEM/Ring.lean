/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Params
import VCVio.LatticeCrypto.Ring

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

/-- Coefficient-vector representation of an element of `T_q`. -/
abbrev Tq := LatticeCrypto.Poly Coeff ringDegree

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.PolyVec Coeff ringDegree k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := LatticeCrypto.PolyVec Coeff ringDegree k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := LatticeCrypto.PolyMatrix Coeff ringDegree rows cols

/-- The NTT-domain operations needed by the FIPS 203 pseudocode. -/
abbrev NTTRingOps := LatticeCrypto.NTTRingOps Coeff ringDegree

namespace NTTRingOps

variable (ops : NTTRingOps)

/-- Transpose a row-major matrix over `T_q`. -/
abbrev transpose {rows cols : ℕ} (A : TqMatrix rows cols) : TqMatrix cols rows :=
  LatticeCrypto.NTTRingOps.transpose A

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
