/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Init.Data.Vector.Algebra

/-!
# Generic Lattice Ring Layer

This file provides vector-backed representations for fixed-degree polynomials, module vectors,
and matrices, together with the abstract NTT-domain operations used by lattice-based
cryptography. The representation is chosen to stay executable today and amenable to more
optimized array-backed implementations later.
-/

set_option autoImplicit false

namespace LatticeCrypto

/-- A degree-`n` polynomial represented by its coefficient vector. -/
abbrev Poly (Coeff : Type) (n : Nat) := Vector Coeff n

/-- A length-`k` vector of degree-`n` polynomials. -/
abbrev PolyVec (Coeff : Type) (n k : Nat) := Vector (Poly Coeff n) k

/-- A `rows × cols` row-major matrix of degree-`n` polynomials. -/
abbrev PolyMatrix (Coeff : Type) (n rows cols : Nat) := Vector (PolyVec Coeff n cols) rows

/-- The abstract NTT-domain operations needed by lattice-based cryptosystems. -/
structure NTTRingOps (Coeff : Type) (n : Nat) where
  ntt : Poly Coeff n → Poly Coeff n
  invNTT : Poly Coeff n → Poly Coeff n
  multiplyNTTs : Poly Coeff n → Poly Coeff n → Poly Coeff n

namespace NTTRingOps

variable {Coeff : Type} {n : Nat}

/-- Transpose a row-major polynomial matrix. -/
def transpose {rows cols : Nat} (A : PolyMatrix Coeff n rows cols) :
    PolyMatrix Coeff n cols rows :=
  Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j

variable (ops : NTTRingOps Coeff n)

/-- Apply NTT coordinate-wise to a polynomial vector. -/
def nttVec {k : Nat} (v : PolyVec Coeff n k) : PolyVec Coeff n k :=
  v.map ops.ntt

/-- Apply inverse NTT coordinate-wise to a polynomial vector. -/
def invNTTVec {k : Nat} (v : PolyVec Coeff n k) : PolyVec Coeff n k :=
  v.map ops.invNTT

/-- Dot product in the NTT domain, using `multiplyNTTs` as the base multiplication. -/
def dot {k : Nat} [Zero Coeff] [Add Coeff] (u v : PolyVec Coeff n k) : Poly Coeff n :=
  (Vector.zipWith ops.multiplyNTTs u v).foldl (· + ·) 0

/-- Matrix-vector multiplication in the NTT domain. -/
def matVecMul {rows cols : Nat} [Zero Coeff] [Add Coeff]
    (A : PolyMatrix Coeff n rows cols) (v : PolyVec Coeff n cols) :
    PolyVec Coeff n rows :=
  A.map fun row => ops.dot row v

/-- Transposed matrix-vector multiplication in the NTT domain. -/
def matTransposeVecMul {rows cols : Nat} [Zero Coeff] [Add Coeff]
    (A : PolyMatrix Coeff n rows cols) (v : PolyVec Coeff n rows) :
    PolyVec Coeff n cols :=
  (transpose A).map fun row => ops.dot row v

end NTTRingOps

end LatticeCrypto
