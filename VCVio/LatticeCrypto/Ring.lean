/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Init.Data.Vector.Algebra
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Generic Lattice Ring Layer

This file provides vector-backed representations for fixed-degree polynomials, module vectors,
and matrices, together with the abstract NTT-domain operations used by lattice-based
cryptography. The representation is chosen to stay executable today and amenable to more
optimized array-backed implementations later.
-/

set_option autoImplicit false

universe u

namespace LatticeCrypto

/-- A degree-`n` polynomial represented by its coefficient vector. -/
abbrev Poly (Coeff : Type u) (n : Nat) := Vector Coeff n

/-- A length-`k` vector of degree-`n` polynomials. -/
abbrev PolyVec (Coeff : Type u) (n k : Nat) := Vector (Poly Coeff n) k

/-- A `rows × cols` row-major matrix of degree-`n` polynomials. -/
abbrev PolyMatrix (Coeff : Type u) (n rows cols : Nat) := Vector (PolyVec Coeff n cols) rows

/-- The abstract NTT-domain operations needed by lattice-based cryptosystems. -/
structure NTTRingOps (Rq Tq : Type u) where
  ntt : Rq → Tq
  invNTT : Tq → Rq
  multiplyNTTs : Tq → Tq → Tq

namespace Poly

variable {Coeff : Type u} {n : Nat}

/-- View a vector-backed polynomial as a `Fin n → Coeff` function. -/
def toPi (p : Poly Coeff n) : Fin n → Coeff :=
  fun i => p.get i

/-- Build a vector-backed polynomial from a `Fin n → Coeff` function. -/
def ofPi (f : Fin n → Coeff) : Poly Coeff n :=
  Vector.ofFn f

@[simp] theorem toPi_ofPi (f : Fin n → Coeff) :
    toPi (ofPi f) = f := by
  funext i
  simp [Vector.get, toPi, ofPi]

@[simp] theorem ofPi_toPi (p : Poly Coeff n) :
    ofPi (toPi p) = p := by
  apply Vector.ext
  intro i hi
  simp [Vector.get, toPi, ofPi]

end Poly

namespace PolyVec

variable {Coeff : Type u} {n k : Nat}

/-- View a vector-backed polynomial vector as a `Fin k → Poly Coeff n` function. -/
def toPi (v : PolyVec Coeff n k) : Fin k → Poly Coeff n :=
  fun i => v.get i

/-- Build a vector-backed polynomial vector from a `Fin k → Poly Coeff n` function. -/
def ofPi (f : Fin k → Poly Coeff n) : PolyVec Coeff n k :=
  Vector.ofFn f

@[simp] theorem toPi_ofPi (f : Fin k → Poly Coeff n) :
    toPi (ofPi f) = f := by
  funext i
  simp [Vector.get, toPi, ofPi]

@[simp] theorem ofPi_toPi (v : PolyVec Coeff n k) :
    ofPi (toPi v) = v := by
  apply Vector.ext
  intro i hi
  simp [Vector.get, toPi, ofPi]

end PolyVec

namespace PolyMatrix

variable {Coeff : Type u} {n rows cols : Nat}

/-- View a row-major polynomial matrix as a Mathlib `Matrix`. -/
def toMatrix (A : PolyMatrix Coeff n rows cols) :
    Matrix (Fin rows) (Fin cols) (Poly Coeff n) :=
  fun i j => (A.get i).get j

/-- Build a row-major polynomial matrix from a Mathlib `Matrix`. -/
def ofMatrix (A : Matrix (Fin rows) (Fin cols) (Poly Coeff n)) :
    PolyMatrix Coeff n rows cols :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] theorem toMatrix_ofMatrix (A : Matrix (Fin rows) (Fin cols) (Poly Coeff n)) :
    toMatrix (ofMatrix A) = A := by
  funext i j
  simp [Vector.get, toMatrix, ofMatrix]

@[simp] theorem ofMatrix_toMatrix (A : PolyMatrix Coeff n rows cols) :
    ofMatrix (toMatrix A) = A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [Vector.get, toMatrix, ofMatrix]

end PolyMatrix

namespace NTTRingOps

variable {Rq Tq α : Type u}

/-- Transpose a row-major polynomial matrix. -/
def transpose {rows cols : Nat} (A : Vector (Vector α cols) rows) :
    Vector (Vector α rows) cols :=
  Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j

variable (ops : NTTRingOps Rq Tq)

/-- Apply NTT coordinate-wise to a polynomial vector. -/
def nttVec {k : Nat} (v : Vector Rq k) : Vector Tq k :=
  v.map ops.ntt

/-- Apply inverse NTT coordinate-wise to a polynomial vector. -/
def invNTTVec {k : Nat} (v : Vector Tq k) : Vector Rq k :=
  v.map ops.invNTT

/-- Dot product in the NTT domain, using `multiplyNTTs` as the base multiplication. -/
def dot {k : Nat} [Zero Tq] [Add Tq] (u v : Vector Tq k) : Tq :=
  (Vector.zipWith ops.multiplyNTTs u v).foldl (· + ·) 0

/-- Matrix-vector multiplication in the NTT domain. -/
def matVecMul {rows cols : Nat} [Zero Tq] [Add Tq]
    (A : Vector (Vector Tq cols) rows) (v : Vector Tq cols) :
    Vector Tq rows :=
  A.map fun row => ops.dot row v

/-- Transposed matrix-vector multiplication in the NTT domain. -/
def matTransposeVecMul {rows cols : Nat} [Zero Tq] [Add Tq]
    (A : Vector (Vector Tq cols) rows) (v : Vector Tq rows) :
    Vector Tq cols :=
  (transpose A).map fun row => ops.dot row v

/-- Algebraic laws needed to connect an NTT-domain implementation back to the coefficient-domain
ring structure it represents. -/
structure Laws (ops : NTTRingOps Rq Tq) (mulRq : Rq → Rq → Rq) : Prop where
  invNTT_ntt : ∀ f : Rq, ops.invNTT (ops.ntt f) = f
  ntt_mul : ∀ f g : Rq, ops.multiplyNTTs (ops.ntt f) (ops.ntt g) = ops.ntt (mulRq f g)

end NTTRingOps

end LatticeCrypto
