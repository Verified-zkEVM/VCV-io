/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Params
import LatticeCrypto.Ring
import LatticeCrypto.Norm

/-!
# Falcon Ring Layer

This file specializes the generic lattice ring layer from `LatticeCrypto.Ring` to the fixed
modulus `q = 12289` used by Falcon. It also defines `IntPoly n`, the type of integer-coefficient
polynomials used for secret keys `f, g, F, G` (which live in `ℤ[x]/(x^n + 1)`, NOT mod `q`).

## Key Distinctions from ML-DSA

- **Secret keys use `IntPoly n`** (integer coefficients), not `Rq n` (mod `q`). The NTRU
  equation `fG - gF = q` is over `ℤ[x]/(x^n + 1)`, and reduction mod `q` only happens
  for the public key `h = g · f⁻¹ mod q`.
- **Verification uses the ℓ₂ norm** (squared), not the ℓ∞ norm.

## References

- Falcon specification v1.2, Sections 3.1–3.2 (ring structure)
- Falcon specification v1.2, Section 3.5 (NTRU lattice and key format)
-/

set_option autoImplicit false

namespace Falcon

/-- Coefficients in the Falcon base ring `ℤ_q` where `q = 12289`. -/
abbrev Coeff := ZMod modulus

/-- Coefficient-vector representation of a polynomial in `R_q = ℤ_q[x]/(x^n + 1)`. -/
abbrev Rq (n : ℕ) := LatticeCrypto.Poly Coeff n

/-- Integer-coefficient polynomial in `ℤ[x]/(x^n + 1)`. Used for the Falcon secret key
polynomials `f, g, F, G` which live over the integers, not mod `q`. -/
abbrev IntPoly (n : ℕ) := Vector ℤ n

/-- NTT-domain polynomials for Falcon, distinct from coefficient-domain. -/
@[ext] structure Tq (n : ℕ) where
  coeffs : LatticeCrypto.Poly Coeff n
deriving Repr, DecidableEq

namespace Tq

variable {n : ℕ}

/-- Forget the `Tq` wrapper and view an NTT-domain polynomial as its underlying polynomial. -/
def toRq (fHat : Tq n) : Rq n := fHat.coeffs

/-- Coercion from `Tq` to the underlying polynomial representation. -/
instance : Coe (Tq n) (Rq n) := ⟨Tq.toRq⟩
/-- The zero NTT-domain polynomial. -/
instance : Zero (Tq n) := ⟨⟨0⟩⟩
/-- Pointwise addition on NTT-domain polynomials. -/
instance : Add (Tq n) := ⟨fun fHat gHat => ⟨fHat.coeffs + gHat.coeffs⟩⟩
/-- Pointwise subtraction on NTT-domain polynomials. -/
instance : Sub (Tq n) := ⟨fun fHat gHat => ⟨fHat.coeffs - gHat.coeffs⟩⟩
/-- Pointwise negation on NTT-domain polynomials. -/
instance : Neg (Tq n) := ⟨fun fHat => ⟨-fHat.coeffs⟩⟩

/-- Indexing into an NTT-domain polynomial by coefficient position. -/
instance : GetElem (Tq n) Nat Coeff (fun _ i => i < n) where
  getElem fHat i hi := fHat.coeffs[i]'hi

/-- Indexing through `Tq` agrees with indexing the underlying polynomial. -/
@[simp] theorem getElem_eq_coeffs_getElem (fHat : Tq n) {i : Nat} (hi : i < n) :
    fHat[i] = fHat.coeffs[i] := rfl

end Tq

/-- The NTT-domain operations for Falcon. -/
abbrev NTTRingOps (n : ℕ) := LatticeCrypto.NTTRingOps (Rq n) (Tq n)

section Norms

variable {n : ℕ}

/-- The squared ℓ₂ norm of a Falcon polynomial. -/
abbrev polyL2NormSq (f : Rq n) : ℕ := LatticeCrypto.l2NormSq f

/-- The squared ℓ₂ norm of a pair of Falcon polynomials `(s₁, s₂)`.
Used for Falcon verification: accept iff `pairL2NormSq s₁ s₂ ≤ betaSquared`. -/
abbrev pairL2NormSq (s₁ s₂ : Rq n) : ℕ := LatticeCrypto.pairL2NormSq s₁ s₂

end Norms

section IntPolyOps

variable {n : ℕ}

/-- Reduce an integer polynomial mod `q` to obtain an element of `R_q`. -/
def IntPoly.toRq (f : IntPoly n) : Rq n :=
  Vector.map (fun (z : ℤ) => (z : ZMod modulus)) f

/-- The centered representative of a `ZMod q` element, mapping to `[-(q-1)/2, (q-1)/2]`. -/
def centeredRepr (x : ZMod modulus) : ℤ := LatticeCrypto.centeredRepr x

/-- Check whether all NTT coefficients of a polynomial are nonzero (i.e., invertible mod `q`).
This is needed to verify that `f` is invertible in `R_q`, which is required for computing
the public key `h = g · f⁻¹ mod q`. -/
def isInvertibleModQ (nttOps : NTTRingOps n) (f : Rq n) : Bool :=
  let fHat := nttOps.ntt f
  (Vector.toList fHat.coeffs).all (· != 0)

end IntPolyOps

/-- Schoolbook negacyclic multiplication in `R_q = ℤ_q[x]/(x^n + 1)`. -/
def negacyclicMul {n : ℕ} (f g : Rq n) : Rq n := Id.run do
  let fa := f.toArray
  let ga := g.toArray
  let mut h : Array Coeff := Array.replicate n 0
  for i in [0:n] do
    for j in [0:n] do
      let fi := fa.getD i 0
      let gj := ga.getD j 0
      let k := (i + j) % n
      if i + j < n then
        h := h.set! k ((h.getD k 0) + fi * gj)
      else
        h := h.set! k ((h.getD k 0) - fi * gj)
  return Vector.ofFn fun ⟨i, _⟩ => h.getD i 0

/-- Schoolbook negacyclic multiplication for integer polynomials in `ℤ[x]/(x^n + 1)`.
Used for checking the NTRU equation `fG - gF = q`. -/
def intPolyMul {n : ℕ} (f g : IntPoly n) : IntPoly n := Id.run do
  let fa := f.toArray
  let ga := g.toArray
  let mut h : Array ℤ := Array.replicate n 0
  for i in [0:n] do
    for j in [0:n] do
      let fi := fa.getD i 0
      let gj := ga.getD j 0
      let k := (i + j) % n
      if i + j < n then
        h := h.set! k ((h.getD k 0) + fi * gj)
      else
        h := h.set! k ((h.getD k 0) - fi * gj)
  return Vector.ofFn fun ⟨i, _⟩ => h.getD i 0

/-- The constant integer polynomial with value `c` at position 0 and 0 elsewhere. -/
def intPolyConst {n : ℕ} (c : ℤ) : IntPoly n :=
  Vector.ofFn fun i => if i.val = 0 then c else 0

end Falcon
