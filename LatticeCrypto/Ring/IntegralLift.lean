/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.ZMod.Basic
import LatticeCrypto.Ring.VectorBackend

/-!
# Integral Lifts For Negacyclic Rings

Packages integer-polynomial arithmetic needed by Falcon-style schemes into
the generic ring layer. Defines:

- `IntegralLift`: a bundle carrying a reduction map `toRq : IntPoly → Rq`,
  integer-polynomial multiplication, and constant embedding. Falcon uses
  integer-coefficient polynomials for secret-key operations (NTRU solving,
  signing) before reducing mod `q`.
- `constPoly`: the constant polynomial with a single nonzero coefficient at
  position 0.
- `vectorIntegralLift`: the canonical instance lifting `Vector ℤ n` to
  `Vector (ZMod q) n` via `PolyBackend.mapCoeffs`.
-/


namespace LatticeCrypto

/-- Integer-lift structure for Falcon-style secret-key arithmetic.

Bundles a reduction map from integer polynomials to `R_q`, integer-polynomial
multiplication in `ℤ[X]/(X^n + 1)`, and constant embedding. The multiplication
uses `schoolbookNegacyclicMul` over the integer backend. -/
structure IntegralLift (IntPoly Rq : Type*) where
  toRq : IntPoly → Rq
  mul : IntPoly → IntPoly → IntPoly
  const : ℤ → IntPoly

/-- The constant polynomial with value `c` at position `0` and `0` elsewhere. -/
def constPoly {Coeff : Type*} [Zero Coeff] (n : Nat) (c : Coeff) : Poly Coeff n :=
  Vector.ofFn fun i => if i.val = 0 then c else 0

/-- The canonical integral lift from vector-backed integer polynomials to vector-backed
`ZMod q` polynomials. -/
def vectorIntegralLift (q n : Nat) :
    IntegralLift (Poly ℤ n) (Poly (ZMod q) n) where
  toRq := PolyBackend.mapCoeffs (vectorBackend ℤ n) (vectorBackend (ZMod q) n) rfl
    (fun z => (z : ZMod q))
  mul := schoolbookNegacyclicMul (vectorKernel ℤ n)
  const := constPoly n

end LatticeCrypto
