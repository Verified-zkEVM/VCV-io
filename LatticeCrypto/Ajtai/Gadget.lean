/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.Kernel
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Ajtai Gadget Matrices

Shared matrix and vector operations for Ajtai-style commitments over the generic
`LatticeCrypto.NegacyclicRing` interface.

The main object is `Ajtai.gadgetMatrix ring base rows digits`, the block
diagonal gadget matrix
`I_rows ⊗ [1, base, base^2, ..., base^(digits - 1)]`.  It maps
`rows * digits` ring elements to `rows` ring elements and is used by the
inner-outer Hachi commitment layer.
-/

open scoped BigOperators

universe u

namespace LatticeCrypto
namespace Ajtai

variable {Coeff : Type u} [CommRing Coeff]

/-! ## Backend-generic linear algebra -/

/-- The polynomial carrier for a bundled negacyclic ring. -/
abbrev Rq (ring : NegacyclicRing Coeff) := ring.Poly

/-- Vectors over the polynomial carrier of a bundled negacyclic ring. -/
abbrev RqVec (ring : NegacyclicRing Coeff) (n : Nat) := PolyVec ring.Poly n

/-- Matrices over the polynomial carrier of a bundled negacyclic ring. -/
abbrev RqMatrix (ring : NegacyclicRing Coeff) (rows cols : Nat) :=
  PolyMatrix ring.Poly rows cols

/-- The constant ring element with coefficient `c` in position zero. -/
def scalarPoly (ring : NegacyclicRing Coeff) (c : Coeff) : ring.Poly :=
  ring.backend.build fun i => if i.val = 0 then c else 0

/-- Dot product over a bundled negacyclic ring, using the ring's explicit multiplication. -/
def dot (ring : NegacyclicRing Coeff) {n : Nat}
    (u v : RqVec ring n) : ring.Poly :=
  (Vector.zipWith ring.mul u v).foldl ring.add ring.zero

/-- Matrix-vector multiplication over a bundled negacyclic ring. -/
def matVecMul (ring : NegacyclicRing Coeff) {rows cols : Nat}
    (A : RqMatrix ring rows cols) (v : RqVec ring cols) : RqVec ring rows :=
  A.map fun row => dot ring row v

/-- Pointwise vector addition over the additive group induced by the bundled ring. -/
def vecAdd (ring : NegacyclicRing Coeff) {n : Nat}
    (u v : RqVec ring n) : RqVec ring n :=
  Vector.zipWith ring.add u v

/-- Flatten equally sized vector blocks into one row-major vector. -/
def flattenBlocks {α : Type u} {blocks width : Nat}
    (xs : PolyVec (PolyVec α width) blocks) : PolyVec α (blocks * width) :=
  Vector.ofFn fun j =>
    if hwidth : width = 0 then
      False.elim (by
        have hj := j.isLt
        simp [hwidth] at hj)
    else
      let block : Fin blocks :=
        ⟨j.val / width, by
          have hj : j.val < width * blocks :=
            Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm blocks width)
          exact Nat.div_lt_of_lt_mul hj⟩
      let offset : Fin width :=
        ⟨j.val % width, Nat.mod_lt _ (Nat.pos_of_ne_zero hwidth)⟩
      (xs.get block).get offset

/-! ## Gadget matrices -/

/-- Entry of the base-`base` gadget matrix `I_rows ⊗ [1, base, ..., base^(digits-1)]`. -/
def gadgetEntry (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat} (i : Fin rows) (j : Fin (rows * digits)) : ring.Poly :=
  if j.val / digits = i.val then
    scalarPoly ring (base ^ (j.val % digits))
  else
    ring.zero

/-- The base-`base` gadget matrix `I_rows ⊗ [1, base, ..., base^(digits-1)]`. -/
def gadgetMatrix (ring : NegacyclicRing Coeff) (base : Coeff)
    (rows digits : Nat) : RqMatrix ring rows (rows * digits) :=
  Vector.ofFn fun i => Vector.ofFn fun j => gadgetEntry ring base i j

/-- Apply the gadget matrix to a decomposed vector. -/
def gadgetMul (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat} (v : RqVec ring (rows * digits)) : RqVec ring rows :=
  matVecMul ring (gadgetMatrix ring base rows digits) v

end Ajtai
end LatticeCrypto
