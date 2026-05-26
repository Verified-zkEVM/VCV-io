/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
import LatticeCrypto.Ring.Kernel

/-!
# Module-SIS Over Bundled Negacyclic Rings

This file specializes the generic SIS game to the bundled lattice-ring matrix
interface.  The relation is stated in collision form: given a random matrix
`A`, find two distinct short vectors with the same image under `A`.

For algebraic instantiations where `ring.matVecMul` is linear, this is the
usual kernel form of Module-SIS by taking the difference of the two vectors.
-/

open OracleComp ENNReal

universe u

namespace LatticeCrypto
namespace ModuleSIS

variable {Coeff : Type u} [CommRing Coeff]

/-- A collision-form Module-SIS solution for a matrix with `cols` columns. -/
structure Solution (ring : NegacyclicRing Coeff) (cols : Nat) where
  /-- First short vector. -/
  left : PolyVec ring.Poly cols
  /-- Second short vector. -/
  right : PolyVec ring.Poly cols

/-- The collision-form Module-SIS relation for a fixed matrix. -/
def relation (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (PolyVec ring.Poly cols)]
    [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : Solution ring cols → Bool)
    (A : PolyMatrix ring.Poly rows cols) (z : Solution ring cols) : Bool :=
  decide (z.left ≠ z.right) &&
    isShort z &&
    decide (ring.matVecMul A z.left = ring.matVecMul A z.right)

/-- Module-SIS as an instance of the generic SIS search game. -/
def problem (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PolyMatrix ring.Poly rows cols)]
    [DecidableEq (PolyVec ring.Poly cols)]
    [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : Solution ring cols → Bool) :
    SIS.Problem (PolyMatrix ring.Poly rows cols) (Solution ring cols) where
  sampleChallenge := $ᵗ PolyMatrix ring.Poly rows cols
  isValid := relation ring isShort

/-- A Module-SIS adversary. -/
abbrev Adversary (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PolyMatrix ring.Poly rows cols)]
    [DecidableEq (PolyVec ring.Poly cols)]
    [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : Solution ring cols → Bool) :=
  SIS.Adversary (problem ring rows cols isShort)

/-- The Module-SIS experiment. -/
def experiment (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PolyMatrix ring.Poly rows cols)]
    [DecidableEq (PolyVec ring.Poly cols)]
    [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : Solution ring cols → Bool)
    (adv : Adversary ring rows cols isShort) : ProbComp Bool :=
  SIS.experiment (problem ring rows cols isShort) adv

/-- The Module-SIS advantage. -/
noncomputable def advantage (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PolyMatrix ring.Poly rows cols)]
    [DecidableEq (PolyVec ring.Poly cols)]
    [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : Solution ring cols → Bool)
    (adv : Adversary ring rows cols isShort) : ℝ≥0∞ :=
  SIS.advantage (problem ring rows cols isShort) adv

end ModuleSIS
end LatticeCrypto
