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
interface.  The relation is stated in kernel form: given a random matrix
`A`, find a nonzero short vector in the kernel of `A`.
-/

open OracleComp ENNReal

universe u

namespace LatticeCrypto
namespace ModuleSIS

variable {Coeff : Type u} [CommRing Coeff]

/-- A Module-SIS solution for a matrix with `cols` columns. -/
abbrev Solution (ring : NegacyclicRing Coeff) (cols : Nat) :=
  PolyVec ring.Poly cols

/-- The kernel-form Module-SIS relation for a fixed matrix. -/
def relation (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (PolyVec ring.Poly cols)]
    [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : Solution ring cols → Bool)
    (A : PolyMatrix ring.Poly rows cols) (z : Solution ring cols) : Bool :=
  decide (z ≠ 0) &&
    isShort z &&
    decide (A *ᵥ z = 0)

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
