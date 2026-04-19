/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ProbComp

/-!
# Hard Relations

This file defines a typeclass `HardRelation X W r` for relations `r : X → W → Prop`
that are "hard" in the sense that given `x : X` no polynomial adversary can find `w : W`
such that `r x w` holds.

In the actual implementation all of these are indexed by some security parameter.
-/

open OracleSpec OracleComp ENNReal

/-! ## Non-asymptotic version

Simplified version without the asymptotic security parameter framework.
The full asymptotic version (below, commented) needs `OracleAlg` to be redesigned. -/

/-- A relation `r` is generable if there is an efficient algorithm `gen`
that produces instance-witness pairs satisfying the relation. -/
structure GenerableRelation
    (X W : Type) (r : X → W → Bool) where
  gen : ProbComp (X × W)
  gen_sound (x : X) (w : W) : (x, w) ∈ support gen → r x w

/-- Experiment for checking whether an adversary can find a witness for a generated instance. -/
def hardRelationExp {X W : Type}
    {r : X → W → Bool} (hr : GenerableRelation X W r)
    (adversary : X → ProbComp W) : ProbComp Bool := do
  let ⟨x, _⟩ ← hr.gen
  let w ← adversary x
  return (r x w)

