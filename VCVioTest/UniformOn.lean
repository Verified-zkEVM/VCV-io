/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.Probability.UniformOn

/-!
# Regression tests for finite uniform measures

These examples exercise the measure-level finite-uniform API on fair bits. They check point mass,
the independent-pair characterization, and the bijective pushforward used by one-time-pad
arguments.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace VCVioTest.UniformOn

/-- A fair bit assigns mass one half to each outcome. -/
example (bit : Bool) :
    uniformOn (Set.univ : Set Bool) {bit} = (2 : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ_apply_singleton]
  norm_num

/-- Two independent fair bits are uniform on the four pairs. -/
example :
    uniformOn (Set.univ : Set (Bool × Bool)) =
      (uniformOn (Set.univ : Set Bool)).prod (uniformOn (Set.univ : Set Bool)) :=
  uniformOn_univ_prod

/-- XOR by a fixed bit is a bijection, so encrypting a uniform bit preserves uniformity. -/
example (message : Bool) :
    Measure.map (fun key => Bool.xor message key) (uniformOn (Set.univ : Set Bool)) =
      uniformOn (Set.univ : Set Bool) := by
  apply map_uniformOn_univ_of_bijective Measurable.of_discrete
  cases message <;> decide

/-- Uniformity is not vacuous: a fair bit is not concentrated on `false`. -/
example : uniformOn (Set.univ : Set Bool) ≠ Measure.dirac false := by
  intro h
  have htrue := uniformOn_univ_apply_singleton (α := Bool) true
  rw [h] at htrue
  norm_num at htrue
  exact ENNReal.inv_ne_zero.mpr (by norm_num) htrue.symm

end VCVioTest.UniformOn
