/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.Linarith

/-!
# Boolean observation distances

The distance of the `true` event and Boolean bias are expressed in real numbers.
The hidden-bit identity requires total branches explicitly; missing mass cannot be
silently identified with the `false` outcome.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure
/-- Absolute difference between the masses of the two Boolean outcomes. -/
@[expose]
noncomputable def boolBias (μ : Measure Bool) : ℝ :=
  |(μ {true}).toReal - (μ {false}).toReal|
/-- Absolute difference between two measures on the event `{true}`. -/
@[expose]
noncomputable def boolDist (μ ν : Measure Bool) : ℝ :=
  |(μ {true}).toReal - (ν {true}).toReal|
/-- The Boolean event distance satisfies the triangle inequality. -/
lemma boolDist_triangle (μ ν ρ : Measure Bool) :
    μ.boolDist ρ ≤ μ.boolDist ν + ν.boolDist ρ := abs_sub_le _ _ _
/-- Boolean event distance is symmetric. -/
lemma boolDist_comm (μ ν : Measure Bool) : μ.boolDist ν = ν.boolDist μ := abs_sub_comm _ _
/-- A fair hidden-bit guessing experiment has the event distance of its two total branches. -/
lemma boolBias_bind_coin (coin μ ν : Measure Bool)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcT : coin {true} = 1 / 2) (hcF : coin {false} = 1 / 2)
    (hμ : μ {true} + μ {false} = 1) (hν : ν {true} + ν {false} = 1) :
    (coin.bind fun b => (if b then μ else ν).bind
      fun z => Measure.dirac (b == z)).boolBias = μ.boolDist ν := by
  have hgame : ∀ x : Bool, (coin.bind fun b => (if b then μ else ν).bind
        fun z => Measure.dirac (b == z)) {x} = (μ {x} + ν {!x}) / 2 := by
    intro x
    simp only [Measure.bind_apply (MeasurableSet.singleton x) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool, hcT, hcF]
    cases x <;> simp [Measure.dirac_apply', div_eq_mul_inv, mul_add, mul_comm]
  have hm := congrArg ENNReal.toReal hμ
  have hn := congrArg ENNReal.toReal hν
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one] at hm hn
  unfold boolBias boolDist
  rw [hgame true, hgame false]
  simp only [Bool.not_true, Bool.not_false, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  congr 1
  linarith
end MeasureTheory.Measure

