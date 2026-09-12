/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.TVDist.Positivity
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Positivity of total variation expressions

Total variation is nonnegative, including under casts and products, but may vanish.
-/

public section

namespace VCVioTest.Positivity

example {α : Type} (mx my : ProbComp α) (n : ℕ) : 0 ≤ (n : ℝ) * tvDist mx my := by
  positivity

example {α : Type} (mx my : ProbComp α) : 0 < tvDist mx my + 1 := by
  positivity

example {α : Type} (mx : ProbComp α) : tvDist mx mx = 0 := by
  fail_if_success have : 0 < tvDist mx mx := by positivity
  fail_if_success have : tvDist mx mx ≠ 0 := by positivity
  simp

end VCVioTest.Positivity
