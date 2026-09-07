/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Data.ENNReal.AbsDiff

/-!
# Gate for `ENNReal.absDiff` as `edist`

`ENNReal.absDiff` is the extended distance Mathlib puts on `ℝ≥0∞` through the weak extended
metric on `WithTop ℝ≥0`. The bridge `absDiff_eq_edist` is what lets the metric axioms be read
off `WeakEMetricSpace ℝ≥0∞` instead of being re-proved from truncated subtraction; the entries
pin that bridge and the two laws that go through it.
-/

public section

open scoped ENNReal

namespace VCVioTest.AbsDiff

example (a b : ℝ≥0∞) : ENNReal.absDiff a b = edist a b := ENNReal.absDiff_eq_edist a b

example (a b c : ℝ≥0∞) : ENNReal.absDiff a c ≤ ENNReal.absDiff a b + ENNReal.absDiff b c :=
  ENNReal.absDiff_triangle a b c

example (a b : ℝ≥0∞) : ENNReal.absDiff a b = 0 ↔ a = b := ENNReal.absDiff_eq_zero

example (a b : ℝ≥0∞) : edist a b = 0 ↔ a = b := by
  rw [← ENNReal.absDiff_eq_edist, ENNReal.absDiff_eq_zero]

example : edist (3 : ℝ≥0∞) ⊤ = ⊤ :=
  (ENNReal.edist_eq_top_iff 3 ⊤).2 ⟨ENNReal.ofNat_ne_top, Or.inr rfl⟩

end VCVioTest.AbsDiff
