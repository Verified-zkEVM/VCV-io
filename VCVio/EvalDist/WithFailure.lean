/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Measure

/-! # Evaluation with an explicit failure result

`evalDistWithFailure` names the semantic completion of a computation's successful-output
measure. `none` is execution failure/nontermination mass; `some x` is a returned value, including
any explicit protocol rejection or fault already encoded by `x`. This is a measure operation,
not an executable recovery procedure or a decoder that silently identifies these outcomes.

This is a thin measure-only interface to `Measure.withFailure`. Unlike the discrete probability
bridges in `VCVio.EvalDist.FailureMeasure`, its laws require no `SPMF` lift or compatibility
instance. ArkLib uses this boundary before choosing a discrete probability interpretation.
-/

public section

open MeasureTheory

universe u v
variable {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α]

/-- Evaluate a distribution with `none` for failure to return and `some` for returned values. -/
noncomputable def evalDistWithFailure (program : m α) : Measure (Option α) :=
  (evalDist program).withFailure

/-- The semantics' subprobability bound makes the result a probability measure. -/
theorem evalDistWithFailure_isProbabilityMeasure (program : m α) :
    IsProbabilityMeasure (evalDistWithFailure program) :=
  Measure.withFailure_isProbabilityMeasure _ (evalDist_apply_univ_le_one program)

/-- Execution failure/nontermination is precisely the missing successful-output mass. -/
theorem evalDistWithFailure_none [DiscreteMeasurableSpace α] (program : m α) :
    evalDistWithFailure program {none} = 1 - evalDist program Set.univ :=
  Measure.withFailure_apply_none _

/-- Explicit returned outcomes keep their original mass, including returned faults. -/
theorem evalDistWithFailure_some [DiscreteMeasurableSpace α] (program : m α) (x : α) :
    evalDistWithFailure program {some x} = evalDist program {x} :=
  Measure.withFailure_apply_some _ x

/-- When the computation has total mass one, `none` has probability zero. -/
theorem evalDistWithFailure_none_of_total [DiscreteMeasurableSpace α] (program : m α)
    (total : evalDist program Set.univ = 1) :
    evalDistWithFailure program {none} = 0 := by
  rw [evalDistWithFailure_none, total, tsub_self]
