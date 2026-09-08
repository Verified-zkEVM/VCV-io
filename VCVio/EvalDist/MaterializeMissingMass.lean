/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Measure

/-! # Explicit execution missing-mass outcomes

`materializeMissingMass` names the semantic completion of a computation's successful-output
measure. `none` is execution failure/nontermination mass; `some x` is a returned value, including
any explicit protocol rejection or fault already encoded by `x`. This is a measure operation,
not an executable recovery procedure or a decoder that silently identifies these outcomes.
-/

public section

open MeasureTheory

universe u v
variable {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α]

/-- Materialize execution missing mass as `none`, retaining returned values as `some`. -/
noncomputable def materializeMissingMass (program : m α) : Measure (Option α) :=
  (evalDist program).withFailure

/-- The semantics' subprobability bound makes the materialized outcome measure a probability. -/
theorem materializeMissingMass_isProbabilityMeasure (program : m α) :
    IsProbabilityMeasure (materializeMissingMass program) :=
  Measure.withFailure_isProbabilityMeasure _ (evalDist_apply_univ_le_one program)

/-- Execution failure/nontermination is precisely the missing successful-output mass. -/
theorem materializeMissingMass_none [DiscreteMeasurableSpace α] (program : m α) :
    materializeMissingMass program {none} = 1 - evalDist program Set.univ :=
  Measure.withFailure_apply_none _

/-- Explicit returned outcomes keep their original mass, including returned faults. -/
theorem materializeMissingMass_some [DiscreteMeasurableSpace α] (program : m α) (x : α) :
    materializeMissingMass program {some x} = evalDist program {x} :=
  Measure.withFailure_apply_some _ x

/-- Under an explicit total-mass proof, materialization contributes no execution fault. -/
theorem materializeMissingMass_none_of_total [DiscreteMeasurableSpace α] (program : m α)
    (total : evalDist program Set.univ = 1) :
    materializeMissingMass program {none} = 0 := by
  rw [materializeMissingMass_none, total, tsub_self]
