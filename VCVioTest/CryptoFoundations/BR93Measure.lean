/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Examples.BR93
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# BR93 transcript reduction under native measure semantics

The transcript implication is independent of the probabilities assigned to sampling queries.
These checks state the result using the direct free-program measure fold, including a
nonuniform interpretation that always returns the first answer. The computation frontend
still uses `SampleableType`; its discrete uniformity certificates do not calibrate this bound.
-/

public section

open OracleSpec OracleComp BR93.br93AsymmEnc OneWay MeasureTheory

namespace VCVioTest.BR93Measure

variable {PK SK Rand M : Type} [Inhabited Rand] [DecidableEq Rand]
  [SampleableType Rand] [SampleableType M] [AddCommGroup M]
  (tdp : TrapdoorPermutation PK SK Rand)
  (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M))

example [unifSpec.toPFunctor.IsMeasureSpec] :
    PFunctor.FreeM.denote (badEventExp tdp adv) {true} ≤
      PFunctor.FreeM.denote (tdpExp tdp (inverter tdp adv)) {true} := by
  exact measure_badEventExp_le_tdpExp adv

noncomputable local instance : unifSpec.toPFunctor.IsMeasureSpec where
  toMeasure _ := Measure.dirac 0
  isProbabilityMeasure _ := inferInstance

example : PFunctor.FreeM.denote (badEventExp tdp adv) {true} ≤
    PFunctor.FreeM.denote (tdpExp tdp (inverter tdp adv)) {true} := by
  exact measure_badEventExp_le_tdpExp adv

end VCVioTest.BR93Measure
