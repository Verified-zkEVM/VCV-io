/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.ProbabilityTheory.FinRatPMF
import VCVio.EvalDist.Defs.Basic

/-!
# EvalDist Instances for `FinRatPMF.Raw`

This file exposes the executable `FinRatPMF.Raw` monad to the generic `EvalDist` API.
-/

universe u

namespace FinRatPMF
namespace Raw

variable {α : Type u}

noncomputable instance : HasEvalPMF Raw where
  toPMF := Raw.toPMFHom
  support_eq _ := rfl
  toSPMF_eq _ := rfl

instance : HasEvalFinset Raw where
  finSupport := Raw.support
  coe_finSupport mx := by
    ext x
    rw [Finset.mem_coe, _root_.mem_support_iff, Raw.mem_support_iff]
    rw [probOutput_def, HasEvalPMF.evalDist_of_hasEvalPMF_def, SPMF.liftM_apply]
    change mx.prob x ≠ 0 ↔ ((@Raw.toPMF _ (Classical.decEq _) mx) x) ≠ 0
    simp [Raw.toPMF_apply, Raw.prob_eq_prob inferInstance (Classical.decEq _) mx x]

@[simp] lemma finSupport_eq_support [DecidableEq α] (mx : Raw α) :
    finSupport mx = mx.support := rfl

end Raw
end FinRatPMF
