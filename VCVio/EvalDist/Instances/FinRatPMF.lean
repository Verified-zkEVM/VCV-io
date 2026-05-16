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

noncomputable instance : MonadLift Raw PMF where
  monadLift := Raw.toPMFHom.toFun _

noncomputable instance : LawfulMonadLift Raw PMF where
  monadLift_pure := Raw.toPMFHom.toFun_pure'
  monadLift_bind := Raw.toPMFHom.toFun_bind'

/-- Direct `MonadLiftT Raw SetM` defined via the underlying PMF lift. This *is* the
chain `Raw → PMF → SetM`, but expressed directly so it does not get re-derived
via `MonadLift SPMF SetM` (which would conflict with other monads' direct lifts). -/
noncomputable instance instMonadLiftTRawSetM : MonadLiftT Raw SetM where
  monadLift mx := ((liftM mx : PMF _).support : Set _)

noncomputable instance instLawfulMonadLiftTRawSetM : LawfulMonadLiftT Raw SetM where
  monadLift_pure x := by
    show ((liftM (pure x : Raw _) : PMF _).support : Set _) = {x}
    have : (liftM (pure x : Raw _) : PMF _) = pure x :=
      LawfulMonadLift.monadLift_pure (m := Raw) (n := PMF) x
    rw [this]; exact PMF.support_pure x
  monadLift_bind mx my := by
    show ((liftM (mx >>= my) : PMF _).support : Set _) =
      Bind.bind (m := SetM)
        ((liftM mx : PMF _).support : Set _)
        (fun x => ((liftM (my x) : PMF _).support : Set _))
    have hbind : (liftM (mx >>= my) : PMF _) =
        (liftM mx : PMF _) >>= fun x => (liftM (my x) : PMF _) :=
      LawfulMonadLift.monadLift_bind (m := Raw) (n := PMF) mx my
    rw [hbind]; exact PMF.support_bind _ _

/-- Compatibility: `Raw`'s SetM support equals the SPMF support of its `evalDist`. -/
noncomputable instance : EvalDistCompatible Raw where
  support_eq_SPMF_support mx := by
    show ((liftM mx : PMF _).support : Set _) =
      SPMF.support (liftM (liftM mx : PMF _) : SPMF _)
    rw [SPMF.support_liftM]

instance : HasEvalFinset Raw where
  finSupport := Raw.support
  coe_finSupport mx := by
    ext x
    rw [Finset.mem_coe, _root_.mem_support_iff, Raw.mem_support_iff]
    rw [probOutput_def, evalDist_def]
    change mx.prob x ≠ 0 ↔ (liftM (liftM mx : PMF _) : SPMF _) x ≠ 0
    rw [SPMF.liftM_apply]
    change mx.prob x ≠ 0 ↔ ((@Raw.toPMF _ (Classical.decEq _) mx) x) ≠ 0
    simp [Raw.toPMF_apply, Raw.prob_eq_prob inferInstance (Classical.decEq _) mx x]

@[simp] lemma finSupport_eq_support [DecidableEq α] (mx : Raw α) :
    finSupport mx = mx.support := rfl

end Raw
end FinRatPMF
