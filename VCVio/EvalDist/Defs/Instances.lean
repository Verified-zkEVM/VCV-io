/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Basic

/-!
# Monad Evaluation Semantics Instances

This file defines various instances of evaluation semantics for different monads
-/

universe u v w

variable {α β γ : Type u}

namespace SetM

/-- Enable `support` notation for `SetM` (note the need for the monadic instance and not `Set`). -/
instance : HasEvalSet SetM where
  toSet := MonadHom.id SetM

@[simp, grind =]
lemma support_eq_run (s : SetM α) : support s = s.run := rfl

end SetM

namespace SPMF

/-- Enable probability notation for `SPMF`, using identity as the `SPMF` embedding. -/
instance : HasEvalSPMF SPMF where
  toSPMF := MonadHom.id SPMF
  support_eq _ := rfl

@[simp, grind =]
protected lemma evalDist_def (p : SPMF α) : evalDist p = p := rfl

@[grind =]
protected lemma support_eq_support (p : SPMF α) : support p = SPMF.support p := rfl

@[grind =]
lemma probOutput_eq_apply (p : SPMF α) (x : α) : Pr[= x | p] = p x := rfl

lemma evalDist_eq_iff {m} [Monad m] [HasEvalSPMF m] (mx : m α) (p : SPMF α) :
    evalDist mx = p ↔ ∀ x, Pr[= x | mx] = p x := by aesop

end SPMF

namespace PMF

/-- Enable probability notation for `PMF`, using `liftM` as the `SPMF` embedding. -/
noncomputable instance : HasEvalPMF PMF where
  toPMF := MonadHom.id PMF
  support_eq _ := by grind
  toSPMF_eq _ := rfl

@[simp] lemma evalDist_eq (p : PMF α) : evalDist p = liftM p := rfl

@[simp] lemma probOutput_eq_apply (p : PMF α) (x : α) : Pr[= x | p] = p x := by
  simp [probOutput_def]

end PMF

@[simp] lemma SPMF.evalDist_liftM (p : PMF α) :
    evalDist (m := SPMF) (liftM p) = evalDist p := rfl

@[simp] lemma SPMF.probOutput_liftM (p : PMF α) (x : α) :
    Pr[= x | (liftM p : SPMF α)] = Pr[= x | p] := rfl

@[simp] lemma SPMF.probEvent_liftM (p : PMF α) (e : α → Prop) :
    Pr[e | (liftM p : SPMF α)] = Pr[e | p] := rfl

@[simp] lemma SPMF.probFailure_liftM (p : PMF α) :
    Pr[⊥ | (liftM p : SPMF α)] = Pr[⊥ | p] := rfl

namespace Id

/-- The support of a computation in `Id` is the result being returned. -/
noncomputable instance : HasEvalPMF Id where
  toSet := MonadHom.pure SetM
  toSPMF := MonadHom.pure SPMF
  toPMF := MonadHom.pure PMF
  support_eq mx := by grind
  toSPMF_eq mx := by aesop

instance : HasEvalFinset Id where
  finSupport x := {x}
  coe_finSupport x := by aesop

@[simp, grind =]
lemma support_eq_singleton (x : Id α) : support x = {x.run} := rfl

@[simp, grind =]
lemma finSupport_eq_singleton [DecidableEq α] (x : Id α) : finSupport x = {x.run} := rfl

@[simp, grind =]
lemma probOutput_eq_ite [DecidableEq α] (x : Id α) (y : α) :
    Pr[= y | x] = if y = x.run then 1 else 0 := by
  rw [← Id.pure_run x, probOutput_pure]
  aesop

@[simp, grind =]
lemma probEvent_eq_ite [DecidableEq α] (x : Id α) (p : α → Prop) [DecidablePred p] :
    Pr[p | x] = if p x.run then 1 else 0 := by
  simp [probEvent_eq_sum_finSupport_ite]

lemma probFailure_eq_zero (x : Id α) : Pr[⊥ | x] = 0 := by aesop

end Id
