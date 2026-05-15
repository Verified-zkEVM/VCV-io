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
  monadLift x := x
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

@[simp, grind =]
lemma support_eq_run (s : SetM α) : support s = s.run := rfl

end SetM

namespace SPMF

/-- Enable probability notation for `SPMF`, using identity as the `SPMF` embedding. -/
instance : HasEvalSPMF SPMF where
  monadLift x := x
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

@[simp, grind =]
protected lemma evalDist_def (p : SPMF α) : evalDist p = p := rfl

@[grind =]
protected lemma support_eq_support (p : SPMF α) : support p = SPMF.support p := rfl

@[grind =]
lemma probOutput_eq_apply (p : SPMF α) (x : α) : Pr[= x | p] = p x := rfl

lemma evalDist_eq_iff {m} [Monad m] [HasEvalSPMF m] (mx : m α) (p : SPMF α) :
    𝒟[mx] = p ↔ ∀ x, Pr[= x | mx] = p x := by aesop

end SPMF

namespace PMF

/-- Enable probability notation for `PMF`, using `liftM` as the `SPMF` embedding. -/
noncomputable instance : HasEvalPMF PMF where
  monadLift x := x
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

@[simp] lemma evalDist_eq (p : PMF α) : evalDist p = liftM p := rfl

@[simp] lemma probOutput_eq_apply (p : PMF α) (x : α) : Pr[= x | p] = p x := by
  simp [probOutput_def]

end PMF

@[simp] lemma SPMF.evalDist_liftM (p : PMF α) :
    evalDist (m := SPMF) (liftM p) = 𝒟[p] := rfl

@[simp] lemma SPMF.probOutput_liftM (p : PMF α) (x : α) :
    Pr[= x | (liftM p : SPMF α)] = Pr[= x | p] := rfl

@[simp] lemma SPMF.probEvent_liftM (p : PMF α) (e : α → Prop) :
    Pr[ e | (liftM p : SPMF α)] = Pr[ e | p] := rfl

@[simp] lemma SPMF.probFailure_liftM (p : PMF α) :
    Pr[⊥ | (liftM p : SPMF α)] = Pr[⊥ | p] := rfl

namespace Id

/-- The support of a computation in `Id` is the result being returned. -/
instance : HasEvalSet Id where
  monadLift x := pure x.run
  monadLift_pure _ := rfl
  monadLift_bind _ _ := by
    show ({_} : Set _) = ⋃ _ ∈ ({_} : Set _), {_}
    simp

noncomputable instance : HasEvalPMF Id where
  monadLift x := pure x.run
  monadLift_pure _ := rfl
  monadLift_bind _ _ := by
    show (pure _ : PMF _) = _ >>= _
    simp [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind]

instance : HasEvalFinset Id where
  finSupport x := {x}
  coe_finSupport x := by
    ext y
    show y ∈ (↑({x.run} : Finset _) : Set _) ↔ y ∈ SetM.run (pure x.run : SetM _)
    rw [Finset.coe_singleton]
    rfl

@[simp, grind =]
lemma support_eq_singleton (x : Id α) : support x = {x.run} := by
  show SetM.run (pure x.run : SetM α) = _
  rfl

@[simp, grind =]
lemma finSupport_eq_singleton [DecidableEq α] (x : Id α) : finSupport x = {x.run} := rfl

@[simp, grind =]
lemma probOutput_eq_ite [DecidableEq α] (x : Id α) (y : α) :
    Pr[= y | x] = if y = x.run then 1 else 0 := by
  rw [← Id.pure_run x, probOutput_pure]
  aesop

@[simp, grind =]
lemma probEvent_eq_ite (x : Id α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | x] = if p x.run then 1 else 0 := by
  classical
  rw [show x = pure x.run from rfl, probEvent_pure]
  rfl

lemma probFailure_eq_zero (x : Id α) : Pr[⊥ | x] = 0 := by aesop

end Id
