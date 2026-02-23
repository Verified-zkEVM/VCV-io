/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.OptionT
import VCVio.EvalDist.Option
import VCVio.EvalDist.Defs.AlternativeMonad

/-!
# Probability Distributions on Potentially Failing Computations

This file gives an instance to extend a `evalDist` instance on a monad to one transformed by
the `OptionT` monad transformer.

dt: should add more instances and connecting lemmas
-/

universe u v w

variable (m : Type u → Type v) [Monad m] [HasEvalSPMF m] {α β γ : Type u}

namespace OptionT

/-- TODO: fintype version of this lemma -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSet m] :
    HasEvalSet (OptionT m) where
  toSet := OptionT.mapM' HasEvalSet.toSet

@[simp]
lemma support_liftM (m : Type u → Type v) [Monad m] [HasEvalSet m]
    (mx : m α) : support (liftM mx : OptionT m α) = support mx := by
  exact mapM'_lift HasEvalSet.toSet mx

/-- If we have a `HasEvalPMF m` instance, we can lift it to `HasEvalSPMF (OptionT m)`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSPMF (OptionT m) where
  toSPMF := OptionT.mapM' HasEvalSPMF.toSPMF
  support_eq _ := sorry

lemma evalDist_eq (mx : OptionT m α) :
    evalDist mx = OptionT.mapM' HasEvalSPMF.toSPMF mx := rfl

@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  simp only [probOutput_def]
  show (OptionT.mapM' HasEvalSPMF.toSPMF mx) x = HasEvalSPMF.toSPMF mx.run (some x)
  rw [show (OptionT.mapM' HasEvalSPMF.toSPMF mx : SPMF α) =
    HasEvalSPMF.toSPMF mx.run >>= fun y =>
      match y with | some a => pure a | none => failure from rfl]
  rw [SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (some x) fun y hy => ?_).trans (by simp)
  cases y with
  | none => simp
  | some a =>
      have : x ≠ a := by intro h; subst h; exact hy rfl
      simp [this]

@[aesop unsafe norm, grind =]
lemma support_eq (mx : OptionT m α) : support mx = some ⁻¹' support mx.run := by
  ext x
  simp only [Set.mem_preimage, mem_support_iff, probOutput_eq]

/-- Lift a `finSupport` instance to `OptionT`. by just taking preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] [HasEvalFinset m] :
    HasEvalFinset (OptionT m) where
  finSupport mx := (finSupport mx.run).preimage Option.some (by simp)
  coe_finSupport := by aesop

@[aesop unsafe norm]
lemma finSupport_eq [HasEvalFinset m] [DecidableEq α] (mx : OptionT m α) :
    finSupport mx = (finSupport mx.run).preimage Option.some (by simp) := rfl

@[simp, grind =]
lemma mem_finSupport_iff [HasEvalFinset m] [DecidableEq α] (mx : OptionT m α) (x : α) :
    x ∈ finSupport mx ↔ ∃ y ∈ finSupport mx.run, x = some y := by
  grind

instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSet.LawfulFailure (OptionT m) where
  support_failure' := by aesop

@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] + Pr[= none | mx.run] := by
  simp only [probFailure_def, probOutput_def]
  rw [show evalDist mx = (HasEvalSPMF.toSPMF mx.run >>= fun y =>
      match y with | some a => pure a | none => failure : SPMF α) from rfl]
  simp [SPMF.toPMF_bind, Option.elimM, PMF.bind_apply, tsum_option,
    SPMF.toPMF_failure, SPMF.toPMF_pure, SPMF.apply_eq_toPMF_some, evalDist_def]

@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] + Pr[= none | mx.run] = Pr[fun x => x.all p | mx.run] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_eq]
  rw [add_comm, tsum_option _ ENNReal.summable]
  congr 1
  · simp
  · congr 1; ext a; simp [Set.indicator_apply, decide_eq_true_eq]

@[simp, grind =]
lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | OptionT.lift mx] = Pr[= x | mx] := by
  simp [probOutput_eq]

@[simp, grind =]
lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | OptionT.lift mx] = Pr[p | mx] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_lift]

@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | liftM (n := OptionT m) mx] = Pr[= x | mx] := by
  simp [probOutput_eq]

@[simp, grind =]
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | liftM (n := OptionT m) mx] = Pr[p | mx] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_liftM]

@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | liftM (n := OptionT m) mx] = Pr[⊥ | mx] := by
  rw [probFailure_eq]
  simp [probOutput_some_map_none]

end OptionT
