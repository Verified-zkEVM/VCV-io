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

/-- If we have a `HasEvalPMF m` instance, we can lift it to `HasEvalSPMF (OptionT m)`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSPMF (OptionT m) where
  toSPMF := OptionT.mapM' HasEvalSPMF.toSPMF
  support_eq _ := rfl

@[aesop unsafe norm, grind =]
lemma support_eq (mx : OptionT m α) : support mx = some ⁻¹' support mx.run := by
  ext x
  sorry

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

lemma evalDist_eq (mx : OptionT m α) :
    evalDist mx = OptionT.mapM' HasEvalSPMF.toSPMF mx := rfl

@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := sorry

@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = Pr[fun x => x.all p | mx.run] := by
  simp [probEvent_def, run]
  sorry

@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[= none | mx.run] := by
  sorry

@[simp, grind =]
lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | OptionT.lift mx] = Pr[= x | mx] := by
  simp [probOutput_eq]

@[simp, grind =]
lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | OptionT.lift mx] = Pr[p | mx] := by
  simp [probEvent_def]
  sorry

@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | liftM (n := OptionT m) mx] = Pr[= x | mx] := by
  simp [probOutput_eq]

@[simp, grind =]
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | liftM (n := OptionT m) mx] = Pr[p | mx] := by
  simp [probEvent_def]
  sorry

@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | liftM (n := OptionT m) mx] = 0 := by
  grind

end OptionT
