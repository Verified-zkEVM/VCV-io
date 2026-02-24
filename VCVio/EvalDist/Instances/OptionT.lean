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

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace OptionT

section HasEvalSet

/-- Lift a `HasEvalSet` instance to `OptionT` by taking the preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSet m] :
    HasEvalSet (OptionT m) where
  toSet.toFun α mx := some ⁻¹' (support (OptionT.run mx))
  toSet.toFun_pure' mx := Set.ext fun x => by simp
  toSet.toFun_bind' mx my := Set.ext fun x => by simp [Option.elimM, Option.exists]

variable [HasEvalSet m]

@[aesop unsafe norm, grind =]
lemma support_def (mx : OptionT m α) :
    support mx = some ⁻¹' (support mx.run) := rfl

@[simp low]
lemma mem_support_iff (mx : OptionT m α) (x : α) :
    x ∈ support mx ↔ some x ∈ support mx.run := by grind

@[simp]
lemma support_liftM (mx : m α) :
    support (liftM mx : OptionT m α) = support mx := by grind

@[simp]
lemma support_lift (mx : m α) :
    support (OptionT.lift mx) = support mx := by grind

end HasEvalSet

section HasEvalFinset

/-- Lift a `HasEvalFinset` instance to `OptionT`. by just taking preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSet m] [HasEvalFinset m] :
    HasEvalFinset (OptionT m) where
  finSupport mx := (finSupport mx.run).preimage some (by simp)
  coe_finSupport := by aesop

variable [HasEvalSet m] [HasEvalFinset m]

@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : OptionT m α) :
    finSupport mx = (finSupport mx.run).preimage some (by simp) := rfl

@[simp low]
lemma mem_finSupport_iff [DecidableEq α] (mx : OptionT m α) (x : α) :
    x ∈ finSupport mx ↔ ∃ y ∈ finSupport mx.run, x = some y := by grind

@[simp]
lemma finSupport_liftM [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : OptionT m α) = finSupport mx := by grind

@[simp]
lemma finSupport_lift [DecidableEq α] (mx : m α) :
    finSupport (OptionT.lift mx) = finSupport mx := by grind

end HasEvalFinset

section HasEvalSPMF

/-- Lift a `HasEvalSPMF` instance to `OptionT` by setting probability `Pr[= x | mx]` to
be the probability `Pr[= some x | mx.run]`, so `none` corresponds to `Pr[⊥ | mx]`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSPMF (OptionT m) where
  toSPMF := OptionT.mapM' HasEvalSPMF.toSPMF
  support_eq _ := sorry

instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSet.LawfulFailure (OptionT m) where
  support_failure' := by aesop

variable [HasEvalSPMF m]

lemma evalDist_def (mx : OptionT m α) :
    evalDist mx = OptionT.mapM' HasEvalSPMF.toSPMF mx := rfl

@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  sorry

@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = Pr[fun x => x.all p | mx.run] := by
  sorry

@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[= none | mx.run] := by
  rw [probFailure_eq_sub_probEvent]
  sorry

@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | liftM (n := OptionT m) mx] = Pr[= x | mx] := by simp [probOutput_eq]

@[simp, grind =]
lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | OptionT.lift mx] = Pr[= x | mx] := by simp [probOutput_eq]

@[simp, grind =]
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | liftM (n := OptionT m) mx] = Pr[p | mx] := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_liftM]

@[simp, grind =]
lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | OptionT.lift mx] = Pr[p | mx] := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_lift]

@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | liftM (n := OptionT m) mx] = 0 := by grind

@[simp, grind =]
lemma probFailure_lift [LawfulMonad m] (mx : m α) :
    Pr[⊥ | OptionT.lift mx] = 0 := by grind

end HasEvalSPMF

end OptionT
