/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Option
import ToMathlib.Control.OptionT

/-!
# Probability Distributions on Potentially Failing Computations

This file gives an instance to extend a `evalDist` instance on a monad to one transformed by
the `OptionT` monad transformer.

dtumad: should add more instances and connecting lemmas
-/

universe u v w

variable (m : Type u → Type v) [Monad m] {α β γ : Type u}

namespace OptionT

instance (m : Type u → Type v) [Monad m] [HasSupport m] :
    HasSupport (OptionT m) where
  toFun mx := {x | some x ∈ support mx.run}
  toFun_pure' := by simp
  toFun_bind' x y := by
    refine Set.ext fun z => ?_
    simp [Function.comp_def, Option.elimM]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨i, hi⟩ := h
      cases i with
      | none => simp at hi
      | some j => use j; simp at hi; simp [hi]
    · obtain ⟨i, hi⟩ := h
      use some i
      simp [hi]

@[simp] lemma support_eq [HasSupport m] (mx : OptionT m α) :
    support mx = {x | some x ∈ support mx.run} := rfl

@[simp] lemma support_failure [HasSupport m] :
    support (failure : OptionT m α) = ∅ := by
  simp [support_eq]

/-- If we have a `HasPMF m` instance, we can lift it to `HasSPMF (OptionT m)`

NOTE: we do _not_ want to lift `HasSPMF` to itself (wrapped in `OptionT`). This means we only support one layer of failure (i.e. `OracleComp` satisfies `HasPMF`, and so `OptionT OracleComp` satisfies `HasSPMF`). This suffices for all known purposes. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasPMF m] :
    HasSPMF (OptionT m) where
  toSPMF := OptionT.mapM' evalDist

@[simp] lemma evalDist_eq [HasPMF m] (mx : OptionT m α) :
    evalDist mx = OptionT.mapM' evalDist mx := rfl

@[simp]
lemma probOutput_eq [HasPMF m] (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  simp [probOutput_def, OptionT.mapM', run]
  sorry

lemma probEvent_eq [HasPMF m] (mx : OptionT m α) (p : α → Prop) :
    Pr[p | mx] = Pr[Option.rec false p | mx.run] := by
  simp [probEvent_def, run]
  sorry

lemma probFailure_eq [HasPMF m] (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[= none | mx.run] := by
  sorry

@[simp] lemma probOutput_lift [HasPMF m] [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | OptionT.lift mx] = Pr[= x | mx] := by
  simp [probOutput_eq]

@[simp] lemma probEvent_lift [HasPMF m] [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | OptionT.lift mx] = Pr[p | mx] := by
  simp [probEvent_def]

instance (m : Type u → Type v) [Monad m] [HasPMF m] :
    LawfulProbFailure (OptionT m) where
    probFailure_failure := by simp [probFailure_eq]

end OptionT
