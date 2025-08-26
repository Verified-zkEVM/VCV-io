/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Bind
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

instance (m : Type u → Type v) [Monad m] [HasSupportM m] :
    HasSupportM (OptionT m) where
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

@[simp] lemma support_eq [HasSupportM m] (mx : OptionT m α) :
    support mx = {x | some x ∈ support mx.run} := rfl

noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalDist m] :
    HasEvalDist (OptionT m) where
  evalDist := OptionT.mapM' evalDist
  support_eq mx := by
    simp
    ext x
    simp [mem_support_iff]
    simp [OptionT.mapM', Option.elimM, Function.comp_def]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · use x
      simp
      exact h
    · obtain ⟨x', hx'⟩ := h
      cases x' with
      | none => simp at hx'
      | some x' =>
        simp at hx'
        cases x' with
        | none => simp at hx'
        | some x' =>
          simp at hx'
          rw [hx'.2]
          exact hx'.1

@[simp] lemma probOutput_eq [HasEvalDist m] (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  sorry

@[simp] lemma probEvent_eq [HasEvalDist m] (mx : OptionT m α) (p : α → Prop) :
    Pr[p | mx] = Pr[Option.rec false p | mx.run] := by
  sorry

@[simp] lemma probFailure_eq [HasEvalDist m] (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] := by
  sorry

end OptionT
