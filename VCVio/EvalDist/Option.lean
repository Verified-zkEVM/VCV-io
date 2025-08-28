/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Basic
import ToMathlib.Control.OptionT

/-!
# Probability Distributions on `Option` return types

File for lemmas about `evalDist` on optional values.
-/

universe u v w

variable {m : Type u → Type v} [Monad m] [HasEvalDist m] {α β γ : Type u}

@[simp] lemma probOutput_some_map_some (mx : m α) (x : α) :
    Pr[= some x | some <$> mx] = Pr[= x | mx] := by
  sorry

@[simp] lemma probOutput_some_map_none (mx : m α) :
    Pr[= none | some <$> mx] = 0 := sorry
