/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Map

/-!
# Probability Distributions on `Option` return types

File for lemmas about `evalDist` on involving `Option`.
-/

universe u v w

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [HasEvalSPMF m] {α β γ : Type u}

@[simp, grind =]
lemma probOutput_some_map_some (mx : m α) (x : α) :
    Pr[= some x | some <$> mx] = Pr[= x | mx] :=
  probOutput_map_injective mx (Option.some_injective α) x

lemma probOutput_some_map_none (mx : m α) :
    Pr[= none | some <$> mx] = 0 := by simp
