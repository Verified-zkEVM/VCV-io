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

section double_option

variable (mx : m (Option α))

omit [LawfulMonad m] in
lemma probOutput_none_add_tsum_some :
    Pr[= none | mx] + ∑' x, Pr[= some x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_probOutput_eq_sub mx]
  rw [← tsum_option _ ENNReal.summable]

@[simp]
lemma probOutput_some_map_option_map {f : α → β} (hf : f.Injective) (x : α) :
    Pr[= some (f x) | Option.map f <$> mx] = Pr[= some x | mx] := by
  refine probOutput_map_injective mx ?_ (some x)
  intro a b h
  cases a <;> cases b <;> simp_all [Option.map, hf.eq_iff]

@[simp]
lemma probOutput_none_map_option_map [DecidableEq β] (f : α → β) :
    Pr[= none | Option.map f <$> mx] = Pr[= none | mx] := by
  rw [probOutput_map_eq_tsum_ite]
  refine (tsum_eq_single none fun x hx => ?_).trans (by simp)
  cases x with
  | none => exact absurd rfl hx
  | some => simp

end double_option
