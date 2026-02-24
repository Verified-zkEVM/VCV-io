/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Monad.Map
import VCVio.EvalDist.Defs.NeverFails

/-!
# Evaluation Distributions on Boolean-Valued Computations

Specialization lemmas for `HasEvalSPMF` computations returning `Bool`.
-/

variable {m : Type _ → Type _} [Monad m] [HasEvalSPMF m] {α : Type _}

@[simp]
lemma probOutput_true_add_false (mx : m Bool) :
    Pr[= true | mx] + Pr[= false | mx] = 1 - Pr[⊥ | mx] := by
  have h := tsum_probOutput_eq_sub mx
  rwa [tsum_fintype (L := .unconditional _), Fintype.sum_bool] at h

@[simp]
lemma probOutput_false_add_true (mx : m Bool) :
    Pr[= false | mx] + Pr[= true | mx] = 1 - Pr[⊥ | mx] := by
  rw [add_comm, probOutput_true_add_false]

lemma probOutput_true_eq_sub (mx : m Bool) :
    Pr[= true | mx] = 1 - Pr[⊥ | mx] - Pr[= false | mx] := by
  rw [← probOutput_true_add_false]
  exact (ENNReal.add_sub_cancel_right probOutput_ne_top).symm

lemma probOutput_false_eq_sub (mx : m Bool) :
    Pr[= false | mx] = 1 - Pr[⊥ | mx] - Pr[= true | mx] := by
  rw [← probOutput_false_add_true]
  exact (ENNReal.add_sub_cancel_right probOutput_ne_top).symm

@[simp]
lemma probOutput_not_map [LawfulMonad m] (mx : m Bool) :
    Pr[= true | (! ·) <$> mx] = Pr[= false | mx] :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) false

@[simp]
lemma probOutput_not_map' [LawfulMonad m] (mx : m Bool) :
    Pr[= false | (! ·) <$> mx] = Pr[= true | mx] :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) true

@[simp]
lemma probOutput_true_add_false_of_neverFail {mx : m Bool} [NeverFail mx] :
    Pr[= true | mx] + Pr[= false | mx] = 1 := by simp

@[simp]
lemma probEvent_true_eq_probOutput (mx : m Bool) :
    Pr[(· = true) | mx] = Pr[= true | mx] := probEvent_eq_eq_probOutput mx true

@[simp]
lemma probEvent_not_eq_probOutput (mx : m Bool) :
    Pr[(· = false) | mx] = Pr[= false | mx] := probEvent_eq_eq_probOutput mx false
