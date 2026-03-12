/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Map
import VCVio.EvalDist.Defs.NeverFails

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

omit [LawfulMonad m] in
lemma probEvent_isSome_eq_one_sub_probOutput_none [NeverFail mx] :
    Pr[fun r => r.isSome | mx] = 1 - Pr[= none | mx] := by
  rw [probEvent_eq_tsum_ite]
  rw [tsum_option (fun r : Option α => if r.isSome then Pr[= r | mx] else 0) ENNReal.summable]
  simp only [Option.isSome, reduceCtorEq, ↓reduceIte, zero_add]
  have htotal : Pr[= none | mx] + ∑' x, Pr[= some x | mx] = 1 := by
    simpa [probFailure_eq_zero (mx := mx), tsub_zero] using probOutput_none_add_tsum_some (mx := mx)
  have hnone_ne_top : Pr[= none | mx] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
  have htotal' : (∑' x, Pr[= some x | mx]) + Pr[= none | mx] = 1 := by
    simpa [add_comm] using htotal
  exact ENNReal.eq_sub_of_add_eq hnone_ne_top htotal'

omit [LawfulMonad m] in
lemma sum_probOutput_some_le_one [Fintype α] :
    ∑ x : α, Pr[= (some x : Option α) | mx] ≤ 1 := by
  classical
  calc
    ∑ x : α, Pr[= (some x : Option α) | mx]
      ≤ ∑' y : Option α, Pr[= y | mx] := by
          rw [← tsum_fintype (L := .unconditional _)]
          have h := tsum_option (fun y : Option α => Pr[= y | mx]) ENNReal.summable
          rw [h]
          exact le_add_self
    _ ≤ 1 := tsum_probOutput_le_one

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
