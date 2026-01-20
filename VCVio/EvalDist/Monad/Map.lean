/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Distributions of Computations with `map`

File for lemmas about `evalDist` and `support` involving the monadic `map`.

Note: we focus on lemmas that don't hold naively when reducing `<$>` to `>>=` using monad laws,
since `map_eq_bind_pure_comp` can be applied to use `bind` lemmas fairly easily.
Instead we focus on the cases like `f <$> mx` for injective `f`, which allow stronger statements.

TODO: many lemmas should probably have mirrored `bind_pure` versions.
-/

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

@[simp] lemma support_map [HasEvalSet m] [LawfulMonad m] (f : α → β) (mx : m α) :
    support (f <$> mx) = f '' support mx := by aesop (rule_sets := [UnfoldEvalDist])

@[simp] lemma finSupport_map [HasEvalSet m] [HasEvalFinset m] [LawfulMonad m]
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (mx : m α) : finSupport (f <$> mx) = (finSupport mx).image f := by
  grind [map_eq_bind_pure_comp]

@[simp] lemma evalDist_map [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (f : α → β) :
    evalDist (f <$> mx) = f <$> (evalDist mx) := by simp [map_eq_bind_pure_comp]

@[simp] lemma evalDist_comp_map [HasEvalSPMF m] [LawfulMonad m] (mx : m α) :
    evalDist ∘ (fun f => f <$> mx) = fun f : (α → β) => f <$> evalDist mx := by aesop

variable [HasEvalSPMF m] (mx : m α) (f : α → β)

@[simp, grind =]
lemma probEvent_bind_pure_comp (q : β → Prop) :
    Pr[q | mx >>= pure ∘ f] = Pr[q ∘ f | mx] := by
  have := Classical.decPred q
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  simp

variable [LawfulMonad m]

/-- Write the probability of an output after mapping the result of a computation as a sum
over all outputs such that they map to the correct final output, using subtypes.
This lemma notably doesn't require decidable equality on the final type, unlike most
lemmas about probability when mapping a computation. -/
lemma probOutput_map_eq_tsum_subtype (y : β) :
    Pr[= y | f <$> mx] = ∑' x : {x ∈ support mx | y = f x}, Pr[= x | mx] := by
  simp only [map_eq_bind_pure_comp, tsum_subtype _, probOutput_bind_eq_tsum, Function.comp_apply,
    Set.indicator, Set.mem_setOf_eq]
  refine (tsum_congr (λ x ↦ ?_))
  by_cases hy : y = f x <;> by_cases hx : x ∈ support mx <;> simp [hy, hx]

lemma probOutput_map_eq_tsum (y : β) :
    Pr[= y | f <$> mx] = ∑' x, Pr[= x | mx] * Pr[= y | (pure (f x) : m β)] := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply]

lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
    Pr[= y | f <$> mx] = ∑' x : support mx, if y = f x then Pr[= x | mx] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
    probOutput_pure, mul_ite, mul_one, mul_zero]

lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    Pr[= y | f <$> mx] = ∑' x : α, if y = f x then Pr[= x | mx] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
    mul_ite, mul_one, mul_zero]

@[grind =]
lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    Pr[= y | f <$> mx] = ∑ x : α, if y = f x then Pr[= x | mx] else 0 :=
  (probOutput_map_eq_tsum_ite mx f y).trans (tsum_eq_sum' <|
    by simp only [Finset.coe_univ, Set.subset_univ])

@[grind =]
lemma probOutput_map_eq_sum_finSupport_ite [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    (y : β) : Pr[= y | f <$> mx] = ∑ x ∈ finSupport mx, if y = f x then Pr[= x | mx] else 0 :=
  (probOutput_map_eq_tsum_ite mx f y).trans (tsum_eq_sum' <|
    by simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
      probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not, and_imp,
      imp_self, implies_true])

@[simp, grind =]
lemma probOutput_map_eq_sum_filter_finSupport [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    (y : β) : Pr[= y | f <$> mx] = ∑ x ∈ (finSupport mx).filter (y = f ·), Pr[= x | mx] := by
  rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

@[simp, grind =]
lemma probFailure_map : Pr[⊥ | f <$> mx] = Pr[⊥ | mx] := by
  simp [map_eq_bind_pure_comp, probFailure_bind_eq_tsum]

@[simp, grind =]
lemma probEvent_map (q : β → Prop) : Pr[q | f <$> mx] = Pr[q ∘ f | mx] := by
  grind [= map_eq_bind_pure_comp]

lemma probEvent_comp (q : β → Prop) : Pr[q ∘ f | mx] = Pr[q | f <$> mx] :=
  symm <| probEvent_map mx f q

lemma probOutput_map_eq_probOutput_inverse (f : α → β) (g : β → α)
    (hl : Function.LeftInverse f g) (hr : Function.RightInverse f g)
    (y : β) : Pr[= y | f <$> mx] = Pr[= g y | mx] := by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single (g y) (λ x hx ↦ ?_)).trans ?_
  · suffices y ≠ f x by simp [this]
    exact (λ h ↦ hx ((congr_arg g h).trans (hr x)).symm)
  · simp [hl y]

lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (mx : m α) (f : α → β) :
    Pr[⊥ | mx] = 1 - ∑ y : β, Pr[= y | f <$> mx] := by
  rw [← probFailure_map (f := f), probFailure_eq_sub_tsum, tsum_fintype]

lemma probOutput_map_eq_single {mx : m α} {f : α → β} {y : β}
    (x : α) (h : ∀ x' ∈ support mx, y = f x' → x = x') (h' : f x = y) :
    Pr[= y | f <$> mx] = Pr[= x | mx] := by
  -- simp [probOutput_map_eq_tsum_sub ]
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single x (λ x' hx' ↦ ?_)).trans (by rw [h', probOutput_pure_self, mul_one])
  specialize h x'
  simp only [mul_eq_zero, probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff]
  tauto

section injective

@[grind ., aesop safe forward]
lemma probOutput_map_injective (mx : m α) {f : α → β} (hf : f.Injective) (x : α) :
    Pr[= f x | f <$> mx] = Pr[= x | mx] := by
  rw [probOutput_map_eq_single x _ rfl]
  grind

end injective
