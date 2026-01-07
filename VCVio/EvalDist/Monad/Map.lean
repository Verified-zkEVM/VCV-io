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


-- variable (oa : OracleComp spec α) (f : α → β)

-- /-- Write the probability of an output after mapping the result of a computation as a sum
-- over all outputs such that they map to the correct final output, using subtypes.
-- This lemma notably doesn't require decidable equality on the final type, unlike most
-- lemmas about probability when mapping a computation. -/
-- lemma probOutput_map_eq_tsum_subtype (y : β) :
--     [= y | f <$> oa] = ∑' x : {x ∈ oa.support | y = f x}, [= x | oa] := by
--   simp only [map_eq_bind_pure_comp, tsum_subtype _ (λ x ↦ [= x | oa]), probOutput_bind_eq_tsum,
--     Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero,
--     Set.indicator, Set.mem_setOf_eq]
--   refine (tsum_congr (λ x ↦ ?_))
--   by_cases hy : y = f x <;> by_cases hx : x ∈ oa.support <;> simp [hy, hx]

-- lemma probOutput_map_eq_tsum (y : β) :
--     [= y | f <$> oa] = ∑' x, [= x | oa] * [= y | (pure (f x) : OracleComp spec β)] := by
--   simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply]

-- lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
--     [= y | f <$> oa] = ∑' x : oa.support, if y = f x then [= x | oa] else 0 := by
--   simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
--     probOutput_pure, mul_ite, mul_one, mul_zero]

-- lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
--     [= y | f <$> oa] = ∑' x : α, if y = f x then [= x | oa] else 0 := by
--   simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
--     mul_ite, mul_one, mul_zero]

-- lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
--     [= y | f <$> oa] = ∑ x : α, if y = f x then [= x | oa] else 0 :=
--   (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
--     by simp only [Finset.coe_univ, Set.subset_univ])

-- lemma probOutput_map_eq_sum_finSupport_ite [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
--     (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport, if y = f x then [= x | oa] else 0 :=
--   (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
--     by simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
--       probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not, and_imp,
--       imp_self, implies_true])

-- lemma probOutput_map_eq_sum_filter_finSupport [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
--     (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport.filter (y = f ·), [= x | oa] := by
--   rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

-- @[simp]
-- lemma probFailure_map : [⊥ | f <$> oa] = [⊥ | oa] := by
--   simp [probFailure, evalDist_map, PMF.map_apply, PMF.monad_map_eq_map]
--   refine (tsum_eq_single none λ x ↦ ?_).trans (if_pos rfl)
--   cases x <;> simp

-- @[simp]
-- lemma probEvent_map (q : β → Prop) : [q | f <$> oa] = [q ∘ f | oa] := by
--   simp only [probEvent, evalDist_map, PMF.toOuterMeasure_map_apply, Function.comp_apply]
--   simp [PMF.monad_map_eq_map]
--   refine congr_arg (oa.evalDist.toOuterMeasure) ?_
--   simp only [Set.preimage, Set.mem_image, Set.mem_setOf_eq, Set.ext_iff]
--   intro x
--   cases x <;> simp
-- lemma probEvent_comp (q : β → Prop) : [q ∘ f | oa] = [q | f <$> oa] :=
--   symm <| probEvent_map oa f q

-- lemma probOutput_map_eq_probOutput_inverse (f : α → β) (g : β → α)
--     (hl : Function.LeftInverse f g) (hr : Function.RightInverse f g)
--     (y : β) : [= y | f <$> oa] = [= g y | oa] := by
--   rw [probOutput_map_eq_tsum]
--   refine (tsum_eq_single (g y) (λ x hx ↦ ?_)).trans ?_
--   · suffices y ≠ f x by simp [this]
--     exact (λ h ↦ hx ((congr_arg g h).trans (hr x)).symm)
--   · simp [hl y]

-- lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (oa : OracleComp spec α) (f : α → β) :
--     [⊥ | oa] = 1 - ∑ y : β, [= y | f <$> oa] := by
--   rw [← probFailure_map (f := f), probFailure_eq_sub_tsum, tsum_fintype]
