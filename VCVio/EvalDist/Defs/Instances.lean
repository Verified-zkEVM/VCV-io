/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Instances Connecting Different Evaluation Semantics

-/

universe u v w

section hasEvalSet_of_hasEvalSPMF

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]
  [HasEvalSPMF m] (mx : m α) (x : α)

/-- Given a `SPMF` evaluation instance, set the support to values of `non-zero` probability.-/
instance hasEvalSet_of_hasEvalSPMF {m : Type u → Type v} [Monad m]
    [HasEvalSPMF m] : HasEvalSet m where
  toSet := MonadHom.comp SPMF.support HasEvalSPMF.toSPMF

lemma support_of_hasEvalSPMF_def  (mx : m α) :
    support mx = SPMF.support (HasEvalSPMF.toSPMF mx) := by
  simp [support, hasEvalSet_of_hasEvalSPMF]

-- instance [HasEvalSet.Decidable m] (mx : m α) :
--     DecidablePred (Pr[= · | mx] = 0) := sorry

lemma mem_support_iff (mx : m α) (x : α) :
    x ∈ support mx ↔ Pr[= x | mx] ≠ 0 := by rfl

@[aesop unsafe 50% forward]
lemma probOutput_ne_zero_of_mem_support {mx : m α} {x : α}
   (h : x ∈ support mx) : Pr[= x | mx] ≠ 0 := by rwa [mem_support_iff] at h

@[aesop unsafe 50% apply]
lemma probOutput_eq_zero_of_not_mem_support {mx : m α} {x : α}
    (h : x ∉ support mx) : Pr[= x | mx] = 0 := by rwa [mem_support_iff, not_not] at h

@[simp low] lemma probOutput_eq_zero_iff :
    Pr[= x | mx] = 0 ↔ x ∉ support mx := by aesop

alias ⟨not_mem_support_of_probOutput_eq_zero, probOutput_eq_zero⟩ := probOutput_eq_zero_iff

@[simp low] lemma zero_eq_probOutput_iff : 0 = Pr[= x | mx] ↔ x ∉ support mx := by
  rw [eq_comm, probOutput_eq_zero_iff]
alias ⟨_, zero_eq_probOutput⟩ := zero_eq_probOutput_iff

@[simp] lemma probOutput_eq_zero_iff' [HasEvalFinset m] :
    Pr[= x | mx] = 0 ↔ x ∉ finSupport mx := by rw [mem_finSupport_iff_mem_support]; aesop
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff

@[simp] lemma zero_eq_probOutput_iff' [HasEvalFinset m] :
    0 = Pr[= x | mx] ↔ x ∉ finSupport mx := by rw [eq_comm, probOutput_eq_zero_iff']
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'

lemma probOutput_ne_zero (h : x ∈ support mx) : Pr[= x | mx] ≠ 0 := by simp [h]

lemma probOutput_ne_zero' [HasEvalFinset m]
    (h : x ∈ finSupport mx) : Pr[= x | mx] ≠ 0 := by
  exact probOutput_ne_zero mx x (mem_support_of_mem_finSupport h)

end hasEvalSet_of_hasEvalSPMF

section hasEvalSPMF_of_hasEvalPMF

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]
  [HasEvalPMF m] (mx : m α) (x : α)

/-- Given a `PMF` evaluation instance, get a `SPMF` evaluation by the natural lifting. -/
noncomputable instance hasEvalSPMF_of_hasEvalPMF {m : Type u → Type v} [Monad m]
    [HasEvalPMF m] : HasEvalSPMF m where
  toSPMF := MonadHom.comp PMF.toSPMF HasEvalPMF.toPMF

lemma evalDist_of_hasEvalPMF_def (mx : m α) :
    evalDist mx = PMF.toSPMF (HasEvalPMF.toPMF mx) := by
  simp [evalDist, hasEvalSPMF_of_hasEvalPMF]

/-- The `evalDist` arising from a `HasEvalPMF` instance never fails. -/
@[simp] lemma probFailure_eq_zero (mx : m α) :
    Pr[⊥ | mx] = 0 := by
  simp [probFailure_def, evalDist_of_hasEvalPMF_def]

@[simp] lemma tsum_probOutput_eq_one (mx : m α) :
    ∑' x, Pr[= x | mx] = 1 := by
  simp only [probOutput_def, evalDist_of_hasEvalPMF_def, SPMF.apply_eq_run_some, OptionT.run_mk,
    PMF.map_apply, Option.some.injEq]
  refine trans ?_ (PMF.tsum_coe (HasEvalPMF.toPMF mx))
  refine tsum_congr fun x => ?_
  refine (tsum_eq_single x (by aesop)).trans (by aesop)

end hasEvalSPMF_of_hasEvalPMF
