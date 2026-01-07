/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic
import VCVio.EvalDist.Defs.Support

/-!
# Monad Evaluation Semantics Instances

This file defines various instances of evaluation semantics for different monads
-/

universe u v w

variable {α β γ : Type u}

namespace SetM

/-- Enable `support` notation for `SetM`. -/
instance : HasEvalSet SetM where
  toSet := MonadHom.id SetM

end SetM

namespace SPMF

/-- Enable probability notation for `SPMF`, using identity as the `SPMF` embedding. -/
instance : HasEvalSPMF SPMF where
  toSet := SPMF.support
  toSPMF := MonadHom.id SPMF
  support_eq _ := rfl

protected lemma evalDist_def (p : SPMF α) : evalDist p = p := rfl

protected lemma support_def (p : SPMF α) : support p = SPMF.support p := rfl

lemma probOutput_eq_apply (p : SPMF α) (x : α) : Pr[= x | p] = p x := rfl

lemma evalDist_eq_iff {m} [Monad m] [HasEvalSPMF m] (mx : m α) (p : SPMF α) :
    evalDist mx = p ↔ ∀ x, Pr[= x | mx] = p x := by aesop

end SPMF

namespace PMF

/-- Enable probability notation for `PMF`, using lift as the `SPMF` embedding. -/
noncomputable instance : HasEvalPMF PMF where
  toSPMF := PMF.toSPMF'
  toPMF := MonadHom.id PMF
  support_eq _ := sorry
  toSPMF_eq := sorry

end PMF

namespace Id

/-- The support of a computation in `Id` is the result being returned. -/
noncomputable instance : HasEvalPMF Id where
  toSet := MonadHom.pure SetM
  toSPMF := MonadHom.pure SPMF
  toPMF := MonadHom.pure PMF
  support_eq mx := by
    simp [Set.ext_iff, support, SPMF.apply_eq_run_some]
  toSPMF_eq mx := sorry

instance : HasEvalFinset Id where
  finSupport x := {x}
  coe_finSupport x := by simp; sorry

end Id

section hasEvalSet_of_hasEvalSPMF

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]
  [HasEvalSPMF m] (mx : m α) (x : α)

lemma support_eq_comp {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    (mx : m α) : support mx = MonadHom.comp SPMF.support HasEvalSPMF.toSPMF mx := by
  simp [HasEvalSPMF.support_eq]

/-- Given a `SPMF` evaluation instance, set the support to values of `non-zero` probability.-/
instance hasEvalSet_of_hasEvalSPMF {m : Type u → Type v} [Monad m]
    [HasEvalSPMF m] : HasEvalSet m where
  toSet := MonadHom.comp SPMF.support HasEvalSPMF.toSPMF

lemma support_of_hasEvalSPMF_def  (mx : m α) :
    support mx = SPMF.support (HasEvalSPMF.toSPMF mx) := by
  simp [support, hasEvalSet_of_hasEvalSPMF]

instance decidablePred_probOutput_eq_zero [HasEvalSet.Decidable m] :
    DecidablePred (Pr[= · | mx] = 0) := by
  sorry

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

@[simp] lemma probOutput_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[= x | mx] = 0 ↔ x ∉ finSupport mx := by rw [mem_finSupport_iff_mem_support]; aesop
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff

@[simp] lemma zero_eq_probOutput_iff' [HasEvalFinset m] [DecidableEq α] :
    0 = Pr[= x | mx] ↔ x ∉ finSupport mx := by rw [eq_comm, probOutput_eq_zero_iff']
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'

lemma probOutput_ne_zero (h : x ∈ support mx) : Pr[= x | mx] ≠ 0 := by simp [h]

lemma probOutput_ne_zero' [HasEvalFinset m] [DecidableEq α]
    (h : x ∈ finSupport mx) : Pr[= x | mx] ≠ 0 := by
  exact probOutput_ne_zero mx x (mem_support_of_mem_finSupport h)

@[simp] lemma probEvent_eq_zero_iff (mx : m α) (p : α → Prop) :
    Pr[p | mx] = 0 ↔ ∀ x ∈ support mx, ¬ p x := by
  simp [probEvent_eq_tsum_indicator]
  aesop

@[simp] lemma probEvent_pos_iff (mx : m α) (p : α → Prop) :
    0 < Pr[p | mx] ↔ ∃ x ∈ support mx, p x := by
  simp [pos_iff_ne_zero]

lemma probEvent_eq_tsum_subtype_mem_support (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : {x ∈ support mx | p x}, Pr[= x | mx] := by
  simp_rw [probEvent_eq_tsum_subtype, tsum_subtype]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hpx : p x
  · refine (if_pos hpx).trans ?_
    by_cases hx : x ∈ support mx
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_self, ↓reduceIte]
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_true, ↓reduceIte,
      probOutput_eq_zero_iff, not_false_eq_true]
  · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

lemma probEvent_eq_tsum_subtype_support_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : support mx, if p x then Pr[= x | mx] else 0 :=
calc
  Pr[p | mx] = (∑' x, if p x then Pr[= x | mx] else 0) := by rw [probEvent_eq_tsum_ite mx p]
  _ = ∑' x, (support mx).indicator (λ x ↦ if p x then Pr[= x | mx] else 0) x := by
    refine tsum_congr (λ x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : support mx, if p x then Pr[= x | mx] else 0 := by
    rw [tsum_subtype (support mx) (λ x ↦ if p x then Pr[= x | mx] else 0)]

lemma probEvent_eq_sum_filter_finSupport [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x ∈ (finSupport mx).filter p, Pr[= x | mx] :=
  (probEvent_eq_tsum_ite mx p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x ∈ finSupport mx, if p x then Pr[= x | mx] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

end hasEvalSet_of_hasEvalSPMF

section hasEvalSPMF_of_hasEvalPMF

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]
  [HasEvalPMF m] (mx : m α) (x : α)

/-- Given a `PMF` evaluation instance, get a `SPMF` evaluation by the natural lifting. -/
noncomputable instance hasEvalSPMF_of_hasEvalPMF {m : Type u → Type v} [Monad m]
    [HasEvalPMF m] : HasEvalSPMF m where
  toSPMF := MonadHom.comp PMF.toSPMF' HasEvalPMF.toPMF
  support_eq := sorry

lemma evalDist_of_hasEvalPMF_def (mx : m α) :
    evalDist mx = PMF.toSPMF (HasEvalPMF.toPMF mx) := by aesop

@[simp] lemma SPMF.evalDist_liftM (p : PMF α) :
    evalDist (m := SPMF) (liftM p) = evalDist (m := PMF) p := by aesop

@[simp] lemma PMF.evalDist_eq (p : PMF α) : evalDist p = liftM p := rfl

@[simp] lemma PMF.probOutput_eq_apply (p : PMF α) (x : α) : Pr[= x | p] = p x := by
  simp [probOutput_def]

@[simp] lemma SPMF.probOutput_liftM (p : PMF α) (x : α) :
    Pr[= x | (liftM p : SPMF α)] = Pr[= x | p] := rfl

@[simp] lemma SPMF.probEvent_liftM (p : PMF α) (e : α → Prop) :
    Pr[e | (liftM p : SPMF α)] = Pr[e | p] := rfl

@[simp] lemma SPMF.probFailure_liftM (p : PMF α) :
    Pr[⊥ | (liftM p : SPMF α)] = Pr[⊥ | p] := rfl

/-- The `evalDist` arising from a `HasEvalPMF` instance never fails. -/
@[simp] lemma probFailure_eq_zero (mx : m α) :
    Pr[⊥ | mx] = 0 := by
  simp [probFailure_def, evalDist_of_hasEvalPMF_def]
  sorry

@[simp] lemma tsum_probOutput_eq_one (mx : m α) :
    ∑' x, Pr[= x | mx] = 1 := by
  simp only [probOutput_def, evalDist_of_hasEvalPMF_def, SPMF.apply_eq_run_some, OptionT.run_mk,
    PMF.map_apply, Option.some.injEq]
  refine trans ?_ (PMF.tsum_coe (HasEvalPMF.toPMF mx))
  refine tsum_congr fun x => ?_
  refine (tsum_eq_single x (by aesop)).trans (by aesop)

@[simp] lemma HasEvalPMF.evalDist_eq_liftM_iff [DecidableEq α]
    (mx : m α) (p : PMF α) : evalDist mx = liftM p ↔ ∀ x, Pr[= x | mx] = p x := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · simp [probOutput_def, h]
  · simpa [SPMF.eq_liftM_iff_forall, probOutput_def] using h

@[simp] lemma HasEvalPMF.evalDist_eq_mk_iff [DecidableEq α]
    (mx : m α) (p : PMF (Option α)) : evalDist mx = SPMF.mk p ↔
      ∀ x, Pr[= x | mx] = p (some x) := by aesop

lemma HasEvalPMF.evalDist_ext [DecidableEq α] {mx : m α} {p : PMF α}
    (h : ∀ x, Pr[= x | mx] = p x) : evalDist mx = liftM p := by aesop

end hasEvalSPMF_of_hasEvalPMF
