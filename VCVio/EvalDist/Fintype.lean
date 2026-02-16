/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Basic

/-!
# Lemmas for Probability Over Finite Spaces

This file houses lemmas about `HasEvalDist m` and related classes when a computation `mx : m α`
is defined via a binding/mapping operation over a finite type.
In particular `Finset.sum` versions of many `tsum` related lemmas about `HasEvalDist`.
-/

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

namespace HasEvalSPMF

lemma probOutput_bind_eq_sum_fintype [HasEvalSPMF m]
    (mx : m α) (my : α → m β) [Fintype α] (y : β) :
    Pr[= y | mx >>= my] = ∑ x : α, Pr[= x | mx] * Pr[= y | my x] :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_fintype _)

lemma probFailure_bind_eq_sum_fintype [HasEvalSPMF m]
    (mx : m α) (my : α → m β) [Fintype α] :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑ x : α, Pr[= x | mx] * Pr[⊥ | my x] :=
  (probFailure_bind_eq_add_tsum mx my).trans (congr_arg (Pr[⊥ | mx] + ·) <| tsum_fintype _)

lemma probEvent_bind_eq_sum_fintype [HasEvalSPMF m]
    (mx : m α) (my : α → m β) [Fintype α] (q : β → Prop) :
    Pr[q | mx >>= my] = ∑ x : α, Pr[= x | mx] * Pr[q | my x] :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_fintype _)

end HasEvalSPMF
