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

/-- Union bound: the probability that *some* event `E i` holds is at most the sum of the
individual probabilities, over a finite index set `s`. -/
lemma probEvent_exists_finset_le_sum [HasEvalSPMF m]
    {ι : Type u} (s : Finset ι) (mx : m α) (E : ι → α → Prop)
    [DecidablePred (fun x => ∃ i ∈ s, E i x)]
    [∀ i, DecidablePred (E i)] :
    Pr[(fun x => ∃ i ∈ s, E i x) | mx] ≤ s.sum (fun i => Pr[E i | mx]) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s haNotMem ih
  have hE : (fun x => ∃ i ∈ insert a s, E i x) = fun x => E a x ∨ ∃ i ∈ s, E i x := by
    funext x; simp [Finset.mem_insert, or_and_right, exists_or]
  have hor :
      Pr[(fun x => E a x ∨ ∃ i ∈ s, E i x) | mx]
        ≤ Pr[E a | mx] + Pr[(fun x => ∃ i ∈ s, E i x) | mx] := by
    rw [probEvent_eq_tsum_ite (mx := mx) (p := fun x => E a x ∨ ∃ i ∈ s, E i x),
        probEvent_eq_tsum_ite (mx := mx) (p := E a),
        probEvent_eq_tsum_ite (mx := mx) (p := fun x => ∃ i ∈ s, E i x)]
    have hle : (∑' y : α, if (E a y ∨ ∃ i ∈ s, E i y) then Pr[= y | mx] else 0)
        ≤ ∑' y : α, ((if E a y then Pr[= y | mx] else 0) +
                     (if (∃ i ∈ s, E i y) then Pr[= y | mx] else 0)) :=
      ENNReal.tsum_le_tsum fun y => by
        by_cases ha' : E a y <;> by_cases hs' : (∃ i ∈ s, E i y) <;> simp [ha', hs']
    calc _ ≤ _ := hle
      _ = _ := by simpa using ENNReal.tsum_add
  calc Pr[(fun x => ∃ i ∈ insert a s, E i x) | mx]
      = Pr[(fun x => E a x ∨ ∃ i ∈ s, E i x) | mx] := by rw [hE]
    _ ≤ Pr[E a | mx] + Pr[(fun x => ∃ i ∈ s, E i x) | mx] := hor
    _ ≤ Pr[E a | mx] + s.sum (fun i => Pr[E i | mx]) := by
        gcongr
    _ = (insert a s).sum (fun i => Pr[E i | mx]) := by
        rw [Finset.sum_insert haNotMem]

end HasEvalSPMF
