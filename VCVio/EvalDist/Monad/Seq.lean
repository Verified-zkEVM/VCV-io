/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Monad.Map

/-!
# Evaluation Distributions of Computations with `seq`

File for lemmas about `evalDist` and `support` involving the monadic `seq`, `seqLeft`,
and `seqRight` operations.

TODO: many lemmas should probably have mirrored versions for `bind_map`.
-/

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

section seq

@[simp] lemma support_seq [HasEvalSet m] [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
    support (mf <*> mx) = ⋃ f ∈ support mf, f '' support mx := by
  simp [seq_eq_bind_map]

@[simp] lemma finSupport_seq [HasEvalSet m] [HasEvalFinset m] [LawfulMonad m]
    [DecidableEq (α → β)] [DecidableEq α] [DecidableEq β]
    (mf : m (α → β)) (mx : m α) :
    finSupport (mf <*> mx) = (finSupport mf).biUnion fun f => (finSupport mx).image f := by
  simp [seq_eq_bind_map]

@[simp] lemma evalDist_seq [HasEvalSPMF m] [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
    evalDist (mf <*> mx) = evalDist mf <*> evalDist mx := by simp [seq_eq_bind_map]

lemma probOutput_seq_eq_tsum [HasEvalSPMF m] [LawfulMonad m]
    (mf : m (α → β)) (mx : m α) (y : β) :
    Pr[= y | mf <*> mx] =
      ∑' f, ∑' x, Pr[= f | mf] * Pr[= x | mx] * Pr[= y | (pure (f x) : m β)] := by
  simp [seq_eq_bind_map, probOutput_bind_eq_tsum, probOutput_map_eq_tsum,
    ← ENNReal.tsum_mul_left, mul_assoc]

lemma probOutput_seq_eq_tsum_ite [HasEvalSPMF m] [LawfulMonad m] [DecidableEq β]
    (mf : m (α → β)) (mx : m α) (y : β) :
    Pr[= y | mf <*> mx] =
      ∑' f, ∑' x, if y = f x then Pr[= f | mf] * Pr[= x | mx] else 0 := by
  simp [seq_eq_bind_map, probOutput_bind_eq_tsum,
    probOutput_map_eq_tsum_ite, ← ENNReal.tsum_mul_left]

@[simp]
lemma probFailure_seq [HasEvalSPMF m] [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
    Pr[⊥ | mf <*> mx] = Pr[⊥ | mf] + Pr[⊥ | mx] - Pr[⊥ | mf] * Pr[⊥ | mx] := by
  rw [seq_eq_bind_map]
  exact probFailure_bind_of_const' probFailure_ne_top (fun g _ => probFailure_map mx g)

lemma probEvent_seq_eq_tsum [HasEvalSPMF m] [LawfulMonad m]
    (mf : m (α → β)) (mx : m α) (p : β → Prop) :
    Pr[p | mf <*> mx] = ∑' f, Pr[= f | mf] * Pr[p ∘ f | mx] := by
  simp only [seq_eq_bind_map, probEvent_bind_eq_tsum, probEvent_map]

lemma probEvent_seq_eq_tsum_ite [HasEvalSPMF m] [LawfulMonad m]
    (mf : m (α → β)) (mx : m α) (p : β → Prop) [DecidablePred p] :
    Pr[p | mf <*> mx] = ∑' (f : α → β) (x : α),
      if p (f x) then Pr[= f | mf] * Pr[= x | mx] else 0 := by
  simp_rw [probEvent_seq_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left,
    Function.comp_apply, mul_ite, mul_zero]

end seq

section seqLeft

@[simp] lemma support_seqLeft [HasEvalSet m] [LawfulMonad m]
    (mx : m α) (my : m β) [Decidable (support my).Nonempty] :
    support (mx <* my) = if (support my).Nonempty then support mx else ∅ := by
  rw [seqLeft_eq, Set.ext_iff]; aesop

@[simp] lemma evalDist_seqLeft [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β) :
    evalDist (mx <* my) = evalDist mx <* evalDist my := by
  simp [seqLeft_eq]

@[simp] lemma probOutput_seqLeft [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β) (x : α) :
    Pr[= x | mx <* my] = (1 - Pr[⊥ | my]) * Pr[= x | mx] := by
  rw [seqLeft_eq, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, probOutput_bind_eq_tsum]
  simp_rw [show ∀ a : α, Pr[= x | (Function.const β a <$> my : m α)] =
    (1 - Pr[⊥ | my]) * Pr[= x | (pure a : m α)] from fun a => probOutput_map_const my a x,
    mul_left_comm _ (1 - Pr[⊥ | my])]
  rw [ENNReal.tsum_mul_left, ← probOutput_bind_eq_tsum, bind_pure]

@[simp] lemma probFailure_seqLeft [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β) :
    Pr[⊥ | mx <* my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [seqLeft_eq, probFailure_seq, probFailure_map]

@[simp] lemma probEvent_seqLeft [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β)
    (p : α → Prop) :
    Pr[p | mx <* my] = (1 - Pr[⊥ | my]) * Pr[p | mx] := by
  rw [seqLeft_eq, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, probEvent_bind_eq_tsum]
  simp_rw [show ∀ a : α, Pr[p | (Function.const β a <$> my : m α)] =
    (1 - Pr[⊥ | my]) * Pr[p | (pure a : m α)] from fun a => probEvent_map_const my a p,
    mul_left_comm _ (1 - Pr[⊥ | my])]
  rw [ENNReal.tsum_mul_left, ← probEvent_bind_eq_tsum, bind_pure]

end seqLeft

section seqRight

@[simp] lemma support_seqRight [HasEvalSet m] [LawfulMonad m]
    (mx : m α) (my : m β) [Decidable (support mx).Nonempty] :
    support (mx *> my) = if (support mx).Nonempty then support my else ∅ := by
  rw [seqRight_eq, Set.ext_iff]; aesop

@[simp] lemma evalDist_seqRight [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β) :
    evalDist (mx *> my) = evalDist mx *> evalDist my := by
  simp [seqRight_eq]

@[simp] lemma probOutput_seqRight [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by
  have h : mx *> my = mx >>= fun _ => my := by simp [seqRight_eq, seq_eq_bind_map]
  rw [h, probOutput_bind_const]

@[simp] lemma probFailure_seqRight [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β) :
    Pr[⊥ | mx *> my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [seqRight_eq, probFailure_seq, probFailure_map]

@[simp] lemma probEvent_seqRight [HasEvalSPMF m] [LawfulMonad m] (mx : m α) (my : m β)
    (p : β → Prop) :
    Pr[p | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[p | my] := by
  have h : mx *> my = mx >>= fun _ => my := by simp [seqRight_eq, seq_eq_bind_map]
  rw [h, probEvent_bind_const]

end seqRight

section seq_map

variable [LawfulMonad m] (mx : m α) (my : m β) (f : α → β → γ)

@[simp low + 1]
lemma support_seq_map_eq_image2 [HasEvalSet m] :
    support (f <$> mx <*> my) = Set.image2 f (support mx) (support my) := by
  ext z; simp [seq_eq_bind_map, Set.mem_image2]

@[simp low + 1]
lemma finSupport_seq_map_eq_image2 [HasEvalSet m] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    finSupport (f <$> mx <*> my) = Finset.image₂ f (finSupport mx) (finSupport my) := by
  ext z; simp [seq_eq_bind_map, Finset.mem_image₂]

lemma evalDist_seq_map [HasEvalSPMF m] :
    evalDist (f <$> mx <*> my) = f <$> evalDist mx <*> evalDist my := by
  rw [evalDist_seq, evalDist_map]

lemma probOutput_seq_map_eq_tsum [HasEvalSPMF m]
    (z : γ) : Pr[= z | f <$> mx <*> my] = ∑' (x : α) (y : β),
      Pr[= x | mx] * Pr[= y | my] * Pr[= z | (pure (f x y) : m γ)] := by
  simp only [map_eq_bind_pure_comp, Function.comp, seq_eq_bind_map, bind_assoc, pure_bind,
    probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_assoc]

lemma probOutput_seq_map_eq_tsum_ite [HasEvalSPMF m] [DecidableEq γ]
    (z : γ) : Pr[= z | f <$> mx <*> my] =
      ∑' (x : α) (y : β), if z = f x y then Pr[= x | mx] * Pr[= y | my] else 0 := by
  simp only [probOutput_seq_map_eq_tsum, probOutput_pure, mul_ite, mul_one, mul_zero]

section injective2

lemma probOutput_seq_map_eq_mul_of_injective2 [HasEvalSPMF m] [DecidableEq γ]
    (hf : f.Injective2) (x : α) (y : β) :
    Pr[= f x y | f <$> mx <*> my] = Pr[= x | mx] * Pr[= y | my] := by
  rw [probOutput_seq_map_eq_tsum]
  simp only [probOutput_pure, mul_ite, mul_one, mul_zero]
  refine (tsum_eq_single x fun x' hx' => ?_).trans ?_
  · exact ENNReal.tsum_eq_zero.mpr fun b =>
      if_neg (show f x y ≠ f x' b from fun h' => hx' (hf h').1.symm)
  · refine (tsum_eq_single y fun y' hy' => ?_).trans ?_
    · exact if_neg (show f x y ≠ f x y' from fun h' => hy' (hf h').2.symm)
    · simp

lemma mem_support_seq_map_iff_of_injective2 [HasEvalSet m]
    (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ support (f <$> mx <*> my) ↔ x ∈ support mx ∧ y ∈ support my := by
  rw [support_seq_map_eq_image2, Set.mem_image2_iff hf]

lemma mem_finSupport_seq_map_iff_of_injective2 [HasEvalSet m] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ finSupport (f <$> mx <*> my) ↔ x ∈ finSupport mx ∧ y ∈ finSupport my := by
  rw [finSupport_seq_map_eq_image2]
  simp only [Finset.mem_image₂]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨(hf hab).1 ▸ ha, (hf hab).2 ▸ hb⟩
  · exact fun ⟨hx, hy⟩ => ⟨x, hx, y, hy, rfl⟩

end injective2

section swap

@[simp]
lemma probOutput_seq_map_swap [HasEvalSPMF m] [DecidableEq γ] (z : γ) :
    Pr[= z | Function.swap f <$> my <*> mx] = Pr[= z | f <$> mx <*> my] := by
  simp only [probOutput_seq_map_eq_tsum_ite, Function.swap]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x' => tsum_congr fun y' => ?_
  rw [mul_comm (Pr[= y' | my])]

@[simp]
lemma evalDist_seq_map_swap [HasEvalSPMF m] :
    evalDist (Function.swap f <$> my <*> mx) = evalDist (f <$> mx <*> my) := by
  have : DecidableEq γ := Classical.decEq γ
  exact evalDist_ext (probOutput_seq_map_swap mx my f)

@[simp]
lemma probEvent_seq_map_swap [HasEvalSPMF m] (p : γ → Prop) :
    Pr[p | Function.swap f <$> my <*> mx] = Pr[p | f <$> mx <*> my] := by
  have : DecidableEq γ := Classical.decEq γ
  simp only [probEvent_eq_tsum_indicator, probOutput_seq_map_swap]

@[simp]
lemma support_seq_map_swap [HasEvalSet m] :
    support (Function.swap f <$> my <*> mx) = support (f <$> mx <*> my) := by
  simp only [support_seq_map_eq_image2, Set.image2_swap f]

@[simp]
lemma finSupport_seq_map_swap [HasEvalSet m] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    finSupport (Function.swap f <$> my <*> mx) = finSupport (f <$> mx <*> my) := by
  simp only [finSupport_seq_map_eq_image2, Finset.image₂_swap f]

end swap

lemma probEvent_seq_map_eq_mul [HasEvalSPMF m]
    (p : γ → Prop) (q1 : α → Prop) (q2 : β → Prop)
    (h : ∀ x ∈ support mx, ∀ y ∈ support my, p (f x y) ↔ q1 x ∧ q2 y) :
    Pr[p | f <$> mx <*> my] = Pr[q1 | mx] * Pr[q2 | my] := by
  classical
  rw [show f <$> mx <*> my = mx >>= fun x => f x <$> my from by simp [seq_eq_bind_map]]
  rw [probEvent_bind_eq_tsum]
  simp only [probEvent_map]
  suffices hs : ∀ x, Pr[= x | mx] * Pr[p ∘ f x | my] =
      (if q1 x then Pr[= x | mx] else 0) * Pr[q2 | my] by
    trans (∑' x, (if q1 x then Pr[= x | mx] else 0) * Pr[q2 | my])
    · exact tsum_congr hs
    · rw [ENNReal.tsum_mul_right]; symm; rw [probEvent_eq_tsum_ite]
  intro x
  by_cases hx : x ∈ support mx <;> by_cases hq : q1 x
  · simp only [if_pos hq]; congr 1
    exact probEvent_ext fun y hy => (h x hx y hy).trans (by simp [hq])
  · simp only [if_neg hq, zero_mul]
    rw [probEvent_eq_zero fun y hy => (by
      show ¬(p ∘ f x) y; simp only [Function.comp_apply]; rw [h x hx y hy]; simp [hq]), mul_zero]
  · simp [probOutput_eq_zero_of_not_mem_support hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_seq_map_eq_mul [HasEvalSPMF m] (x : α) (y : β) (z : γ)
    (h : ∀ x' ∈ support mx, ∀ y' ∈ support my, z = f x' y' ↔ x' = x ∧ y' = y) :
    Pr[= z | f <$> mx <*> my] = Pr[= x | mx] * Pr[= y | my] := by
  have : DecidableEq γ := Classical.decEq γ
  rw [probOutput_seq_map_eq_tsum_ite]
  refine (tsum_eq_single x fun x' hx' => ?_).trans ?_
  · refine ENNReal.tsum_eq_zero.mpr fun y' => ?_
    by_cases hx's : x' ∈ support mx
    · by_cases hy's : y' ∈ support my
      · exact if_neg fun heq => hx' ((h x' hx's y' hy's).mp heq).1
      · simp [probOutput_eq_zero_of_not_mem_support hy's]
    · simp [probOutput_eq_zero_of_not_mem_support hx's]
  · refine (tsum_eq_single y fun y' hy' => ?_).trans ?_
    · by_cases hxs : x ∈ support mx
      · by_cases hy's : y' ∈ support my
        · exact if_neg fun heq => hy' ((h x hxs y' hy's).mp heq).2
        · simp [probOutput_eq_zero_of_not_mem_support hy's]
      · simp [probOutput_eq_zero_of_not_mem_support hxs]
    · by_cases hxs : x ∈ support mx
      · by_cases hys : y ∈ support my
        · simp [(h x hxs y hys).mpr ⟨rfl, rfl⟩]
        · simp [probOutput_eq_zero_of_not_mem_support hys]
      · simp [probOutput_eq_zero_of_not_mem_support hxs]

lemma probEvent_seq_map_eq_probEvent_comp_uncurry [HasEvalSPMF m] (p : γ → Prop) :
    Pr[p | f <$> mx <*> my] = Pr[p ∘ Function.uncurry f | Prod.mk <$> mx <*> my] := by
  rw [← probEvent_map]
  congr 1
  rw [map_seq, Functor.map_map]
  congr 1

lemma probEvent_seq_map_eq_probEvent [HasEvalSPMF m] (p : γ → Prop) :
    Pr[p | f <$> mx <*> my] = Pr[fun z => p (f z.1 z.2) | Prod.mk <$> mx <*> my] :=
  probEvent_seq_map_eq_probEvent_comp_uncurry mx my f p

end seq_map
