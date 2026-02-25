/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Monad.Seq

/-!
# Evaluation Distributions of Computations with `Prod`

Lemmas about `evalDist` and `support` involving `Prod`, ported to generic `[HasEvalSPMF m]`.
-/

open ENNReal Prod

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
  {α β γ δ : Type u}

omit [LawfulMonad m] in
lemma probOutput_prod_mk_eq_probEvent [DecidableEq α] [DecidableEq β]
    (mx : m (α × β)) (x : α) (y : β) :
    Pr[= (x, y) | mx] = Pr[fun z => z.1 = x ∧ z.2 = y | mx] := by
  simp [← probEvent_eq_eq_probOutput, Prod.eq_iff_fst_eq_snd_eq]

omit [HasEvalSPMF m] in
@[simp]
lemma fst_map_prod_map (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.fst <$> Prod.map f g <$> mx = (f ∘ Prod.fst) <$> mx := by
  simp [Functor.map_map]; rfl

omit [HasEvalSPMF m] in
@[simp]
lemma snd_map_prod_map (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.snd <$> Prod.map f g <$> mx = (g ∘ Prod.snd) <$> mx := by
  simp [Functor.map_map]; rfl

@[simp]
lemma probOutput_fst_map_eq_tsum (mx : m (α × β)) (x : α) :
    Pr[= x | Prod.fst <$> mx] = ∑' y, Pr[= (x, y) | mx] := by
  have : DecidableEq α := Classical.decEq _
  simp only [probOutput_map_eq_tsum_ite]
  rw [ENNReal.tsum_prod']; dsimp only [Prod.fst]
  refine (tsum_eq_single x ?_).trans (by simp)
  intro a ha; simp [Ne.symm ha]

@[simp]
lemma probOutput_fst_map_eq_sum [Fintype β]
    (mx : m (α × β)) (x : α) :
    Pr[= x | Prod.fst <$> mx] = ∑ y, Pr[= (x, y) | mx] := by
  rw [probOutput_fst_map_eq_tsum, tsum_fintype]

@[simp]
lemma probOutput_snd_map_eq_tsum (mx : m (α × β)) (y : β) :
    Pr[= y | Prod.snd <$> mx] = ∑' x, Pr[= (x, y) | mx] := by
  have : DecidableEq β := Classical.decEq _
  simp only [probOutput_map_eq_tsum_ite]
  rw [ENNReal.tsum_prod']; dsimp only [Prod.snd]
  refine tsum_congr fun _ => (tsum_eq_single y ?_).trans (by simp)
  intro b hb; simp [Ne.symm hb]

@[simp]
lemma probOutput_snd_map_eq_sum [Fintype α]
    (mx : m (α × β)) (y : β) :
    Pr[= y | Prod.snd <$> mx] = ∑ x, Pr[= (x, y) | mx] := by
  rw [probOutput_snd_map_eq_tsum, tsum_fintype]

omit [LawfulMonad m] in
lemma probEvent_fst_eq_snd [DecidableEq α] (mx : m (α × α)) :
    Pr[fun z => z.1 = z.2 | mx] = ∑' x : α, Pr[= (x, x) | mx] := by
  rw [probEvent_eq_tsum_ite, ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  refine (tsum_eq_single x fun b hb => ?_).trans (by simp)
  exact if_neg (Ne.symm hb)

@[simp]
lemma probOutput_seq_map_prod_mk_eq_mul [DecidableEq α] [DecidableEq β]
    (mx : m α) (my : m β) (x : α) (y : β) :
    Pr[= (x, y) | Prod.mk <$> mx <*> my] = Pr[= x | mx] * Pr[= y | my] :=
  probOutput_seq_map_eq_mul_of_injective2 mx my Prod.mk Prod.mk.injective2 x y
