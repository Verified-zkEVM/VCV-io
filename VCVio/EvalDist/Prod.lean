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

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [HasEvalSPMF m] {α β γ δ : Type u}

omit [LawfulMonad m] in
lemma probOutput_prod_mk_eq_probEvent (mx : m (α × β)) (x : α) (y : β) :
    Pr[= (x, y) | mx] = Pr[ fun z => z.1 = x ∧ z.2 = y | mx] := by
  simp [← probEvent_eq_eq_probOutput, Prod.eq_iff_fst_eq_snd_eq]

@[grind =]
lemma probOutput_fst_map_eq_tsum (mx : m (α × β)) (x : α) :
    Pr[= x | Prod.fst <$> mx] = ∑' y, Pr[= (x, y) | mx] := by
  have : DecidableEq α := Classical.decEq _
  simp only [probOutput_map_eq_tsum_ite]
  rw [ENNReal.tsum_prod']; dsimp only [Prod.fst]
  refine (tsum_eq_single x ?_).trans (by simp)
  intro a ha; simp [Ne.symm ha]

@[grind =]
lemma probOutput_fst_map_eq_sum [Fintype β] (mx : m (α × β)) (x : α) :
    Pr[= x | Prod.fst <$> mx] = ∑ y, Pr[= (x, y) | mx] := by
  rw [probOutput_fst_map_eq_tsum, tsum_fintype]

@[grind =]
lemma probOutput_snd_map_eq_tsum (mx : m (α × β)) (y : β) :
    Pr[= y | Prod.snd <$> mx] = ∑' x, Pr[= (x, y) | mx] := by
  have : DecidableEq β := Classical.decEq _
  simp only [probOutput_map_eq_tsum_ite]
  rw [ENNReal.tsum_prod']; dsimp only [Prod.snd]
  refine tsum_congr fun _ => (tsum_eq_single y ?_).trans (by simp)
  intro b hb; simp [Ne.symm hb]

@[grind =]
lemma probOutput_snd_map_eq_sum [Fintype α] (mx : m (α × β)) (y : β) :
    Pr[= y | Prod.snd <$> mx] = ∑ x, Pr[= (x, y) | mx] := by
  rw [probOutput_snd_map_eq_tsum, tsum_fintype]

@[grind =]
lemma probOutput_fst_map_eq_probEvent (mx : m (α × β)) (x : α) :
    Pr[= x | Prod.fst <$> mx] = Pr[ fun z => z.1 = x | mx] := by grind

/-- Unlike `probEvent_map` this unfolds the function composition automatically. -/
@[simp high, grind =]
lemma probEvent_fst_map (mx : m (α × β)) (p : α → Prop) :
    Pr[ p | Prod.fst <$> mx] = Pr[ fun x => p x.1 | mx] := by grind

@[grind =]
lemma probOutput_snd_map_eq_probEvent (mx : m (α × β)) (y : β) :
    Pr[= y | Prod.snd <$> mx] = Pr[ fun z => z.2 = y | mx] := by grind

/-- Unlike `probEvent_map` this unfolds the function composition automatically. -/
@[simp high, grind =]
lemma probEvent_snd_map (mx : m (α × β)) (p : β → Prop) :
    Pr[ p | Prod.snd <$> mx] = Pr[ fun y => p y.2 | mx] := by grind

omit [LawfulMonad m] in
@[simp, grind =]
lemma probEvent_fst_eq_snd (mx : m (α × α)) :
    Pr[ fun z => z.1 = z.2 | mx] = ∑' x : α, Pr[= (x, x) | mx] := by
  classical
  rw [probEvent_eq_tsum_ite, ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  refine (tsum_eq_single x fun b hb => ?_).trans (by simp)
  exact if_neg (Ne.symm hb)

section prod_mk

variable (mx : m α) (my : m β) (f : α → γ) (g : β → δ)

@[simp high]
lemma probOutput_seq_map_prod_mk_eq_mul (z : α × β) :
    Pr[= z | Prod.mk <$> mx <*> my] = Pr[= z.1 | mx] * Pr[= z.2 | my] :=
  probOutput_seq_map_eq_mul_of_injective2 mx my Prod.mk Prod.mk.injective2 z.1 z.2

@[simp high]
lemma support_seq_map_prod_mk : support (Prod.mk <$> mx <*> my) = support mx ×ˢ support my := by
  simp [Set.ext_iff]

lemma finSupport_seq_map_prod_mk [HasEvalFinset m] [DecidableEq α] [DecidableEq β] :
    finSupport (Prod.mk <$> mx <*> my) = Finset.product (finSupport mx) (finSupport my) := by
  simp

@[simp]
lemma probOutput_seq_map_prod_mk_map_eq_mul (z : γ × δ) :
    Pr[= z | (f ·, g ·) <$> mx <*> my] = Pr[= z.1 | f <$> mx] * Pr[= z.2 | g <$> my] := by
  have hseq : (f ·, g ·) <$> mx <*> my = Prod.mk <$> (f <$> mx) <*> (g <$> my) := by
    simp [seq_eq_bind_map, Functor.map_map]
  rw [hseq, probOutput_seq_map_prod_mk_eq_mul]

@[simp]
lemma probOutput_seq_map_prod_mk_map_eq_mul' (z : γ × δ) :
    Pr[= z | (fun y x => (f x, g y)) <$> my <*> mx] =
      Pr[= z.1 | f <$> mx] * Pr[= z.2 | g <$> my] := by
  rw [← probOutput_seq_map_swap]; simp

@[simp]
lemma probOutput_bind_map_prod_mk_eq_mul (z : γ × δ) :
    Pr[= z | do let x ← mx; (f x, g ·) <$> my] = Pr[= z.1 | f <$> mx] * Pr[= z.2 | g <$> my] := by
  simpa [seq_eq_bind_map, map_eq_bind_pure_comp] using
    probOutput_seq_map_prod_mk_map_eq_mul mx my f g z

@[simp]
lemma probOutput_bind_map_prod_mk_eq_mul'
    (mx : m α) (my : m β) (f : α → γ) (g : β → δ) (z : γ × δ) :
    Pr[= z | do let y ← my; (f ·, g y) <$> mx] = Pr[= z.1 | f <$> mx] * Pr[= z.2 | g <$> my] := by
  simpa [seq_eq_bind_map, map_eq_bind_pure_comp] using
    probOutput_seq_map_prod_mk_map_eq_mul' mx my f g z

@[simp high]
lemma support_seq_map_prod_mk_eq_sprod :
    support ((f ·, g ·) <$> mx <*> my) = (f '' support mx) ×ˢ (g '' support my) := by
  simp [Set.ext_iff]; grind

lemma finSupport_seq_map_prod_mk_eq_product [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] : finSupport ((f ·, g ·) <$> mx <*> my) =
      ((finSupport mx).image f).product ((finSupport my).image g) := by
  simp [Finset.ext_iff]; grind

lemma probOutput_bind_bind_prod_mk_eq_mul
    (mx : m α) (my : m β) (f : α → γ) (g : β → δ) (z : γ × δ) :
    Pr[= z | do let x ← mx; let y ← my; return (f x, g y)] =
      Pr[= z.1 | f <$> mx] * Pr[= z.2 | g <$> my] := by simp

lemma probOutput_bind_bind_prod_mk_eq_mul'
    (mx : m α) (my : m β) (f : α → γ) (g : β → δ) (x : γ) (y : δ) :
    Pr[= (x, y) | do let a ← mx; let b ← my; return (f a, g b)] =
      Pr[= x | f <$> mx] * Pr[= y | g <$> my] := by simp

@[simp]
lemma probOutput_prod_mk_fst_map [DecidableEq β] (mx : m α) (y : β) (z : α × β) :
    Pr[= z | (·, y) <$> mx] = if z.2 = y then Pr[= z.1 | mx] else 0 :=
  calc Pr[= z | (·, y) <$> mx]
    _ = Pr[= z | Prod.mk <$> mx <*> pure y] := by simp; rfl
    _ = if z.2 = y then Pr[= z.1 | mx] else 0 := by simp only [probOutput_seq_map_prod_mk_eq_mul,
      probOutput_pure, mul_ite, mul_one, mul_zero]

@[simp]
lemma probOutput_prod_mk_snd_map [DecidableEq α] (my : m β) (x : α) (z : α × β) :
    Pr[= z | (x, ·) <$> my] = if z.1 = x then Pr[= z.2 | my] else 0 :=
  calc Pr[= z | (x, ·) <$> my]
    _ = Pr[= z | Prod.mk <$> pure x <*> my] := by simp [seq_eq_bind_map]; rfl
    _ = if z.1 = x then Pr[= z.2 | my] else 0 := by simp only [probOutput_seq_map_prod_mk_eq_mul,
      probOutput_pure, ite_mul, one_mul, zero_mul]

end prod_mk
