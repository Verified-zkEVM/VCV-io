/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.EvalDist

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa qb` stating that `oa` makes at most `qb t`
queries to oracle `t` along any execution path.

The definition is structural via `OracleComp.construct`: `pure` satisfies any bound, and
`query t >>= mx` satisfies `qb` when `qb t > 0` and each continuation satisfies the
decremented bound `Function.update qb t (qb t - 1)`.
-/

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq ι] {α β : Type u}

section IsQueryBound

/-- `IsQueryBound oa qb` means that `oa` makes at most `qb t` queries to oracle `t`
along any execution path. -/
def IsQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
  OracleComp.construct
    (C := fun _ => (ι → ℕ) → Prop)
    (fun _ _ => True)
    (fun t _mx ih qb => 0 < qb t ∧ ∀ u, ih u (Function.update qb t (qb t - 1)))
    oa qb

@[simp]
lemma isQueryBound_pure (x : α) (qb : ι → ℕ) :
    IsQueryBound (pure x : OracleComp spec α) qb := trivial

lemma isQueryBound_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α) (qb : ι → ℕ) :
    IsQueryBound (liftM (query (spec := spec) t) >>= mx) qb ↔
      0 < qb t ∧ ∀ u, IsQueryBound (mx u) (Function.update qb t (qb t - 1)) :=
  Iff.rfl

@[simp]
lemma isQueryBound_query_iff (t : ι) (qb : ι → ℕ) :
    IsQueryBound (liftM (query (spec := spec) t) : OracleComp spec _) qb ↔ 0 < qb t := by
  show (0 < qb t ∧ ∀ _ : spec t, True) ↔ _
  simp

private lemma update_le_update {qb qb' : ι → ℕ} {t : ι} (hle : qb ≤ qb') :
    Function.update qb t (qb t - 1) ≤ Function.update qb' t (qb' t - 1) := by
  intro j
  by_cases hj : j = t
  · rw [hj, Function.update_self, Function.update_self]
    exact Nat.sub_le_sub_right (hle t) 1
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    exact hle j

private lemma isQueryBound_mono_aux (oa : OracleComp spec α) :
    ∀ {qb qb' : ι → ℕ}, qb ≤ qb' → oa.IsQueryBound qb → oa.IsQueryBound qb' := by
  induction oa using OracleComp.inductionOn with
  | pure _ => intros; trivial
  | query_bind t mx ih =>
    intro qb qb' hle h
    rw [isQueryBound_query_bind_iff] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 (hle t), fun u => ih u (update_le_update hle) (h.2 u)⟩

lemma IsQueryBound.mono {oa : OracleComp spec α} {qb qb' : ι → ℕ}
    (h : IsQueryBound oa qb) (hle : qb ≤ qb') : IsQueryBound oa qb' :=
  isQueryBound_mono_aux oa hle h

private lemma update_add_eq_update_add {qb₁ qb₂ : ι → ℕ} {t : ι} (ht : 0 < qb₁ t) :
    Function.update qb₁ t (qb₁ t - 1) + qb₂ =
      Function.update (qb₁ + qb₂) t ((qb₁ + qb₂) t - 1) := by
  ext j
  by_cases hj : j = t
  · rw [hj, Pi.add_apply, Function.update_self, Pi.add_apply, Function.update_self]; omega
  · simp only [Pi.add_apply, Function.update_of_ne hj]

private lemma isQueryBound_bind_aux (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (qb₂ : ι → ℕ) (h2 : ∀ x, IsQueryBound (ob x) qb₂) :
    ∀ {qb₁}, oa.IsQueryBound qb₁ → (oa >>= ob).IsQueryBound (qb₁ + qb₂) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qb₁ _
    simp only [pure_bind]
    exact (h2 x).mono le_add_self
  | query_bind t mx ih =>
    intro qb₁ h1
    rw [isQueryBound_query_bind_iff] at h1
    rw [bind_assoc, isQueryBound_query_bind_iff]
    refine ⟨Nat.add_pos_left h1.1 _, fun u => ?_⟩
    rw [← update_add_eq_update_add h1.1]
    exact ih u (h1.2 u)

lemma isQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {qb₁ qb₂ : ι → ℕ}
    (h1 : IsQueryBound oa qb₁) (h2 : ∀ x, IsQueryBound (ob x) qb₂) :
    IsQueryBound (oa >>= ob) (qb₁ + qb₂) :=
  isQueryBound_bind_aux oa ob qb₂ h2 h1

private lemma isQueryBound_map_aux (oa : OracleComp spec α) (f : α → β) :
    ∀ {qb : ι → ℕ}, (f <$> oa).IsQueryBound qb ↔ oa.IsQueryBound qb := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind t mx ih =>
    intro qb
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    rw [isQueryBound_query_bind_iff, isQueryBound_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun u => ih u

@[simp]
lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
    IsQueryBound (f <$> oa) qb ↔ IsQueryBound oa qb :=
  isQueryBound_map_aux oa f

end IsQueryBound

end OracleComp
