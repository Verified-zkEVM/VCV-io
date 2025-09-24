/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.EvalDist

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa qb` to say that a computation with oracles `spec`
never makes a larger number of queries than is given by a bound `qb : spec.ι → ℕ`.
This is useful for showing that some simulated computation is polynomial time,
and in things like seeding query values for a computation.

We also define a function `minimalQueryBound oa` that returns the smallest such count.
Calculating this is generally expensive, and so it shouldn't be used in actual algorithms,
but it can be useful in some proofs that only care about the existence of a bound.
-/

open OracleSpec Prod

universe u v w

namespace OracleComp

section IsQueryBound

variable {spec : OracleSpec} {ι : Type _} [HasIndexing spec ι] [DecidableEq ι] {α β γ : Type u}

/-- Predicate expressing that `queryBound` is a bound on the number of queries made by `oa`.
In particular any simulation with a `countingOracle` produces counts that are smaller. -/
def IsQueryBound (oa : OracleComp spec α) (queryBound : QueryCount ι) : Prop :=
    ∀ qc ∈ support (snd <$> (simulateQ (countingOracle HasIndexing.idx) oa).run),
      qc ≤ queryBound

lemma isQueryBound_def (oa : OracleComp spec α) (qb : QueryCount ι) :
    IsQueryBound oa qb ↔
      ∀ qc ∈ support (snd <$> (simulateQ (countingOracle HasIndexing.idx) oa).run),
        qc ≤ qb :=
  Iff.rfl

lemma isQueryBound_mono {oa : OracleComp spec α} (qb : ι → ℕ) {qb' : ι → ℕ}
    (h' : IsQueryBound oa qb) (h : qb ≤ qb') : IsQueryBound oa qb' :=
  λ qc hqc ↦ le_trans (h' qc hqc) h

lemma isQueryBound_iff_probEvent [spec.Fintype] [spec.Inhabited] {oa : OracleComp spec α} {qb : ι → ℕ} :
    IsQueryBound oa qb ↔
      Pr[(· ≤ qb) | snd <$> (simulateQ (countingOracle HasIndexing.idx) oa).run] = 1 := by
  stop
  simp [probEvent_eq_one_iff, isQueryBound_def]
  apply Iff.intro
  · intro a x a_1
    split at a_1
    next h =>
      simp_all only [Set.mem_image, Prod.exists, exists_eq_right]
      obtain ⟨w, h_1⟩ := a_1
      apply a
      · exact h_1
    next h =>
      simp_all only [Set.mem_insert_iff, Set.mem_image, Prod.exists, exists_eq_right]
      cases a_1 with
      | inl h_1 =>
        subst h_1
        simp_all only [zero_le]
      | inr h_2 =>
        obtain ⟨w, h_1⟩ := h_2
        apply a
        · exact h_1
  · intro a qc x h
    split at a
    next h_1 =>
      simp_all only [Set.mem_image, Prod.exists, exists_eq_right, forall_exists_index]
      apply a
      · exact h
    next
      h_1 =>
      simp_all only [Set.mem_insert_iff, Set.mem_image,
                    Prod.exists, exists_eq_right, forall_eq_or_imp, zero_le,
        forall_exists_index, true_and]
      apply a
      · exact h

@[simp]
lemma isQueryBound_pure (a : α) (qb : ι → ℕ) : IsQueryBound (pure a : OracleComp spec α) qb := by
  simp [isQueryBound_def]

-- @[simp]
-- lemma isQueryBound_failure (qb : ι → ℕ) : IsQueryBound (failure : OracleComp spec α) qb := by
--   simp [isQueryBound_def]

-- @[simp]
-- lemma isQueryBound_query_iff_pos [Nonempty α] (q : OracleQuery spec α) (qb : ι → ℕ) :
--     IsQueryBound (q : OracleComp spec α) qb ↔ 0 < qb q.index := by
--   simp [isQueryBound_def]

-- lemma isQueryBound_query (i : ι) (t : spec.domain i) {qb : ι → ℕ} (hqb : qb i ≠ 0) :
--     IsQueryBound (query i t : OracleComp spec _) qb :=
--   (isQueryBound_query_iff i t qb).2 hqb

-- lemma update_isQueryBound_query (i : ι) (t : spec.domain i) (f : ι → ℕ) (n : ℕ) :
--     IsQueryBound (query i t : OracleComp spec _) (Function.update f i (n + 1)) :=
--   isQueryBound_query i t (by simp)

-- lemma isQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β} {qb₁ qb₂ : ι → ℕ}
--     (h1 : IsQueryBound oa qb₁) (h2 : ∀ x ∈ oa.support, IsQueryBound (ob x) qb₂) :
--     IsQueryBound (oa >>= ob) (qb₁ + qb₂) := by
--   intros count h
--   simp at h
--   obtain ⟨x, count₁, h₁, y, h⟩ := h
--   have hc := countingOracle.le_of_mem_support_simulate h
--   specialize h1 count₁ (mem_support_map h₁ snd)
--   specialize h2 x (SimOracle.IsTracking.mem_support_of_mem_support_simulate' <|
--       mem_support_map h₁ fst) (count - count₁)
--       (countingOracle.sub_mem_support_snd_map_simulate <| mem_support_map h snd)
--   refine le_of_eq_of_le (funext (λ i ↦ Nat.add_sub_of_le (hc i))).symm (add_le_add h1 h2)

-- /-- Version of `isQueryBound_bind` that allows the second query bound to vary based on the
-- output of the first computation, assuming it remains below the final desired bound.-/
-- lemma isQueryBound_bind' {oa : OracleComp spec α} {ob : α → OracleComp spec β} {qb : ι → ℕ}
--     (qb₁ : ι → ℕ) (qb₂ : α → ι → ℕ)
--     (hqb₁ : IsQueryBound oa qb₁) (hqb₂ : ∀ u ∈ oa.support, IsQueryBound (ob u) (qb₂ u))
--         (h : ∀ u ∈ oa.support, qb₁ + qb₂ u ≤ qb) :
--     IsQueryBound (oa >>= ob) qb := by
--   sorry
--   -- have hα : DecidableEq α := Classical.decEq α
--   -- let qb₂' : ι → ℕ := λ i ↦ Finset.max' (oa.finSupport.image λ x ↦ qb₂ x i) (by simp)
--   -- refine isQueryBound_mono (qb₁ + qb₂') ?_ ?_
--   -- · refine isQueryBound_bind hqb₁ ?_
--   --   intro x hx
--   --   specialize hqb₂ x
--   --   refine isQueryBound_mono (qb₂ x) (hqb₂ hx) ?_
--   --   intro i
--   --   refine Finset.le_max' _ _ ?_
--   --   simp only [Finset.mem_image]
--   --   refine ⟨x, ?_, rfl⟩
--   --   refine mem_finSupport_of_mem_support _ hx
--   -- · intro i
--   --   refine Nat.add_le_of_le_sub' ?_ ?_
--   --   · specialize h oa.defaultResult (defaultResult_mem_support oa) i
--   --     refine le_trans ?_ h
--   --     refine le_self_add
--   --   · simp only [Finset.max'_le_iff, Finset.mem_image, forall_exists_index, and_imp,
--   --     forall_apply_eq_imp_iff₂, qb₂']
--   --     intro x hx
--   --     specialize h x (mem_support_of_mem_finSupport _ hx) i
--   --     rw [Nat.le_sub_iff_add_le']
--   --     · exact h
--   --     · refine le_trans le_self_add h

-- -- lemma isQueryBound_query_bind_iff (i : ι) (t : spec.domain i)
-- --     (oa : spec.range i → OracleComp spec α) (qb : ι → ℕ) :
-- --     IsQueryBound (query i t >>= oa) qb ↔
-- --       qb i ≠ 0 ∧ ∀ u, IsQueryBound (oa u) (Function.update qb i (qb i - 1)) := by
-- --   refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
-- --   ·
-- --     sorry
-- --   · sorry

-- @[simp]
-- lemma isQueryBound_pure (a : α) (qb : ι → ℕ) : IsQueryBound (pure a : OracleComp spec α) qb := by
--   simp [isQueryBound_def]

-- @[simp]
-- lemma isQueryBound_failure (qb : ι → ℕ) : IsQueryBound (failure : OracleComp spec α) qb := by
--   simp [isQueryBound_def]

-- @[simp]
-- lemma isQueryBound_query_iff_pos [Nonempty α] (q : OracleQuery spec α) (qb : ι → ℕ) :
--     IsQueryBound (q : OracleComp spec α) qb ↔ 0 < qb q.index := by
--   simp [isQueryBound_def, liftM_query_eq_liftM_liftM]

-- -- lemma isQueryBound_query (i : ι) (t : spec.domain i) {qb : ι → ℕ} (hqb : qb i ≠ 0) :
-- --     IsQueryBound (query i t : OracleComp spec _) qb :=
-- --   (isQueryBound_query_iff i t qb).2 hqb

-- -- lemma update_isQueryBound_query (i : ι) (t : spec.domain i) (f : ι → ℕ) (n : ℕ) :
-- --     IsQueryBound (query i t : OracleComp spec _) (Function.update f i (n + 1)) :=
-- --   isQueryBound_query i t (by simp)

-- -- lemma isQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β} {qb₁ qb₂ : ι → ℕ}
-- --     (h1 : IsQueryBound oa qb₁) (h2 : ∀ x ∈ oa.support, IsQueryBound (ob x) qb₂) :
-- --     IsQueryBound (oa >>= ob) (qb₁ + qb₂) := by
-- --   intros count h
-- --   simp at h
-- --   obtain ⟨x, count₁, h₁, y, h⟩ := h
-- --   have hc := countingOracle.le_of_mem_support_simulate h
-- --   specialize h1 count₁ (mem_support_map h₁ snd)
-- --   specialize h2 x (SimOracle.IsTracking.mem_support_of_mem_support_simulate' <|
-- --       mem_support_map h₁ fst) (count - count₁)
-- --       (countingOracle.sub_mem_support_snd_map_simulate <| mem_support_map h snd)
-- --   refine le_of_eq_of_le (funext (λ i ↦ Nat.add_sub_of_le (hc i))).symm (add_le_add h1 h2)

-- -- /-- Version of `isQueryBound_bind` that allows the second query bound to vary based on the
-- -- output of the first computation, assuming it remains below the final desired bound.-/
-- -- lemma isQueryBound_bind' {oa : OracleComp spec α} {ob : α → OracleComp spec β} {qb : ι → ℕ}
-- --     (qb₁ : ι → ℕ) (qb₂ : α → ι → ℕ)
-- --     (hqb₁ : IsQueryBound oa qb₁) (hqb₂ : ∀ u ∈ oa.support, IsQueryBound (ob u) (qb₂ u))
-- --         (h : ∀ u ∈ oa.support, qb₁ + qb₂ u ≤ qb) :
-- --     IsQueryBound (oa >>= ob) qb := by
-- --   sorry
-- --   -- have hα : DecidableEq α := Classical.decEq α
-- --   -- let qb₂' : ι → ℕ := λ i ↦ Finset.max' (oa.finSupport.image λ x ↦ qb₂ x i) (by simp)
-- --   -- refine isQueryBound_mono (qb₁ + qb₂') ?_ ?_
-- --   -- · refine isQueryBound_bind hqb₁ ?_
-- --   --   intro x hx
-- --   --   specialize hqb₂ x
-- --   --   refine isQueryBound_mono (qb₂ x) (hqb₂ hx) ?_
-- --   --   intro i
-- --   --   refine Finset.le_max' _ _ ?_
-- --   --   simp only [Finset.mem_image]
-- --   --   refine ⟨x, ?_, rfl⟩
-- --   --   refine mem_finSupport_of_mem_support _ hx
-- --   -- · intro i
-- --   --   refine Nat.add_le_of_le_sub' ?_ ?_
-- --   --   · specialize h oa.defaultResult (defaultResult_mem_support oa) i
-- --   --     refine le_trans ?_ h
-- --   --     refine le_self_add
-- --   --   · simp only [Finset.max'_le_iff, Finset.mem_image, forall_exists_index, and_imp,
-- --   --     forall_apply_eq_imp_iff₂, qb₂']
-- --   --     intro x hx
-- --   --     specialize h x (mem_support_of_mem_finSupport _ hx) i
-- --   --     rw [Nat.le_sub_iff_add_le']
-- --   --     · exact h
-- --   --     · refine le_trans le_self_add h

-- -- -- lemma isQueryBound_query_bind_iff (i : ι) (t : spec.domain i)
-- -- --     (oa : spec.range i → OracleComp spec α) (qb : ι → ℕ) :
-- -- --     IsQueryBound (query i t >>= oa) qb ↔
-- -- --       qb i ≠ 0 ∧ ∀ u, IsQueryBound (oa u) (Function.update qb i (qb i - 1)) := by
-- -- --   refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
-- -- --   ·
-- -- --     sorry
-- -- --   · sorry

-- -- @[simp]
-- -- lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
-- --     IsQueryBound (f <$> oa) qb ↔ IsQueryBound oa qb := by
-- --   simp [isQueryBound_def]

-- -- section minimalQueryBound

-- -- -- def minimalQueryBound [spec.Fintype] [DecidableEq ι] [spec.DecidableEq]
-- -- --   {α : Type} (oa : OracleComp spec α) : (ι → ℕ) := by
-- -- --   induction oa using OracleComp.construct with
-- -- --   | pure x => exact 0
-- -- --   | query_bind i t oa r => {
-- -- --     refine λ j ↦ (if j = i then 1 else 0) +
-- -- --       (Finset.max' (Finset.univ.image <| λ u ↦ r u)
-- -- --         (Finset.image_nonempty.2 Finset.univ_nonempty))
-- -- --   }
-- -- --   | failure => exact 0

-- -- --   -- | _, pure' _ _ => 0
-- -- --   -- | _, queryBind' i _ _ oa => λ j ↦ (if j = i then 1 else 0) +
-- -- --   --     (Finset.max' (Finset.univ.image <| λ u ↦ minimalQueryBound (oa u) j)
-- -- --   --       (Finset.image_nonempty.2 Finset.univ_nonempty))
-- -- --   -- | _, failure' _ => 0

-- -- -- @[simp]
-- -- -- lemma minimalQueryBound_pure (x : α) :
-- -- --     minimalQueryBound (pure x : OracleComp spec α) = 0 := rfl

-- -- -- @[simp]
-- -- -- lemma minimalQueryBound_query_bind (i : ι) (t : spec.domain i)
-- -- --     (oa : spec.range i → OracleComp spec α) :
-- -- --     minimalQueryBound (query i t >>= oa) = λ j ↦ (if j = i then 1 else 0) +
-- -- --       (Finset.max' (Finset.univ.image <| λ u ↦ minimalQueryBound (oa u) j)
-- -- --         (Finset.image_nonempty.2 Finset.univ_nonempty)) := rfl

-- -- -- @[simp]
-- -- -- lemma minimalQueryBound_query (i : ι) (t : spec.domain i) :
-- -- --     minimalQueryBound (query i t) = Function.update (0 : ι → ℕ) i 1 := by
-- -- --   rw [query_def, minimalQueryBound]
-- -- --   refine funext (λ j ↦ ?_)
-- -- --   by_cases hj : j = i
-- -- --   · induction hj
-- -- --     simp only [↓reduceIte, minimalQueryBound_pure, Pi.zero_apply, Function.update_same,
-- -- --       add_right_eq_self, ← Nat.le_zero, Finset.max'_le_iff]
-- -- --     simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_const, nonpos_iff_eq_zero,
-- -- --       forall_eq']
-- -- --   · simp only [hj, ↓reduceIte, minimalQueryBound_pure, Pi.zero_apply, zero_add, ne_eq,
-- -- --     not_false_eq_true, Function.update_noteq, ← Nat.le_zero, Finset.max'_le_iff]
-- -- --     simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_const, nonpos_iff_eq_zero,
-- -- --       forall_eq']

-- -- -- -- NOTE: pretty certain this isn't true in general
-- -- -- -- lemma minimalQueryBound_bind [hα : DecidableEq α] (oa : OracleComp spec α)
-- -- -- -- (ob : α → OracleComp spec β) :
-- -- -- --     minimalQueryBound (oa >>= ob) = minimalQueryBound oa +
-- -- -- --       (λ j ↦ Finset.max' (oa.finSupport.image (λ x ↦ minimalQueryBound (ob x) j))
-- -- -- --         <| by simp) := by
-- -- -- --   revert hα
-- -- -- --   induction oa using OracleComp.inductionOn with
-- -- -- --   | h_pure x => {
-- -- -- --     simp
-- -- -- --   }
-- -- -- --   | h_queryBind i t oa hoa => {
-- -- -- --     intro hα
-- -- -- --     rw [bind_assoc]
-- -- -- --     rw [minimalQueryBound_query_bind]
-- -- -- --   simp only [hoa, Pi.add_apply, minimalQueryBound_query_bind,
-- --   --finSupport_bind, finSupport_query]
-- -- -- --     refine funext (λ j ↦ ?_)
-- -- -- --     by_cases hj : j = i
-- -- -- --     · induction hj
-- -- -- --       simp [add_assoc]
-- -- -- --       sorry
-- -- -- --     · simp [hj]
-- -- -- --       sorry
-- -- -- --   }

-- -- -- lemma isQueryBound_minimalQueryBound (oa : OracleComp spec α) :
-- -- --     IsQueryBound oa (minimalQueryBound oa) := by
-- -- --   induction oa using OracleComp.inductionOn with
-- -- --   | pure x => exact isQueryBound_pure x _
-- -- --   | query_bind i t oa hoa =>
-- -- --     · refine isQueryBound_bind (by simp) <| λ u _ ↦ isQueryBound_mono _ (hoa u)
-- -- --         (λ j ↦ Finset.le_max' _ _ ?_)
-- -- --       simp only [OracleComp.bind'_eq_bind, pure_bind, Finset.mem_image,
-- --     -- Finset.mem_univ, true_and,
-- -- --         exists_apply_eq_apply]
-- -- --   | failure => sorry

-- -- -- lemma le_minimalQueryBound_of_mem_support_simulate {oa : OracleComp spec α}
-- -- --     {x : α} {qc : ι → ℕ} (h : (x, qc) ∈ (simulate countingOracle 0 oa).support) :
-- -- --     qc ≤ minimalQueryBound oa := by
-- -- --   refine isQueryBound_minimalQueryBound oa qc ?_
-- -- --   rw [support_map]
-- -- --   refine ⟨(x, qc), h, rfl⟩

-- -- -- -- /-- Slightly stronger than just being `Minimal` among all query bounds, as the space of
-- -- -- -- query counts is not a total order usually. -/
-- -- -- -- lemma minimalQueryBound_le_of_isQueryBound {oa : OracleComp spec α} {qc : ι → ℕ}
-- -- -- --     (hqc : IsQueryBound oa qc) : minimalQueryBound oa ≤ qc := by
-- -- -- --   induction oa using OracleComp.inductionOn with
-- -- -- --   | h_pure x => exact zero_le qc
-- -- -- --   | h_queryBind i t oa hoa => {
-- -- -- --     simp
-- -- -- --     rw [IsQueryBound] at hqc
-- -- -- --     sorry
-- -- -- --   }

-- -- -- -- lemma minimalQueryBound_minimal (oa : OracleComp spec α) :
-- -- -- --     Minimal (IsQueryBound oa) (minimalQueryBound oa) := by
-- -- -- --   rw [minimal_iff]

-- -- -- --   refine ⟨isQueryBound_minimalQueryBound oa, ?_⟩
-- -- -- --   intro qc hqc h
-- -- -- --   refine le_antisymm ?_ h
-- -- -- --   clear h
-- -- -- --   induction oa using OracleComp.inductionOn with
-- -- -- --   | h_pure x => {
-- -- -- --     -- simp at h
-- -- -- --     simp
-- -- -- --   }
-- -- -- --   | h_queryBind i t oa hoa => {
-- -- -- --     have : qc i ≠ 0 := by sorry
-- -- -- --     rw [minimalQueryBound_query_bind]

-- -- -- --     intro j

-- -- -- --     by_cases hj : j = i
-- -- -- --     · induction hj



-- -- -- --       sorry

-- -- -- --     · simp [hj]

-- -- -- --       sorry
-- -- -- --   }




-- -- -- lemma exists_isQueryBound (oa : OracleComp spec α) : ∃ qc, IsQueryBound oa qc :=
-- -- --   ⟨minimalQueryBound oa, isQueryBound_minimalQueryBound oa⟩

-- -- end minimalQueryBound

-- -- -- lemma isQueryBound_query_bind_iff (i : ι) (t : spec.domain i)
-- -- --     (oa : spec.range i → OracleComp spec α) (qc : ι → ℕ) :
-- -- --     IsQueryBound (query i t >>= oa) qc ↔ qc i ≠ 0 ∧
-- -- --       ∀ u, IsQueryBound (oa u) (Function.update qc i (qc i - 1)) := by
-- -- --   refine ⟨λ h ↦ ⟨?_, ?_⟩, λ h ↦ ?_⟩
-- -- --   · specialize h (minimalQueryBound (query i t >>= oa))
-- -- --     sorry
-- -- --   · sorry
-- -- --   · refine isQueryBound_mono (isQueryBound_bind (update_isQueryBound_query i t) h.2) ?_
-- -- --     intro j
-- -- --     by_cases hj : j = i
-- -- --     · simp only [hj, Pi.add_apply, Function.update_same]
-- -- --       rw [Nat.add_sub_of_le]
-- -- --       rw [Nat.one_le_iff_ne_zero]
-- -- --       exact h.1
-- -- --     · simp [hj]

-- -- section simulate

-- -- end simulate

-- end IsQueryBound

-- section PolyQueries

-- /-- If `oa` is an computation indexed by a security parameter, then `PolyQueries oa`
-- means that for each oracle index there is a polynomial function `qb` of the security parameter,
-- such that the number of queries to that oracle is bounded by the corresponding polynomial. -/
-- structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
--   {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
--   /-- `qb i` is a polynomial bound on the queries made to oracle `i`. -/
--   qb : ι → Polynomial ℕ
--   /-- The bound is actually a bound on the number of queries made. -/
--   qb_isQueryBound (n : ℕ) (x : α n) :
--     IsQueryBound (oa n x) (λ i ↦ (qb i).eval n)

-- end PolyQueries

-- end OracleComp
