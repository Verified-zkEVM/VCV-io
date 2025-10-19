/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.WriterT
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle` for counting the number of queries made
while running the computation. The count is represented by a function from oracle indices to
counts, allowing each oracle to be tracked individually.

Tracking individually is not necessary, but gives tighter security bounds in some cases.
It also allows for generating things like seed values for a computation more tightly.
-/

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Count the queries made by the computation using `idx` to categorize them. -/
def withCounting (so : QueryImpl spec m) (idx : spec.Domain → ι) :
    QueryImpl spec (WriterT (QueryCount ι) m) :=
  fun t => tell (QueryCount.single (idx t)) *> so t

-- @[simp] lemma withCounting_apply {α} (so : QueryImpl spec m) (q : OracleQuery spec α) :
--     so.withCounting.impl q = tell (QueryCount.single q.index) *> ↑(so.impl q) := rfl

end QueryImpl

/-- Oracle for counting the number of queries made by a computation. The count is stored as a
function from oracle indices to counts, to give finer grained information about the count. -/
def countingOracle (idx : spec.Domain → ι) :
    QueryImpl spec (WriterT (QueryCount ι) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCounting idx

namespace countingOracle

-- @[simp]
-- protected lemma impl_apply_eq (q : OracleQuery spec α) :
--     countingOracle.impl q = (tell (QueryCount.single q.index) *> liftM q) := rfl

-- /-- `countingOracle` has no effect on the behavior of the computation itself. -/
-- @[simp]
-- lemma fst_map_run_simulateQ (oa : OracleComp spec α) :
--     Prod.fst <$> (simulateQ countingOracle oa).run = oa :=
--   fst_map_writerT_run_simulateQ (by simp) oa

-- @[simp]
-- lemma run_simulateQ_bind_fst (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     ((simulateQ countingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
--   rw [← bind_map_left Prod.fst, fst_map_run_simulateQ]

-- @[simp]
-- lemma probFailure_run_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
--     [⊥ | (simulateQ countingOracle oa).run] = [⊥ | oa] :=
--   probFailure_writerT_run_simulateQ (by simp) (by simp) oa

-- @[simp]
-- lemma NeverFail_run_simulateQ_iff (oa : OracleComp spec α) :
--     NeverFail (simulateQ countingOracle oa).run ↔ NeverFail oa :=
--   NeverFail_writerT_run_simulateQ_iff (by simp) (by sorry) oa

-- alias ⟨_, NeverFail_simulateQ⟩ := NeverFail_run_simulateQ_iff

-- -- lemma run_simulateT_eq_run_simulateT_zero (oa : OracleComp spec α) (qc : ι → ℕ) :
-- --     (simulateT countingOracle oa).run qc =
-- --       map id (qc + ·) <$> (simulateT countingOracle oa).run 0 := by
-- --   revert qc
-- --   induction oa using OracleComp.inductionOn with
-- --   | pure x => simp
-- --   | query_bind i t oa h =>
-- --       intro qc
-- --       simp [h _ (update qc i (qc i + 1)), h _ (update 0 i 1)]
-- --       refine funext λ y ↦ congr_arg (· <$> _) (funext λ x ↦ ?_)
-- --       simp only [eq_iff_fst_eq_snd_eq, map_fst, id_eq, map_snd, true_and]
-- --       cases x
-- --       ext j
-- --       by_cases hj : j = i
-- --       · induction hj
-- --         simp [add_assoc]
-- --       · simp [hj]
-- --   | failure => simp [StateT.monad_failure_def]

-- -- section support

-- -- /-- We can always reduce the initial state of simulation with a counting oracle to start with a
-- -- count of zero, and add the initial count back on at the end. -/
-- -- lemma support_simulate (oa : OracleComp spec α) (qc : ι → ℕ) :
-- --     (simulate countingOracle qc oa).support =
-- --       Prod.map id (qc + ·) '' (simulate countingOracle 0 oa).support := by
-- --   revert qc
-- --   induction oa using OracleComp.inductionOn with
-- --   | pure a => simp only [simulate_pure, support_pure, Set.image_singleton, Prod.map_apply,
--   -- id_eq,
-- --       add_zero, implies_true]
-- --   | query_bind i t oa hoa =>
-- --       refine λ qc ↦ ?_
-- --       -- simp
-- --       sorry -- refine λ qc ↦ ?_
-- --       -- simp only [simulate_bind, simulate_query,countingOracle.apply_eq,
-- -- support_bind,support_map,
-- --       --   support_query, Set.image_univ, Set.mem_range, Set.iUnion_exists,
-- -- Set.iUnion_iUnion_eq',
-- --       --   Prod.map_apply, id_eq, Pi.zero_apply, zero_add, Set.image_iUnion]
-- --       -- refine Set.iUnion_congr (λ u ↦ ?_)
-- --       -- simp only [hoa u (update qc i (qc i + 1)), hoa u (update 0 i 1),
-- --       --   ← Set.image_comp, Function.comp, Prod.map_apply, id_eq, ← add_assoc]
-- --       -- refine Set.image_congr' (λ z ↦ Prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, funext (λ j ↦ ?_)⟩)
-- --       -- by_cases hij : j = i <;> simp [hij, add_assoc]
-- --   | failure => simp only [simulate_failure, support_failure, Set.image_empty, implies_true]

-- -- /-- Reduce membership in the support of simulation with counting to membership in simulation
-- -- starting with the count at `0`.
-- -- TODO: lemmas like this suggest maybe support shouldn't auto reduce on the computation type?
-- -- TODO: implicit parameters, and add extra helper lemmas -/
-- -- lemma mem_support_simulate_iff (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
-- --     z ∈ (simulate countingOracle qc oa).support ↔
-- --       ∃ qc', (z.1, qc') ∈ (simulate countingOracle 0 oa).support ∧ qc + qc' = z.2 := by
-- --   rw [support_simulate]
-- --   simp only [Prod.map_apply, id_eq, Set.mem_image, Prod.eq_iff_fst_eq_snd_eq, Prod.exists]
-- --   exact ⟨λ h ↦ let ⟨x, qc', h, hx, hqc'⟩ := h; ⟨qc', hx ▸ ⟨h, hqc'⟩⟩,
-- --     λ h ↦ let ⟨qc', h, hqc'⟩ := h; ⟨z.1, qc', h, rfl, hqc'⟩⟩

-- -- lemma mem_support_simulate_iff_of_le (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ))
-- --     (hz : qc ≤ z.2) : z ∈ (simulate countingOracle qc oa).support ↔
-- --       (z.1, z.2 - qc) ∈ (simulate countingOracle 0 oa).support := by
-- --   rw [mem_support_simulate_iff oa 0]
-- --   simp only [mem_support_simulate_iff oa qc z, zero_add, exists_eq_right]
-- --   refine ⟨λ ⟨qc', h, hqc'⟩ ↦ ?_, λ h ↦ ?_⟩
-- --   · convert h
-- --     refine funext (λ x ↦ ?_)
-- --     rw [Pi.sub_apply, Nat.sub_eq_iff_eq_add' (hz x)]
-- --     exact symm (congr_fun hqc' x)
-- --   · refine ⟨z.2 - qc, h, ?_⟩
-- --     refine funext (λ x ↦ ?_)
-- --     refine Nat.add_sub_cancel' (hz x)

-- -- lemma le_of_mem_support_simulate {oa : OracleComp spec α} {qc : ι → ℕ} {z : α × (ι → ℕ)}
-- --     (h : z ∈ (simulate countingOracle qc oa).support) : qc ≤ z.2 := by
-- --   rw [mem_support_simulate_iff] at h
-- --   obtain ⟨qc'', _, h⟩ := h
-- --   exact le_of_le_of_eq le_self_add h

-- -- section snd_map

-- -- lemma mem_support_snd_map_simulate_iff {α ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
-- --     (oa : OracleComp spec α) (qc qc' : ι → ℕ) :
-- --     qc' ∈ (@snd α _ <$> simulate countingOracle qc oa).support ↔
-- --       ∃ qc'', ∃ x, (x, qc'') ∈ (simulate countingOracle 0 oa).support ∧ qc + qc'' = qc' := by
-- --   simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right]
-- --   refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
-- --   · obtain ⟨x, hx⟩ := h
-- --     rw [mem_support_simulate_iff] at hx
-- --     obtain ⟨qc'', h, hqc''⟩ := hx
-- --     refine ⟨qc'', x, h, hqc''⟩
-- --   · obtain ⟨qc'', x, h, hqc''⟩ := h
-- --     refine ⟨x, ?_⟩
-- --     rw [mem_support_simulate_iff]
-- --     refine ⟨qc'', h, hqc''⟩

-- -- lemma mem_support_snd_map_simulate_iff_of_le (oa : OracleComp spec α) {qc qc' : ι → ℕ}
-- --     (hqc : qc ≤ qc') : qc' ∈ (@snd α _ <$> simulate countingOracle qc oa).support ↔
-- --       qc' - qc ∈ (@snd α _ <$> simulate countingOracle 0 oa).support := by
-- --   simp only [mem_support_snd_map_simulate_iff, zero_add]
-- --   refine exists_congr (λ qc'' ↦ exists_congr (λ x ↦ ?_))
-- --   refine and_congr_right' ⟨λ h ↦ funext (λ x ↦ ?_), λ h ↦ funext (λ x ↦ ?_)⟩
-- --   · simp only [← h, Pi.sub_apply, Pi.add_apply, add_tsub_cancel_left]
-- --   · simp [h, Nat.add_sub_cancel' (hqc x)]

-- -- lemma le_of_mem_support_snd_map_simulate {oa : OracleComp spec α} {qc qc' : ι → ℕ}
-- --     (h : qc' ∈ (@snd α _ <$> simulate countingOracle qc oa).support) : qc ≤ qc' := by
-- --   simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right] at h
-- --   obtain ⟨y, hy⟩ := h
-- --   exact le_of_mem_support_simulate hy

-- -- lemma sub_mem_support_snd_map_simulate {oa : OracleComp spec α} {qc qc' : ι → ℕ}
-- --     (h : qc' ∈ (@snd α _ <$> simulate countingOracle qc oa).support) :
-- --     qc' - qc ∈ (@snd α _ <$> simulate countingOracle 0 oa).support := by
-- --   rwa [mem_support_snd_map_simulate_iff_of_le] at h
-- --   convert le_of_mem_support_snd_map_simulate h

-- -- end snd_map

-- -- lemma add_mem_support_simulate {oa : OracleComp spec α} {qc : ι → ℕ} {z : α × (ι → ℕ)}
-- --     (hz : z ∈ (simulate countingOracle qc oa).support) (qc' : ι → ℕ) :
-- --     (z.1, z.2 + qc') ∈ (simulate countingOracle (qc + qc') oa).support := by
-- --   obtain ⟨qc1, hqc', h⟩ := (mem_support_simulate_iff _ _ _).1 hz
-- --   exact (mem_support_simulate_iff _ _ _).2 ⟨qc1, hqc', h ▸ by ring⟩

-- -- @[simp]
-- -- lemma add_right_mem_support_simulate_iff (oa : OracleComp spec α) (qc qc' : ι → ℕ) (x : α) :
-- --     (x, qc + qc') ∈ (simulate countingOracle qc oa).support ↔
-- --       (x, qc') ∈ (simulate countingOracle 0 oa).support := by
-- --   rw [support_simulate, Set.mem_image]
-- --   simp only [Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq, add_right_inj,
-- --     exists_eq_right_right, exists_eq_right]

-- -- @[simp]
-- -- lemma add_left_mem_support_simulate_iff (oa : OracleComp spec α) (qc qc' : ι → ℕ) (x : α) :
-- --     (x, qc' + qc) ∈ (simulate countingOracle qc oa).support ↔
-- --       (x, qc') ∈ (simulate countingOracle 0 oa).support := by
-- --   rw [add_comm qc' qc, add_right_mem_support_simulate_iff]

-- -- lemma mem_support_simulate_pure_iff (x : α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
-- --     z ∈ (simulate countingOracle qc (pure x : OracleComp spec α)).support ↔ z = (x, qc) := by
-- --   simp only [simulate_pure, support_pure, Set.mem_singleton_iff]

-- -- lemma apply_ne_zero_of_mem_support_simulate_queryBind {i : ι} {t : spec.Domain i}
-- --     {oa : spec.Range i → OracleComp spec α} {qc : ι → ℕ} {z : α × (ι → ℕ)}
-- --     (hz : z ∈ (simulate countingOracle qc ((query i t : OracleComp spec _) >>= oa)).support) :
-- --       z.2 i ≠ 0 := by
-- --   rw [mem_support_simulate_iff, simulate_query_bind] at hz
-- --   rw [support_bind] at hz
-- --   simp at hz
-- --   obtain ⟨qc', ⟨⟨u, hu⟩, hqc⟩⟩ := hz
-- --   sorry
-- --   -- have := le_of_mem_support_simulate hu i
-- --   -- simp at this
-- --   -- refine Nat.pos_iff_ne_zero.1 ?_
-- --   -- rw [← hqc, Pi.add_apply]
-- --   -- refine Nat.add_pos_right ?_ ?_
-- --   -- refine Nat.lt_of_succ_le this

-- -- lemma exists_mem_support_of_mem_support_simulate_queryBind {i : ι} {t : spec.Domain i}
-- --     {oa : spec.Range i → OracleComp spec α} {qc : ι → ℕ} {z : α × (ι → ℕ)}
-- --     (hz : z ∈ (simulate countingOracle qc ((query i t : OracleComp spec _) >>= oa)).support) :
-- --     ∃ u, (z.1, Function.update z.2 i (z.2 i - 1)) ∈
-- --       (simulate countingOracle qc (oa u)).support := by
-- --   rw [mem_support_simulate_iff, simulate_query_bind, support_bind] at hz
-- --   simp at hz
-- --   obtain ⟨qc', ⟨⟨u, hu⟩, hqc⟩⟩ := hz
-- --   refine ⟨u, ?_⟩
-- --   simp [← hqc]
-- --   have hqc' : qc' i ≠ 0 := by {
-- --     sorry
-- --     -- have := le_of_mem_support_simulate hu i
-- --     -- refine Nat.pos_iff_ne_zero.1 ?_
-- --     -- refine lt_of_lt_of_le ?_ this
-- --     -- simp only [update_same, zero_lt_one]
-- --   }
-- --   rw [mem_support_simulate_iff_of_le]
-- --   · simp
-- --     sorry
-- --     -- rw [mem_support_simulate_iff_of_le] at hu
-- --     -- · simp at hu
-- --     --   convert hu using 2
-- --     --   refine funext (λ j ↦ ?_)
-- --     --   by_cases hj : j = i
-- --     --   · simp [hj]
-- --     --     refine Nat.sub_eq_of_eq_add ?_
-- --     --     rw [add_comm _ (qc i)]
-- --     --     rw [Nat.add_sub_assoc]
-- --     --     rw [Nat.one_le_iff_ne_zero]

-- --     --     exact hqc'
-- --     --   · simp [hj]
-- --     -- · intro j
-- --     --   by_cases hj : j = i
-- --     --   · induction hj
-- --     --     simp only [update_same]
-- --     --     have := le_of_mem_support_simulate hu j
-- --     --     refine le_trans ?_ this
-- --     --     simp
-- --     --   · simp [hj]
-- --   · intro j
-- --     by_cases hj : j = i
-- --     · induction hj
-- --       simp only [update_self]
-- --       rw [Nat.le_sub_one_iff_lt]
-- --       · refine Nat.lt_add_of_pos_right ?_
-- --         rw [pos_iff_ne_zero]
-- --         assumption
-- --       · refine Nat.add_pos_right _ ?_
-- --         rwa [pos_iff_ne_zero]
-- --     · simp [hj]

-- -- lemma mem_support_simulate_queryBind_iff (i : ι) (t : spec.Domain i)
-- --     (oa : spec.Range i → OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
-- --     z ∈ (simulate countingOracle qc ((query i t : OracleComp spec _) >>= oa)).support ↔
-- --       z.2 i ≠ 0 ∧ ∃ u, (z.1, Function.update z.2 i (z.2 i - 1)) ∈
-- --         (simulate countingOracle qc (oa u)).support := by
-- --   refine ⟨λ h ↦ ⟨?_, ?_⟩, λ h ↦ ?_⟩
-- --   · refine apply_ne_zero_of_mem_support_simulate_queryBind h
-- --   · refine exists_mem_support_of_mem_support_simulate_queryBind h
-- --   · obtain ⟨hz0, ⟨u, hu⟩⟩ := h
-- --     simp only [simulate_bind, simulate_query, countingOracle.apply_eq, support_bind,
-- --       support_query, Set.image_univ, Set.mem_range, Set.iUnion_exists,
-- --       Set.iUnion_iUnion_eq', Set.mem_iUnion]
-- --     sorry
-- --     -- refine ⟨u, ?_⟩
-- --     -- have := add_mem_support_simulate hu (update 0 i 1)
-- --     -- convert this
-- --     -- · refine funext (λ j ↦ symm ?_)
-- --     --   by_cases hij : j = i
-- --     --   · simp [Function.update_apply, hij]
-- --     --   · simp [hij]
-- --     -- ·
-- --     --   refine funext (λ j ↦ ?_)
-- --     --   by_cases hij : j = i
-- --     --   · induction hij
-- --     --     simpa using (Nat.succ_pred_eq_of_ne_zero hz0).symm
-- --     --   · simp [hij]

-- -- lemma exists_mem_support_of_mem_support {oa : OracleComp spec α} {x : α} (hx : x ∈ oa.support)
-- --     (qc : ι → ℕ) : ∃ qc', (x, qc') ∈ (simulate countingOracle qc oa).support := by
-- --   rw [← SimOracle.IsTracking.run'_simulateT_eq_self countingOracle oa] at hx
-- --   sorry; sorry
-- --   -- simp at hx
-- --   -- exact hx

-- -- end support

-- end countingOracle
