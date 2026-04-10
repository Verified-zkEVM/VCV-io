/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa budget canQuery cost` parameterized by:
- `B` — the budget type
- `budget : B` — the initial budget
- `canQuery : ι → B → Prop` — whether a query to oracle `t` is allowed under budget `b`
- `cost : ι → B → B` — how the budget is updated after a query to oracle `t`

The definition is structural via `OracleComp.construct`: `pure` satisfies any bound, and
`query t >>= mx` satisfies the bound when `canQuery t b` holds and each continuation
satisfies the bound with the updated budget `cost t b`.

The classical per-index and total query bounds are recovered by `IsPerIndexQueryBound`
and `IsTotalQueryBound`.
-/

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

section IsQueryBound

variable {B : Type*}

/-- Generalized query bound parameterized by a budget type, a validity check, and a cost
function. `pure` satisfies any bound; `query t >>= mx` satisfies the bound when
`canQuery t b` and every continuation satisfies the bound at `cost t b`. -/
def IsQueryBound (oa : OracleComp spec α) (budget : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) : Prop :=
  OracleComp.construct
    (C := fun _ => B → Prop)
    (fun _ _ => True)
    (fun t _mx ih b => canQuery t b ∧ ∀ u, ih u (cost t b))
    oa budget

@[simp]
lemma isQueryBound_pure (x : α) (b : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (pure x : OracleComp spec α) b canQuery cost := trivial

lemma isQueryBound_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α)
    (b : B) (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (liftM (query (spec := spec) t) >>= mx) b canQuery cost ↔
      canQuery t b ∧ ∀ u, IsQueryBound (mx u) (cost t b) canQuery cost :=
  Iff.rfl

@[simp]
lemma isQueryBound_query_iff (t : ι) (b : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (liftM (query (spec := spec) t) : OracleComp spec _) b canQuery cost ↔
    canQuery t b := by
  simp [IsQueryBound]

private lemma isQueryBound_map_aux (oa : OracleComp spec α) (f : α → β)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    ∀ {b : B}, (f <$> oa).IsQueryBound b canQuery cost ↔
      oa.IsQueryBound b canQuery cost := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind t mx ih =>
    intro b
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    rw [isQueryBound_query_bind_iff, isQueryBound_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun u => ih u

@[simp]
lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (b : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (f <$> oa) b canQuery cost ↔ IsQueryBound oa b canQuery cost :=
  isQueryBound_map_aux oa f canQuery cost

private lemma isQueryBound_congr_aux
    (oa : OracleComp spec α)
    (canQuery₁ canQuery₂ : ι → B → Prop) (cost₁ cost₂ : ι → B → B)
    (hcan : ∀ (t : ι) (b : B), canQuery₁ t b ↔ canQuery₂ t b)
    (hcost : ∀ (t : ι) (b : B), cost₁ t b = cost₂ t b) :
    ∀ {b : B}, oa.IsQueryBound b canQuery₁ cost₁ ↔ oa.IsQueryBound b canQuery₂ cost₂ := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro b
      simp
  | query_bind t mx ih =>
      intro b
      rw [isQueryBound_query_bind_iff, isQueryBound_query_bind_iff]
      constructor
      · intro h
        refine ⟨(hcan t b).1 h.1, fun u => ?_⟩
        have hu : IsQueryBound (mx u) (cost₁ t b) canQuery₂ cost₂ :=
          (ih u (b := cost₁ t b)).1 (h.2 u)
        simpa [hcost t b] using hu
      · intro h
        refine ⟨(hcan t b).2 h.1, fun u => ?_⟩
        have hu : IsQueryBound (mx u) (cost₁ t b) canQuery₂ cost₂ := by
          simpa [hcost t b] using h.2 u
        exact (ih u (b := cost₁ t b)).2 hu

lemma isQueryBound_congr
    {oa : OracleComp spec α} {b : B}
    {canQuery₁ canQuery₂ : ι → B → Prop} {cost₁ cost₂ : ι → B → B}
    (hcan : ∀ (t : ι) (b : B), canQuery₁ t b ↔ canQuery₂ t b)
    (hcost : ∀ (t : ι) (b : B), cost₁ t b = cost₂ t b) :
    oa.IsQueryBound b canQuery₁ cost₁ ↔ oa.IsQueryBound b canQuery₂ cost₂ :=
  isQueryBound_congr_aux oa canQuery₁ canQuery₂ cost₁ cost₂ hcan hcost

end IsQueryBound

section IsPerIndexQueryBound

variable [DecidableEq ι]

/-- Per-index query bound: `qb t` gives the maximum number of queries to oracle `t`.
Each query to `t` decrements `qb t` by one. Recovers the classical notion. -/
abbrev IsPerIndexQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
  IsQueryBound oa qb (fun t qb => 0 < qb t) (fun t qb => Function.update qb t (qb t - 1))

@[simp]
lemma isPerIndexQueryBound_pure (x : α) (qb : ι → ℕ) :
    IsPerIndexQueryBound (pure x : OracleComp spec α) qb := trivial

lemma isPerIndexQueryBound_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α)
    (qb : ι → ℕ) :
    IsPerIndexQueryBound (liftM (query (spec := spec) t) >>= mx) qb ↔
      0 < qb t ∧ ∀ u, IsPerIndexQueryBound (mx u) (Function.update qb t (qb t - 1)) :=
  Iff.rfl

@[simp]
lemma isPerIndexQueryBound_query_iff (t : ι) (qb : ι → ℕ) :
    IsPerIndexQueryBound (liftM (query (spec := spec) t) : OracleComp spec _) qb ↔
    0 < qb t := by
  simp [IsPerIndexQueryBound]

private lemma update_le_update {qb qb' : ι → ℕ} {t : ι} (hle : qb ≤ qb') :
    Function.update qb t (qb t - 1) ≤ Function.update qb' t (qb' t - 1) := by
  intro j
  by_cases hj : j = t
  · rw [hj, Function.update_self, Function.update_self]
    exact Nat.sub_le_sub_right (hle t) 1
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    exact hle j

private lemma isPerIndexQueryBound_mono_aux (oa : OracleComp spec α) :
    ∀ {qb qb' : ι → ℕ}, qb ≤ qb' →
      oa.IsPerIndexQueryBound qb → oa.IsPerIndexQueryBound qb' := by
  induction oa using OracleComp.inductionOn with
  | pure _ => intros; trivial
  | query_bind t mx ih =>
    intro qb qb' hle h
    rw [isPerIndexQueryBound_query_bind_iff] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 (hle t), fun u => ih u (update_le_update hle) (h.2 u)⟩

lemma IsPerIndexQueryBound.mono {oa : OracleComp spec α} {qb qb' : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (hle : qb ≤ qb') : IsPerIndexQueryBound oa qb' :=
  isPerIndexQueryBound_mono_aux oa hle h

private lemma update_add_eq_update_add {qb₁ qb₂ : ι → ℕ} {t : ι} (ht : 0 < qb₁ t) :
    Function.update qb₁ t (qb₁ t - 1) + qb₂ =
      Function.update (qb₁ + qb₂) t ((qb₁ + qb₂) t - 1) := by
  ext j
  by_cases hj : j = t
  · rw [hj, Pi.add_apply, Function.update_self, Pi.add_apply, Function.update_self]; omega
  · simp only [Pi.add_apply, Function.update_of_ne hj]

private lemma isPerIndexQueryBound_bind_aux (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) (qb₂ : ι → ℕ)
    (h2 : ∀ x, IsPerIndexQueryBound (ob x) qb₂) :
    ∀ {qb₁}, oa.IsPerIndexQueryBound qb₁ →
      (oa >>= ob).IsPerIndexQueryBound (qb₁ + qb₂) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qb₁ _
    simp only [pure_bind]
    exact (h2 x).mono le_add_self
  | query_bind t mx ih =>
    intro qb₁ h1
    rw [isPerIndexQueryBound_query_bind_iff] at h1
    rw [bind_assoc, isPerIndexQueryBound_query_bind_iff]
    refine ⟨Nat.add_pos_left h1.1 _, fun u => ?_⟩
    rw [← update_add_eq_update_add h1.1]
    exact ih u (h1.2 u)

lemma isPerIndexQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {qb₁ qb₂ : ι → ℕ}
    (h1 : IsPerIndexQueryBound oa qb₁) (h2 : ∀ x, IsPerIndexQueryBound (ob x) qb₂) :
    IsPerIndexQueryBound (oa >>= ob) (qb₁ + qb₂) :=
  isPerIndexQueryBound_bind_aux oa ob qb₂ h2 h1

@[simp]
lemma isPerIndexQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
    IsPerIndexQueryBound (f <$> oa) qb ↔ IsPerIndexQueryBound oa qb :=
  isQueryBound_map_aux oa f _ _

/-! ### Soundness: structural bound implies dynamic count bound -/

/-- The structural query bound `IsPerIndexQueryBound` is sound with respect to the dynamic
query count produced by `countingOracle`: if a computation satisfies a per-index query bound,
then every execution path's query count is bounded.

Proof strategy: induction on `OracleComp`, matching the structural `IsQueryBound` decomposition
with the `mem_support_simulate_queryBind_iff` characterization of counting oracle support. -/
theorem IsPerIndexQueryBound.counting_bounded {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    z.2 ≤ qb := by
  induction oa using OracleComp.inductionOn generalizing qb z with
  | pure x =>
    rw [countingOracle.mem_support_simulate_pure_iff] at hz
    subst hz
    intro i; exact Nat.zero_le _
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
    obtain ⟨hne, u, hu⟩ := hz
    have h_snd : Function.update z.2 t (z.2 t - 1) ≤
        Function.update qb t (qb t - 1) := by
      change (z.1, Function.update z.2 t (z.2 t - 1)).2 ≤ _
      exact ih u (h.2 u) hu
    intro i
    by_cases hi : i = t
    · rw [hi]
      have hle := h_snd t
      simp only [Function.update_self] at hle
      have hz_pos : 0 < z.2 t := Nat.pos_of_ne_zero hne
      have hq_pos := h.1
      calc z.2 t = (z.2 t - 1) + 1 := (Nat.succ_pred_eq_of_pos hz_pos).symm
        _ ≤ (qb t - 1) + 1 := Nat.succ_le_succ hle
        _ = qb t := Nat.succ_pred_eq_of_pos hq_pos
    · have hle := h_snd i
      rw [Function.update_of_ne hi, Function.update_of_ne hi] at hle
      exact hle

end IsPerIndexQueryBound

/-! ### Total query bounds -/

/-- A total query bound: the computation makes at most `n` queries total
(across all oracle indices). -/
def IsTotalQueryBound (oa : OracleComp spec α) (n : ℕ) : Prop :=
  IsQueryBound oa n (fun _ b => 0 < b) (fun _ b => b - 1)

lemma isTotalQueryBound_query_bind_iff {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound (liftM (query t) >>= mx) n ↔
      0 < n ∧ ∀ u, IsTotalQueryBound (mx u) (n - 1) :=
  Iff.rfl

lemma IsTotalQueryBound.mono {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h : IsTotalQueryBound oa n₁) (hle : n₁ ≤ n₂) :
    IsTotalQueryBound oa n₂ := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure _ =>
      exact trivial
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h ⊢
      exact ⟨Nat.lt_of_lt_of_le h.1 hle,
        fun u => ih u (h.2 u) (Nat.sub_le_sub_right hle 1)⟩

lemma isTotalQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {n₁ n₂ : ℕ}
    (h1 : IsTotalQueryBound oa n₁) (h2 : ∀ x, IsTotalQueryBound (ob x) n₂) :
    IsTotalQueryBound (oa >>= ob) (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ with
  | pure x =>
      simp only [pure_bind]
      exact (h2 x).mono (Nat.le_add_left _ _)
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h1
      rw [bind_assoc, isTotalQueryBound_query_bind_iff]
      refine ⟨Nat.add_pos_left h1.1 _, fun u => ?_⟩
      have h3 := ih u (h1.2 u)
      have heq : n₁ - 1 + n₂ = n₁ + n₂ - 1 := by omega
      rw [heq] at h3
      exact h3

lemma not_isTotalQueryBound_bind_query_prefix_zero
    {oa : OracleComp spec α}
    {next : α → spec.Domain}
    {ob : ∀ x, spec.Range (next x) → OracleComp spec β} :
    ¬ IsTotalQueryBound
        (oa >>= fun x => (liftM (query (spec := spec) (next x)) >>= ob x))
        0 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rw [pure_bind, isTotalQueryBound_query_bind_iff]
      simp
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff]
      simp

/-- If a computation is followed by a continuation that always starts with one query,
then a bound on the whole computation by `n + 1` yields a bound on the prefix by `n`. -/
lemma IsTotalQueryBound.of_bind_query_prefix [spec.Inhabited]
    {oa : OracleComp spec α}
    {next : α → spec.Domain}
    {ob : ∀ x, spec.Range (next x) → OracleComp spec β}
    {n : ℕ}
    (h :
      IsTotalQueryBound
        (oa >>= fun x => (liftM (query (spec := spec) (next x)) >>= ob x))
        (n + 1)) :
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ =>
      exact trivial
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      have hn0 : n ≠ 0 := by
        intro hz
        subst hz
        exact not_isTotalQueryBound_bind_query_prefix_zero
          (oa := mx default) (next := next) (ob := ob) (h.2 default)
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      refine ⟨hn, fun u => ?_⟩
      have hn_succ : n = (n - 1) + 1 := by omega
      have hu : IsTotalQueryBound
          (mx u >>= fun x => (liftM (query (spec := spec) (next x)) >>= ob x))
          ((n - 1) + 1) := by
        rw [← hn_succ]
        exact h.2 u
      exact ih u (n := n - 1) hu

theorem IsTotalQueryBound.simulateQ_run_of_step {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t : spec.Domain, ∀ s : σ, IsTotalQueryBound ((impl t).run s) 1)
    (s : σ) :
    IsTotalQueryBound ((simulateQ impl oa).run s) n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      simpa [simulateQ_pure] using
        (show IsTotalQueryBound (pure (x, s) : OracleComp spec (α × σ)) n from trivial)
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hstep' : IsTotalQueryBound
          ((liftM (impl t) : StateT σ (OracleComp spec) (spec.Range t)).run s) 1 := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s
      have hrest : ∀ p : spec.Range t × σ,
          IsTotalQueryBound ((simulateQ impl (mx p.1)).run p.2) (n - 1) :=
        fun p => ih p.1 (h.2 p.1) p.2
      have hn : 1 + (n - 1) = n := by omega
      simpa [StateT.run_bind, hn] using isTotalQueryBound_bind hstep' hrest

namespace countingOracle

lemma add_single_mem_support_simulate_queryBind [DecidableEq ι] {t : spec.Domain}
    {oa : spec.Range t → OracleComp spec α} {u : spec.Range t}
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate (spec := spec) (oa := oa u) 0)) :
    (z.1, QueryCount.single t + z.2) ∈
      support (countingOracle.simulate (spec := spec)
        (oa := ((query t : OracleComp spec _) >>= oa)) 0) := by
  rw [countingOracle.mem_support_simulate_queryBind_iff]
  refine ⟨by simp [QueryCount.single], ⟨u, ?_⟩⟩
  convert hz using 2
  funext j
  by_cases hj : j = t
  · subst hj
    simp [QueryCount.single]
  · simp [Function.update, hj, QueryCount.single]

section CostSupport

variable [DecidableEq ι] [spec.Fintype] [spec.Inhabited] [Fintype ι]

omit [spec.Fintype] [spec.Inhabited] in
lemma exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
    {σ : Type u} {impl : QueryImpl spec (StateT σ (OracleComp spec))}
    (cost : σ → ℕ)
    (hstep : ∀ t : spec.Domain, ∀ st : σ,
      ∀ x : spec.Range t × σ, x ∈ support ((impl t).run st) →
        cost x.2 ≤ cost st + 1)
    {oa : OracleComp spec α} {st₀ : σ} {z : α × σ}
    (hz : z ∈ support (((simulateQ impl oa).run st₀) : OracleComp spec (α × σ))) :
    ∃ qc : QueryCount ι,
      (z.1, qc) ∈ support ((countingOracle.simulate (spec := spec) (α := α) (oa := oa)
        (0 : QueryCount ι)) : OracleComp spec (α × QueryCount ι)) ∧
      cost z.2 ≤ cost st₀ + ∑ i, qc i := by
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simp [countingOracle.simulate]
      · simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qc, hqc, hcost⟩
      refine ⟨QueryCount.single t + qc, ?_, ?_⟩
      · exact countingOracle.add_single_mem_support_simulate_queryBind hqc
      · have hstep' : cost qu.2 ≤ cost st₀ + 1 :=
            hstep t st₀ qu hqu
        have hsum_single : ∑ i, QueryCount.single t i = 1 := by
          rw [QueryCount.single]
          conv_lhs =>
            rw [← Finset.add_sum_erase Finset.univ (Function.update 0 t 1) (Finset.mem_univ t)]
          simp only [Function.update_self]
          have herase :
              ∑ x ∈ Finset.univ.erase t, Function.update (0 : QueryCount ι) t 1 x = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hjt : j ≠ t := Finset.ne_of_mem_erase hj
            change Function.update (0 : QueryCount ι) t 1 j = 0
            simp [Function.update, hjt]
          rw [herase]
        calc
          cost z.2 ≤ cost qu.2 + ∑ i, qc i := hcost
          _ ≤ (cost st₀ + 1) + ∑ i, qc i := by omega
          _ = cost st₀ + ∑ i, (QueryCount.single t + qc) i := by
              simp [Finset.sum_add_distrib, hsum_single, add_left_comm, add_comm]

end CostSupport

end countingOracle

section CountingResidual

variable [DecidableEq ι] [Fintype ι]

lemma sum_update_pred {qc : ι → ℕ} {t : ι} (ht : 0 < qc t) :
    ∑ i, Function.update qc t (qc t - 1) i = (∑ i, qc i) - 1 := by
  have hsub : ∑ i, Function.update qc t (qc t - 1) i + 1 = (∑ i, qc i) := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => Function.update qc t (qc t - 1) i)
      (Finset.mem_univ t)]
    simp only [Function.update_self]
    conv_rhs => rw [← Finset.add_sum_erase Finset.univ qc (Finset.mem_univ t)]
    have herase : ∑ x ∈ Finset.univ.erase t,
        Function.update qc t (qc t - 1) x = ∑ x ∈ Finset.univ.erase t, qc x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [herase]
    omega
  omega

/-- If `oa >>= ob` is totally query-bounded by `n`, then after any support point of the
counting run of `oa`, the continuation `ob` is bounded by the residual budget. -/
theorem IsTotalQueryBound.residual_of_mem_support_counting
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsTotalQueryBound (oa >>= ob) n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    IsTotalQueryBound (ob z.1) (n - ∑ i, z.2 i) := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simpa [pure_bind] using h
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz'⟩ := hz
      have hu :
          IsTotalQueryBound (ob z.1)
            ((n - 1) - ∑ i, (Function.update z.2 t (z.2 t - 1)) i) :=
        ih u (h.2 u) hz'
      have hsum : ∑ i, Function.update z.2 t (z.2 t - 1) i = (∑ i, z.2 i) - 1 := by
        exact sum_update_pred (Nat.pos_of_ne_zero hz0)
      rw [hsum] at hu
      have hsum_pos : 0 < ∑ i, z.2 i := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      have hbudget : (n - 1) - ((∑ i, z.2 i) - 1) = n - ∑ i, z.2 i := by
        omega
      simpa [hbudget] using hu

/-- Any support point of the counting simulation of a totally query-bounded
computation has total query count at most the structural bound. -/
theorem IsTotalQueryBound.counting_total_le
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    (∑ i, z.2 i) ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simp
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz'⟩ := hz
      have hu :
          ∑ i, Function.update z.2 t (z.2 t - 1) i ≤ n - 1 :=
        ih u (h.2 u) hz'
      have hsum : ∑ i, Function.update z.2 t (z.2 t - 1) i = (∑ i, z.2 i) - 1 := by
        exact sum_update_pred (Nat.pos_of_ne_zero hz0)
      rw [hsum] at hu
      have hsum_pos : 0 < ∑ i, z.2 i := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      omega

omit [Fintype ι] [DecidableEq ι] in
/-- If a stateful simulation has support cost at most one per query step, then any support
point of the simulated prefix leaves the continuation bounded by the residual budget measured
by that cost. The cost may under-approximate the true query count, so the resulting residual
budget is correspondingly weaker but still sound. -/
theorem IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
    [spec.Fintype] [spec.Inhabited] [Finite ι]
    {σ : Type u} {impl : QueryImpl spec (StateT σ (OracleComp spec))}
    (cost : σ → ℕ)
    (hstep : ∀ t : spec.Domain, ∀ st : σ,
      ∀ x : spec.Range t × σ, x ∈ support ((impl t).run st) →
        cost x.2 ≤ cost st + 1)
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsTotalQueryBound (oa >>= ob) n)
    {st₀ : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run st₀)) :
    IsTotalQueryBound (ob z.1) (n - (cost z.2 - cost st₀)) := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := Fintype.ofFinite ι
  rcases countingOracle.exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
      (spec := spec) (ι := ι) (impl := impl) cost hstep hz with
    ⟨qc, hqc, hcost⟩
  have hres :
      IsTotalQueryBound (ob z.1) (n - ∑ i, qc i) :=
    IsTotalQueryBound.residual_of_mem_support_counting
      (spec := spec) (ι := ι) (oa := oa) (ob := ob) (n := n) (z := (z.1, qc)) h hqc
  have hdiff : cost z.2 - cost st₀ ≤ ∑ i, qc i := by
    omega
  exact hres.mono (by omega)

end CountingResidual

/-- Per-index bound implies total bound (sum over indices). -/
theorem IsTotalQueryBound.of_perIndex [DecidableEq ι] [Fintype ι] {oa : OracleComp spec α}
    {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ =>
      exact trivial
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      have hpos : 0 < ∑ i, qb i :=
        Nat.lt_of_lt_of_le h.1 (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))
      refine ⟨hpos, fun u => ?_⟩
      rw [← sum_update_pred h.1]
      exact ih u (h.2 u)

/-! ### Worst-case query bounds as a function of input size -/

/-- Worst-case per-index query bound as a function of input size:
for all inputs `x` with `size x ≤ n`, the computation `f x` makes at most `bound n i`
queries to oracle `i`. -/
def QueryUpperBound [DecidableEq ι] (f : α → OracleComp spec β) (size : α → ℕ)
    (bound : ℕ → ι → ℕ) : Prop :=
  ∀ n x, size x ≤ n → IsPerIndexQueryBound (f x) (bound n)

/-- Total query upper bound: there exists a constant `k` such that for all inputs `x`
with `size x ≤ n`, the computation `f x` makes at most `k * bound n` total queries.
Uses the structural `IsQueryBound` to avoid dependence on oracle responses. -/
def TotalQueryUpperBound (f : α → OracleComp spec β) (size : α → ℕ) (bound : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n x, size x ≤ n → IsQueryBound (f x) (k * bound n)
    (fun _ b => 0 < b) (fun _ b => b - 1)

/-- `PolyQueryUpperBound` says the per-index query count is polynomially bounded
in the input size. This is a non-parameterized version of `PolyQueries`. -/
def PolyQueryUpperBound [DecidableEq ι] (f : α → OracleComp spec β) (size : α → ℕ) : Prop :=
  ∃ qb : ι → Polynomial ℕ, QueryUpperBound f size (fun n i => (qb i).eval n)

/-- If `f` has a `QueryUpperBound`, then each `f x` satisfies `IsPerIndexQueryBound`. -/
lemma QueryUpperBound.apply [DecidableEq ι]
    {f : α → OracleComp spec β} {size : α → ℕ} {bound : ℕ → ι → ℕ}
    (h : QueryUpperBound f size bound) (x : α) :
    IsPerIndexQueryBound (f x) (bound (size x)) :=
  h (size x) x le_rfl

/-- If `oa` is a computation indexed by a security parameter, then `PolyQueries oa`
means that for each oracle index there is a polynomial function `qb` of the security parameter,
such that the number of queries to that oracle is bounded by the corresponding polynomial. -/
structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
    {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  /-- `qb i` is a polynomial bound on the queries made to oracle `i`. -/
  qb : ι → Polynomial ℕ
  /-- The bound is actually a bound on the number of queries made. -/
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsPerIndexQueryBound (oa n x) (fun i => (qb i).eval n)

end OracleComp
