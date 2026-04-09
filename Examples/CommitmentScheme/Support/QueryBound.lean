/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, jpwaters
-/
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Commitment Scheme local total query bound support

This file adds the total-query-bound API used by the commitment-scheme proofs on
top of `main`'s `IsQueryBound` infrastructure.
-/

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}
/-! ## Total Query Bound -/

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
  | pure x =>
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
      simp [simulateQ_pure] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa [countingOracle.simulate]
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
            show Function.update (0 : QueryCount ι) t 1 j = 0
            simp [Function.update, hjt]
          rw [herase]
        calc
          cost z.2 ≤ cost qu.2 + ∑ i, qc i := hcost
          _ ≤ (cost st₀ + 1) + ∑ i, qc i := by omega
          _ = cost st₀ + ∑ i, (QueryCount.single t + qc) i := by
              simp [Finset.sum_add_distrib, hsum_single, add_assoc, add_left_comm, add_comm]

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

/-- If a stateful simulation has support cost at most one per query step, then any support
point of the simulated prefix leaves the continuation bounded by the residual budget measured
by that cost. The cost may under-approximate the true query count, so the resulting residual
budget is correspondingly weaker but still sound. -/
theorem IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
    [spec.Fintype] [spec.Inhabited]
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


end OracleComp
