/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import PolyFun.PFunctor.Bound
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.CountingOracle
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import all VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Query-bound transfer through oracle simulation
-/

public section

open OracleSpec

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-! ### Forward query-bound transfer for `preInsert` / `postInsert`

Unlike the trace-flavour transfers (which are biconditional because `tell` makes zero
oracle queries), an arbitrary insertion `nx` may itself query the underlying oracle. So
the transfer is forward-only: a per-step bound on the inserted computation translates to
a multiplicative bound on the simulation.

The shape is `n * (b_nx + b_so)` where:
* `n` bounds the source computation `oa`,
* `b_so` bounds each per-query handler `impl t`,
* `b_nx` bounds each inserted computation `nx t` (or `nx t u` for `postInsert`).

When `b_nx = 0` (the trace case), the formula collapses to `n * b_so`, recovering the
biconditional trace transfer in one direction. -/

theorem isTotalQueryBound_simulateQ_preInsert
    {ι' : Type u} {spec' : OracleSpec ι'} {β : Type u}
    {impl : QueryImpl spec (OracleComp spec')}
    {nx : spec.Domain → OracleComp spec' β}
    {oa : OracleComp spec α} {n b_so b_nx : ℕ}
    (hoa : IsTotalQueryBound oa n)
    (h_so : ∀ t, IsTotalQueryBound (impl t) b_so)
    (h_nx : ∀ t, IsTotalQueryBound (nx t) b_nx) :
    IsTotalQueryBound (simulateQ (impl.preInsert nx) oa) (n * (b_nx + b_so)) := by
  refine IsTotalQueryBound.simulateQ_of_step_le hoa fun t => ?_
  simp only [QueryImpl.preInsert_apply, monadLift_self]
  exact isTotalQueryBound_bind (h_nx t) (fun _ => h_so t)

theorem isTotalQueryBound_simulateQ_postInsert
    {ι' : Type u} {spec' : OracleSpec ι'} {β : Type u}
    {impl : QueryImpl spec (OracleComp spec')}
    {nx : (t : spec.Domain) → spec.Range t → OracleComp spec' β}
    {oa : OracleComp spec α} {n b_so b_nx : ℕ}
    (hoa : IsTotalQueryBound oa n)
    (h_so : ∀ t, IsTotalQueryBound (impl t) b_so)
    (h_nx : ∀ t u, IsTotalQueryBound (nx t u) b_nx) :
    IsTotalQueryBound (simulateQ (impl.postInsert nx) oa) (n * (b_so + b_nx)) := by
  refine IsTotalQueryBound.simulateQ_of_step_le hoa fun t => ?_
  simp only [QueryImpl.postInsert_apply, monadLift_self]
  refine isTotalQueryBound_bind (h_so t) (fun u => ?_)
  exact isTotalQueryBound_bind (h_nx t u)
    (fun _ => show IsTotalQueryBound (pure u : OracleComp spec' _) 0 from trivial)

/-- Predicated version of `simulateQ_of_step_le`: a total bound on the source plus a
predicated step bound transfers to a predicated bound on the simulation. -/
theorem IsQueryBoundP.simulateQ_of_step_le_total
    {ι' : Type u} {spec' : OracleSpec ι'}
    {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')}
    {oa : OracleComp spec α} {n step : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t : spec.Domain, IsQueryBoundP (impl t) q step) :
    IsQueryBoundP (simulateQ impl oa) q (n * step) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hrest : ∀ u, IsQueryBoundP (simulateQ impl (mx u)) q ((n - 1) * step) :=
        fun u => ih u (h.2 u)
      have hbind := isQueryBoundP_bind (hstep t) (fun u _ => hrest u)
      exact hbind.mono
        (Nat.le_of_eq (by rw [Nat.sub_one_mul,
          Nat.add_sub_cancel' (Nat.le_mul_of_pos_left step h.1)]))

theorem isQueryBoundP_simulateQ_preInsert
    {ι' : Type u} {spec' : OracleSpec ι'} {β : Type u}
    {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')}
    {nx : spec.Domain → OracleComp spec' β}
    {oa : OracleComp spec α} {n b_so b_nx : ℕ}
    (hoa : IsTotalQueryBound oa n)
    (h_so : ∀ t, IsQueryBoundP (impl t) q b_so)
    (h_nx : ∀ t, IsQueryBoundP (nx t) q b_nx) :
    IsQueryBoundP (simulateQ (impl.preInsert nx) oa) q (n * (b_nx + b_so)) := by
  refine IsQueryBoundP.simulateQ_of_step_le_total hoa fun t => ?_
  simp only [QueryImpl.preInsert_apply, monadLift_self]
  exact isQueryBoundP_bind (h_nx t) (fun _ _ => h_so t)

theorem isQueryBoundP_simulateQ_postInsert
    {ι' : Type u} {spec' : OracleSpec ι'} {β : Type u}
    {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')}
    {nx : (t : spec.Domain) → spec.Range t → OracleComp spec' β}
    {oa : OracleComp spec α} {n b_so b_nx : ℕ}
    (hoa : IsTotalQueryBound oa n)
    (h_so : ∀ t, IsQueryBoundP (impl t) q b_so)
    (h_nx : ∀ t u, IsQueryBoundP (nx t u) q b_nx) :
    IsQueryBoundP (simulateQ (impl.postInsert nx) oa) q (n * (b_so + b_nx)) := by
  refine IsQueryBoundP.simulateQ_of_step_le_total hoa fun t => ?_
  simp only [QueryImpl.postInsert_apply, monadLift_self]
  refine isQueryBoundP_bind (h_so t) (fun u _ => ?_)
  exact isQueryBoundP_bind (h_nx t u)
    (fun _ _ => show IsQueryBoundP (pure u : OracleComp spec' _) q 0 from trivial)

/-- Sanity check: instrumenting an oracle with a side-querying "monitor" computation
fired before each query gives a clean multiplicative bound. -/
example {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α β : Type u}
    {impl : QueryImpl spec (OracleComp spec)} {monitor : OracleComp spec β}
    {oa : OracleComp spec α} {n b_so b_mon : ℕ}
    (hoa : IsTotalQueryBound oa n)
    (h_so : ∀ t, IsTotalQueryBound (impl t) b_so)
    (h_mon : IsTotalQueryBound monitor b_mon) :
    IsTotalQueryBound (simulateQ (impl.preInsert (fun _ => monitor)) oa)
      (n * (b_mon + b_so)) :=
  isTotalQueryBound_simulateQ_preInsert hoa h_so (fun _ => h_mon)

/-- The total query count of a single-query `QueryCount` is one. Shared by the counting-oracle
support lemmas that peel off one `QueryCount.single t` per query step. -/
private lemma sum_single_eq_one [DecidableEq ι] [Fintype ι] (t : ι) :
    ∑ i, QueryCount.single t i = 1 := by
  simp [QueryCount.single]

namespace countingOracle

lemma add_single_mem_support_simulate_queryBind [DecidableEq ι]
     {t : spec.Domain}
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
  by_cases hj : j = t <;> simp [hj, QueryCount.single]

section CostSupport

variable [DecidableEq ι] [IsUniformSpec spec] [Fintype ι]

omit [IsUniformSpec spec] in
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
      · have hstep' : cost qu.2 ≤ cost st₀ + 1 := hstep t st₀ qu hqu
        calc
          cost z.2 ≤ cost qu.2 + ∑ i, qc i := hcost
          _ ≤ (cost st₀ + 1) + ∑ i, qc i := by omega
          _ = cost st₀ + ∑ i, (QueryCount.single t + qc) i := by
              simp [Finset.sum_add_distrib, sum_single_eq_one t, add_left_comm, add_comm]

end CostSupport

end countingOracle

section CountingResidual

variable [DecidableEq ι] [Fintype ι]

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
      simpa [monad_norm] using h
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz'⟩ := hz
      have hu : IsTotalQueryBound (ob z.1)
          ((n - 1) - ∑ i, (Function.update z.2 t (z.2 t - 1)) i) := ih u (h.2 u) hz'
      rw [sum_update_pred (Nat.pos_of_ne_zero hz0)] at hu
      have hsum_pos : 0 < ∑ i, z.2 i := Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      simpa [show (n - 1) - ((∑ i, z.2 i) - 1) = n - ∑ i, z.2 i by omega] using hu

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
      have hu : ∑ i, Function.update z.2 t (z.2 t - 1) i ≤ n - 1 := ih u (h.2 u) hz'
      have hsum : ∑ i, Function.update z.2 t (z.2 t - 1) i = (∑ i, z.2 i) - 1 :=
        sum_update_pred (Nat.pos_of_ne_zero hz0)
      rw [hsum] at hu
      have hsum_pos : 0 < ∑ i, z.2 i := Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      omega

omit [Fintype ι] in
/-- The counting-oracle simulation of any `OracleComp` has non-empty support whenever every
oracle range is inhabited. Used by the converse direction of
`isTotalQueryBound_iff_counting_total_le`. -/
lemma countingOracle.support_simulate_nonempty [IsUniformSpec spec]
    (oa : OracleComp spec α) :
    (support (countingOracle.simulate oa 0)).Nonempty := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨(x, 0), by rw [countingOracle.mem_support_simulate_pure_iff]⟩
  | query_bind t mx ih =>
      obtain ⟨z, hz⟩ := ih default
      refine ⟨(z.1, QueryCount.single t + z.2), ?_⟩
      exact countingOracle.add_single_mem_support_simulate_queryBind hz

/-- Converse of `IsTotalQueryBound.counting_total_le`: a counting-oracle bound on every
support path implies the structural total query bound. Together they characterize
`IsTotalQueryBound` purely in terms of the counting-oracle support. -/
theorem isTotalQueryBound_iff_counting_total_le [IsUniformSpec spec]
    {oa : OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound oa n ↔
      ∀ z ∈ support (countingOracle.simulate oa 0), (∑ i, z.2 i) ≤ n := by
  refine ⟨fun h _ hz => IsTotalQueryBound.counting_total_le h hz, fun h => ?_⟩
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff]
      have hsplit : ∀ q : QueryCount ι, (∑ i, (QueryCount.single t + q) i) = 1 + ∑ i, q i :=
        fun q => by simp [Pi.add_apply, Finset.sum_add_distrib, sum_single_eq_one]
      obtain ⟨z₀, hz₀⟩ := countingOracle.support_simulate_nonempty (mx default)
      have hbig : (z₀.1, QueryCount.single t + z₀.2) ∈
          support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
        countingOracle.add_single_mem_support_simulate_queryBind hz₀
      have hbound : 1 + (∑ i, z₀.2 i) ≤ n := (hsplit z₀.2) ▸ h _ hbig
      have hpos : 0 < n := by omega
      refine ⟨hpos, fun u => ?_⟩
      apply ih u
      intro z hz
      have hbig' : (z.1, QueryCount.single t + z.2) ∈
          support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
        countingOracle.add_single_mem_support_simulate_queryBind hz
      have hb : 1 + (∑ i, z.2 i) ≤ n := (hsplit z.2) ▸ h _ hbig'
      omega

omit [Fintype ι] [DecidableEq ι] in
/-- If a stateful simulation has support cost at most one per query step, then any support
point of the simulated prefix leaves the continuation bounded by the residual budget measured
by that cost. The cost may under-approximate the true query count, so the resulting residual
budget is correspondingly weaker but still sound. -/
theorem IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
     [Finite ι]
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
  let : DecidableEq ι := Classical.decEq ι
  let : Fintype ι := Fintype.ofFinite ι
  rcases countingOracle.exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
      (spec := spec) (ι := ι) (impl := impl) cost hstep hz with
    ⟨qc, hqc, hcost⟩
  have hres : IsTotalQueryBound (ob z.1) (n - ∑ i, qc i) :=
    IsTotalQueryBound.residual_of_mem_support_counting
      (spec := spec) (ι := ι) (oa := oa) (ob := ob) (n := n) (z := (z.1, qc)) h hqc
  exact hres.mono (by omega)

end CountingResidual

/-- Per-index bound implies total bound (sum over indices). -/
theorem IsTotalQueryBound.of_perIndex [DecidableEq ι] [Fintype ι]
     {oa : OracleComp spec α}
    {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      refine ⟨Nat.lt_of_lt_of_le h.1
        (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)), fun u => ?_⟩
      rw [← sum_update_pred h.1]
      exact ih u (h.2 u)

/-! ### Conversions and soundness for `IsQueryBoundP` -/

section IsQueryBoundPRelations

variable {p : ι → Prop} [DecidablePred p]

/-- The `p`-filtered total of a single-query `QueryCount` is one when `t` satisfies `p`. Shared
by the counting-oracle characterizations that peel off one `QueryCount.single t` per step. -/
private lemma sum_single_filter_eq_one [DecidableEq ι] [Fintype ι] {t : ι} (hpt : p t) :
    ∑ i ∈ Finset.univ.filter p, QueryCount.single t i = 1 := by
  simp [QueryCount.single, hpt]

/-- The `p`-filtered total of a single-query `QueryCount` is zero when `t` fails `p`. -/
private lemma sum_single_filter_eq_zero [DecidableEq ι] [Fintype ι] {t : ι} (hpt : ¬ p t) :
    ∑ i ∈ Finset.univ.filter p, QueryCount.single t i = 0 :=
  Finset.sum_eq_zero fun j hj =>
    have hjt : j ≠ t := fun he => hpt (he ▸ (Finset.mem_filter.mp hj).2)
    by simp [QueryCount.single, hjt]

/-- A total query bound implies a predicate-targeted bound for every predicate `p`. -/
theorem IsTotalQueryBound.isQueryBoundP {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr h.1, fun u => ?_⟩
      split
      · exact ih u (h.2 u)
      · exact (ih u (h.2 u)).mono (Nat.sub_le _ _)

/-- With the always-true predicate, `IsQueryBoundP` reduces to `IsTotalQueryBound`. -/
lemma isQueryBoundP_true_iff (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => True) n ↔ IsTotalQueryBound oa n := by
  refine isQueryBound_congr (fun t b => ?_) (fun t b => ?_) <;> simp

/-- The always-false predicate places no constraint. -/
@[simp]
lemma isQueryBoundP_false (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => False) n := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun u => by simpa using ih u⟩

/-- A per-index bound implies a predicate-targeted bound at the sum of the per-index budgets
over the indices satisfying `p`. -/
theorem IsPerIndexQueryBound.isQueryBoundP [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsQueryBoundP oa p (∑ i ∈ Finset.univ.filter p, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun u => ?_⟩
      · by_cases hpt : p t
        · exact Or.inr (Nat.lt_of_lt_of_le h.1 (Finset.single_le_sum (f := qb)
            (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩)))
        · exact Or.inl hpt
      · split
        · next hpt =>
            rw [← sum_filter_update_of_pred_pos hpt h.1]
            exact ih u (h.2 u)
        · next hpt =>
            rw [← sum_filter_update_of_not_pred hpt]
            exact ih u (h.2 u)

/-- Soundness: any path of the counting-oracle simulation of a `p`-bounded computation has
sum of per-index counts over `p`-indices at most `n`. -/
theorem IsQueryBoundP.counting_bounded [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    (∑ i ∈ Finset.univ.filter p, z.2 i) ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst hz
      simp
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hne, u, hu⟩ := hz
      have hrec :
          (∑ i ∈ Finset.univ.filter p, (Function.update z.2 t (z.2 t - 1)) i) ≤
            (if p t then n - 1 else n) :=
        ih u (h.2 u) hu
      have hz_pos : 0 < z.2 t := Nat.pos_of_ne_zero hne
      by_cases hpt : p t
      · simp only [if_pos hpt] at hrec
        rw [sum_filter_update_of_pred_pos hpt hz_pos] at hrec
        have hp_pos : 0 < ∑ i ∈ Finset.univ.filter p, z.2 i :=
          Nat.lt_of_lt_of_le hz_pos
            (Finset.single_le_sum (f := z.2) (fun _ _ => Nat.zero_le _)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩))
        have hn_pos : 0 < n := h.1.resolve_left (fun hnp => hnp hpt)
        have hshift : (∑ i ∈ Finset.univ.filter p, z.2 i) - 1 + 1 ≤ (n - 1) + 1 :=
          Nat.add_le_add_right hrec 1
        rwa [Nat.sub_add_cancel hp_pos, Nat.sub_add_cancel hn_pos] at hshift
      · simp only [if_neg hpt] at hrec
        rwa [sum_filter_update_of_not_pred hpt] at hrec

/-- Residual bound via the counting oracle: after any partial counting-simulation of `oa`, the
continuation `ob` is `p`-bounded by `n` minus the filtered count so far. -/
theorem IsQueryBoundP.residual_of_mem_support_counting [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsQueryBoundP (oa >>= ob) p n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    IsQueryBoundP (ob z.1) p (n - ∑ i ∈ Finset.univ.filter p, z.2 i) := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simpa [monad_norm] using h
  | query_bind t mx ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hne, u, hu⟩ := hz
      have hz_pos : 0 < z.2 t := Nat.pos_of_ne_zero hne
      have hrec :
          IsQueryBoundP (ob z.1) p
              ((if p t then n - 1 else n) -
                ∑ i ∈ Finset.univ.filter p, (Function.update z.2 t (z.2 t - 1)) i) :=
        ih u (h.2 u) hu
      by_cases hpt : p t
      · simp only [if_pos hpt] at hrec
        rw [sum_filter_update_of_pred_pos hpt hz_pos] at hrec
        have hp_pos : 0 < ∑ i ∈ Finset.univ.filter p, z.2 i :=
          Nat.lt_of_lt_of_le hz_pos
            (Finset.single_le_sum (f := z.2) (fun _ _ => Nat.zero_le _)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩))
        refine hrec.mono ?_
        rw [Nat.sub_sub, Nat.add_sub_of_le hp_pos]
      · simp only [if_neg hpt] at hrec
        rwa [sum_filter_update_of_not_pred hpt] at hrec

/-- Predicate-targeted analogue of `isTotalQueryBound_iff_counting_total_le`: a
counting-oracle filtered-sum bound characterizes the structural `IsQueryBoundP` bound. -/
theorem isQueryBoundP_iff_counting_filter_le
    [DecidableEq ι] [Fintype ι] [IsUniformSpec spec]
    {oa : OracleComp spec α} {n : ℕ} :
    IsQueryBoundP oa p n ↔
      ∀ z ∈ support (countingOracle.simulate oa 0),
        (∑ i ∈ Finset.univ.filter p, z.2 i) ≤ n := by
  refine ⟨fun h _ hz => IsQueryBoundP.counting_bounded h hz, fun h => ?_⟩
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff]
      have hsplit : ∀ (q : QueryCount ι),
          (∑ i ∈ Finset.univ.filter p, (QueryCount.single t + q) i) =
          (∑ i ∈ Finset.univ.filter p, QueryCount.single t i) +
          (∑ i ∈ Finset.univ.filter p, q i) := by
        intro q
        simp [Pi.add_apply, Finset.sum_add_distrib]
      refine ⟨?_, fun u => ?_⟩
      · by_cases hpt : p t
        · refine Or.inr ?_
          obtain ⟨z₀, hz₀⟩ := countingOracle.support_simulate_nonempty (mx default)
          have hbig : (z₀.1, QueryCount.single t + z₀.2) ∈
              support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
            countingOracle.add_single_mem_support_simulate_queryBind hz₀
          have hbound := h _ hbig
          rw [hsplit, sum_single_filter_eq_one hpt] at hbound
          omega
        · exact Or.inl hpt
      · apply ih u
        intro z hz
        have hbig' : (z.1, QueryCount.single t + z.2) ∈
            support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
          countingOracle.add_single_mem_support_simulate_queryBind hz
        have hbound := h _ hbig'
        rw [hsplit] at hbound
        by_cases hpt : p t
        · simp only [if_pos hpt]
          rw [sum_single_filter_eq_one hpt] at hbound
          omega
        · simp only [if_neg hpt]
          rwa [sum_single_filter_eq_zero hpt, zero_add] at hbound

end IsQueryBoundPRelations

/-- Transfer a predicate-targeted query bound through `simulateQ` into a stateful target
semantics, provided each simulated source query step is itself `q`-bounded (by `1` on
`p`-indices, by `0` on `¬ p`-indices). -/
theorem IsQueryBoundP.simulateQ_run_of_step {ι' : Type u} {spec' : OracleSpec ι'}
     {σ : Type u}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → ∀ s, IsQueryBoundP ((impl t).run s) q 1)
    (hstep_np : ∀ t, ¬ p t → ∀ s, IsQueryBoundP ((impl t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hlift :
          IsQueryBoundP
            ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) q
            (if p t then 1 else 0) := by
        by_cases hpt : p t
        · simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift, if_pos hpt] using
            hstep_p t hpt s
        · simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift, if_neg hpt] using
            hstep_np t hpt s
      have hbound : (if p t then 1 else 0) + (if p t then n - 1 else n) = n := by grind
      simpa [hbound] using isQueryBoundP_bind hlift
        fun pu _ => ih pu.1 (h.2 pu.1) pu.2

/-- Stateless analogue of `IsQueryBoundP.simulateQ_run_of_step`: when the simulation target
monad is `OracleComp spec'` directly (no `StateT` layer), the per-step bounds apply without
an external state argument. Captures the `liftComp` shape, where each `p`-step becomes one
`q`-query and each `¬ p`-step is `q`-free. -/
theorem IsQueryBoundP.simulateQ_of_step {ι' : Type u} {spec' : OracleSpec ι'}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → IsQueryBoundP (impl t) q 1)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (impl t) q 0) :
    IsQueryBoundP (simulateQ impl oa) q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hlift : IsQueryBoundP (impl t) q (if p t then 1 else 0) := by
        by_cases hpt : p t
        · simpa [if_pos hpt] using hstep_p t hpt
        · simpa [if_neg hpt] using hstep_np t hpt
      have hbound : (if p t then 1 else 0) + (if p t then n - 1 else n) = n := by grind
      simpa [hbound] using isQueryBoundP_bind hlift fun u _ => ih u (h.2 u)

/-- Transfer a predicate-targeted bound through `simulateQ` with a sum-of-implementations
`impl₁ + impl₂` on a sum source spec `spec₁ + spec₂`. The source predicate `p` is split into
its `.inl` and `.inr` branches, with separate step hypotheses for each impl on its own
sub-predicate. -/
theorem IsQueryBoundP.simulateQ_run_add_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec']
      {σ : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p₁ : ∀ t, p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 1)
    (hstep_np₁ : ∀ t, ¬ p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_p₂ : ∀ t, p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 1)
    (hstep_np₂ : ∀ t, ¬ p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n := by
  refine IsQueryBoundP.simulateQ_run_of_step h ?_ ?_ s
  · rintro (t | t) hp s
    · exact hstep_p₁ t hp s
    · exact hstep_p₂ t hp s
  · rintro (t | t) hnp s
    · exact hstep_np₁ t hnp s
    · exact hstep_np₂ t hnp s

/-- Specialization of `IsQueryBoundP.simulateQ_run_add_of_step` when the source predicate
is vacuously false on `.inr _` queries: only `impl₁` interacts with the predicate, and
`impl₂` only needs a uniform 0-bound step. -/
theorem IsQueryBoundP.simulateQ_run_add_inl_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec']
      {σ : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (hp_inr : ∀ t, ¬ p (.inr t))
    (h : IsQueryBoundP oa p n)
    (hstep_p₁ : ∀ t, p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 1)
    (hstep_np₁ : ∀ t, ¬ p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_right : ∀ t s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n :=
  IsQueryBoundP.simulateQ_run_add_of_step h hstep_p₁ hstep_np₁
    (fun t hp _ => absurd hp (hp_inr t))
    (fun t _ s => hstep_right t s) s

/-- Specialization of `IsQueryBoundP.simulateQ_run_add_of_step` when the source predicate
is vacuously false on `.inl _` queries: only `impl₂` interacts with the predicate, and
`impl₁` only needs a uniform 0-bound step. -/
theorem IsQueryBoundP.simulateQ_run_add_inr_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec']
      {σ : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (hp_inl : ∀ t, ¬ p (.inl t))
    (h : IsQueryBoundP oa p n)
    (hstep_left : ∀ t s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_p₂ : ∀ t, p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 1)
    (hstep_np₂ : ∀ t, ¬ p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n :=
  IsQueryBoundP.simulateQ_run_add_of_step h
    (fun t hp _ => absurd hp (hp_inl t))
    (fun t _ s => hstep_left t s)
    hstep_p₂ hstep_np₂ s

/-! ### Total-bound sum-handler transfer

`IsTotalQueryBound` lifts across `simulateQ (impl₁ + impl₂) oa` whenever each underlying
handler makes at most one query per step. The signature mirrors
`IsQueryBoundP.simulateQ_run_add_of_step` without the predicate machinery: every step on
either side counts toward the same uniform budget. -/

theorem IsTotalQueryBound.simulateQ_run_add_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec']
      {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsTotalQueryBound ((impl₁ t).run s) 1)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsTotalQueryBound ((impl₂ t).run s) 1)
    (s : σ) :
    IsTotalQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) n := by
  refine IsTotalQueryBound.simulateQ_run_of_step h ?_ s
  rintro (t | t) s'
  · exact hstep₁ t s'
  · exact hstep₂ t s'

/-- Specialization of `IsTotalQueryBound.simulateQ_run_add_of_step` to a left-only
interaction: `impl₂` only needs a uniform 0-bound step. -/
theorem IsTotalQueryBound.simulateQ_run_add_inl_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec']
      {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsTotalQueryBound ((impl₁ t).run s) 1)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsTotalQueryBound ((impl₂ t).run s) 0)
    (s : σ) :
    IsTotalQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) n :=
  IsTotalQueryBound.simulateQ_run_add_of_step h hstep₁
    (fun t s' => (hstep₂ t s').mono (Nat.zero_le _)) s

/-- Specialization of `IsTotalQueryBound.simulateQ_run_add_of_step` to a right-only
interaction: `impl₁` only needs a uniform 0-bound step. -/
theorem IsTotalQueryBound.simulateQ_run_add_inr_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec']
      {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsTotalQueryBound ((impl₁ t).run s) 0)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsTotalQueryBound ((impl₂ t).run s) 1)
    (s : σ) :
    IsTotalQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) n :=
  IsTotalQueryBound.simulateQ_run_add_of_step h
    (fun t s' => (hstep₁ t s').mono (Nat.zero_le _))
    hstep₂ s

/-! ### Per-index sum-handler transfer

The per-index analogue of `IsTotalQueryBound.simulateQ_run_add_of_step`: each side's step
is required to make at most one query of its corresponding sum-tagged index in the result
spec, mirroring the single-spec `simulateQ_run_of_uniform_step`. -/

theorem IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step
    {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {oa : OracleComp (spec₁ + spec₂) α} {qb : ι₁ ⊕ ι₂ → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ,
      IsPerIndexQueryBound ((impl₁ t).run s) (Function.update 0 (Sum.inl t) 1))
    (hstep₂ : ∀ t : ι₂, ∀ s : σ,
      IsPerIndexQueryBound ((impl₂ t).run s) (Function.update 0 (Sum.inr t) 1))
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) qb := by
  refine IsPerIndexQueryBound.simulateQ_run_of_uniform_step h ?_ s
  rintro (t | t) s'
  · exact hstep₁ t s'
  · exact hstep₂ t s'

/-- Specialization of `IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step` to a left-only
interaction: `impl₂` only needs a uniform 0-step. -/
theorem IsPerIndexQueryBound.simulateQ_run_add_inl_of_uniform_step
    {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {oa : OracleComp (spec₁ + spec₂) α} {qb : ι₁ ⊕ ι₂ → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ,
      IsPerIndexQueryBound ((impl₁ t).run s) (Function.update 0 (Sum.inl t) 1))
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsPerIndexQueryBound ((impl₂ t).run s) 0)
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) qb :=
  IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step h hstep₁
    (fun t s' => (hstep₂ t s').mono (fun _ => Nat.zero_le _)) s

/-- Specialization of `IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step` to a right-only
interaction: `impl₁` only needs a uniform 0-step. -/
theorem IsPerIndexQueryBound.simulateQ_run_add_inr_of_uniform_step
    {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {oa : OracleComp (spec₁ + spec₂) α} {qb : ι₁ ⊕ ι₂ → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsPerIndexQueryBound ((impl₁ t).run s) 0)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ,
      IsPerIndexQueryBound ((impl₂ t).run s) (Function.update 0 (Sum.inr t) 1))
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) qb :=
  IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step h
    (fun t s' => (hstep₁ t s').mono (fun _ => Nat.zero_le _))
    hstep₂ s

/-! ## Biconditional transfer under query-count-preserving simulators

`loggingOracle`, `countingOracle`, and the `withTrace*` / `withCost` / `withCounting`
combinators interpret each source query as exactly one underlying query, threading writer
bookkeeping that the underlying simulation does not see. Bounds transfer *biconditionally*
via the `fst_map_run_*` projection identities and `isXQueryBound_iff_of_map_eq`.

Cache-hit / seed-hit handlers (`cachingOracle`, `randomOracle`, `seededOracle`) discard
queries and so admit only the forward direction — use `simulateQ_run_of_step` for those. -/

theorem isTotalQueryBound_run_simulateQ_countingOracle_iff
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ countingOracle oa).run) n ↔
    IsTotalQueryBound oa n :=
  isQueryBound_iff_of_map_eq (countingOracle.fst_map_run_simulateQ oa) _ _

theorem isQueryBoundP_run_simulateQ_countingOracle_iff
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
     {α : Type}
    (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) :
    IsQueryBoundP ((simulateQ countingOracle oa).run) p n ↔
    IsQueryBoundP oa p n :=
  isQueryBoundP_iff_of_map_eq (p := p) (countingOracle.fst_map_run_simulateQ oa)

theorem isTotalQueryBound_run_simulateQ_withTraceBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTraceBefore traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceBefore so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTraceBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTraceBefore traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTraceBefore so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withTraceAppend_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTraceAppend traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceAppend so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTraceAppend_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTraceAppend traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTraceAppend so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withTrace_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTrace traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTrace so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTrace_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTrace traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTrace so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withTraceAppendBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTraceAppendBefore traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceAppendBefore so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTraceAppendBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTraceAppendBefore traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTraceAppendBefore so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withCost_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withCost costFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCost so costFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withCost_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withCost costFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withCost so costFn mx)

theorem isTotalQueryBound_run_simulateQ_withCounting_iff
    {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withCounting) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCounting so mx) _ _

theorem isQueryBoundP_run_simulateQ_withCounting_iff
    {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withCounting) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withCounting so mx)

/-! ### Per-index analogues -/

theorem isPerIndexQueryBound_run_simulateQ_countingOracle_iff
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
     {α : Type}
    (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsPerIndexQueryBound ((simulateQ countingOracle oa).run) qb ↔
    IsPerIndexQueryBound oa qb :=
  isPerIndexQueryBound_iff_of_map_eq (countingOracle.fst_map_run_simulateQ oa)

theorem isPerIndexQueryBound_run_simulateQ_withTraceBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTraceBefore traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceBefore so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withTrace_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTrace traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTrace so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withTraceAppendBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTraceAppendBefore traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceAppendBefore so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withTraceAppend_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTraceAppend traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceAppend so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withCost_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withCost costFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCost so costFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withCounting_iff
    {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withCounting) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCounting so mx)

/-- Worst-case per-index query bound as a function of input size:
for all inputs `x` with `size x ≤ n`, the computation `f x` makes at most `bound n i`
queries to oracle `i`. -/
@[expose]
def QueryUpperBound [DecidableEq ι] (f : α → OracleComp spec β) (size : α → ℕ)
    (bound : ℕ → ι → ℕ) : Prop :=
  ∀ n x, size x ≤ n → IsPerIndexQueryBound (f x) (bound n)

/-- Total query upper bound: there exists a constant `k` such that for all inputs `x`
with `size x ≤ n`, the computation `f x` makes at most `k * bound n` total queries.
Uses the structural `IsQueryBound` to avoid dependence on oracle responses. -/
@[expose]
def TotalQueryUpperBound (f : α → OracleComp spec β) (size : α → ℕ) (bound : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n x, size x ≤ n → IsQueryBound (f x) (k * bound n)
    (fun _ b => 0 < b) (fun _ b => b - 1)

/-- `PolyQueryUpperBound` says the per-index query count is polynomially bounded
in the input size. This is a non-parameterized version of `PolyQueries`. -/
@[expose]
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
such that the number of queries to that oracle is bounded by the corresponding polynomial.

Currently used only in `CostModel.lean`; retained as scaffolding for future asymptotic analyses. -/
structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
    {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  /-- `qb i` is a polynomial bound on the queries made to oracle `i`. -/
  qb : ι → Polynomial ℕ
  /-- The bound is actually a bound on the number of queries made. -/
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsPerIndexQueryBound (oa n x) (fun i => (qb i).eval n)

end OracleComp
