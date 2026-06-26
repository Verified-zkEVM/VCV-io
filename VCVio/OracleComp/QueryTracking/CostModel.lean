/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.QueryCost
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Cost Models for Oracle Computations

This file defines a general cost model for oracle computations, parametric over any
`AddCommMonoid` cost type. This supports natural numbers, extended non-negative reals,
per-oracle cost vectors, and custom multi-dimensional cost structures.

Uses `AddWriterT` (defined in `ToMathlib.Control.WriterT`) for additive cost accumulation.

## Main Definitions

- `instrumentedRun oa cm`: `oa` interpreted in the canonical free runtime with additive cost
  tracking.
- `addCostOracle costFn`: the corresponding one-query instrumented oracle implementation.
- `CostModel spec ω`: Assigns cost `queryCost t : ω` to each oracle query `t`.
- `costDist oa cm`: Joint distribution of `(output, totalCost)`.
- `expectedCost oa cm val`: Expected total cost `E[val(cost)]`, computed via `wp`.
- `WorstCaseCostBound`, `ExpectedCostBound`: Cost bound predicates.
- `WorstCasePolyTime`, `ExpectedPolyTime`: Asymptotic polynomial-time predicates for computation
  families indexed by a security parameter.

## Key Results

- `fst_map_costDist`: Cost instrumentation doesn't change the output distribution.
- `expectedCost_pure`: Expected cost of a pure computation is `0`.
- `probEvent_cost_gt_le_expectedCost_div`: Markov's inequality for cost distributions.
- `WorstCasePolyTime.toExpectedPolyTime`: Strict polynomial time implies expected polynomial time.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal
open scoped BigOperators

/-! ## Cost Model, Cost Oracle, Cost Distribution

All definitions below operate at `Type` (= `Type 0`), matching `wp`, `support`, and `Pr[ ...]`
which are defined for `{α : Type}` in the program logic.
-/

variable {ι : Type} {spec : OracleSpec ι} {α : Type} {ω : Type}

/-- Oracle that tracks additive cost. Wraps `costOracle` with `Multiplicative`
to get additive accumulation through the existing `WriterT` infrastructure. -/
def addCostOracle [AddCommMonoid ω] (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withAddCost costFn

@[simp]
lemma fst_map_run_simulateQ_addCostOracle [AddCommMonoid ω] (costFn : spec.Domain → ω)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (addCostOracle costFn) oa).run = oa := by
  simp [addCostOracle, QueryImpl.withAddCost, QueryImpl.fst_map_run_withCost]

/-- A cost model assigns a cost in `ω` to each oracle query.
The cost type `ω` can be `ℕ`, `ℝ≥0∞`, `ι → ℕ` (per-oracle), or any `AddCommMonoid`. -/
structure CostModel (spec : OracleSpec ι) (ω : Type) [AddCommMonoid ω] where
  queryCost : spec.Domain → ω

namespace CostModel

/-- The zero cost model: every query is free. -/
def zero [AddCommMonoid ω] : CostModel spec ω where
  queryCost _ := 0

end CostModel

/-- Run `oa` in the canonical free `OracleComp` runtime instrumented by `cm`'s additive
query-cost function. This is the semantic core of `CostModel`. -/
abbrev instrumentedRun [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) :
    AddWriterT ω (OracleComp spec) α :=
  simulateQ ((QueryImpl.ofLift spec (OracleComp spec)).withAddCost cm.queryCost) oa

/-- The joint distribution of `(output, totalCost)` obtained by running `oa` with
additive cost tracking. Cost accumulates via `+` through `AddWriterT`.

Since `Multiplicative ω` and `ω` are definitionally equal, the second component
of the product can be used directly as `ω`. -/
def costDist [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) :=
  (instrumentedRun oa cm).run

/-- Cost instrumentation does not change the output distribution. -/
@[simp]
theorem fst_map_costDist [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) :
    Prod.fst <$> costDist oa cm = oa :=
  fst_map_run_simulateQ_addCostOracle cm.queryCost oa

namespace AddWriterT

variable [IsUniformSpec spec]

/-- For `OracleComp`, `AddWriterT.expectedCost` is the weakest-precondition expectation of the
run semantics projected to the additive cost component. -/
lemma expectedCost_eq_wp_run
    [AddMonoid ω]
    (oa : AddWriterT ω (OracleComp spec) α) (val : ω → ENNReal) :
    AddWriterT.expectedCost oa val =
      wp oa.run (fun z => val (Multiplicative.toAdd z.2)) := by
  simp only [AddWriterT.expectedCost, ← wp_eq_tsum, AddWriterT.costs_def, wp_map,
    Function.comp_def]

end AddWriterT

/-! ## Expected Cost -/

section ExpectedCost

variable [AddCommMonoid ω]
variable [IsUniformSpec spec]

/-- The expected total cost of `oa` under cost model `cm`, valued by `val : ω → ℝ≥0∞`.
Computed as `E[val(cost)] = ∑ (x, c), Pr[= (x, c) | costDist] * val(c)`.

The valuation `val` maps the abstract cost type to `ℝ≥0∞` for expectation computation.
For `ω = ℕ`, use `(↑·)`. For `ω = ℝ≥0∞`, use `id`. For multi-dimensional cost,
choose which dimension to analyze. -/
noncomputable def expectedCost (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) : ℝ≥0∞ :=
  AddWriterT.expectedCost (instrumentedRun oa cm) val

/-- Convenience: expected cost for `ℕ`-valued cost models. -/
noncomputable abbrev expectedCostNat (oa : OracleComp spec α)
    (cm : CostModel spec ℕ) : ℝ≥0∞ :=
  expectedCost oa cm (fun n => ↑n)

/-- The `CostModel.expectedCost` facade agrees definitionally with the weakest-precondition
expectation of the instrumented `costDist`. -/
theorem expectedCost_eq_wp_costDist (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) :
    expectedCost oa cm val =
      wp (costDist oa cm) (fun z => val z.2) :=
  AddWriterT.expectedCost_eq_wp_run _ val

@[simp]
theorem expectedCost_pure (x : α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (hval : val 0 = 0) :
    expectedCost (spec := spec) (pure x) cm val = 0 := by
  simpa [expectedCost_eq_wp_costDist, costDist, instrumentedRun] using hval

/-- If `val z.2 ≤ c` for all `z` in the support of `costDist`, then `expectedCost ≤ c`.
This is the key bridge from worst-case (support) bounds to expected bounds. -/
theorem expectedCost_le_of_support_bound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ z ∈ support (costDist oa cm), val z.2 ≤ c) :
    expectedCost oa cm val ≤ c := by
  rw [expectedCost_eq_wp_costDist, ← wp_const (costDist oa cm) c, wp_eq_tsum, wp_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support (costDist oa cm)
  · gcongr
    exact h z hz
  · simp [probOutput_eq_zero_of_not_mem_support hz]

end ExpectedCost

/-! ## Worst-Case Cost Bounds -/

/-- Every execution path of `oa` under `cm` has total cost at most `bound`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def WorstCaseCostBound [AddCommMonoid ω] [Preorder ω] [IsUniformSpec spec]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) : Prop :=
  AddWriterT.PathwiseCostAtMost (instrumentedRun oa cm) bound

/-- `WorstCaseCostBound` is equivalently a support bound over the old `costDist` view. -/
theorem worstCaseCostBound_iff_support_bound [AddCommMonoid ω] [Preorder ω]
    [IsUniformSpec spec]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) :
    WorstCaseCostBound oa cm bound ↔
      ∀ z ∈ support (costDist oa cm), z.2 ≤ bound := by
  unfold WorstCaseCostBound costDist instrumentedRun AddWriterT.PathwiseCostAtMost
  rfl

/-! ## Cost Bounds -/

section CostBounds

variable [AddCommMonoid ω]
variable [IsUniformSpec spec]

/-- The expected cost of `oa` under `cm` (valued by `val`) is at most `bound`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def ExpectedCostBound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (bound : ℝ≥0∞) : Prop :=
  expectedCost oa cm val ≤ bound

/-- A strict cost bound implies an expected cost bound, provided the valuation `val`
is monotone with respect to `≤` on `ω`. -/
theorem WorstCaseCostBound.toExpectedCostBound [Preorder ω]
    {oa : OracleComp spec α} {cm : CostModel spec ω} {bound : ω}
    (hstrict : WorstCaseCostBound oa cm bound)
    {val : ω → ℝ≥0∞} (hval_mono : Monotone val) :
    ExpectedCostBound oa cm val (val bound) :=
  AddWriterT.expectedCost_le_of_pathwiseCostAtMost hstrict hval_mono

/-- **Markov's inequality for cost distributions** (multiplication form).
The probability that the valued cost exceeds `t`, times `t`, is at most `expectedCost`. -/
theorem probEvent_cost_gt_mul_le_expectedCost
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞) (t : ℝ≥0∞) :
    Pr[ fun z => t < val z.2 | costDist oa cm] * t ≤ expectedCost oa cm val := by
  rw [expectedCost_eq_wp_costDist, probEvent_eq_wp_indicator, ← wp_const_mul]
  exact wp_mono _ fun z => by split_ifs with h <;> simp [h, le_of_lt]

/-- **Markov's inequality for cost distributions** (division form). -/
theorem probEvent_cost_gt_le_expectedCost_div
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : 0 < t) (ht' : t ≠ ⊤) :
    Pr[ fun z => t < val z.2 | costDist oa cm] ≤ expectedCost oa cm val / t :=
  (ENNReal.le_div_iff_mul_le (.inl ht.ne') (.inl ht')).mpr
    (probEvent_cost_gt_mul_le_expectedCost oa cm val t)

end CostBounds

/-! ## Standard Cost Models -/

namespace CostModel

/-- Unit cost model: every oracle query costs 1.
Total cost under this model equals total query count. -/
def unit : CostModel spec ℕ where
  queryCost _ := 1

end CostModel

@[simp]
private lemma addCostOracle_unit_run_apply (t : spec.Domain) :
    (addCostOracle CostModel.unit.queryCost t).run =
      (fun u => (u, Multiplicative.ofAdd 1)) <$>
        (spec.query t : OracleComp spec (spec.Range t)) := by
  simp [CostModel.unit, addCostOracle, QueryImpl.withAddCost]

section UnitCostBridge

private lemma exists_mem_support [IsUniformSpec spec] (oa : OracleComp spec α) :
    ∃ x, x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨x, by simp⟩
  | query_bind t mx ih =>
      obtain ⟨x, hx⟩ := ih default
      exact ⟨x, (mem_support_bind_iff _ _ _).2 ⟨default, mem_support_query t default, hx⟩⟩

private lemma exists_mem_support_costDist_of_mem_support
    [AddCommMonoid ω] [IsUniformSpec spec]
    (oa : OracleComp spec α) (cm : CostModel spec ω) {x : α}
    (hx : x ∈ support oa) :
    ∃ c, (x, c) ∈ support (costDist oa cm) := by
  have hx' : x ∈ support (Prod.fst <$> costDist oa cm) := by
    simpa [fst_map_costDist] using hx
  rw [support_map] at hx'
  obtain ⟨⟨x', c⟩, hz, rfl⟩ := hx'
  exact ⟨c, hz⟩

private lemma mem_support_costDist_unit_query_bind_of_mem_support
    [IsUniformSpec spec]
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (u : spec.Range t)
    {z : α × Multiplicative ℕ} (hz : z ∈ support (costDist (mx u) CostModel.unit)) :
    (z.1, Multiplicative.ofAdd (Multiplicative.toAdd z.2 + 1)) ∈ support
      (costDist ((spec.query t : OracleComp spec (spec.Range t)) >>= mx) CostModel.unit) := by
  rw [costDist, instrumentedRun, simulateQ_bind, simulateQ_query, WriterT.run_bind]
  refine (mem_support_bind_iff _ _ _).2
    ⟨(u, (Multiplicative.ofAdd 1 : Multiplicative ℕ)), ?_, ?_⟩
  · simp [CostModel.unit]
  · rw [support_map]
    exact ⟨z, hz, by simp [Nat.add_comm]⟩

private theorem isPerIndexQueryBound_of_unit_support_bound
    [DecidableEq ι] [IsUniformSpec spec]
    {oa : OracleComp spec α} {bound : ℕ}
    (hSupport : ∀ z ∈ support (costDist oa CostModel.unit), z.2 ≤ bound) :
    IsPerIndexQueryBound oa (fun _ => bound) := by
  induction oa using OracleComp.inductionOn generalizing bound with
  | pure x =>
      exact isPerIndexQueryBound_pure x _
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff]
      refine ⟨?_, fun u => ?_⟩
      · rcases exists_mem_support (mx default) with ⟨x, hx⟩
        rcases exists_mem_support_costDist_of_mem_support (mx default) CostModel.unit hx with
          ⟨c, hc⟩
        have hle : Multiplicative.toAdd c + 1 ≤ bound := by
          simpa using
            hSupport _ (mem_support_costDist_unit_query_bind_of_mem_support t mx default hc)
        omega
      · have hcontSupport :
            ∀ z ∈ support (costDist (mx u) CostModel.unit), z.2 ≤ bound - 1 := by
          intro z hz
          have hle : Multiplicative.toAdd z.2 + 1 ≤ bound := by
            simpa using hSupport _ (mem_support_costDist_unit_query_bind_of_mem_support t mx u hz)
          change Multiplicative.toAdd z.2 ≤ bound - 1
          omega
        refine (ih u hcontSupport).mono fun i => ?_
        simp only [Function.update_apply]
        split <;> omega

/-- A strict bound under the unit cost model yields a uniform per-index query bound:
if every execution uses at most `bound` total unit-cost steps, then each oracle index
is queried at most `bound` times. -/
theorem WorstCaseCostBound.toIsPerIndexQueryBound_unit
    [DecidableEq ι] [IsUniformSpec spec]
    {oa : OracleComp spec α} {bound : ℕ}
    (h : WorstCaseCostBound oa CostModel.unit bound) :
    IsPerIndexQueryBound oa (fun _ => bound) :=
  isPerIndexQueryBound_of_unit_support_bound fun z hz => by
    simpa [WorstCaseCostBound, costDist, instrumentedRun] using h z hz

private lemma sum_update_pred_eq
    [DecidableEq ι] [Fintype ι]
    (qb : ι → ℕ) (t : ι) (ht : 0 < qb t) :
    (∑ j, Function.update qb t (qb t - 1) j) + 1 = ∑ j, qb j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ t), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ qb (Finset.mem_univ t)]
  omega

/-- If `main` makes at most `qb i` queries to each oracle `i`, then its total query count
(under the unit cost model) is at most `∑ i, qb i` on every execution path. -/
theorem IsPerIndexQueryBound.toWorstCaseCostBound_unit_sum
    [DecidableEq ι] [Fintype ι] [IsUniformSpec spec]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    WorstCaseCostBound oa CostModel.unit (∑ i, qb i) := by
  have haux :
      ∀ {oa : OracleComp spec α} {qb : ι → ℕ},
        IsPerIndexQueryBound oa qb →
          AddWriterT.QueryBoundedAboveBy (instrumentedRun oa CostModel.unit) (∑ i, qb i) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure x =>
        intro qb _
        exact AddWriterT.queryBoundedAboveBy_mono
          (by simpa [instrumentedRun] using
            (AddWriterT.queryBoundedAboveBy_pure (m := OracleComp spec) x))
          (Nat.zero_le _)
    | query_bind t mx ih =>
        intro qb hqb
        rw [isPerIndexQueryBound_query_bind_iff] at hqb
        refine AddWriterT.queryBoundedAboveBy_mono
          (oa := instrumentedRun (liftM (query t) >>= mx) CostModel.unit)
          (n₁ := 1 + ∑ i, Function.update qb t (qb t - 1) i) (n₂ := ∑ i, qb i) ?_ ?_
        · have hbind := AddWriterT.queryBoundedAboveBy_bind (n₁ := 1)
            (oa := instrumentedRun (spec.query t : OracleComp spec (spec.Range t)) CostModel.unit)
            (f := fun u => instrumentedRun (mx u) CostModel.unit)
            (n₂ := ∑ i, Function.update qb t (qb t - 1) i)
            (HasQuery.queryBoundedAboveBy_withUnitCost_query
              (QueryImpl.ofLift spec (OracleComp spec)) t) (fun u => ih u (hqb.2 u))
          simpa [instrumentedRun, simulateQ_bind] using hbind
        · have := sum_update_pred_eq qb t hqb.1
          omega
  exact haux h

/-- Corollary: the expected total query count is also at most `∑ i, qb i`. Follows from the
worst-case bound `toWorstCaseCostBound_unit_sum`. -/
theorem IsPerIndexQueryBound.toExpectedCostBound_unit_sum
    [DecidableEq ι] [Fintype ι] [IsUniformSpec spec]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    ExpectedCostBound oa CostModel.unit (fun n => (n : ENNReal)) (∑ i, qb i) := by
  simpa using (toWorstCaseCostBound_unit_sum h).toExpectedCostBound Nat.mono_cast

end UnitCostBridge

namespace OracleComp

/-- Run a `ProbComp` with unit-cost instrumentation: each call to the uniform-selection oracle
is counted as cost 1. -/
abbrev probCompUnitQueryRun {β : Type} (oa : ProbComp β) :
    AddWriterT ℕ ProbComp β :=
  simulateQ ((QueryImpl.ofLift unifSpec ProbComp).withUnitCost) oa

end OracleComp

