/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import VCVio.OracleComp.QueryTracking.QueryRuntime
import VCVio.OracleComp.QueryTracking.QueryBound
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

/-! ## Cost Model, Cost Oracle, Cost Distribution

All definitions below operate at `Type` (= `Type 0`), matching `wp`, `support`, and `Pr[ ...]`
which are defined for `{α : Type}` in the program logic.
-/

variable {ι : Type} {spec : OracleSpec ι} {α : Type} {ω : Type}

/-- Oracle that tracks additive cost. Wraps `costOracle` with `Multiplicative`
to get additive accumulation through the existing `WriterT` infrastructure. -/
def addCostOracle [AddCommMonoid ω] (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω (OracleComp spec)) :=
  ((QueryRuntime.oracleCompRuntime (spec := spec)).withAddCost costFn).impl

@[simp]
lemma fst_map_run_simulateQ_addCostOracle [AddCommMonoid ω] (costFn : spec.Domain → ω)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (addCostOracle costFn) oa).run = oa := by
  simp [addCostOracle, QueryRuntime.withAddCost, QueryImpl.fst_map_run_withCost,
    QueryRuntime.oracleCompRuntime_impl_eq_ofLift]

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
  simulateQ ((QueryRuntime.oracleCompRuntime (spec := spec)).withAddCost cm.queryCost).impl oa

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

variable [spec.Fintype] [spec.Inhabited]

/-- For `OracleComp`, `AddWriterT.expectedCost` is the weakest-precondition expectation of the
run semantics projected to the additive cost component. -/
lemma expectedCost_eq_wp_run
    [AddMonoid ω]
    (oa : AddWriterT ω (OracleComp spec) α) (val : ω → ENNReal) :
    AddWriterT.expectedCost oa val =
      wp oa.run (fun z => val (Multiplicative.toAdd z.2)) := by
  unfold AddWriterT.expectedCost
  rw [← wp_eq_tsum, AddWriterT.costs_def, wp_map]
  rfl

end AddWriterT

/-! ## Expected Cost -/

section ExpectedCost

variable [AddCommMonoid ω]
variable [spec.Fintype] [spec.Inhabited]

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
    expectedCost oa cm val = wp (costDist oa cm) (fun z => val z.2) := by
  unfold expectedCost costDist instrumentedRun
  simpa using
    (AddWriterT.expectedCost_eq_wp_run
      (spec := spec)
      (oa := simulateQ
        ((QueryRuntime.oracleCompRuntime (spec := spec)).withAddCost cm.queryCost).impl oa)
      (val := val))

@[simp]
theorem expectedCost_pure (x : α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (hval : val 0 = 0) :
    expectedCost (spec := spec) (pure x) cm val = 0 := by
  rw [expectedCost_eq_wp_costDist]
  simp [costDist, instrumentedRun]
  simpa using hval

/-- If `val z.2 ≤ c` for all `z` in the support of `costDist`, then `expectedCost ≤ c`.
This is the key bridge from worst-case (support) bounds to expected bounds. -/
theorem expectedCost_le_of_support_bound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ z ∈ support (costDist oa cm), val z.2 ≤ c) :
    expectedCost oa cm val ≤ c := by
  rw [expectedCost_eq_wp_costDist, wp_eq_tsum]
  calc ∑' z, Pr[= z | costDist oa cm] * val z.2
      ≤ ∑' z, Pr[= z | costDist oa cm] * c := by
        apply ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support (costDist oa cm)
        · exact mul_le_mul_of_nonneg_left (h z hz) (zero_le _)
        · simp [probOutput_eq_zero_of_not_mem_support hz]
    _ = c := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

end ExpectedCost

/-! ## Worst-Case Cost Bounds -/

/-- Every execution path of `oa` under `cm` has total cost at most `bound`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def WorstCaseCostBound [AddCommMonoid ω] [Preorder ω]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) : Prop :=
  AddWriterT.PathwiseCostAtMost (instrumentedRun oa cm) bound

/-- `WorstCaseCostBound` is equivalently a support bound over the old `costDist` view. -/
theorem worstCaseCostBound_iff_support_bound [AddCommMonoid ω] [Preorder ω]
    (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) :
    WorstCaseCostBound oa cm bound ↔
      ∀ z ∈ support (costDist oa cm), z.2 ≤ bound := by
  unfold WorstCaseCostBound costDist instrumentedRun AddWriterT.PathwiseCostAtMost
  constructor <;> intro h z hz <;> simpa using h z hz

/-! ## Cost Bounds -/

section CostBounds

variable [AddCommMonoid ω]
variable [spec.Fintype] [spec.Inhabited]

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
    ExpectedCostBound oa cm val (val bound) := by
  simpa [ExpectedCostBound, expectedCost] using
    (AddWriterT.expectedCost_le_of_pathwiseCostAtMost
      (oa := instrumentedRun oa cm) (w := bound) (val := val) hstrict hval_mono)

/-- **Markov's inequality for cost distributions** (multiplication form).
The probability that the valued cost exceeds `t`, times `t`, is at most `expectedCost`. -/
theorem probEvent_cost_gt_mul_le_expectedCost
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞) (t : ℝ≥0∞) :
    Pr[ fun z => t < val z.2 | costDist oa cm] * t ≤ expectedCost oa cm val := by
  rw [expectedCost_eq_wp_costDist]
  rw [probEvent_eq_wp_indicator]
  change wp (costDist oa cm) (fun z => if t < val z.2 then 1 else 0) * t ≤
    wp (costDist oa cm) (fun z => val z.2)
  calc wp (costDist oa cm) (fun z => if t < val z.2 then 1 else 0) * t
      = wp (costDist oa cm) (fun z => t * (if t < val z.2 then 1 else 0)) := by
        rw [wp_mul_const]; ring
    _ ≤ wp (costDist oa cm) (fun z => val z.2) := by
        apply wp_mono
        intro z
        split_ifs with h
        · simpa using le_of_lt h
        · simp

/-- **Markov's inequality for cost distributions** (division form). -/
theorem probEvent_cost_gt_le_expectedCost_div
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : 0 < t) (ht' : t ≠ ⊤) :
    Pr[ fun z => t < val z.2 | costDist oa cm] ≤ expectedCost oa cm val / t :=
  (ENNReal.le_div_iff_mul_le (.inl (ne_of_gt ht)) (.inl ht')).mpr
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
        (liftM (query t) : OracleComp spec (spec.Range t)) := by
  simp [CostModel.unit, addCostOracle, QueryRuntime.withAddCost,
    QueryRuntime.oracleCompRuntime_impl_eq_ofLift, QueryImpl.withCost]

section UnitCostBridge

private lemma exists_mem_support [spec.Inhabited] (oa : OracleComp spec α) :
    ∃ x, x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      exact ⟨x, by simp⟩
  | query_bind t mx ih =>
      let u : spec.Range t := default
      rcases ih u with ⟨x, hx⟩
      refine ⟨x, (mem_support_bind_iff _ _ _).2 ?_⟩
      exact ⟨u, mem_support_query t u, hx⟩

private lemma exists_mem_support_costDist_of_mem_support
    [AddCommMonoid ω] (oa : OracleComp spec α) (cm : CostModel spec ω) {x : α}
    (hx : x ∈ support oa) :
    ∃ c, (x, c) ∈ support (costDist oa cm) := by
  have hx' : x ∈ support (Prod.fst <$> costDist oa cm) := by
    simpa [fst_map_costDist] using hx
  rw [support_map] at hx'
  rcases hx' with ⟨⟨x', c⟩, hz, hfst⟩
  simp only at hfst
  subst x'
  exact ⟨c, hz⟩

private lemma mem_support_costDist_unit_query_bind_of_mem_support
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (u : spec.Range t)
    {z : α × Multiplicative ℕ} (hz : z ∈ support (costDist (mx u) CostModel.unit)) :
    (z.1, Multiplicative.ofAdd (Multiplicative.toAdd z.2 + 1)) ∈ support
      (costDist ((liftM (query t) : OracleComp spec (spec.Range t)) >>= mx) CostModel.unit) := by
  rw [costDist, instrumentedRun, simulateQ_bind, simulateQ_query, WriterT.run_bind]
  refine (mem_support_bind_iff _ _ _).2 ?_
  refine ⟨(u, (Multiplicative.ofAdd 1 : Multiplicative ℕ)), ?_, ?_⟩
  · have hq : (u, Multiplicative.ofAdd 1) ∈
      support ((addCostOracle CostModel.unit.queryCost t).run) := by
      rw [addCostOracle_unit_run_apply, support_map]
      exact ⟨u, mem_support_query t u, by simp⟩
    simp [OracleQuery.cont_query, CostModel.unit]
  · rw [support_map]
    exact ⟨z, hz, by ext <;> simp [Prod.map, Nat.add_comm]⟩

private theorem isPerIndexQueryBound_of_unit_support_bound
    [DecidableEq ι] [spec.Inhabited]
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
        have hparent :=
          mem_support_costDist_unit_query_bind_of_mem_support t mx default hc
        have hle : Multiplicative.toAdd c + 1 ≤ bound := by
          simpa using (hSupport _ hparent)
        omega
      · have hcontSupport : ∀ z ∈ support (costDist (mx u) CostModel.unit), z.2 ≤ bound - 1 := by
          intro z hz
          have hparent :=
            mem_support_costDist_unit_query_bind_of_mem_support t mx u hz
          have hle : Multiplicative.toAdd z.2 + 1 ≤ bound := by
            simpa using (hSupport _ hparent)
          change Multiplicative.toAdd z.2 ≤ bound - 1
          omega
        have hu : IsPerIndexQueryBound (mx u) (fun _ => bound - 1) := ih u hcontSupport
        refine hu.mono ?_
        intro i
        by_cases hi : i = t
        · subst hi
          simp
        · simp [Function.update, hi]

/-- A strict bound under the unit cost model yields a uniform per-index query bound:
if every execution uses at most `bound` total unit-cost steps, then each oracle index
is queried at most `bound` times. -/
theorem WorstCaseCostBound.toIsPerIndexQueryBound_unit
    [DecidableEq ι] [spec.Inhabited]
    {oa : OracleComp spec α} {bound : ℕ}
    (h : WorstCaseCostBound oa CostModel.unit bound) :
    IsPerIndexQueryBound oa (fun _ => bound) := by
  refine isPerIndexQueryBound_of_unit_support_bound ?_
  intro z hz
  simpa [WorstCaseCostBound, costDist, instrumentedRun] using h z hz

end UnitCostBridge

/-! ## Polynomial-Time Predicates

Asymptotic polynomial-time predicates for families of computations indexed by a
security parameter `n : ℕ`. These connect the cost model to asymptotic complexity. -/

section PolyTime

variable [AddCommMonoid ω]
variable [spec.Fintype] [spec.Inhabited]

/-- All execution paths of `family n` have valued cost at most `p(n)` for some polynomial `p`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def WorstCasePolyTime (family : ℕ → OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n z, z ∈ support (costDist (family n) cm) → val z.2 ≤ p.eval n

/-- Expected valued cost of `family n` is at most `p(n)` for some polynomial `p`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def ExpectedPolyTime (family : ℕ → OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, expectedCost (family n) cm val ≤ ↑(p.eval n)

/-- Strict polynomial time implies expected polynomial time.
If every execution path's cost is bounded by `p(n)`, then the expected cost is also
bounded by `p(n)` (since the expectation of a bounded random variable is at most the bound). -/
theorem WorstCasePolyTime.toExpectedPolyTime (family : ℕ → OracleComp spec α)
    (cm : CostModel spec ω) (val : ω → ℕ)
    (h : WorstCasePolyTime family cm val) :
    ExpectedPolyTime family cm (fun w => ↑(val w)) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun n => expectedCost_le_of_support_bound _ _ _ _ fun z hz =>
    Nat.cast_le.mpr (hp n z hz)⟩

/-- Strict polynomial time under the unit cost model yields polynomial query bounds.
The resulting per-index bound uses the same polynomial for every oracle index, since
each individual query count is bounded by the total unit cost. -/
noncomputable def WorstCasePolyTime.toPolyQueries_unit [DecidableEq ι]
    (family : ℕ → OracleComp spec α)
    (h : WorstCasePolyTime family CostModel.unit id) :
    PolyQueries (ι := ι) (spec := fun _ => spec) (α := fun _ => PUnit) (β := fun _ => α)
      (fun n _ => family n) := by
  classical
  let p : Polynomial ℕ := Classical.choose h
  have hp := Classical.choose_spec h
  refine ⟨fun _ => p, ?_⟩
  intro n _
  have hbound : WorstCaseCostBound (family n) CostModel.unit (p.eval n) := by
    intro z hz
    change Multiplicative.toAdd z.2 ≤ p.eval n
    simpa [p] using hp n (z.1, Multiplicative.toAdd z.2)
      (by simpa [costDist, instrumentedRun] using hz)
  exact WorstCaseCostBound.toIsPerIndexQueryBound_unit
    (oa := family n) (bound := p.eval n) hbound

end PolyTime
