/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Cost Models for Oracle Computations

This file defines a general cost model for oracle computations, parametric over any
`AddCommMonoid` cost type. This supports natural numbers, extended non-negative reals,
per-oracle cost vectors, and custom multi-dimensional cost structures.

Uses `AddWriterT` (defined in `ToMathlib.Control.WriterT`) for additive cost accumulation.

## Main Definitions

- `addCostOracle costFn`: Oracle that tracks additive cost via `AddWriterT`.
- `CostModel spec ω`: Assigns cost `queryCost t : ω` to each oracle query `t`.
- `costDist oa cm`: Joint distribution of `(output, totalCost)`.
- `expectedCost oa cm val`: Expected total cost `E[val(cost)]`, computed via `wp`.
- `StrictCostBound`, `ExpectedCostBound`: Cost bound predicates.
- `StrictPolyTime`, `ExpPolyTime`: Asymptotic polynomial-time predicates for computation
  families indexed by a security parameter.

## Key Results

- `fst_map_costDist`: Cost instrumentation doesn't change the output distribution.
- `expectedCost_pure`: Expected cost of a pure computation is `0`.
- `probEvent_cost_gt_le_expectedCost_div`: Markov's inequality for cost distributions.
- `StrictPolyTime.toExpPolyTime`: Strict polynomial time implies expected polynomial time.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

/-! ## Cost Model, Cost Oracle, Cost Distribution

All definitions below operate at `Type` (= `Type 0`), matching `wp`, `support`, and `Pr[...]`
which are defined for `{α : Type}` in the program logic.
-/

variable {ι : Type} {spec : OracleSpec ι} {α : Type}
variable {ω : Type} [AddCommMonoid ω]

/-- Oracle that tracks additive cost. Wraps `costOracle` with `Multiplicative`
to get additive accumulation through the existing `WriterT` infrastructure. -/
def addCostOracle (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω (OracleComp spec)) :=
  costOracle (fun t => Multiplicative.ofAdd (costFn t))

@[simp]
lemma fst_map_run_simulateQ_addCostOracle (costFn : spec.Domain → ω)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (addCostOracle costFn) oa).run = oa := by
  unfold addCostOracle costOracle
  rw [QueryImpl.fst_map_run_withCost, simulateQ_ofLift_eq_self]

/-- A cost model assigns a cost in `ω` to each oracle query.
The cost type `ω` can be `ℕ`, `ℝ≥0∞`, `ι → ℕ` (per-oracle), or any `AddCommMonoid`. -/
structure CostModel (spec : OracleSpec ι) (ω : Type) [AddCommMonoid ω] where
  queryCost : spec.Domain → ω

namespace CostModel

/-- The zero cost model: every query is free. -/
def zero : CostModel spec ω where
  queryCost _ := 0

end CostModel

/-- The joint distribution of `(output, totalCost)` obtained by running `oa` with
additive cost tracking. Cost accumulates via `+` through `AddWriterT`.

Since `Multiplicative ω` and `ω` are definitionally equal, the second component
of the product can be used directly as `ω`. -/
def costDist (oa : OracleComp spec α) (cm : CostModel spec ω) :=
  (simulateQ (addCostOracle cm.queryCost) oa).run

/-- Cost instrumentation does not change the output distribution. -/
@[simp]
theorem fst_map_costDist (oa : OracleComp spec α) (cm : CostModel spec ω) :
    Prod.fst <$> costDist oa cm = oa :=
  fst_map_run_simulateQ_addCostOracle cm.queryCost oa

/-! ## Expected Cost -/

section ExpectedCost

variable [spec.Fintype] [spec.Inhabited]

/-- The expected total cost of `oa` under cost model `cm`, valued by `val : ω → ℝ≥0∞`.
Computed as `E[val(cost)] = ∑ (x, c), Pr[= (x, c) | costDist] * val(c)`.

The valuation `val` maps the abstract cost type to `ℝ≥0∞` for expectation computation.
For `ω = ℕ`, use `(↑·)`. For `ω = ℝ≥0∞`, use `id`. For multi-dimensional cost,
choose which dimension to analyze. -/
noncomputable def expectedCost (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) : ℝ≥0∞ :=
  wp (costDist oa cm) (fun z => val z.2)

/-- Convenience: expected cost for `ℕ`-valued cost models. -/
noncomputable abbrev expectedCostNat (oa : OracleComp spec α)
    (cm : CostModel spec ℕ) : ℝ≥0∞ :=
  expectedCost oa cm (fun n => ↑n)

@[simp]
theorem expectedCost_pure (x : α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (hval : val 0 = 0) :
    expectedCost (spec := spec) (pure x) cm val = 0 := by
  simp only [expectedCost, costDist, addCostOracle, costOracle, simulateQ_pure,
    WriterT.run_pure, wp_pure]
  -- `1 : Multiplicative ω` is definitionally `Multiplicative.ofAdd 0 = 0 : ω`
  exact hval

/-- If `val z.2 ≤ c` for all `z` in the support of `costDist`, then `expectedCost ≤ c`.
This is the key bridge from worst-case (support) bounds to expected bounds. -/
theorem expectedCost_le_of_support_bound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ z ∈ support (costDist oa cm), val z.2 ≤ c) :
    expectedCost oa cm val ≤ c := by
  rw [expectedCost, wp_eq_tsum]
  calc ∑' z, Pr[= z | costDist oa cm] * val z.2
      ≤ ∑' z, Pr[= z | costDist oa cm] * c := by
        apply ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support (costDist oa cm)
        · exact mul_le_mul_of_nonneg_left (h z hz) (zero_le _)
        · simp [probOutput_eq_zero_of_not_mem_support hz]
    _ = c := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

end ExpectedCost

/-! ## Cost Bounds -/

section CostBounds

variable [spec.Fintype] [spec.Inhabited]

/-- Every execution path of `oa` under `cm` has total cost at most `bound`. -/
def StrictCostBound [LE ω] (oa : OracleComp spec α) (cm : CostModel spec ω)
    (bound : ω) : Prop :=
  ∀ z ∈ support (costDist oa cm), z.2 ≤ bound

/-- The expected cost of `oa` under `cm` (valued by `val`) is at most `bound`. -/
def ExpectedCostBound (oa : OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) (bound : ℝ≥0∞) : Prop :=
  expectedCost oa cm val ≤ bound

/-- A strict cost bound implies an expected cost bound, provided the valuation `val`
is monotone with respect to `≤` on `ω`. -/
theorem StrictCostBound.toExpectedCostBound [Preorder ω]
    {oa : OracleComp spec α} {cm : CostModel spec ω} {bound : ω}
    (hstrict : StrictCostBound oa cm bound)
    {val : ω → ℝ≥0∞} (hval_mono : Monotone val) :
    ExpectedCostBound oa cm val (val bound) :=
  expectedCost_le_of_support_bound oa cm val (val bound)
    (fun z hz => hval_mono (hstrict z hz))

/-- **Markov's inequality for cost distributions** (multiplication form).
The probability that the valued cost exceeds `t`, times `t`, is at most `expectedCost`. -/
theorem probEvent_cost_gt_mul_le_expectedCost
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞) (t : ℝ≥0∞) :
    Pr[fun z => t < val z.2 | costDist oa cm] * t ≤ expectedCost oa cm val := by
  rw [probEvent_eq_wp_indicator]
  show wp (costDist oa cm) (fun z => if t < val z.2 then 1 else 0) * t ≤
    wp (costDist oa cm) (fun z => val z.2)
  calc wp (costDist oa cm) (fun z => if t < val z.2 then 1 else 0) * t
      = wp (costDist oa cm) (fun z => t * (if t < val z.2 then 1 else 0)) := by
        rw [wp_mul_const]; ring
    _ ≤ wp (costDist oa cm) (fun z => val z.2) := by
        apply wp_mono
        intro z
        split_ifs with h
        · simp; exact le_of_lt h
        · simp

/-- **Markov's inequality for cost distributions** (division form). -/
theorem probEvent_cost_gt_le_expectedCost_div
    (oa : OracleComp spec α) (cm : CostModel spec ω) (val : ω → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : 0 < t) (ht' : t ≠ ⊤) :
    Pr[fun z => t < val z.2 | costDist oa cm] ≤ expectedCost oa cm val / t :=
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

/-! ## Polynomial-Time Predicates

Asymptotic polynomial-time predicates for families of computations indexed by a
security parameter `n : ℕ`. These connect the cost model to asymptotic complexity. -/

section PolyTime

variable [spec.Fintype] [spec.Inhabited]

/-- All execution paths of `family n` have valued cost at most `p(n)` for some polynomial `p`. -/
def StrictPolyTime (family : ℕ → OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n z, z ∈ support (costDist (family n) cm) → val z.2 ≤ p.eval n

/-- Expected valued cost of `family n` is at most `p(n)` for some polynomial `p`. -/
def ExpPolyTime (family : ℕ → OracleComp spec α) (cm : CostModel spec ω)
    (val : ω → ℝ≥0∞) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, expectedCost (family n) cm val ≤ ↑(p.eval n)

/-- Strict polynomial time implies expected polynomial time.
If every execution path's cost is bounded by `p(n)`, then the expected cost is also
bounded by `p(n)` (since the expectation of a bounded random variable is at most the bound). -/
theorem StrictPolyTime.toExpPolyTime (family : ℕ → OracleComp spec α)
    (cm : CostModel spec ω) (val : ω → ℕ)
    (h : StrictPolyTime family cm val) :
    ExpPolyTime family cm (fun w => ↑(val w)) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun n => expectedCost_le_of_support_bound _ _ _ _ fun z hz =>
    Nat.cast_le.mpr (hp n z hz)⟩

end PolyTime
