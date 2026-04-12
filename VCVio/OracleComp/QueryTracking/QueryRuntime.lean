/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.EvalDist.Monad.Map
import ToMathlib.General
import ToMathlib.Probability.ProbabilityMassFunction.TailSums
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Bundled Query Runtimes

This file packages concrete query implementations as explicit runtime objects.

`HasQuery spec m` is the right *capability* interface for constructions that only need to issue
queries. When we want to instrument, transport, or otherwise analyze that capability, we also need
an explicit `QueryImpl spec m` to work with. `QueryRuntime spec m` is the thin bundle that stores
that implementation without changing the capability layer.

The main use cases are:

- reifying an existing `HasQuery` capability as a `QueryRuntime`;
- adding cost, counting, or logging layers to a runtime;
- instantiating a generic `HasQuery` construction directly in an analysis monad.
-/

open OracleSpec
open scoped BigOperators

/-- Bundled implementation of the oracle family `spec` in the ambient monad `m`. -/
structure QueryRuntime {ι : Type} (spec : OracleSpec ι) (m : Type → Type*) where
  /-- Concrete implementation of each query in the family `spec`. -/
  impl : QueryImpl spec m

namespace QueryRuntime

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}

/-- View a bundled query runtime as the corresponding `HasQuery` capability. -/
@[reducible] def toHasQuery (runtime : QueryRuntime spec m) : HasQuery spec m :=
  runtime.impl.toHasQuery

@[simp]
lemma toHasQuery_query (runtime : QueryRuntime spec m) (t : spec.Domain) :
    (runtime.toHasQuery).query t = runtime.impl t := rfl

/-- Repackage an existing `HasQuery` capability as an explicit query runtime. -/
def ofHasQuery [HasQuery spec m] : QueryRuntime spec m where
  impl := HasQuery.toQueryImpl

@[simp]
lemma ofHasQuery_impl [HasQuery spec m] (t : spec.Domain) :
    (ofHasQuery (spec := spec) (m := m)).impl t =
      HasQuery.query (spec := spec) (m := m) t := rfl

section OracleComp

variable {ι : Type} {spec : OracleSpec ι}

/-- The canonical bundled runtime for the free oracle monad `OracleComp spec`. -/
abbrev oracleCompRuntime (spec : OracleSpec ι) : QueryRuntime spec (OracleComp spec) :=
  QueryRuntime.ofHasQuery (spec := spec) (m := OracleComp spec)

@[simp]
lemma oracleCompRuntime_impl_eq_ofLift :
    (oracleCompRuntime (spec := spec)).impl = QueryImpl.ofLift spec (OracleComp spec) := by
  ext t
  rfl

end OracleComp

section instrumentation

variable [Monad m]

/-- Instrument a query runtime with multiplicative/monoidal cost accumulation in a `WriterT`
layer. -/
def withCost {ω : Type} [Monoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) :
    QueryRuntime spec (WriterT ω m) where
  impl := QueryImpl.withCost (spec := spec) (m := m) runtime.impl costFn

@[simp]
lemma withCost_impl {ω : Type} [Monoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    (runtime.withCost costFn).impl t = (do tell (costFn t); liftM (runtime.impl t)) := by
  simp [withCost]

/-- Instrument a query runtime with additive cost accumulation in an `AddWriterT` layer. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) :
    QueryRuntime spec (AddWriterT ω m) where
  impl := QueryImpl.withCost (spec := spec) (m := m) runtime.impl
    (fun t => Multiplicative.ofAdd (costFn t))

@[simp]
lemma withAddCost_impl {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    (runtime.withAddCost costFn).impl t =
      (do AddWriterT.addTell (M := m) (costFn t); liftM (runtime.impl t)) := by
  simp [withAddCost, AddWriterT.addTell, QueryImpl.withCost]

/-- Instrument a query runtime with unit additive cost for every query. -/
def withUnitCost (runtime : QueryRuntime spec m) :
    QueryRuntime spec (AddWriterT ℕ m) :=
  runtime.withAddCost (fun _ ↦ 1)

@[simp]
lemma withUnitCost_impl (runtime : QueryRuntime spec m) (t : spec.Domain) :
    runtime.withUnitCost.impl t =
      (do AddWriterT.addTell (M := m) 1; liftM (runtime.impl t)) := by
  simp [withUnitCost]

end instrumentation

end QueryRuntime

namespace AddWriterT

variable {m : Type → Type*} [Monad m]
variable {α β : Type}

section pathwiseCost

variable [HasEvalSet m]

/-- Pathwise upper bound for an `AddWriterT` computation: every reachable execution result carries
additive cost at most `w`. -/
def PathwiseCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ z ∈ support oa.run, Multiplicative.toAdd z.2 ≤ w

/-- Pathwise lower bound for an `AddWriterT` computation: every reachable execution result carries
additive cost at least `w`. -/
def PathwiseCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ z ∈ support oa.run, w ≤ Multiplicative.toAdd z.2

/-- Pathwise exactness on support for an `AddWriterT` computation: every reachable execution result
carries exactly the additive cost `w`.

This is the weak extensional notion of pathwise exactness. If `oa.run` has empty support, it holds
vacuously for every `w`. Use [`AddWriterT.PathwiseHasCost`] when the intended meaning is that `oa`
has an exact pathwise cost and admits at least one reachable execution. -/
def PathwiseCostEqOnSupport {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  PathwiseCostAtMost oa w ∧ PathwiseCostAtLeast oa w

@[simp] lemma pathwiseCostEqOnSupport_iff {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) :
    PathwiseCostEqOnSupport oa w ↔ PathwiseCostAtMost oa w ∧ PathwiseCostAtLeast oa w :=
  Iff.rfl

/-- Pathwise exact cost for an `AddWriterT` computation: `oa` has at least one reachable execution,
and every reachable execution result carries exactly the additive cost `w`.

This is the strong semantic notion of exact cost over execution paths.
Unlike [`AddWriterT.HasCost`], it does not require cost to be recoverable
from the final output alone. Unlike
[`AddWriterT.PathwiseCostEqOnSupport`], it is not vacuous on computations with empty support. -/
def PathwiseHasCost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  (support oa.run).Nonempty ∧ PathwiseCostEqOnSupport oa w

@[simp] lemma pathwiseHasCost_iff {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) :
    PathwiseHasCost oa w ↔
      (support oa.run).Nonempty ∧ PathwiseCostEqOnSupport oa w :=
  Iff.rfl

lemma PathwiseHasCost.nonempty {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    (support oa.run).Nonempty :=
  h.1

lemma PathwiseCostEqOnSupport.atMost {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostAtMost oa w :=
  h.1

lemma PathwiseCostEqOnSupport.atLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostAtLeast oa w :=
  h.2

lemma PathwiseHasCost.eqOnSupport {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostEqOnSupport oa w :=
  h.2

lemma PathwiseHasCost.atMost {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostAtMost oa w :=
  h.2.1

lemma PathwiseHasCost.atLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostAtLeast oa w :=
  h.2.2

lemma PathwiseHasCost.unique {ω : Type} [AddMonoid ω] [PartialOrder ω]
    {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h₁ : PathwiseHasCost oa w₁) (h₂ : PathwiseHasCost oa w₂) :
    w₁ = w₂ := by
  rcases h₁.nonempty with ⟨z, hz⟩
  exact le_antisymm
    (le_trans (h₁.atLeast z hz) (h₂.atMost z hz))
    (le_trans (h₂.atLeast z hz) (h₁.atMost z hz))

lemma pathwiseCostAtMost_of_hasCost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : AddWriterT ω m α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hwb : w ≤ b) :
    PathwiseCostAtMost oa b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈ support oa.costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h] at hzCost
  rw [support_map] at hzCost
  rcases hzCost with ⟨a, _, hzCost⟩
  simpa [hzCost] using hwb

lemma pathwiseCostAtLeast_of_hasCost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : AddWriterT ω m α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hbw : b ≤ w) :
    PathwiseCostAtLeast oa b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈ support oa.costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h] at hzCost
  rw [support_map] at hzCost
  rcases hzCost with ⟨a, _, hzCost⟩
  simpa [hzCost] using hbw

end pathwiseCost

section expectedCost

variable {ω : Type}

/-- The expected additive cost of an `AddWriterT` computation, obtained by taking the expectation
of its cost marginal.

This expectation is computed over the base monad's subdistribution semantics on `oa.costs`. In
particular, if the underlying computation can fail, the missing mass contributes `0`, exactly as
for other `wp`-style expectations in VCV-io. -/
noncomputable def expectedCost [HasEvalSPMF m]
    (oa : AddWriterT ω m α) (val : ω → ENNReal) : ENNReal :=
  ∑' w : ω, Pr[= w | oa.costs] * val w

/-- Convenience specialization of [`AddWriterT.expectedCost`] to natural-valued additive costs. -/
noncomputable abbrev expectedCostNat [HasEvalSPMF m] (oa : AddWriterT ℕ m α) : ENNReal :=
  expectedCost oa (fun n ↦ ↑n)

/-- Tail-sum formula for the natural-valued expected cost of an `AddWriterT` computation:

`E[cost] = ∑ i, Pr[i < cost]`.

This is the standard discrete expectation identity specialized to the writer-cost marginal. -/
lemma expectedCostNat_eq_tsum_tail_probs [HasEvalSPMF m] (oa : AddWriterT ℕ m α) :
    expectedCostNat oa = ∑' i : ℕ, Pr[ fun c ↦ i < c | oa.costs ] := by
  unfold expectedCostNat expectedCost
  calc
    ∑' n : ℕ, Pr[= n | oa.costs] * (n : ENNReal)
        = ∑' i : ℕ, ∑' n : ℕ, if i < n then Pr[= n | oa.costs] else 0 :=
          ENNReal.tsum_mul_nat_eq_tsum_tail (fun n ↦ Pr[= n | oa.costs])
    _ = ∑' i : ℕ, Pr[ fun c ↦ i < c | oa.costs ] := by
          refine tsum_congr fun i ↦ ?_
          rw [probEvent_eq_tsum_indicator]
          refine tsum_congr fun n ↦ ?_
          by_cases h : i < n <;> simp [Set.indicator, h]

/-- Tail domination bounds the expected natural-valued writer cost.

If the tail probability `Pr[i < cost]` is bounded by `a i` for every `i`, then
`E[cost] ≤ ∑ i, a i`. -/
lemma expectedCostNat_le_tsum_of_tail_probs_le [HasEvalSPMF m]
    (oa : AddWriterT ℕ m α) {a : ℕ → ENNReal}
    (h : ∀ i : ℕ, Pr[ fun c ↦ i < c | oa.costs ] ≤ a i) :
    expectedCostNat oa ≤ ∑' i : ℕ, a i := by
  rw [expectedCostNat_eq_tsum_tail_probs]
  exact ENNReal.tsum_le_tsum h

/-- Finite tail-sum formula for natural-valued writer cost under a pathwise upper bound.

If every execution path of `oa` incurs cost at most `n`, then the tail probabilities vanish above
`n`, so the infinite tail sum truncates to `Finset.range n`. -/
lemma expectedCostNat_eq_sum_tail_probs_of_pathwiseCostAtMost
    [HasEvalSPMF m] [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : PathwiseCostAtMost oa n) :
    expectedCostNat oa = ∑ i ∈ Finset.range n, Pr[ fun c ↦ i < c | oa.costs ] := by
  rw [expectedCostNat_eq_tsum_tail_probs]
  symm
  rw [tsum_eq_sum (s := Finset.range n) (fun b hb => ?_)]
  · have hnb : n ≤ b := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hb)
    refine probEvent_eq_zero ?_
    intro c hc
    rw [AddWriterT.costs_def, support_map] at hc
    rcases hc with ⟨z, hz, rfl⟩
    exact not_lt_of_ge (le_trans (h z hz) hnb)

lemma expectedCost_le_of_support_bound [HasEvalSPMF m]
    (oa : AddWriterT ω m α) (val : ω → ENNReal) (c : ENNReal)
    (h : ∀ w ∈ support oa.costs, val w ≤ c) :
    expectedCost oa val ≤ c := by
  unfold expectedCost
  have hmass : ∑' w : ω, Pr[= w | oa.costs] ≤ 1 :=
    tsum_probOutput_le_one (mx := oa.costs)
  calc
    ∑' w : ω, Pr[= w | oa.costs] * val w
        ≤ ∑' w : ω, Pr[= w | oa.costs] * c := by
          refine ENNReal.tsum_le_tsum ?_
          intro w
          by_cases hw : w ∈ support oa.costs
          · exact mul_le_mul_of_nonneg_left (h w hw) (zero_le _)
          · have hp : Pr[= w | oa.costs] = 0 := by
              rw [AddWriterT.costs_def]
              exact probOutput_eq_zero_of_not_mem_support
                (mx := (fun z ↦ Multiplicative.toAdd z.2) <$> WriterT.run oa)
                (by simpa [AddWriterT.costs_def] using hw)
            rw [hp]
            simp
    _ = (∑' w : ω, Pr[= w | oa.costs]) * c := by
          rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * c := by
          simpa [mul_comm] using (mul_le_mul_right hmass c)
    _ = c := by simp

lemma expectedCost_le_of_pathwiseCostAtMost [AddMonoid ω] [HasEvalSPMF m] [LawfulMonad m]
    [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} {val : ω → ENNReal}
    (h : PathwiseCostAtMost oa w) (hval : Monotone val) :
    expectedCost oa val ≤ val w := by
  refine expectedCost_le_of_support_bound oa val (val w) ?_
  intro c hc
  rw [AddWriterT.costs_def, support_map] at hc
  rcases hc with ⟨z, hz, rfl⟩
  exact hval (h z hz)

lemma expectedCost_ge_of_pathwiseCostAtLeast [AddMonoid ω] [LawfulMonad m] [Preorder ω]
    [HasEvalPMF m]
    {oa : AddWriterT ω m α} {w : ω} {val : ω → ENNReal}
    (h : PathwiseCostAtLeast oa w) (hval : Monotone val) :
    val w ≤ expectedCost oa val := by
  unfold expectedCost
  have hmass : ∑' c : ω, Pr[= c | oa.costs] = 1 :=
    HasEvalPMF.tsum_probOutput_eq_one (mx := oa.costs)
  calc
    val w = 1 * val w := by simp
    _ = (∑' c : ω, Pr[= c | oa.costs]) * val w := by
          rw [← hmass]
    _ = ∑' c : ω, Pr[= c | oa.costs] * val w := by
          rw [← ENNReal.tsum_mul_right]
    _ ≤ ∑' c : ω, Pr[= c | oa.costs] * val c := by
          refine ENNReal.tsum_le_tsum ?_
          intro c
          by_cases hc : c ∈ support oa.costs
          · rw [AddWriterT.costs_def, support_map] at hc
            rcases hc with ⟨z, hz, rfl⟩
            exact mul_le_mul_of_nonneg_left (hval (h z hz)) (zero_le _)
          · have hp : Pr[= c | oa.costs] = 0 := by
              rw [AddWriterT.costs_def]
              exact probOutput_eq_zero_of_not_mem_support
                (mx := (fun z ↦ Multiplicative.toAdd z.2) <$> WriterT.run oa)
                (by simpa [AddWriterT.costs_def] using hc)
            rw [hp]
            simp

lemma expectedCost_eq_tsum_outputs_of_costsAs [HasEvalSPMF m] [LawfulMonad m]
    {oa : AddWriterT ω m α} {f : α → ω} {val : ω → ENNReal}
    (h : oa.CostsAs f) :
    expectedCost oa val = ∑' a : α, Pr[= a | oa.outputs] * val (f a) := by
  classical
  letI : DecidableEq ω := Classical.decEq ω
  unfold expectedCost
  rw [h]
  simp_rw [probOutput_map_eq_tsum]
  calc
    ∑' w : ω, (∑' a : α, Pr[= a | oa.outputs] * Pr[= w | (pure (f a) : m ω)]) * val w
      = ∑' w : ω, ∑' a : α, Pr[= a | oa.outputs] *
          (Pr[= w | (pure (f a) : m ω)] * val w) := by
            refine tsum_congr fun w => ?_
            simpa [mul_assoc] using
              (ENNReal.tsum_mul_right
                (f := fun a : α =>
                  Pr[= a | oa.outputs] * Pr[= w | (pure (f a) : m ω)])
                (a := val w)).symm
    _ = ∑' a : α, ∑' w : ω, Pr[= a | oa.outputs] *
          (Pr[= w | (pure (f a) : m ω)] * val w) := by
            rw [ENNReal.tsum_comm]
    _ = ∑' a : α, Pr[= a | oa.outputs] *
          ∑' w : ω, Pr[= w | (pure (f a) : m ω)] * val w := by
            refine tsum_congr fun a => by
              rw [← ENNReal.tsum_mul_left]
    _ = ∑' a : α, Pr[= a | oa.outputs] * val (f a) := by
            refine tsum_congr fun a => by
              letI : DecidableEq ω := Classical.decEq ω
              simp

end expectedCost

section weightedPathwiseBounds

variable [HasEvalSet m]
variable {ω : Type} [AddCommMonoid ω] [PartialOrder ω]

lemma pathwiseCostAtMost_pure [LawfulMonad m] (x : α) :
    PathwiseCostAtMost (pure x : AddWriterT ω m α) 0 := by
  intro z hz
  rw [WriterT.run_pure, support_pure] at hz
  rcases hz with rfl
  simp

lemma pathwiseCostAtLeast_pure [LawfulMonad m] (x : α) :
    PathwiseCostAtLeast (pure x : AddWriterT ω m α) 0 := by
  intro z hz
  rw [WriterT.run_pure, support_pure] at hz
  rcases hz with rfl
  simp

lemma pathwiseCostEqOnSupport_pure [LawfulMonad m] (x : α) :
    PathwiseCostEqOnSupport (pure x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_pure (m := m) (ω := ω) x,
    pathwiseCostAtLeast_pure (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_pure [LawfulMonad m] (x : α) :
    PathwiseHasCost (pure x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_pure (m := m) (ω := ω) x,
    pathwiseCostAtLeast_pure (m := m) (ω := ω) x⟩⟩
  rw [WriterT.run_pure, support_pure]
  exact ⟨(x, 1), by simp⟩

lemma pathwiseCostAtMost_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostAtMost (monadLift x : AddWriterT ω m α) 0 := by
  intro z hz
  rw [WriterT.run_monadLift, support_map] at hz
  rcases hz with ⟨a, _, rfl⟩
  simp

lemma pathwiseCostAtLeast_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostAtLeast (monadLift x : AddWriterT ω m α) 0 := by
  intro z hz
  rw [WriterT.run_monadLift, support_map] at hz
  rcases hz with ⟨a, _, rfl⟩
  simp

lemma pathwiseCostEqOnSupport_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostEqOnSupport (monadLift x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_monadLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_monadLift (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_monadLift_of_supportNonempty [LawfulMonad m] (x : m α)
    (hx : (support x).Nonempty) :
    PathwiseHasCost (monadLift x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_monadLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_monadLift (m := m) (ω := ω) x⟩⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨(a, 1), ?_⟩
  rw [WriterT.run_monadLift, support_map]
  exact ⟨a, ha, rfl⟩

lemma pathwiseCostAtMost_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostAtMost (liftM x : AddWriterT ω m α) 0 := by
  intro z hz
  rw [WriterT.liftM_def, WriterT.run_mk, support_map] at hz
  rcases hz with ⟨a, _, rfl⟩
  simp

lemma pathwiseCostAtLeast_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostAtLeast (liftM x : AddWriterT ω m α) 0 := by
  intro z hz
  rw [WriterT.liftM_def, WriterT.run_mk, support_map] at hz
  rcases hz with ⟨a, _, rfl⟩
  simp

lemma pathwiseCostEqOnSupport_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostEqOnSupport (liftM x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_liftM (m := m) (ω := ω) x,
    pathwiseCostAtLeast_liftM (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_liftM_of_supportNonempty [LawfulMonad m] (x : m α)
    (hx : (support x).Nonempty) :
    PathwiseHasCost (liftM x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_liftM (m := m) (ω := ω) x,
    pathwiseCostAtLeast_liftM (m := m) (ω := ω) x⟩⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨(a, 1), ?_⟩
  rw [WriterT.liftM_def, WriterT.run_mk, support_map]
  exact ⟨a, ha, rfl⟩

lemma pathwiseCostAtMost_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m] (x : ProbComp α) :
    PathwiseCostAtMost (monadLift x : AddWriterT ω m α) 0 := by
  change PathwiseCostAtMost (monadLift ((liftM x : m α)) : AddWriterT ω m α) 0
  exact pathwiseCostAtMost_monadLift (m := m) (x := (liftM x : m α))

lemma pathwiseCostAtLeast_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m] (x : ProbComp α) :
    PathwiseCostAtLeast (monadLift x : AddWriterT ω m α) 0 := by
  change PathwiseCostAtLeast (monadLift ((liftM x : m α)) : AddWriterT ω m α) 0
  exact pathwiseCostAtLeast_monadLift (m := m) (x := (liftM x : m α))

lemma pathwiseCostEqOnSupport_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m]
    (x : ProbComp α) :
    PathwiseCostEqOnSupport (monadLift x : AddWriterT ω m α) 0 :=
  ⟨
    pathwiseCostAtMost_probCompLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_probCompLift (m := m) (ω := ω) x
  ⟩

lemma pathwiseHasCost_probCompLift_of_supportNonempty [LawfulMonad m] [MonadLiftT ProbComp m]
    (x : ProbComp α) (hx : (support (liftM x : m α)).Nonempty) :
    PathwiseHasCost (monadLift x : AddWriterT ω m α) 0 := by
  change PathwiseHasCost (monadLift ((liftM x : m α)) : AddWriterT ω m α) 0
  exact pathwiseHasCost_monadLift_of_supportNonempty (m := m) (ω := ω) (x := (liftM x : m α)) hx

lemma pathwiseCostAtMost_mono {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h : PathwiseCostAtMost oa w₁) (hw : w₁ ≤ w₂) :
    PathwiseCostAtMost oa w₂ := by
  intro z hz
  exact le_trans (h z hz) hw

lemma pathwiseCostAtLeast_mono {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h : PathwiseCostAtLeast oa w₂) (hw : w₁ ≤ w₂) :
    PathwiseCostAtLeast oa w₁ := by
  intro z hz
  exact le_trans hw (h z hz)

lemma pathwiseCostAtMost_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostAtMost (AddWriterT.addTell (M := m) w) w := by
  intro z hz
  rw [AddWriterT.run_addTell, support_pure] at hz
  rcases hz with rfl
  simp

lemma pathwiseCostAtLeast_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostAtLeast (AddWriterT.addTell (M := m) w) w := by
  intro z hz
  rw [AddWriterT.run_addTell, support_pure] at hz
  rcases hz with rfl
  simp

lemma pathwiseCostEqOnSupport_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostEqOnSupport (AddWriterT.addTell (M := m) w) w :=
  ⟨pathwiseCostAtMost_addTell (m := m) w, pathwiseCostAtLeast_addTell (m := m) w⟩

lemma pathwiseHasCost_addTell [LawfulMonad m] (w : ω) :
    PathwiseHasCost (AddWriterT.addTell (M := m) w) w := by
  refine ⟨?_, ⟨pathwiseCostAtMost_addTell (m := m) w, pathwiseCostAtLeast_addTell (m := m) w⟩⟩
  rw [AddWriterT.run_addTell, support_pure]
  exact ⟨(PUnit.unit, Multiplicative.ofAdd w), by simp⟩

lemma pathwiseCostAtMost_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostAtMost oa w) :
    PathwiseCostAtMost (f <$> oa) w := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'

lemma pathwiseCostAtLeast_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostAtLeast oa w) :
    PathwiseCostAtLeast (f <$> oa) w := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'

lemma pathwiseCostEqOnSupport_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostEqOnSupport (f <$> oa) w :=
  ⟨pathwiseCostAtMost_map f h.atMost, pathwiseCostAtLeast_map f h.atLeast⟩

lemma pathwiseHasCost_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseHasCost oa w) :
    PathwiseHasCost (f <$> oa) w := by
  refine ⟨?_, ⟨pathwiseCostAtMost_map f h.atMost, pathwiseCostAtLeast_map f h.atLeast⟩⟩
  rcases h.nonempty with ⟨z, hz⟩
  refine ⟨Prod.map f id z, ?_⟩
  rw [WriterT.run_map, support_map]
  exact ⟨z, hz, rfl⟩

lemma pathwiseCostAtMost_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostAtMost oa w₁) (h₂ : ∀ a, PathwiseCostAtMost (f a) w₂) :
    PathwiseCostAtMost (oa >>= f) (w₁ + w₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff
    (mx := oa.run)
    (my := fun aw ↦ Prod.map id (aw.2 * ·) <$> (f aw.1).run)
    (y := z)).1 hz with ⟨aw, haw, hz⟩
  rcases aw with ⟨a, wa⟩
  rw [support_map] at hz
  rcases hz with ⟨bw, hbw, rfl⟩
  rcases bw with ⟨b, wb⟩
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

lemma pathwiseCostAtLeast_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostAtLeast oa w₁) (h₂ : ∀ a, PathwiseCostAtLeast (f a) w₂) :
    PathwiseCostAtLeast (oa >>= f) (w₁ + w₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff
    (mx := oa.run)
    (my := fun aw ↦ Prod.map id (aw.2 * ·) <$> (f aw.1).run)
    (y := z)).1 hz with ⟨aw, haw, hz⟩
  rcases aw with ⟨a, wa⟩
  rw [support_map] at hz
  rcases hz with ⟨bw, hbw, rfl⟩
  rcases bw with ⟨b, wb⟩
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

lemma pathwiseCostEqOnSupport_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostEqOnSupport oa w₁) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) w₂) :
    PathwiseCostEqOnSupport (oa >>= f) (w₁ + w₂) :=
  ⟨pathwiseCostAtMost_bind h₁.atMost (fun a ↦ (h₂ a).atMost),
    pathwiseCostAtLeast_bind h₁.atLeast (fun a ↦ (h₂ a).atLeast)⟩

lemma pathwiseHasCost_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseHasCost oa w₁) (h₂ : ∀ a, PathwiseHasCost (f a) w₂) :
    PathwiseHasCost (oa >>= f) (w₁ + w₂) := by
  refine ⟨?_, ⟨pathwiseCostAtMost_bind h₁.atMost (fun a ↦ (h₂ a).atMost),
    pathwiseCostAtLeast_bind h₁.atLeast (fun a ↦ (h₂ a).atLeast)⟩⟩
  rcases h₁.nonempty with ⟨aw, haw⟩
  rcases aw with ⟨a, wa⟩
  rcases (h₂ a).nonempty with ⟨bw, hbw⟩
  rcases bw with ⟨b, wb⟩
  refine ⟨(b, wa * wb), ?_⟩
  rw [WriterT.run_bind, mem_support_bind_iff]
  refine ⟨(a, wa), haw, ?_⟩
  rw [support_map]
  exact ⟨(b, wb), hbw, rfl⟩

lemma pathwiseHasCost_bind_zero_left [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseHasCost oa 0) (h₂ : ∀ a, PathwiseHasCost (f a) w) :
    PathwiseHasCost (oa >>= f) w := by
  simpa [zero_add] using pathwiseHasCost_bind (w₁ := 0) (w₂ := w) h₁ h₂

lemma pathwiseHasCost_bind_zero_right [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseHasCost oa w) (h₂ : ∀ a, PathwiseHasCost (f a) 0) :
    PathwiseHasCost (oa >>= f) w := by
  simpa [add_zero] using pathwiseHasCost_bind (w₁ := w) (w₂ := 0) h₁ h₂

lemma pathwiseCostEqOnSupport_bind_zero_left [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseCostEqOnSupport oa 0) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) w) :
    PathwiseCostEqOnSupport (oa >>= f) w := by
  simpa [zero_add] using pathwiseCostEqOnSupport_bind (w₁ := 0) (w₂ := w) h₁ h₂

lemma pathwiseCostEqOnSupport_bind_zero_right [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseCostEqOnSupport oa w) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) 0) :
    PathwiseCostEqOnSupport (oa >>= f) w := by
  simpa [add_zero] using pathwiseCostEqOnSupport_bind (w₁ := w) (w₂ := 0) h₁ h₂

lemma pathwiseCostAtMost_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseCostAtMost (f i) k) :
    PathwiseCostAtMost (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      simpa [zero_nsmul] using
        (pathwiseCostAtMost_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α)))
  | succ n ih =>
      simp only [Fin.mOfFn, succ_nsmul']
      let consA : α → (Fin n → α) → Fin n.succ → α :=
        fun a ↦ @Fin.cons n (fun _ : Fin n.succ ↦ α) a
      simpa [add_comm, consA] using
        (pathwiseCostAtMost_bind (w₁ := k) (w₂ := n • k)
          (by simpa using h 0)
          (fun a ↦
            pathwiseCostAtMost_map (consA a)
              (ih (fun i ↦ h i.succ))))

lemma pathwiseCostAtLeast_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseCostAtLeast (f i) k) :
    PathwiseCostAtLeast (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      simpa [zero_nsmul] using
        (pathwiseCostAtLeast_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α)))
  | succ n ih =>
      simp only [Fin.mOfFn, succ_nsmul']
      let consA : α → (Fin n → α) → Fin n.succ → α :=
        fun a ↦ @Fin.cons n (fun _ : Fin n.succ ↦ α) a
      simpa [add_comm, consA] using
        (pathwiseCostAtLeast_bind (w₁ := k) (w₂ := n • k)
          (by simpa using h 0)
          (fun a ↦
            pathwiseCostAtLeast_map (consA a)
              (ih (fun i ↦ h i.succ))))

lemma pathwiseHasCost_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseHasCost (f i) k) :
    PathwiseHasCost (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      simpa [Fin.mOfFn, zero_nsmul] using
        (pathwiseHasCost_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α)))
  | succ n ih =>
      let consA : α → (Fin n → α) → Fin n.succ → α :=
        fun a ↦ @Fin.cons n (fun _ : Fin n.succ ↦ α) a
      have htail : ∀ i : Fin n, PathwiseHasCost (f i.succ) k := fun i ↦ h i.succ
      have ih' : PathwiseHasCost (Fin.mOfFn n (fun i ↦ f i.succ)) (n • k) := ih htail
      have hbind :
          PathwiseHasCost
            (f 0 >>= fun a ↦ (consA a) <$> Fin.mOfFn n (fun i ↦ f i.succ))
            (k + n • k) :=
        pathwiseHasCost_bind (m := m) (ω := ω) (w₁ := k) (w₂ := n • k)
          (h 0)
          (fun a ↦ pathwiseHasCost_map (f := consA a) ih')
      simpa [Fin.mOfFn, succ_nsmul', add_comm, consA] using hbind

end weightedPathwiseBounds

section unitCostBounds

variable [HasEvalSet m]

/-- Pathwise upper bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedAboveBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostAtMost oa n

/-- Pathwise lower bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedBelowBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostAtLeast oa n

lemma queryBoundedAboveBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedAboveBy (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtMost_pure x

lemma queryBoundedBelowBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedBelowBy (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtLeast_pure x

lemma queryBoundedAboveBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedAboveBy (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtMost_monadLift x

lemma queryBoundedBelowBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedBelowBy (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtLeast_monadLift x

lemma queryBoundedAboveBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedAboveBy oa n₁) (hn : n₁ ≤ n₂) :
    QueryBoundedAboveBy oa n₂ :=
  pathwiseCostAtMost_mono h hn

lemma queryBoundedBelowBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedBelowBy oa n₂) (hn : n₁ ≤ n₂) :
    QueryBoundedBelowBy oa n₁ :=
  pathwiseCostAtLeast_mono h hn

lemma queryBoundedAboveBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedAboveBy (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostAtMost_addTell w

lemma queryBoundedBelowBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedBelowBy (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostAtLeast_addTell w

lemma queryBoundedAboveBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedAboveBy oa n) :
    QueryBoundedAboveBy (f <$> oa) n :=
  pathwiseCostAtMost_map f h

lemma queryBoundedBelowBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedBelowBy oa n) :
    QueryBoundedBelowBy (f <$> oa) n :=
  pathwiseCostAtLeast_map f h

lemma queryBoundedAboveBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedAboveBy oa n₁) (h₂ : ∀ a, QueryBoundedAboveBy (f a) n₂) :
    QueryBoundedAboveBy (oa >>= f) (n₁ + n₂) :=
  pathwiseCostAtMost_bind h₁ h₂

lemma queryBoundedBelowBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedBelowBy oa n₁) (h₂ : ∀ a, QueryBoundedBelowBy (f a) n₂) :
    QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) :=
  pathwiseCostAtLeast_bind h₁ h₂

lemma queryBoundedAboveBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedAboveBy (f i) k) :
    QueryBoundedAboveBy (Fin.mOfFn n f) (n * k) :=
  pathwiseCostAtMost_fin_mOfFn h

lemma queryBoundedBelowBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedBelowBy (f i) k) :
    QueryBoundedBelowBy (Fin.mOfFn n f) (n * k) :=
  pathwiseCostAtLeast_fin_mOfFn h

end unitCostBounds

section expectedUnitCost

variable [HasEvalSPMF m]

lemma expectedCostNat_le_of_queryBoundedAboveBy [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryBoundedAboveBy oa n) :
    expectedCostNat oa ≤ n := by
  simpa [expectedCostNat, QueryBoundedAboveBy] using
    (expectedCost_le_of_pathwiseCostAtMost
      (oa := oa) (w := n) (val := fun k ↦ (k : ENNReal)) h
      (fun a b hle ↦ by
        simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))

end expectedUnitCost

section expectedUnitCostPMF

variable [HasEvalPMF m]

lemma expectedCostNat_ge_of_queryBoundedBelowBy [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryBoundedBelowBy oa n) :
    (n : ENNReal) ≤ expectedCostNat oa := by
  simpa [expectedCostNat, QueryBoundedBelowBy] using
    (expectedCost_ge_of_pathwiseCostAtLeast
      (oa := oa) (w := n) (val := fun k ↦ (k : ENNReal)) h
      (fun a b hle ↦ by
        simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))

end expectedUnitCostPMF

end AddWriterT

namespace HasQuery

section runtimeInstantiation

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}

/-- Instantiate a generic `HasQuery` computation in the concrete runtime `runtime`. -/
def inRuntime (oa : [HasQuery spec m] → m α) (runtime : QueryRuntime spec m) : m α := by
  letI := runtime.toHasQuery
  exact oa

section instrumentation

variable [Monad m]

/-- Instantiate a generic `HasQuery` computation in the additive-cost instrumented runtime
obtained from `runtime`. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (oa : [HasQuery spec (AddWriterT ω m)] → AddWriterT ω m α)
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) : AddWriterT ω m α := by
  letI := (runtime.withAddCost costFn).toHasQuery
  exact oa

/-- Instantiate a generic `HasQuery` computation in the unit-cost instrumented runtime obtained
from `runtime`. -/
def withUnitCost (oa : [HasQuery spec (AddWriterT ℕ m)] → AddWriterT ℕ m α)
    (runtime : QueryRuntime spec m) : AddWriterT ℕ m α := by
  letI := runtime.withUnitCost.toHasQuery
  exact oa

end instrumentation
end runtimeInstantiation

section queryBounds

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}
variable [Monad m] [LawfulMonad m]

lemma hasCost_withAddCost_query {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    Cost[
      HasQuery.withAddCost
        (fun [HasQuery spec (AddWriterT ω m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ω m) t)
        runtime costFn
    ] = costFn t := by
  change Cost[(runtime.withAddCost costFn).impl t] = costFn t
  rw [QueryRuntime.withAddCost_impl, AddWriterT.hasCost_iff]
  simp [AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell]

lemma queryBoundedAboveBy_withUnitCost_query
    [HasEvalSet m]
    (runtime : QueryRuntime spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedAboveBy
      (HasQuery.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  change AddWriterT.QueryBoundedAboveBy ((runtime.withUnitCost).impl t) 1
  rw [QueryRuntime.withUnitCost_impl]
  apply AddWriterT.queryBoundedAboveBy_bind (n₁ := 1) (n₂ := 0)
  · exact AddWriterT.queryBoundedAboveBy_addTell 1
  · intro _
    exact AddWriterT.queryBoundedAboveBy_monadLift (runtime.impl t)

lemma queryBoundedBelowBy_withUnitCost_query
    [HasEvalSet m]
    (runtime : QueryRuntime spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedBelowBy
      (HasQuery.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  change AddWriterT.QueryBoundedBelowBy ((runtime.withUnitCost).impl t) 1
  rw [QueryRuntime.withUnitCost_impl]
  apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 1) (n₂ := 0)
  · exact AddWriterT.queryBoundedBelowBy_addTell 1
  · intro _
    exact AddWriterT.queryBoundedBelowBy_monadLift (runtime.impl t)

end queryBounds

section costAccounting

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}

/-- A computation generic over a `HasQuery spec m` capability. -/
abbrev Computation (spec : OracleSpec ι) (m : Type → Type*) (α : Type) :=
  [HasQuery spec m] → m α

section genericCost

variable [Monad m]

/-- Running `oa` in the additive-cost instrumentation of `runtime` yields an output-dependent
cost described by `f`. -/
def UsesCostAs {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (f : α → ω) : Prop :=
  AddWriterT.CostsAs (HasQuery.withAddCost oa runtime costFn) f

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs constant cost `w`. -/
def UsesCostExactly {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  Cost[ HasQuery.withAddCost oa runtime costFn ] = w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at most `w` on
every execution path. This is a semantic support bound, not merely an output-indexed cost
description. -/
def UsesCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.PathwiseCostAtMost (HasQuery.withAddCost oa runtime costFn) w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at least `w` on
every execution path. -/
def UsesCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.PathwiseCostAtLeast (HasQuery.withAddCost oa runtime costFn) w

lemma usesCostAtMost_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hwb : w ≤ b) :
    HasQuery.UsesCostAtMost oa runtime costFn b :=
  AddWriterT.pathwiseCostAtMost_of_hasCost h hwb

lemma usesCostAtLeast_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hbw : b ≤ w) :
    HasQuery.UsesCostAtLeast oa runtime costFn b :=
  AddWriterT.pathwiseCostAtLeast_of_hasCost h hbw

lemma usesCostAtMost_query_of_le {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) (t : spec.Domain) {b : ω}
    (ht : costFn t ≤ b) :
    HasQuery.UsesCostAtMost
      (fun [HasQuery spec (AddWriterT ω m)] =>
        HasQuery.query (spec := spec) (m := AddWriterT ω m) t)
      runtime costFn b :=
  usesCostAtMost_of_usesCostExactly
    (hasCost_withAddCost_query (runtime := runtime) (costFn := costFn) (t := t))
    ht

/-- Unit-cost specialization: every query contributes cost `1`. -/
def UsesExactlyQueries (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostExactly oa runtime (fun _ ↦ 1) n

/-- Unit-cost specialization: every query contributes cost `1`, with an upper bound. -/
def UsesAtMostQueries [HasEvalSet m]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedAboveBy (HasQuery.withUnitCost oa runtime) n

/-- Unit-cost specialization: every query contributes cost `1`, with a lower bound. -/
def UsesAtLeastQueries [HasEvalSet m]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedBelowBy (HasQuery.withUnitCost oa runtime) n

lemma usesAtMostQueries_of_usesExactlyQueries
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hnb : n ≤ b) :
    HasQuery.UsesAtMostQueries oa runtime b :=
  usesCostAtMost_of_usesCostExactly h hnb

lemma usesAtLeastQueries_of_usesExactlyQueries
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hbn : b ≤ n) :
    HasQuery.UsesAtLeastQueries oa runtime b :=
  usesCostAtLeast_of_usesCostExactly h hbn

end genericCost

section expectedCost

variable [Monad m] [HasEvalSPMF m]

/-- The expected weighted query cost of `oa`, instantiated in `runtime` and instrumented by
`costFn`.

This is the primary expectation notion for generic `HasQuery` computations. It is computed from
the additive cost marginal in the base monad's subdistribution semantics, valued by `val`.

The unit-cost query-counting notion [`HasQuery.expectedQueries`] is a specialization of this
definition with `costFn := fun _ ↦ 1` and `val := fun n ↦ (n : ENNReal)`. -/
noncomputable def expectedQueryCost {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (val : ω → ENNReal) : ENNReal :=
  AddWriterT.expectedCost (HasQuery.withAddCost oa runtime costFn) val

/-- The marginal distribution of weighted query costs induced by running `oa` in `runtime` with
query-cost function `costFn`. -/
def queryCostDist {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) : m ω :=
  AddWriterT.costs (HasQuery.withAddCost oa runtime costFn)

/-- The marginal distribution of the unit-cost query count induced by running `oa` in `runtime`. -/
abbrev queryCountDist
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryRuntime spec m) : m ℕ :=
  HasQuery.queryCostDist oa runtime (fun _ ↦ 1)

/-- Expected number of oracle queries made by `oa` when run in `runtime`, counting each query
with unit additive cost. -/
noncomputable abbrev expectedQueries
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryRuntime spec m) : ENNReal :=
  HasQuery.expectedQueryCost oa runtime (fun _ ↦ 1) (fun n ↦ (n : ENNReal))

/-- Tail-sum formula for the expected number of oracle queries made by `oa` in `runtime`:

`E[number of queries] = ∑ i, Pr[i < number of queries]`.

This is the generic `HasQuery` version of [`AddWriterT.expectedCostNat_eq_tsum_tail_probs`]. -/
lemma expectedQueries_eq_tsum_tail_probs
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryRuntime spec m) :
    HasQuery.expectedQueries oa runtime =
      ∑' i : ℕ, Pr[ fun c ↦ i < c | HasQuery.queryCountDist oa runtime ] := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost] using
    AddWriterT.expectedCostNat_eq_tsum_tail_probs (oa := HasQuery.withUnitCost oa runtime)

/-- Tail domination bounds expected query count.

If `Pr[i < number of queries] ≤ a i` for every `i`, then
`ExpectedQueries[ oa in runtime ] ≤ ∑ i, a i`. -/
lemma expectedQueries_le_tsum_of_tail_probs_le
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryRuntime spec m)
    {a : ℕ → ENNReal}
    (h : ∀ i : ℕ, Pr[ fun c ↦ i < c | HasQuery.queryCountDist oa runtime ] ≤ a i) :
    HasQuery.expectedQueries oa runtime ≤ ∑' i : ℕ, a i := by
  rw [HasQuery.expectedQueries_eq_tsum_tail_probs]
  exact ENNReal.tsum_le_tsum h

/-- Finite tail-sum formula for expected query count under a pathwise upper bound.

If `oa` uses at most `n` oracle queries in every execution, then its expected query count is the
finite sum of the probabilities that the query count exceeds `i`, for `i < n`. -/
lemma expectedQueries_eq_sum_tail_probs_of_usesAtMostQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m} {n : ℕ}
    (h : HasQuery.UsesAtMostQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime =
      ∑ i ∈ Finset.range n, Pr[ fun c ↦ i < c | HasQuery.queryCountDist oa runtime ] := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost, HasQuery.queryCountDist,
    HasQuery.withUnitCost, HasQuery.queryCostDist] using
    (AddWriterT.expectedCostNat_eq_sum_tail_probs_of_pathwiseCostAtMost
      (oa := HasQuery.withUnitCost oa runtime) h)

lemma expectedQueryCost_le_of_usesCostAtMost
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAtMost oa runtime costFn w) (hval : Monotone val) :
    HasQuery.expectedQueryCost oa runtime costFn val ≤ val w :=
  AddWriterT.expectedCost_le_of_pathwiseCostAtMost h hval

lemma expectedQueryCost_eq_tsum_outputs_of_usesCostAs
    {ω : Type} [AddMonoid ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {f : α → ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAs oa runtime costFn f) :
    HasQuery.expectedQueryCost oa runtime costFn val =
      ∑' a : α,
        Pr[= a | AddWriterT.outputs (HasQuery.withAddCost oa runtime costFn)] * val (f a) := by
  simpa [HasQuery.expectedQueryCost, HasQuery.UsesCostAs] using
    (AddWriterT.expectedCost_eq_tsum_outputs_of_costsAs
      (oa := HasQuery.withAddCost oa runtime costFn) (f := f) (val := val) h)

lemma expectedQueries_le_of_usesAtMostQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m} {n : ℕ}
    (h : HasQuery.UsesAtMostQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime ≤ n := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost] using
    (AddWriterT.expectedCost_le_of_pathwiseCostAtMost
      (oa := HasQuery.withUnitCost oa runtime) (w := n) (val := fun k ↦ (k : ENNReal)) h
      (fun a b hle ↦ by
        simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))

end expectedCost

section expectedCostPMF

variable [Monad m] [HasEvalPMF m]

lemma expectedQueryCost_ge_of_usesCostAtLeast
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAtLeast oa runtime costFn w) (hval : Monotone val) :
    val w ≤ HasQuery.expectedQueryCost oa runtime costFn val := by
  have h' : AddWriterT.PathwiseCostAtLeast (HasQuery.withAddCost oa runtime costFn) w := by
    simpa [HasQuery.UsesCostAtLeast] using h
  simpa [HasQuery.expectedQueryCost] using
    (AddWriterT.expectedCost_ge_of_pathwiseCostAtLeast
      (oa := HasQuery.withAddCost oa runtime costFn) (w := w) (val := val) h' hval)

lemma expectedQueryCost_eq_of_usesCostExactly
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hval : Monotone val) :
    HasQuery.expectedQueryCost oa runtime costFn val = val w :=
  le_antisymm
    (expectedQueryCost_le_of_usesCostAtMost
      (usesCostAtMost_of_usesCostExactly h le_rfl) hval)
    (expectedQueryCost_ge_of_usesCostAtLeast
      (usesCostAtLeast_of_usesCostExactly h le_rfl) hval)

lemma expectedQueries_ge_of_usesAtLeastQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m} {n : ℕ}
    (h : HasQuery.UsesAtLeastQueries oa runtime n) :
    (n : ENNReal) ≤ HasQuery.expectedQueries oa runtime := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost] using
    (AddWriterT.expectedCost_ge_of_pathwiseCostAtLeast
      (oa := HasQuery.withUnitCost oa runtime) (w := n) (val := fun k ↦ (k : ENNReal)) h
      (fun a b hle ↦ by
        simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))

lemma expectedQueries_eq_of_usesAtMostQueries_of_usesAtLeastQueries
    [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m} {n : ℕ}
    (hUpper : HasQuery.UsesAtMostQueries oa runtime n)
    (hLower : HasQuery.UsesAtLeastQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime = n :=
  le_antisymm
    (expectedQueries_le_of_usesAtMostQueries hUpper)
    (expectedQueries_ge_of_usesAtLeastQueries hLower)

lemma expectedQueries_eq_of_usesExactlyQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m} {n : ℕ}
    (h : HasQuery.UsesExactlyQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime = n :=
  expectedQueries_eq_of_usesAtMostQueries_of_usesAtLeastQueries
    (m := m) (oa := oa) (runtime := runtime) (n := n)
    (usesAtMostQueries_of_usesExactlyQueries h le_rfl)
    (usesAtLeastQueries_of_usesExactlyQueries h le_rfl)

end expectedCostPMF

/-- `Queries[ oa in runtime ] = n` means that the generic `HasQuery` computation `oa` makes
exactly `n` oracle queries when instantiated in `runtime` and instrumented with unit additive
cost per query.

The computation `oa` is written in direct `HasQuery` style. The notation elaborates it against
the unit-cost analysis monad induced by `runtime`, so statements can usually be written without
explicit monad annotations such as `m := AddWriterT ℕ m`. -/
syntax:max "Queries[ " term " in " term " ]" " = " term:50 : term

macro_rules
  | `(Queries[ $oa in $runtime ] = $n) =>
      `(HasQuery.UsesExactlyQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- `Queries[ oa in runtime ] ≤ n` means that every execution path of `oa` makes at most `n`
oracle queries when run in the unit-cost instrumentation of `runtime`.

This packages the common cryptographic statement “the construction uses at most `n` queries” on
top of [`HasQuery.UsesAtMostQueries`]. -/
syntax:max "Queries[ " term " in " term " ]" " ≤ " term:50 : term

macro_rules
  | `(Queries[ $oa in $runtime ] ≤ $n) =>
      `(HasQuery.UsesAtMostQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- `Queries[ oa in runtime ] ≥ n` means that every execution of `oa` in the unit-cost
instrumentation of `runtime` incurs at least `n` query-cost units.

This is less common than the exact and upper-bound forms, but it is useful for statements saying
that a construction must query the oracle at least a certain number of times. -/
syntax:max "Queries[ " term " in " term " ]" " ≥ " term:50 : term

macro_rules
  | `(Queries[ $oa in $runtime ] ≥ $n) =>
      `(HasQuery.UsesAtLeastQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- `QueryCost[ oa in runtime ] = n` is the unit-cost specialization of weighted query cost:
each oracle query contributes additive cost `1`, so the total query cost is just the number of
queries made by `oa`. -/
syntax:max "QueryCost[ " term " in " term " ]" " = " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime ] = $w) =>
      `(HasQuery.UsesExactlyQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $w)

/-- `QueryCost[ oa in runtime by costFn ] = w` means that `oa`, instantiated in `runtime` and
instrumented so that each query `t` contributes cost `costFn t`, has constant total query cost
`w`.

Use this when the cost model is not unit cost, for example when different query families or
different query shapes carry different weights. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " = " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] = $w) =>
      `(HasQuery.UsesCostExactly
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- `QueryCost[ oa in runtime ] ≤ n` is the unit-cost specialization of pathwise query-cost upper
bounds. It says that every execution of `oa` makes at most `n` oracle queries. -/
syntax:max "QueryCost[ " term " in " term " ]" " ≤ " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime ] ≤ $w) =>
      `(HasQuery.UsesAtMostQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $w)

/-- `QueryCost[ oa in runtime by costFn ] ≤ w` means that every execution path of `oa` has total
query cost bounded above by `w` under the weighting function `costFn`.

This is the weighted analogue of [`Queries[ oa in runtime ] ≤ n`]. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≤ " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] ≤ $w) =>
      `(HasQuery.UsesCostAtMost
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- `QueryCost[ oa in runtime ] ≥ n` is the unit-cost specialization of pathwise query-cost lower
bounds. It says that every execution of `oa` makes at least `n` oracle queries. -/
syntax:max "QueryCost[ " term " in " term " ]" " ≥ " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime ] ≥ $w) =>
      `(HasQuery.UsesAtLeastQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $w)

/-- `QueryCost[ oa in runtime by costFn ] ≥ w` means that every execution path of `oa` has total
query cost bounded below by `w` under the weighting function `costFn`.

This is the weighted analogue of [`Queries[ oa in runtime ] ≥ n`]. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≥ " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] ≥ $w) =>
      `(HasQuery.UsesCostAtLeast
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- `ExpectedQueryCost[ oa in runtime ]` is the expected number of oracle queries made by `oa`
when run in `runtime`, viewed as the unit-cost specialization of weighted expected query cost. -/
syntax:max "ExpectedQueryCost[ " term " in " term " ]" : term

macro_rules
  | `(ExpectedQueryCost[ $oa in $runtime ]) =>
      `(HasQuery.expectedQueryCost
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime (fun _ ↦ 1) (fun n ↦ (n : ENNReal)))

/-- `ExpectedQueryCost[ oa in runtime by costFn via val ]` is the expected weighted query cost of
`oa` when instantiated in `runtime`.

Each query `t` contributes additive cost `costFn t`, and the total cost is then valued by
`val : ω → ENNReal` before taking expectation. This is the primary expected-cost term for generic
`HasQuery` constructions. -/
syntax:max "ExpectedQueryCost[ " term " in " term " by " term " via " term " ]" : term

macro_rules
  | `(ExpectedQueryCost[ $oa in $runtime by $costFn via $val ]) =>
      `(HasQuery.expectedQueryCost
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $val)

/-- `ExpectedQueries[ oa in runtime ]` is the expected number of oracle queries made by `oa` when
run in `runtime`, with each query carrying unit additive cost.

The result is an `ℝ≥0∞` expectation, so it can be compared directly against natural-number
bounds such as `ExpectedQueries[ oa in runtime ] ≤ n`.

This is the unit-cost specialization of
[`ExpectedQueryCost[ oa in runtime by costFn via val ]`], with `costFn := fun _ ↦ 1` and
`val := fun n ↦ (n : ENNReal)`. -/
syntax:max "ExpectedQueries[ " term " in " term " ]" : term

macro_rules
  | `(ExpectedQueries[ $oa in $runtime ]) =>
      `(HasQuery.expectedQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime)

end costAccounting

end HasQuery
