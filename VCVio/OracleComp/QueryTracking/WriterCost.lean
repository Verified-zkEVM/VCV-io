/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Monad.Map
import ToMathlib.Control.WriterT
import ToMathlib.General
import ToMathlib.Probability.ProbabilityMassFunction.TailSums
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Writer Cost Accounting

This file collects reusable `AddWriterT` facts for pathwise and expected cost reasoning.
It also equips `QueryImpl` with additive writer-cost instrumentation.
-/

open OracleSpec
open scoped BigOperators

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}

section addCost

variable [Monad m]

/-- Instrument an implementation with additive cost accumulation in an `AddWriterT` layer. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω m) :=
  QueryImpl.withCost (spec := spec) (m := m) impl
    (fun t => Multiplicative.ofAdd (costFn t))

@[simp]
lemma withAddCost_apply {ω : Type} [AddMonoid ω]
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    impl.withAddCost costFn t =
      (do AddWriterT.addTell (M := m) (costFn t); liftM (impl t)) := by
  simp [withAddCost, AddWriterT.addTell, QueryImpl.withCost]

/-- Instrument an implementation with unit additive cost for every query. -/
def withUnitCost (impl : QueryImpl spec m) :
    QueryImpl spec (AddWriterT ℕ m) :=
  impl.withAddCost (fun _ ↦ 1)

@[simp]
lemma withUnitCost_apply (impl : QueryImpl spec m) (t : spec.Domain) :
    impl.withUnitCost t =
      (do AddWriterT.addTell (M := m) 1; liftM (impl t)) := by
  simp [withUnitCost]

end addCost

end QueryImpl

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

/-- Pathwise exact cost for a unit-cost `AddWriterT` computation: every reachable execution
carries exactly `n` unit queries. -/
def QueryCostExactly (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostEqOnSupport oa n

lemma QueryCostExactly.toAbove {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) : QueryBoundedAboveBy oa n := h.atMost

lemma QueryCostExactly.toBelow {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) : QueryBoundedBelowBy oa n := h.atLeast

lemma queryCostExactly_pure [LawfulMonad m] (x : α) :
    QueryCostExactly (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostEqOnSupport_pure (m := m) (ω := ℕ) x

lemma queryCostExactly_monadLift [LawfulMonad m] (x : m α) :
    QueryCostExactly (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostEqOnSupport_monadLift (m := m) (ω := ℕ) x

lemma queryCostExactly_addTell [LawfulMonad m] (w : ℕ) :
    QueryCostExactly (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostEqOnSupport_addTell (m := m) w

lemma queryCostExactly_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ}
    (f : α → β) (h : QueryCostExactly oa n) :
    QueryCostExactly (f <$> oa) n :=
  pathwiseCostEqOnSupport_map f h

lemma queryCostExactly_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryCostExactly oa n₁) (h₂ : ∀ a, QueryCostExactly (f a) n₂) :
    QueryCostExactly (oa >>= f) (n₁ + n₂) :=
  pathwiseCostEqOnSupport_bind h₁ h₂

lemma queryCostExactly_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryCostExactly (f i) k) :
    QueryCostExactly (Fin.mOfFn n f) (n * k) :=
  ⟨queryBoundedAboveBy_fin_mOfFn (fun i => (h i).toAbove),
    queryBoundedBelowBy_fin_mOfFn (fun i => (h i).toBelow)⟩

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

lemma expectedCostNat_eq_of_queryCostExactly [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) :
    expectedCostNat oa = n :=
  le_antisymm
    (expectedCostNat_le_of_queryBoundedAboveBy h.toAbove)
    (expectedCostNat_ge_of_queryBoundedBelowBy h.toBelow)

end expectedUnitCostPMF

end AddWriterT

