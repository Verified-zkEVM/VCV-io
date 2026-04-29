/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Query Cost Accounting

This file defines the `HasQuery`-level accounting surface for direct-style query programs.
A direct-style program is evaluated against a concrete `QueryImpl`, and query-cost statements
are phrased by running that implementation through the writer-cost instrumentation from
`WriterCost.lean`.
-/

open OracleSpec
open scoped BigOperators

namespace HasQuery

section programInstantiation

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}

/-- A direct-style computation parameterized by an oracle-query capability. -/
abbrev Program (spec : OracleSpec ι) (m : Type → Type*) (α : Type) :=
  [HasQuery spec m] → m α

namespace Program

/-- Evaluate a direct-style query program against a concrete implementation. -/
def eval (oa : Program spec m α) (impl : QueryImpl spec m) : m α := by
  letI := impl.toHasQuery
  exact oa

section instrumentation

variable [Monad m]

/-- Evaluate a direct-style query program against an additive-cost instrumentation of `impl`. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (oa : Program spec (AddWriterT ω m) α)
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) : AddWriterT ω m α := by
  letI := (impl.withAddCost costFn).toHasQuery
  exact oa

/-- Evaluate a direct-style query program against the unit-cost instrumentation of `impl`. -/
def withUnitCost (oa : Program spec (AddWriterT ℕ m) α)
    (impl : QueryImpl spec m) : AddWriterT ℕ m α := by
  letI := impl.withUnitCost.toHasQuery
  exact oa

end instrumentation

end Program
end programInstantiation

section queryBounds

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}
variable [Monad m] [LawfulMonad m]

lemma hasCost_withAddCost_query {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    Cost[
      HasQuery.Program.withAddCost
        (fun [HasQuery spec (AddWriterT ω m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ω m) t)
        runtime costFn
    ] = costFn t := by
  change Cost[runtime.withAddCost costFn t] = costFn t
  rw [QueryImpl.withAddCost_apply, AddWriterT.hasCost_iff]
  simp [AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell]

lemma queryBoundedAboveBy_withUnitCost_query
    [HasEvalSet m]
    (runtime : QueryImpl spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedAboveBy
      (HasQuery.Program.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  change AddWriterT.QueryBoundedAboveBy (runtime.withUnitCost t) 1
  rw [QueryImpl.withUnitCost_apply]
  apply AddWriterT.queryBoundedAboveBy_bind (n₁ := 1) (n₂ := 0)
  · exact AddWriterT.queryBoundedAboveBy_addTell 1
  · intro _
    exact AddWriterT.queryBoundedAboveBy_monadLift (runtime t)

lemma queryBoundedBelowBy_withUnitCost_query
    [HasEvalSet m]
    (runtime : QueryImpl spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedBelowBy
      (HasQuery.Program.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  change AddWriterT.QueryBoundedBelowBy (runtime.withUnitCost t) 1
  rw [QueryImpl.withUnitCost_apply]
  apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 1) (n₂ := 0)
  · exact AddWriterT.queryBoundedBelowBy_addTell 1
  · intro _
    exact AddWriterT.queryBoundedBelowBy_monadLift (runtime t)

lemma queryCostExactly_withUnitCost_query
    [HasEvalSet m]
    (runtime : QueryImpl spec m) (t : spec.Domain) :
    AddWriterT.QueryCostExactly
      (HasQuery.Program.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 :=
  ⟨queryBoundedAboveBy_withUnitCost_query runtime t,
    queryBoundedBelowBy_withUnitCost_query runtime t⟩

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
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (f : α → ω) : Prop :=
  AddWriterT.CostsAs (HasQuery.Program.withAddCost oa runtime costFn) f

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs constant cost `w`. -/
def UsesCostExactly {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  Cost[ HasQuery.Program.withAddCost oa runtime costFn ] = w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at most `w` on
every execution path. This is a semantic support bound, not merely an output-indexed cost
description. -/
def UsesCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.PathwiseCostAtMost (HasQuery.Program.withAddCost oa runtime costFn) w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at least `w` on
every execution path. -/
def UsesCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.PathwiseCostAtLeast (HasQuery.Program.withAddCost oa runtime costFn) w

lemma usesCostAtMost_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hwb : w ≤ b) :
    HasQuery.UsesCostAtMost oa runtime costFn b :=
  AddWriterT.pathwiseCostAtMost_of_hasCost h hwb

lemma usesCostAtLeast_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hbw : b ≤ w) :
    HasQuery.UsesCostAtLeast oa runtime costFn b :=
  AddWriterT.pathwiseCostAtLeast_of_hasCost h hbw

lemma usesCostAtMost_query_of_le {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    (runtime : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain) {b : ω}
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
    (runtime : QueryImpl spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostExactly oa runtime (fun _ ↦ 1) n

/-- Unit-cost specialization: every query contributes cost `1`, with an upper bound. -/
def UsesAtMostQueries [HasEvalSet m]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedAboveBy (HasQuery.Program.withUnitCost oa runtime) n

/-- Unit-cost specialization: every query contributes cost `1`, with a lower bound. -/
def UsesAtLeastQueries [HasEvalSet m]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedBelowBy (HasQuery.Program.withUnitCost oa runtime) n

lemma usesAtMostQueries_of_usesExactlyQueries
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hnb : n ≤ b) :
    HasQuery.UsesAtMostQueries oa runtime b :=
  usesCostAtMost_of_usesCostExactly h hnb

lemma usesAtLeastQueries_of_usesExactlyQueries
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m}
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
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (val : ω → ENNReal) : ENNReal :=
  AddWriterT.expectedCost (HasQuery.Program.withAddCost oa runtime costFn) val

/-- The marginal distribution of weighted query costs induced by running `oa` in `runtime` with
query-cost function `costFn`. -/
def queryCostDist {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) : m ω :=
  AddWriterT.costs (HasQuery.Program.withAddCost oa runtime costFn)

/-- The marginal distribution of the unit-cost query count induced by running `oa` in `runtime`. -/
abbrev queryCountDist
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryImpl spec m) : m ℕ :=
  HasQuery.queryCostDist oa runtime (fun _ ↦ 1)

/-- Expected number of oracle queries made by `oa` when run in `runtime`, counting each query
with unit additive cost. -/
noncomputable abbrev expectedQueries
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryImpl spec m) : ENNReal :=
  HasQuery.expectedQueryCost oa runtime (fun _ ↦ 1) (fun n ↦ (n : ENNReal))

/-- Tail-sum formula for the expected number of oracle queries made by `oa` in `runtime`:

`E[number of queries] = ∑ i, Pr[i < number of queries]`.

This is the generic `HasQuery` version of [`AddWriterT.expectedCostNat_eq_tsum_tail_probs`]. -/
lemma expectedQueries_eq_tsum_tail_probs
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryImpl spec m) :
    HasQuery.expectedQueries oa runtime =
      ∑' i : ℕ, Pr[ fun c ↦ i < c | HasQuery.queryCountDist oa runtime ] := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost] using
    AddWriterT.expectedCostNat_eq_tsum_tail_probs (oa := HasQuery.Program.withUnitCost oa runtime)

/-- Tail domination bounds expected query count.

If `Pr[i < number of queries] ≤ a i` for every `i`, then
`ExpectedQueries[ oa in runtime ] ≤ ∑ i, a i`. -/
lemma expectedQueries_le_tsum_of_tail_probs_le
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryImpl spec m)
    {a : ℕ → ENNReal}
    (h : ∀ i : ℕ, Pr[ fun c ↦ i < c | HasQuery.queryCountDist oa runtime ] ≤ a i) :
    HasQuery.expectedQueries oa runtime ≤ ∑' i : ℕ, a i := by
  rw [HasQuery.expectedQueries_eq_tsum_tail_probs]
  exact ENNReal.tsum_le_tsum h

/-- Finite tail-sum formula for expected query count under a pathwise upper bound.

If `oa` uses at most `n` oracle queries in every execution, then its expected query count is the
finite sum of the probabilities that the query count exceeds `i`, for `i < n`. -/
lemma expectedQueries_eq_sum_tail_probs_of_usesAtMostQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesAtMostQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime =
      ∑ i ∈ Finset.range n, Pr[ fun c ↦ i < c | HasQuery.queryCountDist oa runtime ] := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost, HasQuery.queryCountDist,
    HasQuery.Program.withUnitCost, HasQuery.queryCostDist] using
    (AddWriterT.expectedCostNat_eq_sum_tail_probs_of_pathwiseCostAtMost
      (oa := HasQuery.Program.withUnitCost oa runtime) h)

lemma expectedQueryCost_le_of_usesCostAtMost
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAtMost oa runtime costFn w) (hval : Monotone val) :
    HasQuery.expectedQueryCost oa runtime costFn val ≤ val w :=
  AddWriterT.expectedCost_le_of_pathwiseCostAtMost h hval

lemma expectedQueryCost_eq_tsum_outputs_of_usesCostAs
    {ω : Type} [AddMonoid ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {f : α → ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAs oa runtime costFn f) :
    HasQuery.expectedQueryCost oa runtime costFn val =
      ∑' a : α,
        Pr[= a |
          AddWriterT.outputs (HasQuery.Program.withAddCost oa runtime costFn)] * val (f a) := by
  simpa [HasQuery.expectedQueryCost, HasQuery.UsesCostAs] using
    (AddWriterT.expectedCost_eq_tsum_outputs_of_costsAs
      (oa := HasQuery.Program.withAddCost oa runtime costFn) (f := f) (val := val) h)

lemma expectedQueries_le_of_usesAtMostQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesAtMostQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime ≤ n := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost] using
    (AddWriterT.expectedCost_le_of_pathwiseCostAtMost
      (oa := HasQuery.Program.withUnitCost oa runtime) (w := n) (val := fun k ↦ (k : ENNReal)) h
      (fun a b hle ↦ by
        simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))

end expectedCost

section expectedCostPMF

variable [Monad m] [HasEvalPMF m]

lemma expectedQueryCost_ge_of_usesCostAtLeast
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAtLeast oa runtime costFn w) (hval : Monotone val) :
    val w ≤ HasQuery.expectedQueryCost oa runtime costFn val := by
  have h' : AddWriterT.PathwiseCostAtLeast (HasQuery.Program.withAddCost oa runtime costFn) w := by
    simpa [HasQuery.UsesCostAtLeast] using h
  simpa [HasQuery.expectedQueryCost] using
    (AddWriterT.expectedCost_ge_of_pathwiseCostAtLeast
      (oa := HasQuery.Program.withAddCost oa runtime costFn) (w := w) (val := val) h' hval)

lemma expectedQueryCost_eq_of_usesCostExactly
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hval : Monotone val) :
    HasQuery.expectedQueryCost oa runtime costFn val = val w :=
  le_antisymm
    (expectedQueryCost_le_of_usesCostAtMost
      (usesCostAtMost_of_usesCostExactly h le_rfl) hval)
    (expectedQueryCost_ge_of_usesCostAtLeast
      (usesCostAtLeast_of_usesCostExactly h le_rfl) hval)

lemma expectedQueries_ge_of_usesAtLeastQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesAtLeastQueries oa runtime n) :
    (n : ENNReal) ≤ HasQuery.expectedQueries oa runtime := by
  simpa [HasQuery.expectedQueries, HasQuery.expectedQueryCost] using
    (AddWriterT.expectedCost_ge_of_pathwiseCostAtLeast
      (oa := HasQuery.Program.withUnitCost oa runtime) (w := n) (val := fun k ↦ (k : ENNReal)) h
      (fun a b hle ↦ by
        simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))

lemma expectedQueries_eq_of_usesAtMostQueries_of_usesAtLeastQueries
    [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (hUpper : HasQuery.UsesAtMostQueries oa runtime n)
    (hLower : HasQuery.UsesAtLeastQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime = n :=
  le_antisymm
    (expectedQueries_le_of_usesAtMostQueries hUpper)
    (expectedQueries_ge_of_usesAtLeastQueries hLower)

lemma expectedQueries_eq_of_usesExactlyQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
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
