/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.CountingOracle

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

/-- Bundled implementation of the oracle family `spec` in the ambient monad `m`. -/
structure QueryRuntime {ι : Type} (spec : OracleSpec ι) (m : Type → Type*) where
  /-- Concrete implementation of each query in the family `spec`. -/
  impl : QueryImpl spec m

namespace QueryRuntime

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}

/-- View a bundled query runtime as the corresponding `HasQuery` capability. -/
def toHasQuery (runtime : QueryRuntime spec m) : HasQuery spec m :=
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

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at most `w`. -/
def UsesCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  Cost[ HasQuery.withAddCost oa runtime costFn ] ≤ w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at least `w`. -/
def UsesCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  Cost[ HasQuery.withAddCost oa runtime costFn ] ≥ w

lemma usesCostAtMost_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hwb : w ≤ b) :
    HasQuery.UsesCostAtMost oa runtime costFn b := by
  exact AddWriterT.costAtMost_of_hasCost h hwb

lemma usesCostAtLeast_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hbw : b ≤ w) :
    HasQuery.UsesCostAtLeast oa runtime costFn b := by
  exact AddWriterT.costAtLeast_of_hasCost h hbw

/-- Unit-cost specialization: every query contributes cost `1`. -/
def UsesExactlyQueries (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostExactly oa runtime (fun _ ↦ 1) n

/-- Unit-cost specialization: every query contributes cost `1`, with an upper bound. -/
def UsesAtMostQueries (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostAtMost oa runtime (fun _ ↦ 1) n

/-- Unit-cost specialization: every query contributes cost `1`, with a lower bound. -/
def UsesAtLeastQueries (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostAtLeast oa runtime (fun _ ↦ 1) n

lemma usesAtMostQueries_of_usesExactlyQueries
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hnb : n ≤ b) :
    HasQuery.UsesAtMostQueries oa runtime b :=
  usesCostAtMost_of_usesCostExactly h hnb

lemma usesAtLeastQueries_of_usesExactlyQueries
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hbn : b ≤ n) :
    HasQuery.UsesAtLeastQueries oa runtime b :=
  usesCostAtLeast_of_usesCostExactly h hbn

end genericCost

/-- Human-readable notation for exact query-count statements in the unit-cost model. -/
syntax:max "Queries[ " term " in " term " ]" " = " term : term

macro_rules
  | `(Queries[ $oa in $runtime ] = $n) =>
      `(HasQuery.UsesExactlyQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- Human-readable notation for upper-bound query-count statements in the unit-cost model. -/
syntax:max "Queries[ " term " in " term " ]" " ≤ " term : term

macro_rules
  | `(Queries[ $oa in $runtime ] ≤ $n) =>
      `(HasQuery.UsesAtMostQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- Human-readable notation for lower-bound query-count statements in the unit-cost model. -/
syntax:max "Queries[ " term " in " term " ]" " ≥ " term : term

macro_rules
  | `(Queries[ $oa in $runtime ] ≥ $n) =>
      `(HasQuery.UsesAtLeastQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- Human-readable notation for exact additive-cost statements under a named cost function. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " = " term : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] = $w) =>
      `(HasQuery.UsesCostExactly
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- Human-readable notation for additive-cost upper bounds under a named cost function. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≤ " term : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] ≤ $w) =>
      `(HasQuery.UsesCostAtMost
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- Human-readable notation for additive-cost lower bounds under a named cost function. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≥ " term : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] ≥ $w) =>
      `(HasQuery.UsesCostAtLeast
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

end costAccounting

end HasQuery
