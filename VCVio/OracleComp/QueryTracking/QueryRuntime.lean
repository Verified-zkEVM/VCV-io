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

end instrumentation

end QueryRuntime
