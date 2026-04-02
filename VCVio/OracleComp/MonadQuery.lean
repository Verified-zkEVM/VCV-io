/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.QueryImpl

/-!
# Generic Oracle Query Capability

This file defines `MonadQuery spec m`, a thin capability interface for monads that can issue
queries to an oracle family `spec`.

`OracleComp spec` remains the canonical free syntax for explicit oracle computations, structural
induction, and query-bound reasoning. `MonadQuery` is the lighter interface used when a
construction only needs to *ask* oracle queries, without reifying or analyzing the query syntax.

The key design choice is that `MonadQuery` is just a facade over the existing lifting story:
any monad that supports `MonadLiftT (OracleQuery spec) m` automatically gets a `MonadQuery spec m`
instance. As a result, the capability composes with the existing `SubSpec` coercions and with
standard transformer lifts such as `StateT`, `ReaderT`, `ExceptT`, and `WriterT`.
-/

open OracleSpec

universe u v w

/-- Capability to issue queries to the oracle family `spec` inside the ambient monad `m`. -/
class MonadQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) [Monad m] where
  /-- Issue a single oracle query. -/
  query : (t : spec.Domain) → m (spec.Range t)

namespace MonadQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w} [Monad m]

/-- Repackage `MonadQuery` as a `QueryImpl`, for APIs that still consume explicit oracle
implementations. -/
def toQueryImpl [MonadQuery spec m] : QueryImpl spec m :=
  fun t => MonadQuery.query t

@[simp]
lemma toQueryImpl_apply [MonadQuery spec m] (t : spec.Domain) :
    toQueryImpl (spec := spec) (m := m) t = MonadQuery.query (spec := spec) (m := m) t := rfl

/-- Any lawful lift of `OracleQuery spec` into `m` gives query capability in `m`. This is the
main bridge that makes `MonadQuery` compose with `SubSpec` lifts and standard transformer lifts. -/
instance (priority := low) instOfMonadLift [MonadLiftT (OracleQuery spec) m] :
    MonadQuery spec m where
  query t := liftM (OracleQuery.query (spec := spec) t)

@[simp]
lemma instOfMonadLift_query [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) :
    (instOfMonadLift (spec := spec) (m := m)).query t =
      liftM (OracleQuery.query (spec := spec) t) :=
  rfl

@[simp]
lemma query_eq_liftM_query [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) :
    @MonadQuery.query ι spec m ‹Monad m› (instOfMonadLift (spec := spec) (m := m)) t =
      liftM (OracleQuery.query (spec := spec) t) :=
  rfl

end MonadQuery
