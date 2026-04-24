/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.OracleQuery

/-!
# `HasQuery` capability class

Defines the lightweight `HasQuery spec m` capability interface and the two
canonical instances (the primitive query syntax and the `MonadLiftT`-driven
ambient instance).

This file lives upstream of `VCVio.OracleComp.OracleComp` so that the
`export HasQuery (query)` line below makes the bare identifier `query`
resolve to `HasQuery.query` everywhere downstream (rather than the
`protected` `OracleSpec.query`). Downstream code that wants the primitive
`OracleQuery spec _` form should write `spec.query t` or
`OracleSpec.query t` explicitly.

The heavier `QueryHom`, `PreservesProbCompLift`, and `QueryImpl` bridges
live in `VCVio.OracleComp.HasQuery`, which depends on `QueryImpl` and
`ProbComp`.
-/

universe u v w

/-- Capability to issue queries to the oracle family `spec` inside the ambient monad `m`. -/
class HasQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) where
  /-- Issue a single oracle query. -/
  query : (t : spec.Domain) → m (spec.Range t)

-- Re-export `HasQuery.query` as the bare identifier `query`. With
-- `OracleSpec.query` marked `protected`, the bare `query` resolves to
-- `HasQuery.query`, which yields a value in the ambient monad `m` and lets
-- Lean recover `spec` from the expected return type.
export HasQuery (query)

namespace HasQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w}

/-- The primitive single-query syntax `OracleQuery spec` has the obvious query capability. -/
instance instOracleQuery : HasQuery spec (OracleQuery spec) where
  query := OracleSpec.query

@[simp]
lemma instOracleQuery_query (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := OracleQuery spec) t =
      OracleSpec.query t :=
  rfl

/-- Any lawful lift of `OracleQuery spec` into `m` gives query capability in `m`. This is the
main bridge that makes `HasQuery` compose with `SubSpec` lifts and standard transformer lifts. -/
instance (priority := low) instOfMonadLift [MonadLiftT (OracleQuery spec) m] :
    HasQuery spec m where
  query t := liftM (OracleSpec.query t)

@[simp]
lemma instOfMonadLift_query [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := m) t =
      liftM (OracleSpec.query t) :=
  rfl

end HasQuery
