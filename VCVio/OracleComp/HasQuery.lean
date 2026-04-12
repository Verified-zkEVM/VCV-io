/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.OracleComp.ProbComp
import ToMathlib.Control.Monad.Hom

/-!
# Generic Oracle Query Capability

This file defines `HasQuery spec m`, a thin capability interface for monads that can issue
queries to an oracle family `spec`.

`OracleComp spec` remains the canonical free syntax for explicit oracle computations, structural
induction, and query-bound reasoning. `HasQuery` is the lighter interface used when a
construction only needs to *ask* oracle queries, without reifying or analyzing the query syntax.

The key design choice is that `HasQuery` is just a facade over the existing lifting story:
the primitive single-query syntax `OracleQuery spec` is itself a `HasQuery spec` instance, and
any monad that supports `MonadLiftT (OracleQuery spec) m` automatically gets a `HasQuery spec m`
instance as well. As a result, the capability composes with the existing `SubSpec` coercions
and with standard transformer lifts such as `StateT`, `ReaderT`, `ExceptT`, and `WriterT`.
-/

open OracleSpec

universe u v w x

/-- Capability to issue queries to the oracle family `spec` inside the ambient monad `m`. -/
class HasQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) where
  /-- Issue a single oracle query. -/
  query : (t : spec.Domain) → m (spec.Range t)

namespace QueryImpl

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w}

/-- View a concrete query implementation as query capability in the same monad. This is useful
when instantiating a generic `HasQuery` construction directly inside an analysis monad such as
`StateT σ ProbComp` or `WriterT ω (OracleComp spec)`. -/
@[reducible] def toHasQuery (impl : QueryImpl spec m) : HasQuery spec m where
  query := impl

@[simp]
lemma toHasQuery_query (impl : QueryImpl spec m) (t : spec.Domain) :
    (toHasQuery (spec := spec) (m := m) impl).query t = impl t := rfl

end QueryImpl
namespace HasQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w}

/-- The primitive single-query syntax `OracleQuery spec` has the obvious query capability. -/
instance instOracleQuery : HasQuery spec (OracleQuery spec) where
  query := OracleQuery.query

@[simp]
lemma instOracleQuery_query (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := OracleQuery spec) t =
      OracleQuery.query (spec := spec) t :=
  rfl

/-- Repackage `HasQuery` as a `QueryImpl`, for APIs that still consume explicit oracle
implementations. -/
def toQueryImpl [HasQuery spec m] : QueryImpl spec m :=
  fun t => HasQuery.query t

@[simp]
lemma toQueryImpl_apply [HasQuery spec m] (t : spec.Domain) :
    toQueryImpl (spec := spec) (m := m) t = HasQuery.query (spec := spec) (m := m) t := rfl

/-- Any lawful lift of `OracleQuery spec` into `m` gives query capability in `m`. This is the
main bridge that makes `HasQuery` compose with `SubSpec` lifts and standard transformer lifts. -/
instance (priority := low) instOfMonadLift [MonadLiftT (OracleQuery spec) m] :
    HasQuery spec m where
  query t := liftM (OracleQuery.query (spec := spec) t)

@[simp]
lemma instOfMonadLift_query [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := m) t =
      liftM (OracleQuery.query (spec := spec) t) :=
  rfl

section Morphisms

variable [Monad m] [HasQuery spec m]
  {n : Type v → Type x} [Monad n] [HasQuery spec n]

/-- A `QueryHom spec m n` is a monad morphism `m →ᵐ n` that also preserves the distinguished
oracle-query capability for `spec`. This is the right notion of morphism for proving that a
construction generic over `HasQuery spec` is natural in the chosen oracle semantics. -/
structure QueryHom (spec : OracleSpec.{u, v} ι)
    (m : Type v → Type w) [Monad m] [HasQuery spec m]
    (n : Type v → Type x) [Monad n] [HasQuery spec n]
    extends m →ᵐ n where
  map_query' (t : spec.Domain) :
    toFun _ (HasQuery.query (spec := spec) (m := m) t) =
      HasQuery.query (spec := spec) (m := n) t

/-- A monad morphism preserves public randomness when it commutes with the distinguished lifting
of plain probabilistic computations into the ambient monad. -/
def PreservesProbCompLift
    {m : Type → Type w} [Monad m] [MonadLiftT ProbComp m]
    {n : Type → Type x} [Monad n] [MonadLiftT ProbComp n]
    (F : m →ᵐ n) : Prop :=
  ∀ {α : Type} (oa : ProbComp α), F (liftM oa : m α) = (liftM oa : n α)

@[simp]
lemma map_query (F : QueryHom spec m n) (t : spec.Domain) :
    F.toMonadHom (HasQuery.query (spec := spec) (m := m) t) =
      HasQuery.query (spec := spec) (m := n) t :=
  F.map_query' t

end Morphisms
end HasQuery
