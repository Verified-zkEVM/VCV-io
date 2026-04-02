/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.Append
import ToMathlib.Control.Monad.Hom

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

universe u v w x

/-- Capability to issue queries to the oracle family `spec` inside the ambient monad `m`. -/
class MonadQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) [Monad m] where
  /-- Issue a single oracle query. -/
  query : (t : spec.Domain) → m (spec.Range t)

namespace QueryImpl

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w} [Monad m]

/-- View a concrete query implementation as query capability in the same monad. This is useful
when instantiating a generic `MonadQuery` construction directly inside an analysis monad such as
`StateT σ ProbComp` or `WriterT ω (OracleComp spec)`. -/
def toMonadQuery (impl : QueryImpl spec m) : MonadQuery spec m where
  query := impl

@[simp]
lemma toMonadQuery_query (impl : QueryImpl spec m) (t : spec.Domain) :
    (toMonadQuery (spec := spec) (m := m) impl).query t = impl t := rfl

end QueryImpl

namespace MonadQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}
  {m : Type v → Type w} [Monad m]

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

section Morphisms

variable [MonadQuery spec m]
  {n : Type v → Type x} [Monad n] [MonadQuery spec n]

/-- A `QueryHom spec m n` is a monad morphism `m →ᵐ n` that also preserves the distinguished
oracle-query capability for `spec`. This is the right notion of morphism for proving that a
construction generic over `MonadQuery spec` is natural in the chosen oracle semantics. -/
structure QueryHom (spec : OracleSpec.{u, v} ι)
    (m : Type v → Type w) [Monad m] [MonadQuery spec m]
    (n : Type v → Type x) [Monad n] [MonadQuery spec n]
    extends m →ᵐ n where
  map_query' (t : spec.Domain) :
    toFun _ (MonadQuery.query (spec := spec) (m := m) t) =
      MonadQuery.query (spec := spec) (m := n) t

attribute [simp] QueryHom.map_query'

/-- A monad morphism preserves public randomness when it commutes with the distinguished lifting
of plain probabilistic computations into the ambient monad. -/
def PreservesProbCompLift
    {m : Type → Type w} [Monad m] [MonadLiftT ProbComp m]
    {n : Type → Type x} [Monad n] [MonadLiftT ProbComp n]
    (F : m →ᵐ n) : Prop :=
  ∀ {α : Type} (oa : ProbComp α), F (liftM oa : m α) = (liftM oa : n α)

@[simp]
lemma map_query (F : QueryHom spec m n) (t : spec.Domain) :
    F.toMonadHom (MonadQuery.query (spec := spec) (m := m) t) =
      MonadQuery.query (spec := spec) (m := n) t :=
  F.map_query' t

end Morphisms

end MonadQuery
