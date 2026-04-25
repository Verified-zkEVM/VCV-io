/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.HasQuery.Basic
import VCVio.OracleComp.ProbComp
import ToMathlib.Control.Monad.Hom

/-!
# Morphisms of `HasQuery` Monads

This module contains the heavier `HasQuery` naturality layer.
It imports `ProbComp` and monad homomorphisms, so files that only need the
basic query capability should import `VCVio.OracleComp.HasQuery.Basic`
instead.

Use this module for proofs that a monad morphism preserves oracle queries, or
that it commutes with the canonical lift of public randomness.
-/

universe u v w x

namespace HasQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}
  {m : Type v → Type w} [Monad m] [HasQuery spec m]
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

end HasQuery
