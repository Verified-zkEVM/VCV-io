/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import ToMathlib.Control.Monad.Hom

/-!
# Bundled Lifts from `ProbComp`

This file packages the "public randomness" capability separately from denotational semantics.

Many crypto constructions need two orthogonal pieces of structure on their ambient monad `m`:

1. a way to *observe* computations probabilistically (`SPMFSemantics` / `PMFSemantics`)
2. a way to *inject* plain probabilistic sampling into `m`

This file packages the second capability as a bundled monad homomorphism `ProbComp →ᵐ m`, so it
can be carried independently of whatever denotational semantics the construction uses.
-/

universe v

/-- Bundled way to lift plain probabilistic computations into an ambient monad `m`.

Intuitively, this is the capability "sample fresh public randomness inside `m`". We package it as
a monad homomorphism so it composes lawfully with `pure` and `bind`. -/
structure ProbCompLift (m : Type → Type v) [Monad m] where
  /-- Inject a plain `ProbComp` computation into `m`. -/
  liftProbComp : ProbComp →ᵐ m

namespace ProbCompLift

/-- Build a bundled `ProbCompLift` from an existing lawful `MonadLiftT ProbComp m` instance. -/
def ofMonadLift (m : Type → Type v) [Monad m]
    [MonadLiftT ProbComp m] [LawfulMonadLiftT ProbComp m] : ProbCompLift m where
  liftProbComp := MonadHom.ofLift ProbComp m

/-- The identity lift on `ProbComp` itself. -/
def id : ProbCompLift ProbComp where
  liftProbComp := MonadHom.id ProbComp

end ProbCompLift
