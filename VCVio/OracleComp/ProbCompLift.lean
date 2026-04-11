/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Defs.Semantics
import ToMathlib.Control.Monad.Hom

/-!
# Bundled Lifts from `ProbComp`

This file packages the "public randomness" capability separately from denotational semantics.

Many crypto constructions need two orthogonal pieces of structure on their ambient monad `m`:

1. a way to *observe* computations probabilistically (`SPMFSemantics` / `PMFSemantics`)
2. a way to *inject* plain probabilistic sampling into `m`

This file packages the second capability as a bundled monad homomorphism `ProbComp →ᵐ m`, so it
can be carried independently of whatever denotational semantics the construction uses. It also
defines `ProbCompRuntime`, the common crypto-facing bundle that pairs public-randomness lifting
with bundled `SPMF` semantics for an ambient monad.
-/

universe v w

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

/-- Common runtime bundle for crypto games in an ambient monad `m`.

This packages the two capabilities that security experiments usually need together:

1. `SPMFSemantics m` to observe the experiment as a Boolean subdistribution.
2. `ProbCompLift m` to sample fresh public randomness inside `m`.

The bundle is kept separate from the core scheme definitions so that executable scheme data does
not become noncomputable merely by carrying denotational semantics. -/
structure ProbCompRuntime (m : Type → Type v) [Monad m] where
  /-- Bundled subprobabilistic semantics for the ambient monad. -/
  toSPMFSemantics : SPMFSemantics.{0, v, w} m
  /-- Bundled injection of plain probabilistic sampling into the ambient monad. -/
  toProbCompLift : ProbCompLift m

namespace ProbCompRuntime

variable {m : Type → Type v} [Monad m] {α : Type}

/-- Observe an ambient computation as an `SPMF` using the runtime's bundled semantics. -/
def evalDist (runtime : ProbCompRuntime m) (mx : m α) : SPMF α :=
  runtime.toSPMFSemantics.evalDist mx

/-- Failure probability of an ambient computation under the runtime's bundled semantics. -/
def probFailure (runtime : ProbCompRuntime m) (mx : m α) : ENNReal :=
  runtime.toSPMFSemantics.probFailure mx

/-- Lift a plain `ProbComp` computation into the ambient monad using the runtime's public
randomness capability. -/
def liftProbComp (runtime : ProbCompRuntime m) : ProbComp →ᵐ m :=
  runtime.toProbCompLift.liftProbComp

/-- Canonical runtime for `ProbComp` itself. -/
noncomputable def probComp : ProbCompRuntime ProbComp where
  toSPMFSemantics := SPMFSemantics.ofHasEvalSPMF ProbComp
  toProbCompLift := ProbCompLift.id

end ProbCompRuntime
