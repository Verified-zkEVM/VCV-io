/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Bundled Probability Semantics

This file defines bundled semantics for monads that factor through an internal semantic monad
before being externally observed.

The existing classes `HasEvalSPMF` and `HasEvalPMF` say that a monad already *has* an
`SPMF` or `PMF` denotation. That is convenient when the monad itself is the semantic object,
but it is too rigid for constructions whose natural semantics has hidden internal structure.

The main new idea here is to split semantics into two stages:

1. `interpret`: map computations in the user-facing monad into an internal semantic monad
2. `observe`: forget the internal bookkeeping and expose only the probabilistic behavior

This is useful when the internal semantics carries extra state or other information that should
not be visible at the final security-game interface. Typical examples include:

- oracle caches modeled by hidden state
- auxiliary logs or bookkeeping used only for the semantics
- semantic monads that are more structured than the surface monad being specified

The generic factoring pattern is captured by `SemanticsVia`. The probability-specific notions
`SPMFSemantics` and `PMFSemantics` are then specializations where the observation target is
respectively `SPMF` or `PMF`.

These semantics are deliberately *bundled* rather than typeclasses so that a construction can
carry its intended semantics locally without forcing a single global instance on the ambient
monad.
-/

/-!
## Design Note

The fields are intentionally minimal:

- `Sem` is the internal semantic monad
- `interpret` embeds the surface computation into that internal semantics
- `observe` discards the internal structure and returns the external semantic object

Notably, observation is not required to be a monad morphism. That is important: running a
stateful semantics from a fixed initial state is a perfectly reasonable observation, but it is
not itself a monad homomorphism. The bundling here leaves room for that style of semantics.
-/

universe u v w x

/-- Bundled semantics for `m` obtained by factoring through an internal semantic monad.

`SemanticsVia m Obs` packages the very general pattern:

1. interpret a computation in the surface monad `m` into some internal semantic monad `Sem`
2. observe the resulting internal computation as an external semantic object `Obs α`

The observation target `Obs` is intentionally generic. In this file we mainly care about the
cases `Obs = SPMF` and `Obs = PMF`, but the same factoring pattern could later be reused for
other kinds of denotational semantics such as sets of outcomes, traces, or quantum objects.

The important asymmetry is that `interpret` is required to be a monad morphism, while `observe`
is not. This lets us model semantics where running the internal computation requires fixing hidden
state or discarding auxiliary structure before exposing the final denotation. -/
structure SemanticsVia
    (m : Type u → Type v) [Monad m] (Obs : Type u → Type x) where
  /-- Internal monad used to give denotational meaning to computations in `m`. -/
  Sem : Type u → Type w
  /-- Monad structure on the internal semantic monad. -/
  instMonadSem : Monad Sem
  /-- Interpret a surface computation into the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe the internal semantic computation as an external semantic object, forgetting any
  hidden internal structure. -/
  observe : {α : Type u} → Sem α → Obs α

attribute [instance] SemanticsVia.instMonadSem

namespace SemanticsVia

variable {m : Type u → Type v} [Monad m] {Obs : Type u → Type x} {α : Type u}

/-- The external denotation of `mx` under a bundled semantics factorization. -/
def denote (sem : SemanticsVia m Obs) (mx : m α) : Obs α :=
  sem.observe (sem.interpret mx)

end SemanticsVia

/-- Bundled subprobabilistic semantics for a monad `m`.

This is the specialization of `SemanticsVia` where the external observation target is `SPMF`.
Computations in `m` are therefore interpreted as subprobability distributions on outputs, possibly
with failure mass. -/
structure SPMFSemantics (m : Type u → Type v) [Monad m]
    extends SemanticsVia m SPMF

/-- The internal semantic monad of an `SPMFSemantics` carries the inherited monad structure. -/
instance {m : Type u → Type v} [Monad m] (sem : SPMFSemantics m) : Monad sem.Sem :=
  sem.toSemanticsVia.instMonadSem

namespace SPMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The observation map of an `SPMFSemantics`, specialized to `SPMF`. -/
def observeSPMF (sem : SPMFSemantics m) : {α : Type u} → sem.Sem α → SPMF α :=
  sem.observe

/-- The subdistribution denoted by `mx` under the bundled semantics `sem`.

This first moves `mx` into the internal semantic monad via `interpret`, and then collapses the
internal structure to the externally visible `SPMF` via `observeSPMF`. -/
def evalDist (sem : SPMFSemantics m) (mx : m α) : SPMF α :=
  sem.toSemanticsVia.denote mx

/-- The probability that `mx` fails to return a value under `sem`.

Since `SPMFSemantics` is subprobabilistic, failure is represented by the missing mass of the
resulting `SPMF`, equivalently the probability of `none` in the underlying `Option`-valued PMF. -/
def probFailure (sem : SPMFSemantics m) (mx : m α) : ENNReal :=
  (sem.evalDist mx).run none

/-- Failure probability under an `SPMFSemantics` is always at most `1`. -/
@[simp]
lemma probFailure_le_one (sem : SPMFSemantics m) (mx : m α) :
    sem.probFailure mx ≤ 1 :=
  PMF.coe_le_one (sem.evalDist mx) none

/-- Package an ordinary `HasEvalSPMF` instance as a bundled `SPMFSemantics`.

This is the bridge back to the old style where the surface monad itself already carries its
subprobabilistic denotation. In that case the internal semantic monad is just `m` itself, the
interpreter is the identity monad morphism, and observation is `HasEvalSPMF.toSPMF`. -/
protected def ofHasEvalSPMF (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    SPMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx => HasEvalSPMF.toSPMF mx

end SPMFSemantics

/-- Bundled total probabilistic semantics for a monad `m`.

This is the specialization of `SemanticsVia` where the external observation target is `PMF`.
There is therefore no failure mass in the resulting denotation. -/
structure PMFSemantics (m : Type u → Type v) [Monad m]
    extends SemanticsVia m PMF

/-- The internal semantic monad of a `PMFSemantics` carries the inherited monad structure. -/
instance {m : Type u → Type v} [Monad m] (sem : PMFSemantics m) : Monad sem.Sem :=
  sem.toSemanticsVia.instMonadSem

namespace PMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The observation map of a `PMFSemantics`, specialized to `PMF`. -/
def observePMF (sem : PMFSemantics m) : {α : Type u} → sem.Sem α → PMF α :=
  sem.observe

/-- The total distribution denoted by `mx` under the bundled semantics `sem`. -/
def evalDist (sem : PMFSemantics m) (mx : m α) : PMF α :=
  sem.toSemanticsVia.denote mx

/-- Forget that a total semantics is total, yielding the underlying subprobabilistic semantics.

This simply postcomposes observation with the canonical embedding `PMF α → SPMF α`. The resulting
`SPMFSemantics` has zero failure probability, but it can now be consumed by APIs that are stated in
terms of subprobabilistic semantics. -/
noncomputable def toSPMFSemantics (sem : PMFSemantics m) : SPMFSemantics m where
  Sem := sem.Sem
  instMonadSem := sem.instMonadSem
  interpret := sem.interpret
  observe := fun mx => liftM (sem.observePMF mx)

/-- Package an ordinary `HasEvalPMF` instance as a bundled `PMFSemantics`.

As with `SPMFSemantics.ofHasEvalSPMF`, this recovers the familiar case where the surface monad
already comes with a total probabilistic denotation. -/
protected def ofHasEvalPMF (m : Type u → Type v) [Monad m] [HasEvalPMF m] :
    PMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx => HasEvalPMF.toPMF mx

end PMFSemantics
