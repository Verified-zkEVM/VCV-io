/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Bundled Probability Semantics

This file defines bundled subprobabilistic and probabilistic semantics for monads.

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

`SPMFSemantics` is the general bundled notion for subprobabilistic semantics, while
`PMFSemantics` is the total-probability specialization. They are deliberately *bundled*
rather than typeclasses so that a construction can carry its intended semantics locally
without forcing a single global instance on the ambient monad.
-/

/-!
## Design Note

The fields are intentionally minimal:

- `Sem` is the internal semantic monad
- `interpret` embeds the surface computation into that internal semantics
- `observeSPMF` / `observePMF` discard the internal structure and return the external
  distribution seen by the security definitions

Notably, observation is not required to be a monad morphism. That is important: running a
stateful semantics from a fixed initial state is a perfectly reasonable observation, but it is
not itself a monad homomorphism. The bundling here leaves room for that style of semantics.
-/

universe u v w

/-- Bundled subprobabilistic semantics for a monad `m`.

An `SPMFSemantics m` says that computations in `m` can be understood denotationally by:

1. interpreting them into some internal semantic monad `Sem`, and then
2. observing the resulting computation as a subprobability mass function

The key point is that `Sem` need not be the same as `m`. This lets us model surface monads whose
meaning naturally passes through hidden semantic structure, such as caches, internal state, or
other bookkeeping that should be invisible once we talk about probabilities of externally visible
outcomes. -/
structure SPMFSemantics (m : Type u → Type v) [Monad m] where
  /-- Internal monad used to give denotational meaning to computations in `m`. -/
  Sem : Type u → Type w
  /-- Monad structure on the internal semantic monad. -/
  instMonadSem : Monad Sem
  /-- Interpret a surface computation into the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe the internal semantic computation as an `SPMF`, forgetting any hidden structure. -/
  observeSPMF : {α : Type u} → Sem α → SPMF α

attribute [instance] SPMFSemantics.instMonadSem

namespace SPMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The subdistribution denoted by `mx` under the bundled semantics `sem`.

This first moves `mx` into the internal semantic monad via `interpret`, and then collapses the
internal structure to the externally visible `SPMF` via `observeSPMF`. -/
def evalDist (sem : SPMFSemantics m) (mx : m α) : SPMF α :=
  sem.observeSPMF (sem.interpret mx)

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
  observeSPMF := fun mx => HasEvalSPMF.toSPMF mx

end SPMFSemantics

/-- Bundled total probabilistic semantics for a monad `m`.

This is the total analogue of `SPMFSemantics`. The interpretation still factors through an
internal semantic monad, but observation produces a `PMF`, so there is no failure mass. -/
structure PMFSemantics (m : Type u → Type v) [Monad m] where
  /-- Internal monad used to give denotational meaning to computations in `m`. -/
  Sem : Type u → Type w
  /-- Monad structure on the internal semantic monad. -/
  instMonadSem : Monad Sem
  /-- Interpret a surface computation into the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe the internal semantic computation as a total probability mass function. -/
  observePMF : {α : Type u} → Sem α → PMF α

attribute [instance] PMFSemantics.instMonadSem

namespace PMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The total distribution denoted by `mx` under the bundled semantics `sem`. -/
def evalDist (sem : PMFSemantics m) (mx : m α) : PMF α :=
  sem.observePMF (sem.interpret mx)

/-- Forget that a total semantics is total, yielding the underlying subprobabilistic semantics.

This simply postcomposes observation with the canonical embedding `PMF α → SPMF α`. The resulting
`SPMFSemantics` has zero failure probability, but it can now be consumed by APIs that are stated in
terms of subprobabilistic semantics. -/
noncomputable def toSPMFSemantics (sem : PMFSemantics m) : SPMFSemantics m where
  Sem := sem.Sem
  instMonadSem := sem.instMonadSem
  interpret := sem.interpret
  observeSPMF := fun mx => liftM (sem.observePMF mx)

/-- Package an ordinary `HasEvalPMF` instance as a bundled `PMFSemantics`.

As with `SPMFSemantics.ofHasEvalSPMF`, this recovers the familiar case where the surface monad
already comes with a total probabilistic denotation. -/
protected def ofHasEvalPMF (m : Type u → Type v) [Monad m] [HasEvalPMF m] :
    PMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observePMF := fun mx => HasEvalPMF.toPMF mx

end PMFSemantics
