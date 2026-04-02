/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Bundled Probability Semantics

This file defines bundled subprobabilistic and probabilistic semantics for monads.
Unlike `HasEvalSPMF` and `HasEvalPMF`, these structures allow the denotational semantics
to factor through an internal semantic monad before being observed as an `SPMF` or `PMF`.
-/

universe u v w

structure SPMFSemantics (m : Type u → Type v) [Monad m] where
  Sem : Type u → Type w
  instMonadSem : Monad Sem
  interpret : m →ᵐ Sem
  observeSPMF : {α : Type u} → Sem α → SPMF α

attribute [instance] SPMFSemantics.instMonadSem

namespace SPMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- Evaluate a computation by first interpreting it into the internal semantic monad and then
observing it as an `SPMF`. -/
def evalDist (sem : SPMFSemantics m) (mx : m α) : SPMF α :=
  sem.observeSPMF (sem.interpret mx)

/-- Failure probability of a computation under a bundled `SPMFSemantics`. -/
def probFailure (sem : SPMFSemantics m) (mx : m α) : ENNReal :=
  (sem.evalDist mx).run none

@[simp]
lemma probFailure_le_one (sem : SPMFSemantics m) (mx : m α) :
    sem.probFailure mx ≤ 1 :=
  PMF.coe_le_one (sem.evalDist mx) none

/-- Bundle an existing `HasEvalSPMF` instance as an `SPMFSemantics`. -/
protected def ofHasEvalSPMF (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    SPMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observeSPMF := fun mx => HasEvalSPMF.toSPMF mx

end SPMFSemantics

structure PMFSemantics (m : Type u → Type v) [Monad m] where
  Sem : Type u → Type w
  instMonadSem : Monad Sem
  interpret : m →ᵐ Sem
  observePMF : {α : Type u} → Sem α → PMF α

attribute [instance] PMFSemantics.instMonadSem

namespace PMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- Evaluate a computation by first interpreting it into the internal semantic monad and then
observing it as a `PMF`. -/
def evalDist (sem : PMFSemantics m) (mx : m α) : PMF α :=
  sem.observePMF (sem.interpret mx)

/-- Every probabilistic semantics induces a subprobabilistic semantics by forgetting that failure
never occurs. -/
noncomputable def toSPMFSemantics (sem : PMFSemantics m) : SPMFSemantics m where
  Sem := sem.Sem
  instMonadSem := sem.instMonadSem
  interpret := sem.interpret
  observeSPMF := fun mx => liftM (sem.observePMF mx)

/-- Bundle an existing `HasEvalPMF` instance as a `PMFSemantics`. -/
protected def ofHasEvalPMF (m : Type u → Type v) [Monad m] [HasEvalPMF m] :
    PMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observePMF := fun mx => HasEvalPMF.toPMF mx

end PMFSemantics
