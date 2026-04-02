/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.EvalDist.Defs.Semantics

/-!
# Bundled Subprobability Semantics for Oracle Simulations

This file builds `SPMFSemantics` bundles for the common oracle-simulation pattern used throughout
the crypto constructions in this repo:

1. a surface `OracleComp` program runs in a public-randomness world
2. selected oracle families are implemented by a `StateT`-based simulator over `ProbComp`
3. the final semantics is obtained by running the hidden state from a fixed initial cache and then
   observing the resulting `ProbComp` as an `SPMF`
-/

open OracleComp OracleSpec

namespace SPMFSemantics

/-- Bundled `SPMF` semantics for an oracle world consisting of public randomness plus a hidden
stateful oracle implementation.

The surface monad is `OracleComp (unifSpec + hashSpec)`. Internally, computations are interpreted
by simulating the public-randomness queries with their identity implementation and the additional
oracle family `hashSpec` with the supplied stateful simulator `hashImpl`. The hidden state is then
initialized at `s` and discarded, leaving only the externally visible output subdistribution. -/
noncomputable def withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ) :
    SPMFSemantics (OracleComp (unifSpec + hashSpec)) where
  Sem := StateT σ ProbComp
  instMonadSem := inferInstance
  interpret := simulateQ'
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
  observe := fun mx => HasEvalSPMF.toSPMF (StateT.run' mx s)

end SPMFSemantics
