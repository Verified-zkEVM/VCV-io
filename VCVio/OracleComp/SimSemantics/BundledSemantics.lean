/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
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

/-- `withStateOracle` commutes with `<$>`: mapping a function over the surface computation
is the same as mapping it over the observed `SPMF`.

This holds because `interpret` is the bundled monad morphism `simulateQ'`, and the `StateT`
observer `fun mx => toSPMF (StateT.run' mx s)` preserves `<$>` even though it is not a full
monad morphism: `<$>` does not thread state, so `Prod.fst <$> (f <$> mx).run s` factors as
`f <$> (Prod.fst <$> mx.run s) = f <$> StateT.run' mx s`. -/
@[simp] lemma withStateOracle_evalDist_map
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α β : Type} (f : α → β) (mx : OracleComp (unifSpec + hashSpec) α) :
    (SPMFSemantics.withStateOracle hashImpl s).evalDist (f <$> mx) =
      f <$> (SPMFSemantics.withStateOracle hashImpl s).evalDist mx := by
  unfold SPMFSemantics.evalDist SemanticsVia.denote
  simp only [SPMFSemantics.withStateOracle, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, MonadHom.mmap_map]

/-- `withStateOracle` commutes with the specific `>>= pure ∘ f` pattern produced by
a do-block returning a pure value at the end. A direct corollary of
`withStateOracle_evalDist_map`. -/
lemma withStateOracle_evalDist_bind_pure
    {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α β : Type} (mx : OracleComp (unifSpec + hashSpec) α) (f : α → β) :
    (SPMFSemantics.withStateOracle hashImpl s).evalDist (mx >>= fun x => pure (f x)) =
      f <$> (SPMFSemantics.withStateOracle hashImpl s).evalDist mx := by
  have heq : (mx >>= fun x => pure (f x)) = f <$> mx := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [heq, withStateOracle_evalDist_map]

/-- `withStateOracle` commutes with binding a lifted `ProbComp` prefix: evaluating
`liftM oa >>= rest` under the runtime is the same as first sampling `oa` in `SPMF` and then
evaluating `rest x` under the runtime. The lifted `ProbComp` does not touch the cache state,
so the result distribution factors through `oa` cleanly.

Restricted to `σ = hashSpec.QueryCache` because the underlying `roSim` simulation lemmas hard-code
that state type via `unifFwdImpl`. The vast majority of `withStateOracle` instantiations in this
repo use this state type (e.g. via `randomOracle`). -/
lemma withStateOracle_evalDist_bind_liftM
    {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    (s : hashSpec.QueryCache)
    {α β : Type} (oa : ProbComp α)
    (rest : α → OracleComp (unifSpec + hashSpec) β) :
    (SPMFSemantics.withStateOracle hashImpl s).evalDist (liftM oa >>= rest) =
      𝒟[oa] >>= fun x => (SPMFSemantics.withStateOracle hashImpl s).evalDist (rest x) := by
  classical
  let impl : QueryImpl (unifSpec + hashSpec) (StateT hashSpec.QueryCache ProbComp) :=
    unifFwdImpl hashSpec + hashImpl
  unfold SPMFSemantics.evalDist SemanticsVia.denote
  change 𝒟[(simulateQ impl (liftM oa >>= rest)).run' s] =
      𝒟[oa] >>= fun x => 𝒟[(simulateQ impl (rest x)).run' s]
  rw [simulateQ_bind]
  rw [roSim.run'_liftM_bind (ro := hashImpl) (oa := oa)
    (rest := fun x => simulateQ impl (rest x)) (s := s)]
  rw [evalDist_bind]

end SPMFSemantics
