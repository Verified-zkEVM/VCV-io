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
import VCVio.EvalDist.Defs.LawfulSemantics

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

/-- `withStateOracle` allows commuting a `liftM oa` sample past an arbitrary preceding
ambient computation `mx`. Because `liftM oa` does not interact with the cache state,
sampling it before or after `mx` yields the same observed `SPMF`.

This is the foundation for the `BindLiftSwap` instance on `withStateOracle`-built runtimes:
the buried hidden bit / extra public-randomness sample of a KEM/DEM-style game body factors
out of the bundled observation regardless of where it appears in the do-block. -/
lemma withStateOracle_evalDist_bind_liftM_swap
    {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    (s : hashSpec.QueryCache)
    {α β γ : Type} (mx : OracleComp (unifSpec + hashSpec) α) (oa : ProbComp β)
    (f : α → β → OracleComp (unifSpec + hashSpec) γ) :
    (SPMFSemantics.withStateOracle hashImpl s).evalDist
        (mx >>= fun a => liftM oa >>= fun b => f a b) =
    (SPMFSemantics.withStateOracle hashImpl s).evalDist
        (liftM oa >>= fun b => mx >>= fun a => f a b) := by
  classical
  -- The RHS factors via `withStateOracle_evalDist_bind_liftM` since `liftM oa` is at the top.
  rw [withStateOracle_evalDist_bind_liftM hashImpl s oa
        (fun b => mx >>= fun a => f a b)]
  -- For the LHS, expand via `simulateQ_bind` and `roSim.run'_liftM_bind`, reducing to a
  -- `ProbComp`-level `bind_bind_swap` on `oa` and `(simulateQ impl mx).run s`.
  let impl : QueryImpl (unifSpec + hashSpec) (StateT hashSpec.QueryCache ProbComp) :=
    unifFwdImpl hashSpec + hashImpl
  -- LHS: rewrite the buried liftM via simulateQ_bind + roSim.run'_liftM_bind.
  have hLHS :
      (SPMFSemantics.withStateOracle hashImpl s).evalDist
          (mx >>= fun a => liftM oa >>= fun b => f a b) =
        𝒟[(simulateQ impl mx).run s >>= fun pair =>
          oa >>= fun b => (simulateQ impl (f pair.1 b)).run' pair.2] := by
    unfold SPMFSemantics.evalDist SemanticsVia.denote
    change 𝒟[(simulateQ impl (mx >>= fun a => liftM oa >>= fun b => f a b)).run' s] = _
    congr 1
    change Prod.fst <$>
        (simulateQ impl (mx >>= fun a => liftM oa >>= fun b => f a b)).run s = _
    rw [show simulateQ impl (mx >>= fun a => liftM oa >>= fun b => f a b)
          = simulateQ impl mx >>= fun a =>
              simulateQ impl (liftM oa) >>= fun b => simulateQ impl (f a b) by
        simp [simulateQ_bind]]
    rw [StateT.run_bind]
    simp only [map_bind]
    refine bind_congr fun pair => ?_
    change (simulateQ impl (liftM oa) >>= fun b => simulateQ impl (f pair.1 b)).run' pair.2 = _
    exact roSim.run'_liftM_bind (ro := hashImpl) (oa := oa)
      (rest := fun b => simulateQ impl (f pair.1 b)) (s := pair.2)
  -- RHS inner: rewrite via simulateQ_bind.
  have hRHS_inner : ∀ b : β,
      (SPMFSemantics.withStateOracle hashImpl s).evalDist (mx >>= fun a => f a b) =
        𝒟[(simulateQ impl mx).run s >>= fun pair =>
          (simulateQ impl (f pair.1 b)).run' pair.2] := by
    intro b
    unfold SPMFSemantics.evalDist SemanticsVia.denote
    change 𝒟[(simulateQ impl (mx >>= fun a => f a b)).run' s] = _
    congr 1
    change Prod.fst <$> (simulateQ impl (mx >>= fun a => f a b)).run s = _
    rw [show simulateQ impl (mx >>= fun a => f a b) =
          simulateQ impl mx >>= fun a => simulateQ impl (f a b) by
        rw [simulateQ_bind]]
    rw [StateT.run_bind]
    simp only [map_bind]
    rfl
  rw [hLHS]
  -- Rewrite the RHS inner `withStateOracle.evalDist (mx >>= fun a => f a b)` to `𝒟[...]`
  -- form via `hRHS_inner`, then collapse the outer `𝒟[oa] >>= fun b => 𝒟[…]` to a single
  -- `𝒟[oa >>= …]` via `evalDist_bind` so both sides are `𝒟[ProbComp]`.
  rw [show (𝒟[oa] >>= fun b =>
        (SPMFSemantics.withStateOracle hashImpl s).evalDist (mx >>= fun a => f a b)) =
      𝒟[oa >>= fun b =>
        (simulateQ impl mx).run s >>= fun pair =>
          (simulateQ impl (f pair.1 b)).run' pair.2] from by
    rw [evalDist_bind]
    exact bind_congr fun b => hRHS_inner b]
  -- Both sides are `𝒟[ProbComp]`; the underlying ProbComps differ only in bind order.
  apply evalDist_ext
  intro x
  exact probOutput_bind_bind_swap (mx := (simulateQ impl mx).run s) (my := oa)
    (f := fun pair b => (simulateQ impl (f pair.1 b)).run' pair.2) (z := x)

end SPMFSemantics

/-! ## ROM-friendly `ProbCompRuntime` and its coherence instances

A canonical `ProbCompRuntime` constructor `ProbCompRuntime.withStateOracle` packages
`SPMFSemantics.withStateOracle hashImpl s` with the `MonadLiftT ProbComp _`-derived
`ProbCompLift`. Both `ProbCompRuntime.LiftBindCoherent` and `ProbCompRuntime.BindLiftSwap`
are inhabited for this constructor, so any concrete ROM-style runtime built on
`withStateOracle hashImpl s` (e.g. the Fiat-Shamir `runtimeWithCache`) can re-export the
instances by pointing at this canonical form.

Lawfulness is **not** provided here — `withStateOracle` is not a monad morphism in general
(its bundled `observe` discards final state). The shape-restricted classes above are exactly
what hybrid arguments need without ever requiring full lawfulness. -/

namespace ProbCompRuntime

/-- Canonical `ProbCompRuntime` for the `withStateOracle` semantics: bundles the stateful
oracle observation with the standard `MonadLiftT ProbComp _` lift. -/
noncomputable def withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    (s : hashSpec.QueryCache) :
    ProbCompRuntime (OracleComp (unifSpec + hashSpec)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle hashImpl s
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- The canonical ROM-style runtime is **lift-bind-coherent**: a `liftProbComp`-prefixed bind
factors as the underlying ProbComp distribution bound into the post-prefix evalDist. The three
class fields all follow from existing `withStateOracle_evalDist_*` lemmas (the `_pure` field
goes through `withStateOracle_evalDist_bind_liftM` after rewriting the empty bind). -/
noncomputable instance instLiftBindCoherent_withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    (s : hashSpec.QueryCache) :
    (withStateOracle hashImpl s).LiftBindCoherent where
  evalDist_pure a := by
    -- Reduce evalDist (pure a) via direct unfolding through simulateQ_pure + StateT.run'_pure.
    change (SPMFSemantics.withStateOracle hashImpl s).evalDist (pure a) = pure a
    unfold SPMFSemantics.evalDist SemanticsVia.denote
    simp [SPMFSemantics.withStateOracle, simulateQ', StateT.run'_eq]
  evalDist_map f mx := SPMFSemantics.withStateOracle_evalDist_map _ _ _ _
  evalDist_liftProbComp_bind oa rest :=
    SPMFSemantics.withStateOracle_evalDist_bind_liftM hashImpl s oa rest

/-- The canonical ROM-style runtime admits **bind-lift swap**: a `liftProbComp` sample
buried after a prefix can be commuted to the front. Direct corollary of
`SPMFSemantics.withStateOracle_evalDist_bind_liftM_swap`. -/
noncomputable instance instBindLiftSwap_withStateOracle
    {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    (s : hashSpec.QueryCache) :
    (withStateOracle hashImpl s).BindLiftSwap where
  evalDist_bind_liftProbComp_swap mx oa f :=
    SPMFSemantics.withStateOracle_evalDist_bind_liftM_swap hashImpl s mx oa f

end ProbCompRuntime
