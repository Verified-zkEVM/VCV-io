/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Semantics
import VCVio.EvalDist.Defs.Instances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.ProbCompLift

/-!
# Lawful Bundled Probability Semantics

A `SPMFSemantics m` packages an `interpret : m →ᵐ Sem` (a monad morphism) together with an
`observe : Sem α → SPMF α` that is intentionally **not** required to be a monad morphism.
This generality lets bundled semantics carry hidden state or other auxiliary structure that
state-threads through `>>=` in ways that pointwise `observe` cannot recover.

For most game-hopping arguments — hybrid arguments, triangle bounds on advantages, etc. — we
do need the observation to behave like a monad morphism, i.e. `evalDist (mx >>= my) =
evalDist mx >>= fun x => evalDist (my x)`. This file packages that property as a typeclass
`LawfulSPMFSemantics`, lifts it to `ProbCompRuntime` via `ProbCompRuntime.Lawful`, and
provides the canonical instance for the `ProbComp` runtime.

## What is provided

* `SPMFSemantics.LawfulSPMFSemantics sem` — the property that `sem.evalDist` is a monad
  morphism. Comes with derived `evalDist_map`, `evalDist_seq`, `evalDist_seqLeft`, and
  `evalDist_seqRight` simp lemmas.
* Canonical instance for `SPMFSemantics.ofHasEvalSPMF m` (whenever `HasEvalSPMF m` is
  available) — the `interpret` is identity and `observe` is the underlying typeclass-level
  monad morphism, so lawfulness is automatic.
* `ProbCompRuntime.Lawful runtime` — wrapper class that exposes the same lemmas at the
  runtime level.
* Canonical instance for `ProbCompRuntime.probComp`, which is built on `ofHasEvalSPMF`.

## What is **not** provided

`SPMFSemantics.withStateOracle` is **not** generally lawful. Its observation
`fun mx => HasEvalSPMF.toSPMF (StateT.run' mx s)` runs the internal `StateT σ ProbComp` from
a fixed initial state and discards the final state; binding `mx >>= my` threads the state
output of `mx` into the run of `my`, which is information `observe` has already discarded
when applied pointwise. For specific shapes (e.g. an LHS that is a pure `ProbComp` lift
through `liftProbComp`, which never touches the cache state) bind preservation can still be
recovered as a separate lemma — see `SPMFSemantics.withStateOracle_evalDist_map` and the
companion `_bind_pure` lemma in `OracleComp.SimSemantics.BundledSemantics`. Those local
lemmas are not subsumed by `LawfulSPMFSemantics`.
-/

universe u v w

namespace SPMFSemantics

variable {m : Type → Type v} [Monad m]

/-- A bundled `SPMFSemantics m` is **lawful** when its `evalDist` is a monad morphism: it
preserves `pure` and commutes with `>>=`. This is the property crypto game-hopping arguments
typically require.

**Scope.** Bundles built via `SPMFSemantics.ofHasEvalSPMF` (any `HasEvalSPMF` monad, including
the canonical `ProbComp` one) are automatically lawful. Bundles built via
`SPMFSemantics.withStateOracle` are **not** generally lawful — their `observe` runs the
internal `StateT` from a fixed initial state and discards the final state, so `>>=` does not
commute with `evalDist` in general. Theorems that require `[LawfulSPMFSemantics sem]` therefore
exclude `withStateOracle`-style runtimes; for those the available bind preservation is
shape-restricted (e.g. `withStateOracle_evalDist_bind_liftM`,
`withStateOracle_evalDist_bind_pure`). -/
class LawfulSPMFSemantics (sem : SPMFSemantics m) : Prop where
  /-- `evalDist` of a pure value is the corresponding pure `SPMF`. -/
  evalDist_pure {α : Type} (a : α) : sem.evalDist (pure a) = pure a
  /-- `evalDist` distributes over `>>=`. -/
  evalDist_bind {α β : Type} (mx : m α) (my : α → m β) :
    sem.evalDist (mx >>= my) = sem.evalDist mx >>= fun x => sem.evalDist (my x)

namespace LawfulSPMFSemantics

variable {sem : SPMFSemantics m} [LawfulSPMFSemantics sem]

attribute [simp] evalDist_pure evalDist_bind

@[simp] lemma evalDist_map [LawfulMonad m] {α β : Type} (f : α → β) (mx : m α) :
    sem.evalDist (f <$> mx) = f <$> sem.evalDist mx := by
  rw [map_eq_bind_pure_comp, evalDist_bind,
    map_eq_bind_pure_comp (f := f) (x := sem.evalDist mx)]
  refine bind_congr fun x => ?_
  exact evalDist_pure (f x)

@[simp] lemma evalDist_seq [LawfulMonad m] {α β : Type} (mf : m (α → β)) (mx : m α) :
    sem.evalDist (mf <*> mx) = sem.evalDist mf <*> sem.evalDist mx := by
  simp only [seq_eq_bind_map, evalDist_bind, evalDist_map]

@[simp] lemma evalDist_seqLeft [LawfulMonad m] {α β : Type} (mx : m α) (my : m β) :
    sem.evalDist (mx <* my) = sem.evalDist mx <* sem.evalDist my := by
  simp only [seqLeft_eq, evalDist_seq, evalDist_map]

@[simp] lemma evalDist_seqRight [LawfulMonad m] {α β : Type} (mx : m α) (my : m β) :
    sem.evalDist (mx *> my) = sem.evalDist mx *> sem.evalDist my := by
  simp only [seqRight_eq, evalDist_seq, evalDist_map]

end LawfulSPMFSemantics

/-- The bundle built from a typeclass-level `HasEvalSPMF` is automatically lawful: its
`interpret` is the identity monad morphism and its `observe` is the underlying
`HasEvalSPMF.toSPMF`, which is a monad morphism by construction. -/
instance instLawfulOfHasEvalSPMF [HasEvalSPMF m] :
    LawfulSPMFSemantics (SPMFSemantics.ofHasEvalSPMF m) where
  evalDist_pure a := by
    change HasEvalSPMF.toSPMF (pure a) = pure a
    exact MonadHom.mmap_pure _ a
  evalDist_bind mx my := by
    change HasEvalSPMF.toSPMF (mx >>= my) =
      HasEvalSPMF.toSPMF mx >>= fun x => HasEvalSPMF.toSPMF (my x)
    exact MonadHom.mmap_bind _ mx my

end SPMFSemantics

/-! ## Lawfulness lifted to `ProbCompRuntime` -/

namespace ProbCompRuntime

variable {m : Type → Type v} [Monad m]

/-- A `ProbCompRuntime` is **lawful** when its bundled `SPMFSemantics` is lawful.

See `SPMFSemantics.LawfulSPMFSemantics` for the scope: the canonical `probComp` runtime
satisfies this, but `withStateOracle`-based runtimes (e.g. `FiatShamir.runtime`) do not. -/
class Lawful (runtime : ProbCompRuntime m) : Prop where
  /-- Lawfulness of the underlying bundled semantics. -/
  toLawful : SPMFSemantics.LawfulSPMFSemantics runtime.toSPMFSemantics

attribute [instance] Lawful.toLawful

namespace Lawful

variable {runtime : ProbCompRuntime m} [runtime.Lawful]

@[simp] lemma evalDist_pure {α : Type} (a : α) : runtime.evalDist (pure a) = pure a :=
  SPMFSemantics.LawfulSPMFSemantics.evalDist_pure a

@[simp] lemma evalDist_bind {α β : Type} (mx : m α) (my : α → m β) :
    runtime.evalDist (mx >>= my) =
      runtime.evalDist mx >>= fun x => runtime.evalDist (my x) :=
  SPMFSemantics.LawfulSPMFSemantics.evalDist_bind mx my

@[simp] lemma evalDist_map [LawfulMonad m] {α β : Type} (f : α → β) (mx : m α) :
    runtime.evalDist (f <$> mx) = f <$> runtime.evalDist mx :=
  SPMFSemantics.LawfulSPMFSemantics.evalDist_map f mx

@[simp] lemma evalDist_seq [LawfulMonad m] {α β : Type} (mf : m (α → β)) (mx : m α) :
    runtime.evalDist (mf <*> mx) = runtime.evalDist mf <*> runtime.evalDist mx :=
  SPMFSemantics.LawfulSPMFSemantics.evalDist_seq mf mx

end Lawful

/-- The canonical `ProbComp` runtime is lawful. -/
noncomputable instance instLawful_probComp : ProbCompRuntime.probComp.Lawful where
  toLawful := SPMFSemantics.instLawfulOfHasEvalSPMF

/-- A `ProbCompRuntime` is **lift-coherent** when its bundled `evalDist` agrees with the
underlying `ProbComp` semantics on lifted public-randomness samples. Concretely: for any
`oa : ProbComp α`, the SPMF observed under `runtime.evalDist (runtime.liftProbComp oa)` equals
the canonical SPMF `𝒟[oa]`.

This is the "the runtime correctly observes public randomness" coherence axiom. It is orthogonal
to `Lawful` (which only constrains the monad-morphism shape of `evalDist`), but is needed
whenever a hybrid argument samples public randomness via `liftProbComp` and then reads back the
distribution. The canonical `probComp` runtime satisfies it; concrete `withStateOracle`-style
runtimes (e.g. `FiatShamir.runtime`) also satisfy it via their `withStateOracle_evalDist_bind_liftM`
lemma. -/
class LiftCoherent (runtime : ProbCompRuntime m) : Prop where
  /-- `evalDist` of a lifted `ProbComp` sample is the underlying ProbComp distribution. -/
  evalDist_liftProbComp {α : Type} (oa : ProbComp α) :
    runtime.evalDist (runtime.liftProbComp oa) = 𝒟[oa]

attribute [simp] LiftCoherent.evalDist_liftProbComp

/-- The canonical `ProbComp` runtime is lift-coherent: its `liftProbComp` is the identity monad
homomorphism, so `evalDist (liftProbComp oa) = evalDist oa = 𝒟[oa]`. -/
noncomputable instance instLiftCoherent_probComp : ProbCompRuntime.probComp.LiftCoherent where
  evalDist_liftProbComp _ := rfl

/-! ## Shape-restricted bind coherence

`Lawful` is too strong for `withStateOracle`-style runtimes (their state threads through arbitrary
binds). But the typical hybrid-argument shape only needs `evalDist` to commute with binds whose
LHS is a `liftProbComp` — i.e. samples that don't touch the runtime's hidden state. The class
`LiftBindCoherent` below captures exactly that. It subsumes `LiftCoherent` (set `rest := pure`) and
is satisfied by both `probComp` (via `Lawful`) and `withStateOracle` (via the existing
`withStateOracle_evalDist_bind_liftM` lemma in `OracleComp.SimSemantics.BundledSemantics`).

A second class, `BindLiftSwap`, additionally lets us commute a `liftProbComp` past an arbitrary
preceding ambient computation. This is needed when a `liftProbComp` sample appears not at the top
of a do-block but after a prefix of effectful ambient operations (as in the KEM IND-CPA game,
which samples the hidden bit `b` after `keygen` and `preChallenge`). For `probComp` it follows
from `Lawful` plus SPMF-level bind commutativity; for `withStateOracle` it requires a matching
independence-of-lift lemma which is not yet in the repo. -/

/-- A `ProbCompRuntime` is **lift-bind-coherent** when:

* `evalDist` preserves `pure` (a property all reasonable runtimes satisfy — for
  `withStateOracle` via `StateT.run' (pure a) s = pure a`);
* `evalDist` distributes over `<$>` (used to fold the trailing `pure (b == b')` of game bodies);
* binding a `ProbComp`-lifted prefix commutes with `evalDist`.

This is the shape-restricted bind law that hybrid arguments need: the prefix is a piece of public
randomness with no hidden-state interaction, so it factors out of the bundled observation
cleanly.

Subsumes `LiftCoherent` (specialise `rest := pure`). Strictly weaker than `Lawful`: satisfied by
`withStateOracle hashImpl s` via `SPMFSemantics.withStateOracle_evalDist_{map,bind_liftM}`, even
though `withStateOracle` is not generally lawful. -/
class LiftBindCoherent (runtime : ProbCompRuntime m) : Prop where
  /-- `evalDist` preserves `pure`. -/
  evalDist_pure {α : Type} (a : α) : runtime.evalDist (pure a) = pure a
  /-- `evalDist` distributes over `<$>`. -/
  evalDist_map {α β : Type} (f : α → β) (mx : m α) :
    runtime.evalDist (f <$> mx) = f <$> runtime.evalDist mx
  /-- `evalDist` of a `liftProbComp`-prefixed bind factors as the canonical `ProbComp`
  distribution of the prefix bound into the post-prefix `evalDist`. -/
  evalDist_liftProbComp_bind {α β : Type} (oa : ProbComp α) (rest : α → m β) :
    runtime.evalDist (runtime.liftProbComp oa >>= rest) =
      𝒟[oa] >>= fun x => runtime.evalDist (rest x)

namespace LiftBindCoherent

variable {runtime : ProbCompRuntime m} [runtime.LiftBindCoherent]

attribute [simp] evalDist_pure evalDist_map evalDist_liftProbComp_bind

/-- Folding a final `pure (f ·)` through `evalDist`. This is `evalDist_map` after rewriting
`mx >>= fun x => pure (f x)` to `f <$> mx`. -/
lemma evalDist_bind_pure_comp [LawfulMonad m]
    {α β : Type} (mx : m α) (f : α → β) :
    runtime.evalDist (mx >>= fun x => pure (f x)) =
      f <$> runtime.evalDist mx := by
  rw [show (mx >>= fun x => pure (f x)) = f <$> mx by
    rw [map_eq_bind_pure_comp]; rfl]
  exact evalDist_map f mx

end LiftBindCoherent

/-- Lift-bind-coherence implies lift-coherence (specialise `rest := pure`). -/
instance LiftBindCoherent.toLiftCoherent [LawfulMonad m]
    {runtime : ProbCompRuntime m} [runtime.LiftBindCoherent] : runtime.LiftCoherent where
  evalDist_liftProbComp oa := by
    have h := LiftBindCoherent.evalDist_liftProbComp_bind (runtime := runtime) oa pure
    rw [bind_pure] at h
    simp only [LiftBindCoherent.evalDist_pure, bind_pure] at h
    exact h

/-- Any `Lawful + LiftCoherent` runtime is lift-bind-coherent: all three properties follow
directly from the lawfulness lemmas plus the lift-coherence axiom. This makes the canonical
`probComp` runtime lift-bind-coherent automatically (subsumes the bespoke instance below). -/
instance instLiftBindCoherent_of_lawful [LawfulMonad m]
    {runtime : ProbCompRuntime m} [runtime.Lawful] [runtime.LiftCoherent] :
    runtime.LiftBindCoherent where
  evalDist_pure a := Lawful.evalDist_pure a
  evalDist_map f mx := Lawful.evalDist_map f mx
  evalDist_liftProbComp_bind oa rest := by
    rw [Lawful.evalDist_bind, LiftCoherent.evalDist_liftProbComp]

/-- The canonical `ProbComp` runtime is lift-bind-coherent. Subsumed by
`instLiftBindCoherent_of_lawful`; kept as an explicit instance for ease of debugging. -/
noncomputable instance instLiftBindCoherent_probComp : ProbCompRuntime.probComp.LiftBindCoherent :=
  instLiftBindCoherent_of_lawful

/-- A `ProbCompRuntime` admits **bind-lift swap** when a `liftProbComp` sample can be commuted
past an arbitrary preceding ambient computation — i.e. the lifted public-randomness sample is
independent of any hidden state the prefix may have updated.

For `probComp` this follows from `Lawful` + SPMF bind-commutativity (see the instance below).
For `withStateOracle` it follows from `simulateQ_bind` + the fact that `liftM oa` (the surface
form of `liftProbComp oa`) doesn't touch the cache state — i.e. via `roSim.run'_liftM_bind` plus
`ProbComp` bind-commutativity. A clean instance for `withStateOracle` is left as TODO; the
existing `SPMFSemantics.withStateOracle_evalDist_bind_liftM` is the building block. -/
class BindLiftSwap (runtime : ProbCompRuntime m) : Prop where
  evalDist_bind_liftProbComp_swap {α β γ : Type} (mx : m α) (oa : ProbComp β)
      (f : α → β → m γ) :
    runtime.evalDist (mx >>= fun a => runtime.liftProbComp oa >>= fun b => f a b) =
      runtime.evalDist (runtime.liftProbComp oa >>= fun b => mx >>= fun a => f a b)

/-- Any `Lawful + LiftCoherent` runtime admits bind-lift swap: both sides reduce to nested SPMF
binds (equal as `SPMF`s pointwise by `SPMF.ext` + bind-bind-swap on `SPMF`). -/
instance instBindLiftSwap_of_lawful [LawfulMonad m]
    {runtime : ProbCompRuntime m} [runtime.Lawful] [runtime.LiftCoherent] :
    runtime.BindLiftSwap where
  evalDist_bind_liftProbComp_swap mx oa f := by
    -- Push runtime.evalDist through both binds; the lifted prefix becomes 𝒟[oa].
    simp only [Lawful.evalDist_bind, LiftCoherent.evalDist_liftProbComp]
    -- Now both sides are `SPMF` binds; remaining goal is SPMF-level bind-bind-swap.
    -- Wrap in `𝒟[·]` (= identity on SPMF) to access `evalDist_ext`.
    have h := evalDist_ext (m := SPMF) (n := SPMF)
        (mx := runtime.evalDist mx >>= fun a => 𝒟[oa] >>= fun b => runtime.evalDist (f a b))
        (mx' := 𝒟[oa] >>= fun b => runtime.evalDist mx >>= fun a => runtime.evalDist (f a b))
        (fun x =>
          probOutput_bind_bind_swap (m := SPMF) (runtime.evalDist mx) 𝒟[oa]
            (fun a b => runtime.evalDist (f a b)) x)
    simpa using h

/-- The canonical `ProbComp` runtime admits bind-lift swap. Subsumed by
`instBindLiftSwap_of_lawful`; kept as an explicit instance for ease of debugging. -/
noncomputable instance instBindLiftSwap_probComp : ProbCompRuntime.probComp.BindLiftSwap :=
  instBindLiftSwap_of_lawful

end ProbCompRuntime
