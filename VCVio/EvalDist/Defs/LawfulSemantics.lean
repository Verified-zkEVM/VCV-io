/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Semantics
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
typically require. -/
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

/-- A `ProbCompRuntime` is **lawful** when its bundled `SPMFSemantics` is lawful. -/
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

end ProbCompRuntime
