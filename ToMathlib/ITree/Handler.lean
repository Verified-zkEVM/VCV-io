/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Basic

/-! # Event handlers

A *handler* `Handler E F` interprets each event of the source spec `E` as an
interaction tree over the target spec `F`. Equivalently, a handler is a
choice of `F`-program for every `E`-event. Handlers are the data of the
fundamental ITree simulation operator `ITree.simulate` (see
`ToMathlib.ITree.Sim.Defs`) and the natural ingredient for layered
interpretation of programs.

This file also provides a lightweight notion of *PFunctor morphism*
(`PFunctor.Hom`), the "natural transformation" between event signatures
(matching answer types pointwise). PFunctor morphisms are used by
`ITree.mapSpec` to perform a pure renaming of events without involving
`bind`.

## Naming

| Coq                | Lean                          |
| ------------------ | ----------------------------- |
| `E ~> itree F`     | `ITree.Handler E F`           |
| `E ~> F`           | `PFunctor.Hom E F`            |
| `handler E := ...` | `id_handler`                  |
| `case_ E F`        | (TODO, see `ToMathlib.ITree.Events`) |
-/

@[expose] public section

universe u

namespace PFunctor

/-- A morphism of polynomial functors `E ⟶ F` is a polymorphic event renaming
that preserves answer types. Concretely, each event of `E` gets mapped to an
event of `F` with *the same* answer type.

In Coq's `InteractionTrees`, this is the type `E ~> F`. -/
structure Hom (E F : PFunctor.{u, u}) where
  /-- Map source event names to target event names. -/
  shape : E.A → F.A
  /-- The answer type of the renamed event must agree with the answer type
  of the original. We take the equality in the form `F.B (shape a) = E.B a`
  so that `Eq.mp / Eq.mpr` can transport answers naturally in either
  direction. -/
  arity (a : E.A) : F.B (shape a) = E.B a

namespace Hom

variable {E F G : PFunctor.{u, u}}

/-- Identity morphism. -/
def id (E : PFunctor.{u, u}) : Hom E E where
  shape := _root_.id
  arity _ := rfl

/-- Composition of polynomial-functor morphisms. -/
def comp (g : Hom F G) (f : Hom E F) : Hom E G where
  shape := g.shape ∘ f.shape
  arity a := (g.arity (f.shape a)).trans (f.arity a)

end Hom

end PFunctor

namespace ITree

/-- An event handler `Handler E F` is a polymorphic interpretation of every
`E`-event as an `F`-program.

Concretely, for each event name `a : E.A` we choose an interaction tree of
type `ITree F (E.B a)` returning the answer expected by the source signature.

This is the Lean version of Coq's `Handler E F := E ~> itree F`. -/
def Handler (E F : PFunctor.{u, u}) : Type u :=
  ∀ a : E.A, ITree F (E.B a)

namespace Handler

variable {E F : PFunctor.{u, u}}

/-- The trivial handler that interprets each `E`-event as itself, i.e. the
single-step `lift` from `ToMathlib.ITree.Basic`. -/
def id (E : PFunctor.{u, u}) : Handler E E :=
  fun a => lift a

/-- Promote a polynomial-functor morphism to a handler that performs a pure
renaming (no extra silent steps, no extra queries). -/
def ofHom (φ : PFunctor.Hom E F) : Handler E F :=
  fun a => (φ.arity a) ▸ lift (φ.shape a)

end Handler

end ITree
