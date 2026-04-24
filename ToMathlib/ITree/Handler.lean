/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Basic
public import ToMathlib.PFunctor.Lens.Basic

/-! # Event handlers

A *handler* `Handler E F` interprets each event of the source spec `E` as an
interaction tree over the target spec `F`. Equivalently, a handler is a
choice of `F`-program for every `E`-event. Handlers are the data of the
fundamental ITree simulation operator `ITree.simulate` (see
`ToMathlib.ITree.Sim.Defs`).

For pure event renaming (no extra silent steps and no extra queries),
`ITree.mapSpec` consumes a `PFunctor.Lens`. A `Lens E F` carries a forward
shape map `E.A → F.A` together with a backward arity map
`∀ a, F.B (toFunA a) → E.B a`, which is precisely the data needed to relabel
each `query` node of an interaction tree along an event-spec morphism.

## Naming

| Coq                | Lean                              |
| ------------------ | --------------------------------- |
| `E ~> itree F`     | `ITree.Handler E F`               |
| `E ~> F`           | `PFunctor.Lens E F`               |
| `handler E := ...` | `Handler.id`                      |
| `case_ E F`        | (TODO; coproduct routing on top of `PFunctor.sum`) |
-/

@[expose] public section

universe u

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

/-- Promote a polynomial-functor lens to a handler that performs a pure
renaming. For each source event `a : E.A`, the handler issues the renamed
event `φ.toFunA a` and feeds the answer back through the lens's backward
arity map.

There are no extra silent steps and no extra queries: this is the canonical
"event-renaming" handler. -/
def ofLens (φ : PFunctor.Lens E F) : Handler E F :=
  fun a => query (φ.toFunA a) (fun b => pure (φ.toFunB a b))

end Handler

end ITree
