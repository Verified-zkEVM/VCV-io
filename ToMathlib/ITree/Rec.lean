/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Sim.Defs

/-! # Recursive procedure helpers

`ITree.mutualRec` and `ITree.fixRec` provide the standard recursive
procedure-call combinators built on top of `simulate` / `iter`. The event
`CallE α β` describes "one recursive call expecting an `α`-argument and
returning a `β`-result", and is used as the source signature passed to
`mutualRec`.

This file currently contains only the skeleton shapes; the productive
definitions of `mutualRec` and `fixRec` will be filled in by the next
implementation pass once `simulate` / `iter` interaction with
sum-of-PFunctors (`ToMathlib.ITree.Events`) is in place.

Coq references:

* `Interp/Recursion.v` — `mrec`, `rec`, `interp_mrec`, `calling'`.
* `Core/CategoryOps.v` — the underlying KTree categorical structure.
-/

@[expose] public section

universe u

namespace ITree

/-- `CallE α β` is a polynomial functor with a single event, modelling "make
a recursive call with an `α`-argument and expect a `β`-result".

In Coq this is `inductive callE (A B : Type) : Type → Type | Call : A →
callE A B B`. Translated to a polynomial functor, the event name carries the
input `α`-value and the answer type is constantly `β`. -/
def CallE (α β : Type u) : PFunctor.{u, u} where
  A := α
  B _ := β

namespace CallE

variable {α β : Type u}

/-- Issue a single recursive call, returning its result. -/
def call (a : α) : ITree (CallE α β) β :=
  lift (F := CallE α β) a

end CallE

/-! ### Mutual recursion

`mutualRec` wires up a body `body : Handler D (D + E)` (a function from
each "request name" to an interaction tree over the source spec
augmented with the request signature) into a handler that interprets
recursive calls by re-running `body`.

The actual implementation will live in this module once the sum-of-PFunctors
infrastructure is added. -/

/-- `ITree.mutualRec body req` interprets a `D`-request `req` by repeatedly
invoking `body : Handler D (D + E)` (where `+` is the sum of polynomial
functors). The recursion is silent-step-guarded by `simulate` / `iter`.

This is the Lean version of Coq's `mrec`. -/
def mutualRec {D E : PFunctor.{u, u}} {α : Type u}
    (_body : ∀ a : D.A, ITree E (D.B a)) (req : D.A) : ITree E (D.B req) := by
  sorry

/-- `ITree.fixRec body a` defines a single recursive procedure with input
`α`, recursive-call argument feedback, and result `β`, returning the
specialised tree at input `a`.

This is the Lean version of Coq's `rec`. -/
def fixRec {E : PFunctor.{u, u}} {α β : Type u}
    (_body : α → ITree E β) (a : α) : ITree E β := by
  sorry

end ITree
