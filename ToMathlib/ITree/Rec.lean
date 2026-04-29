/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import ToMathlib.ITree.Sim.Defs

/-! # Recursive procedure helpers

`ITree.mutualRec` and `ITree.fixRec` are the standard recursive procedure-call
combinators built on top of the `PFunctor.sum` infrastructure. The event
`CallE α β` describes "one recursive call expecting an `α`-argument and
returning a `β`-result"; it is the source signature passed to `fixRec`.

Semantically, a body `body : Handler D (D + E)` describes "one layer" of a
potentially recursive procedure: it may emit `D`-calls (recursive) or
`E`-calls (external). `mutualRec body` returns a `Handler D E` that folds
the recursion away while leaving every external `E`-event intact. The
implementation is a single `PFunctor.M.corec` over `ITree (D + E)`, with
each recursive `D`-event replaced by one silent `step` followed by
`bind (body d) continuation`. The silent step is what makes the corec
productive.

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

/-! ### Mutual recursion -/

/-- Step transformer used by `mutualRec`. Given a handler `body` that may
itself emit `D`-calls, produce one node of the output `ITree E α` from the
current state `u : ITree (D + E) α`.

The four cases mirror the ITree shape constructors:

* `.pure r` — emit `.pure r`.
* `.step c` — pass the silent step through.
* `.query (.inl d) c` — emit a silent `.step` whose continuation runs
  `bind (body d) c`, i.e. splice in the recursive body.
* `.query (.inr e) c` — emit `.query e` with the same continuation.

The `.step` inserted in the `.inl` case is what keeps the enclosing
`PFunctor.M.corec` productive even in the presence of unbounded recursive
calls. -/
def mutualRecStep {D E : PFunctor.{u, u}} {α : Type u}
    (body : ∀ a : D.A, ITree (D + E) (D.B a)) (u : ITree (D + E) α) :
    (Poly E α).Obj (ITree (D + E) α) :=
  match PFunctor.M.dest u with
  | ⟨.pure r, _⟩ => ⟨.pure r, PEmpty.elim⟩
  | ⟨.step, c⟩ => ⟨.step, fun _ => c PUnit.unit⟩
  | ⟨.query (.inl d), c⟩ => ⟨.step, fun _ => bind (body d) c⟩
  | ⟨.query (.inr e), c⟩ => ⟨.query e, c⟩

/-- Interpret a tree over the combined spec `D + E` by splicing recursive
`D`-calls into the body. -/
def interpMrec {D E : PFunctor.{u, u}} {α : Type u}
    (body : ∀ a : D.A, ITree (D + E) (D.B a)) (u : ITree (D + E) α) :
    ITree E α :=
  PFunctor.M.corec (mutualRecStep body) u

/-- `ITree.mutualRec body req` interprets a `D`-request `req` by repeatedly
invoking `body : Handler D (D + E)`. Each recursive `D`-call in the body is
silent-step-guarded so the combined corecursive definition is productive.

This is the Lean version of Coq's `mrec`. -/
def mutualRec {D E : PFunctor.{u, u}}
    (body : ∀ a : D.A, ITree (D + E) (D.B a)) (req : D.A) : ITree E (D.B req) :=
  interpMrec body (body req)

/-- `ITree.fixRec body a` defines a single recursive procedure with input
`α`, recursive-call argument feedback, and result `β`, returning the
specialised tree at input `a`.

This is the Lean version of Coq's `rec`. It is a direct specialisation of
`mutualRec` to the single-call event signature `CallE α β`. -/
def fixRec {E : PFunctor.{u, u}} {α β : Type u}
    (body : α → ITree (CallE α β + E) β) (a : α) : ITree E β :=
  mutualRec (D := CallE α β) (E := E) body a

end ITree
