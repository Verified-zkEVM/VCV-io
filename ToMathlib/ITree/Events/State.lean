/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Sim.Defs

/-! # State events

A standard event signature for stateful computations. The polynomial functor
`StateE σ` has two events:

* `get` — returns the current state of type `σ`.
* `put s` — replaces the current state with `s`, returning `PUnit`.

Together with a `simulate`-based handler interpreting `StateE σ` over `σ`
itself (mapping each `get`/`put` to the corresponding `StateT σ` operation),
this gives the standard "state monad as ITree" embedding.

Coq references:

* `Events/State.v` — `stateE`, `interp_state`, `run_state`.
-/

@[expose] public section

universe u

namespace ITree

/-- The two state events. `Shape.get` returns the current state, `Shape.put`
replaces it. -/
inductive StateE.Shape (σ : Type u) : Type u where
  /-- Read the current state. -/
  | get : StateE.Shape σ
  /-- Overwrite the current state with `s : σ`. -/
  | put (s : σ) : StateE.Shape σ

/-- State events over a state space `σ : Type u`. The answer types are:

* for `get` — `σ` (the value read);
* for `put _` — `PUnit` (the unit return of an assignment).
-/
def StateE (σ : Type u) : PFunctor.{u, u} where
  A := StateE.Shape σ
  B
    | .get => σ
    | .put _ => PUnit.{u + 1}

namespace StateE

variable {σ : Type u}

/-- Issue a `get` event, returning the current state. -/
def get : ITree (StateE σ) σ := lift (F := StateE σ) Shape.get

/-- Issue a `put` event, returning `PUnit`. -/
def put (s : σ) : ITree (StateE σ) PUnit.{u + 1} := lift (F := StateE σ) (Shape.put s)

end StateE

end ITree
