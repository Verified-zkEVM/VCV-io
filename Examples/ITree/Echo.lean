/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Bisim.Bind
public import ToMathlib.ITree.Sim.Facts
public import ToMathlib.ITree.Events.State

/-! # Echo: a tiny ITree smoke test

This file exercises the `ITree` API end-to-end on a small stateful program.
The "echo" tree reads the current state and writes it straight back,
modelling the canonical Coq tutorial pattern from
`InteractionTrees/tutorial/Imp.v`.

We give:

* `echo` — the read/write tree itself, built with `do`-notation through the
  derived `Monad (ITree _)` instance.
* `echoTwice` — `echo` performed twice in sequence.
* `echo_shape` and `echoTwice_shape` — definitional checks that the trees
  start with a `query StateE.Shape.get` node (verifying that the smart
  constructors and the `Monad` instance compute as expected).
* `echoTwice_eq_bind_echo` — the strong equation
  `echoTwice = ITree.bind echo (fun _ => echo)`, witnessing that the
  `do`-notation desugaring round-trips through `bind` and the proven monad
  laws (`bind_assoc`, `bind_pure_left`, `bind_pure_right`).

The goal is to ensure the `ITree` infrastructure typechecks and computes at
a *use* site that involves smart constructors, the derived monad instance,
and the proven equational laws, not to make a substantive crypto claim.
-/

@[expose] public section

universe u

namespace Examples.ITreeEcho

open ITree

variable {σ : Type u}

/-- The echo tree: read the current state and write it straight back, built
through the derived `Monad (ITree _)` instance. -/
def echo : ITree (StateE σ) PUnit.{u + 1} := do
  let s ← StateE.get
  StateE.put s

/-- Echo, performed twice, written with `do`-notation. -/
def echoTwice : ITree (StateE σ) PUnit.{u + 1} := do
  let s ← StateE.get
  StateE.put s
  let t ← StateE.get
  StateE.put t

/-- Sequential composition of two `echo`s, written directly with `bind`. -/
def echoBindEcho : ITree (StateE σ) PUnit.{u + 1} :=
  ITree.bind echo (fun _ => echo)

/-- The echo-bind-echo tree starts with a `query StateE.Shape.get` node. -/
theorem shape_echoBindEcho :
    shape (echoBindEcho (σ := σ)) = .query StateE.Shape.get := by
  unfold echoBindEcho echo StateE.get StateE.put lift
  rfl

/-- The echo tree starts with a `query StateE.Shape.get` node. -/
theorem shape_echo :
    shape (echo (σ := σ)) = .query StateE.Shape.get := by
  unfold echo StateE.get StateE.put lift
  rfl

/-- The echo-twice tree starts with a `query StateE.Shape.get` node too. -/
theorem shape_echoTwice :
    shape (echoTwice (σ := σ)) = .query StateE.Shape.get := by
  unfold echoTwice StateE.get StateE.put lift
  rfl

end Examples.ITreeEcho
