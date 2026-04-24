/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Init

/-! # Iterative monads

A monad `m` is *iterative* when it provides a uniform iteration combinator
`MonadIter.iterM : (β → m (β ⊕ α)) → β → m α` that turns any "loop body"
sending each input to either a fresh input (`Sum.inl`) or a final result
(`Sum.inr`) into a transformer producing the result.

The notion is due to Adámek, Milius, and Velebil (and used pervasively in
the Coq `InteractionTrees` library, `Basics/Basics.v`, where it is called
`MonadIter`). It generalises uniform definition of recursive functions
across monadic effects and is the data underlying `ITree.iter`,
`OracleComp`'s simulators, the `MonadIter` instances on `OptionT` /
`StateT`, and so on.

## Main definitions

* `MonadIter m` — typeclass packaging a single iteration combinator.

## Conventions

We use `Sum.inl` for "loop continues with new input" and `Sum.inr` for
"loop terminates with this final result", matching the Coq library and
the standard Bekic / iterative-monads literature. (Some Haskell libraries
flip the convention; we stick with `inl = continue`, `inr = stop`.)

## Implementation notes

Lean does not yet have a canonical iterative-monad class, so we introduce
one here with the minimal interface needed for the `ToMathlib.ITree` port.
A future Mathlib upstreaming should add the standard laws (fixed-point,
naturality, codiagonal, dinaturality) and the `LawfulMonadIter` companion
class.
-/

@[expose] public section

universe u v

/-- A monad `m` is *iterative* when it admits a uniform iteration operator
turning loop bodies of type `β → m (β ⊕ α)` into transformers of type
`β → m α`. The operator should iterate the body, restarting on each
`Sum.inl` and terminating on each `Sum.inr`. -/
class MonadIter (m : Type u → Type v) where
  /-- Iterate `f`, restarting the loop on each `Sum.inl j` and terminating
  with the result of each `Sum.inr r`. -/
  iterM {α β : Type u} (f : β → m (β ⊕ α)) (init : β) : m α

export MonadIter (iterM)
