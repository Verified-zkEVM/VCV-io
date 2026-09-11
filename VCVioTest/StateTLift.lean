/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Control.StateT
public import ToMathlib.Control.WriterT

/-!
# Canonical lifting through state and writer transformers

Lifting a base effect uses the standard outer state lift. Explicitly lifting a stateful program
between base monads continues to use the covariance instance. The equations check the selected
instance paths under ordinary imports, without assuming laws about the supplied base lift.
-/

public section

universe u v w

/-- An unrelated base effect enters the writer transformer before the outer state transformer. -/
example {m : Type u → Type v} {n : Type u → Type w} [Monad m] [MonadLiftT n m]
    {α σ W : Type u} [Monoid W] (sample : n α) :
    (liftM sample : StateT σ (WriterT W m) α) =
      StateT.lift (liftM (liftM sample : m α) : WriterT W m α) := rfl

/-- Covariant lifting still transports an already stateful program between base monads. -/
example {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n]
    {α σ : Type u} (program : StateT σ m α) :
    (liftM program : StateT σ n α) = StateT.mk (fun s => liftM (program.run s)) := rfl
