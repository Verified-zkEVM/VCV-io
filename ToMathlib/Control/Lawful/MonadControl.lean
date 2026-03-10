/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Control.Monad.Basic
public import Init.Control.State

/-!
# Lawful version of `MonadControl`

This file defines the `LawfulMonadControl` class, which adds laws to the `MonadControl` class.
These laws ensure that control operations behave consistently and preserve monad laws.

-/

@[expose] public section

universe u v w

class LawfulMonadControl (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadControl m n] : Prop where

  /-- Lifting a pure computation should be pure -/
  liftWith_pure {α : Type u} (a : α) :
    MonadControl.liftWith (m := m) (n := n) (fun _ => pure a) = pure a

  /-- Lifting a bind computation should respect bind -/
  liftWith_bind {α β : Type u} (ma : m α) (f : α → m β) :
    MonadControl.liftWith (fun _ => ma) >>= MonadControl.liftWith ∘ (fun a _ => f a) =
        MonadControl.liftWith (n := n) (fun _ => ma >>= f)

  /-- Restoring after lifting should be identity -/
  liftWith_restoreM {α : Type u} (t : n α) :
    MonadControl.liftWith (m := m) (fun run => run t) >>= MonadControl.restoreM ∘ pure = t

class LawfulMonadControlT (m : Type u → Type v) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadControlT m n] : Prop where

  /-- Lifting a pure computation should be pure -/
  liftWith_pure {α : Type u} (a : α) :
    liftWith (m := m) (n := n) (fun _ => pure a) = pure a

  /-- Lifting a bind computation should respect bind -/
  liftWith_bind {α β : Type u} (ma : m α) (f : α → m β) :
    liftWith (fun _ => ma) >>= liftWith ∘ (fun a _ => f a) = liftWith (n := n) (fun _ => ma >>= f)

  /-- Restoring after lifting should be identity -/
  liftWith_restoreM {α : Type u} (t : n α) :
    liftWith (m := m) (fun run => run t) >>= restoreM = t

export LawfulMonadControlT (liftWith_pure liftWith_bind liftWith_restoreM)

attribute [simp] liftWith_pure liftWith_bind liftWith_restoreM

/-! ## Implementation for StateT -/

namespace StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

-- @[simp]
-- theorem liftWith_pure {α : Type u} (a : α) :
--     liftWith (fun _ => pure a) = pure a := by
--   sorry -- Implementation details

-- @[simp]
-- theorem restore_bind_eq {α β : Type u} (ma : m (α × σ))
--     (f : α → m (β × σ)) :
--     restoreM (ma >>= fun a => f (← restoreM (pure a))) =
--     restoreM ma >>= fun a => restoreM (f a) := by
--   sorry -- Implementation details

-- @[simp]
-- theorem restore_liftWith_eq {α : Type u} (x : StateT σ m α) :
--     restoreM (liftWith fun run => run x) = x := by
--   sorry -- Implementation details

-- instance : LawfulMonadControl m (StateT σ m) where
--   liftWith_pure := liftWith_pure
--   liftWith_bind := liftWith_bind
--   liftWith_restoreM := liftWith_restoreM

end StateT
