/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Batteries.Control.LawfulMonadState

/-!
# Lawful version of `MonadState`

The core `LawfulMonadState(Of)` API now lives in Batteries. This module keeps only the small
helper lemmas that are still locally useful under the `ToMathlib` import path.
-/

@[expose] public section

universe u v

@[simp] theorem toMonadState_get_eq_monadStateOf_get {m : Type u → Type v} {σ : Type u}
    [MonadStateOf σ m] : (MonadState.get : m σ) = MonadStateOf.get := by
  exact (monadStateOf_get_eq_get (σ := σ) (m := m)).symm

@[simp] theorem toMonadState_set_eq_monadStateOf_set {m : Type u → Type v} {σ : Type u}
    [MonadStateOf σ m] : (MonadState.set : σ → m PUnit) = MonadStateOf.set := rfl
