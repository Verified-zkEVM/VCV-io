/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Lawful version of `MonadState`

This file defines the `LawfulMonadState(Of)` class, which adds laws to the `MonadState(Of)` class.
-/

universe u v w

@[simp] theorem toMonadState_get_eq_monadStateOf_get {m : Type u → Type v} {σ : Type u}
    [MonadStateOf σ m] : (MonadState.get : m σ) = MonadStateOf.get := rfl

@[simp] theorem toMonadState_set_eq_monadStateOf_set {m : Type u → Type v} {σ : Type u}
    [MonadStateOf σ m] : (MonadState.set : σ → m PUnit) = MonadStateOf.set := rfl

class LawfulMonadStateOf (σ : outParam (Type u)) (m : Type u → Type v) [Monad m] [MonadStateOf σ m]
    : Prop where

  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); set s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    MonadStateOf.modifyGet (m := m) f = do let (a, s) := f (← MonadStateOf.get); set s; pure a

  /-- `get` twice doesn't change the state -/
  get_get : (MonadStateOf.get : m σ) *> (MonadStateOf.get : m σ) = MonadStateOf.get

  -- {a : σ → σ → m α} →
  --   (do let s₁ ← MonadStateOf.get; let s₂ ← MonadStateOf.get; a s₁ s₂)
  --     = do let s ← MonadStateOf.get; a s s

  /-- `set` twice has the same effect as the second `set` -/
  set_set : {s₁ s₂ : σ} → (do set s₁; set s₂) = set (m := m) s₂

  /-- Getting the state after setting it returns the `set` value -/
  get_set : {s : σ} → (do set (m := m) s; MonadStateOf.get) = do set s; pure s

  /-- Setting the state to the value just gotten is redundant -/
  set_get : (do let s ← MonadStateOf.get (m := m); set (σ := σ) s) = pure ⟨⟩

-- Should this be simp?
-- attribute [simp] LawfulMonadStateOf.modifyGet_eq
--   LawfulMonadStateOf.get_get LawfulMonadStateOf.set_set
--   LawfulMonadStateOf.get_set LawfulMonadStateOf.set_get

namespace LawfulMonadStateOf

variable {σ : Type u} {m : Type u → Type v}

@[simp]
theorem getThe_eq [MonadStateOf σ m] : getThe σ (m := m) = MonadStateOf.get := rfl

@[simp]
theorem modifyGetThe_eq [MonadStateOf σ m] {α : Type u} (f : σ → α × σ) :
    modifyGetThe σ (m := m) f = MonadStateOf.modifyGet f := rfl

variable [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m]

-- Should this be simp?
@[simp]
theorem modifyThe_eq (f : σ → σ) :
    modifyThe σ (m := m) f = (do set (f (← MonadStateOf.get))) := by
  simp only [modifyThe, modifyGet_eq, bind_pure_comp, id_map']

end LawfulMonadStateOf

-- TOOD: don't think this should extend, same way `LawfulMonad` doesn't.
class LawfulMonadState (σ : outParam (Type u)) (m : Type u → Type v) [Monad m] :
    Type (max (u+1) v) extends MonadState σ m where

  /-- `modifyGet f` is equivalent to `do let (a, s) := f (← get); set s; pure a` -/
  modifyGet_eq : {α : Type u} → (f : σ → α × σ) →
    modifyGet f = do let (a, s) := f (← get); set s; pure a

  /-- `get` twice doesn't change the state -/
  get_get : get *> get = get

  /-- `set` twice has the same effect as the second `set` -/
  set_set : {s₁ s₂ : σ} → (do set s₁; set s₂) = set s₂

  /-- Getting the state after setting it returns the `set` value -/
  get_set : {s : σ} → (do set s; get) = (do set s; pure s)

  /-- Setting the state to the value just gotten is redundant -/
  set_get : (do let s ← get; set s) = pure ⟨⟩

attribute [simp] LawfulMonadState.modifyGet_eq LawfulMonadState.get_get
  LawfulMonadState.set_set LawfulMonadState.get_set LawfulMonadState.set_get

namespace LawfulMonadState

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] [LawfulMonadState σ m]

@[simp]
theorem modify_eq (f : σ → σ) :
    modify (m := m) f = (do MonadState.set (f (← get))) := by
  simp only [modify, modifyGet_eq, bind_pure_comp, id_map']

-- Do we need extra property of `get` here? That `get` twice is the same as `get` once?
-- @[simp]
-- theorem getModify_eq (f : σ → σ) :
--     getModify (m := m) f = get <* modify f := by
--   simp [getModify, seqLeft_eq_bind]
--   refine bind_congr fun s => ?_
--   sorry
  -- have := bind_assoc get
  -- rw [← bind_assoc get get]

end LawfulMonadState

instance {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadStateOf σ m]
    [LawfulMonadStateOf σ m] : LawfulMonadState σ m where
  modifyGet_eq f := LawfulMonadStateOf.modifyGet_eq f
  get_get := LawfulMonadStateOf.get_get
  set_set := LawfulMonadStateOf.set_set
  get_set := LawfulMonadStateOf.get_set
  set_get := LawfulMonadStateOf.set_get

-- instance  {m : Type u → Type v} {n : Type u → Type w} {σ : Type u}
--     [Monad m] [Monad n] [MonadLift m n] [MonadStateOf σ m]
--     [LawfulMonad m] [LawfulMonad n] [LawfulMonadLift m n] [LawfulMonadStateOf σ m] :
--       LawfulMonadStateOf σ n where
--   modifyGet_eq f := by
--     simp [MonadStateOf.modifyGet, LawfulMonadState.modifyGet_eq, bind_pure_comp,
--       MonadStateOf.get, liftM, MonadStateOf.set]
--   get_get {α} {f} := by {
--     simp [MonadStateOf.get]
--     rw [bind_assoc]
--     rw [← LawfulMonadStateOf.get_get (m := m)]
--     sorry
--   }
--   set_set := sorry
--   get_set := sorry
--   set_get := sorry

namespace StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

theorem modifyGet_eq_monadState {α : Type u} (f : σ → α × σ) :
    StateT.modifyGet (m := m) f = (do let (a, s) := f (← StateT.get); StateT.set s; pure a) := by
  unfold StateT.modifyGet StateT.get StateT.set StateT.instMonad StateT.bind StateT.pure
  simp only [bind_pure_comp, map_pure]

theorem get_get {α : Type u} {a : σ → σ → StateT σ m α} :
    (do let s₁ ← StateT.get; let s₂ ← StateT.get; a s₁ s₂) = (do let s ← StateT.get; a s s) := by
  unfold StateT.get StateT.instMonad StateT.bind
  simp only [pure_bind]

theorem set_set {s₁ s₂ : σ} : (do StateT.set s₁; StateT.set s₂) = StateT.set (m := m) s₂ := by
  unfold StateT.set StateT.instMonad StateT.bind
  simp only [bind_pure_comp, map_pure]

theorem get_set {s : σ} : (do StateT.set (m := m) s; StateT.get) = (do StateT.set s; pure s) := by
  unfold StateT.get StateT.instMonad StateT.bind StateT.set StateT.pure
  simp only [bind_pure_comp, map_pure]

theorem set_get : (do let s ← @StateT.get σ m _; StateT.set s) = pure ⟨⟩ := by
  unfold StateT.get StateT.instMonad StateT.bind StateT.set StateT.pure
  simp only [bind_pure_comp, map_pure]

instance : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := by
    simp only [MonadStateOf.modifyGet, modifyGet_eq_monadState, pure, MonadStateOf.get, set]
  get_get := by
    -- intro α a
    simp only [MonadStateOf.get, get_get, StateT.get]
    unfold StateT.get
    simp [seqRight_eq]
    simp [seq_eq_bind]
    refine funext fun s => ?_
    show _ >>= _ = _
    simp
    -- rw [StateT.run_bind]
    -- apply StateT.ext fun s => ?_
    -- rw [StateT.run_bind]
    -- simp [StateT.run]
  set_set := by
    intro s₁ s₂
    simp only [set, set_set]
  get_set := by
    intro s
    simp only [set, MonadStateOf.get, get_set, pure]
  set_get := by
    simp only [MonadStateOf.get, set, set_get, pure]
instance : LawfulMonadState σ (StateT σ m) := inferInstance

end StateT
