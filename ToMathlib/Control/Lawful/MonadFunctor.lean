/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Lawful version of `MonadFunctor`

This file defines the `LawfulMonadFunctor` class, which adds laws to the `MonadFunctor` class.
These laws ensure that functor operations behave consistently and preserve monad laws.

-/

@[expose] public section

universe u v w

class LawfulMonadFunctor (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadFunctor m n] : Prop where
  /-- Monad map preserves identity -/
  monadMap_id {α : Type u} :
    MonadFunctor.monadMap (fun {β} => (id : m β → _)) = (id : n α → _)

  /-- Monad map preserves composition -/
  monadMap_comp {α : Type u} (f : {β : Type u} → m β → m β) (g : {γ : Type u} → m γ → m γ) :
    (@MonadFunctor.monadMap m n _ α f) ∘ (@MonadFunctor.monadMap m n _ α g) =
      @MonadFunctor.monadMap m n _ α (f ∘ g)

class LawfulMonadFunctorT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadFunctorT m n] : Prop where
  /-- Monad map preserves identity -/
  monadMap_id {α : Type u} :
    monadMap (fun {β} => (id : m β → _)) = (id : n α → _)

  /-- Monad map preserves composition -/
  monadMap_comp {α : Type u} (f : {β : Type u} → m β → m β) (g : {γ : Type u} → m γ → m γ) :
    (@monadMap m n _ α f) ∘ (@monadMap m n _ α g) = @monadMap m n _ α (f ∘ g)

export LawfulMonadFunctorT (monadMap_id monadMap_comp)

attribute [simp] monadMap_id monadMap_comp

instance {m n o} [Monad m] [Monad n] [Monad o] [MonadFunctor n o] [MonadFunctorT m n]
    [LawfulMonadFunctor n o] [LawfulMonadFunctorT m n] : LawfulMonadFunctorT m o where
  monadMap_id := by
    intro α
    simp only [instMonadFunctorTOfMonadFunctor, monadMap_id, LawfulMonadFunctor.monadMap_id]
  monadMap_comp := by
    intro α f g
    simp only [instMonadFunctorTOfMonadFunctor, monadMap_comp, LawfulMonadFunctor.monadMap_comp]

instance lawfulMonadFunctorRefl {m} [Monad m] : LawfulMonadFunctorT m m where
  monadMap_id := by intro α; simp only [monadFunctorRefl]
  monadMap_comp := by intro α f g; simp only [monadFunctorRefl]

instance {m n} [MonadFunctor m n] : MonadFunctorT m n := inferInstance
