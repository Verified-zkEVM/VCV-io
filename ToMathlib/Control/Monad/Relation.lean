/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Tactic.Alias

/-! # Monad relations -/

universe u v w v₁ w₁ v₂ w₂

class MonadRelation (m : Type u → Type v) (n : Type u → Type w) where
  monadRel {α : Type u} : m α → n α → Prop

export MonadRelation (monadRel)

namespace MonadRelation

scoped infix:50 " ∼ₘ " => monadRel

end MonadRelation

class LawfulMonadRelation (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadRelation m n] where
  monadRel_pure {α : Type u} (a : α) : monadRel (pure a : m α) (pure a : n α)
  monadRel_bind {α β : Type u} {ma : m α} {mb : α → m β} {na : n α} {nb : α → n β}
    (ha : monadRel ma na) (hb : ∀ a, monadRel (mb a) (nb a)) : monadRel (ma >>= mb) (na >>= nb)

export LawfulMonadRelation (monadRel_pure monadRel_bind)

attribute [simp] monadRel_pure monadRel_bind

-- TODO: add examples & interactions with other monad classes

namespace MonadRelation

/-- A (transitive) monad lift defines a monad relation via its graph -/
instance instOfMonadLiftT {m n} [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun ma na => liftM ma = na

/-- A (transitive) lawful monad lift defines a lawful monad relation via its graph -/
instance instOfLawfulMonadLiftT {m n} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
    LawfulMonadRelation m n where
  monadRel_pure _ := by simp only [monadRel, liftM_pure]
  monadRel_bind _ _ := by simp_all only [monadRel, liftM_bind]

end MonadRelation

class MonadRelationHom (m₁ : Type u → Type v₁) (n₁ : Type u → Type w₁)
    (m₂ : Type u → Type v₂) (n₂ : Type u → Type w₂) where
  monadRelHomFst {α : Type u} : m₁ α → m₂ α
  monadRelHomSnd {α : Type u} : n₁ α → n₂ α

export MonadRelationHom (monadRelHomFst monadRelHomSnd)

open MonadRelation in
class LawfulMonadRelationHom (m₁ : Type u → Type v₁) (n₁ : Type u → Type w₁)
    (m₂ : Type u → Type v₂) (n₂ : Type u → Type w₂)
    [MonadRelation m₁ n₁] [MonadRelation m₂ n₂]
    [MonadRelationHom m₁ n₁ m₂ n₂] where
  monadRel_hom {α : Type u} {ma : m₁ α} {na : n₁ α} (h : ma ∼ₘ na) :
    (monadRelHomFst n₁ n₂ ma : m₂ α) ∼ₘ (monadRelHomSnd m₁ m₂ na : n₂ α)
