/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-! # Monad algebras -/

universe u v

class MonadAlgebra (m : Type u → Type v) where
  monadAlg {α : Type u} : m α → α

export MonadAlgebra (monadAlg)

class LawfulMonadAlgebra (m : Type u → Type v) [Monad m] [MonadAlgebra m] where
  monadAlg_pure {α : Type u} (a : α) : monadAlg (pure a : m α) = a
  monadAlg_bind {α β : Type u} (ma : m α) (mb : α → m β) :
    monadAlg (mb (monadAlg ma)) = monadAlg (ma >>= mb)

export LawfulMonadAlgebra (monadAlg_pure monadAlg_bind)

attribute [simp] monadAlg_pure monadAlg_bind

-- TODO: add examples & interactions with other monad classes
