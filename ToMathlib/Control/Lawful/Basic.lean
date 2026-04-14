/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Monad laws restated via `do` notation

Lean 4.29 changed `do`-notation elaboration so that the desugared bind may use a `Bind`
instance that differs syntactically from `Monad.toBind`. This prevents the standard
`pure_bind`, `bind_assoc`, and `bind_pure` lemmas from matching `do`-block goals via
`simp` or `rw`.

The lemmas in this file re-derive the laws with their statements written using `do`
notation, so the elaborated `Bind` instance matches the one produced in proof goals.
-/

@[expose] public section

namespace LawfulMonad

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

@[simp]
theorem do_pure_bind {α β : Type u} (a : α) (f : α → m β) :
    (do let x ← (pure a : m α); f x) = f a :=
  pure_bind a f

@[simp]
theorem do_bind_pure {α : Type u} (x : m α) :
    (do let a ← x; pure a) = x :=
  bind_pure x

@[simp]
theorem do_bind_assoc {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ) :
    (do let b ← (do let a ← x; f a); g b) = (do let a ← x; let b ← f a; g b) :=
  bind_assoc x f g

@[simp]
theorem do_bind_pure_comp {α β : Type u} (f : α → β) (x : m α) :
    (do let a ← x; pure (f a)) = f <$> x :=
  bind_pure_comp f x

@[simp]
theorem do_map_bind {α β γ : Type u} (f : β → γ) (x : m α) (g : α → m β) :
    f <$> (do let a ← x; g a) = (do let a ← x; f <$> g a) :=
  map_bind f x g

@[simp]
theorem do_bind_map_left {α β γ : Type u} (f : α → β) (x : m α) (g : β → m γ) :
    (do let b ← f <$> x; g b) = (do let a ← x; g (f a)) :=
  bind_map_left f x g

end LawfulMonad

end
