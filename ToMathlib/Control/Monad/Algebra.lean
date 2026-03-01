/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Order.CompleteLattice.Basic

/-!
# Monad algebras

This file contains two layers:

1. A minimal `MonadAlgebra` interface used by existing `ToMathlib` files.
2. A Loom-style ordered monad algebra interface `MAlgOrdered` with `wp`/`triple`.

Public credit / attribution:
- Loom project: https://github.com/verse-lab/loom
- POPL 2026 paper: "Foundational Multi-Modal Program Verifiers", Vladimir Gladshtein, George
  Pîrlea, Qiyuan Zhao, Vitaly Kurin, and Ilya Sergey.
  DOI: https://doi.org/10.1145/3776719

The ordered monad algebra perspective (`MAlgOrdered`, `wp`, `triple`) in this file is adapted from
Loom's `MonadAlgebras` development.
-/

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

/-! ## Loom-style ordered monad algebras -/

universe w

/-- Ordered monad algebra interface used for quantitative WP/triple reasoning. -/
class MAlgOrdered (m : Type u → Type v) (l : Type u) [Monad m] [CompleteLattice l] where
  μ : m l → l
  μ_pure : ∀ x : l, μ (pure x) = x
  μ_bind_mono {α : Type u} :
    ∀ (f g : α → m l), (∀ a, μ (f a) ≤ μ (g a)) →
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [CompleteLattice l] [MAlgOrdered m l]
variable {α β : Type u}

/-- Weakest precondition induced by `μ`. -/
def wp (x : m α) (post : α → l) : l :=
  MAlgOrdered.μ (x >>= fun a => pure (post a))

/-- Hoare-style triple induced by `wp`. -/
def Triple (pre : l) (x : m α) (post : α → l) : Prop :=
  pre ≤ wp x post

theorem μ_bind (x : m α) (f g : α → m l) (h : ∀ a, MAlgOrdered.μ (f a) = MAlgOrdered.μ (g a)) :
    MAlgOrdered.μ (x >>= f) = MAlgOrdered.μ (x >>= g) := by
  apply le_antisymm
  · exact MAlgOrdered.μ_bind_mono f g (fun a => by simp [h a]) x
  · exact MAlgOrdered.μ_bind_mono g f (fun a => by simp [h a]) x

@[simp]
theorem wp_pure [LawfulMonad m] (x : α) (post : α → l) :
    wp (pure x : m α) post = post x := by
  unfold wp
  simp [MAlgOrdered.μ_pure]

theorem wp_bind [LawfulMonad m] (x : m α) (f : α → m β) (post : β → l) :
    wp (x >>= f) post = wp x (fun a => wp (f a) post) := by
  unfold wp
  rw [bind_assoc]
  exact μ_bind
    x
    (fun a => f a >>= fun b => pure (post b))
    (fun a => pure (MAlgOrdered.μ (f a >>= fun b => pure (post b))))
    (fun a => by
      simpa using
        (MAlgOrdered.μ_pure
          (m := m) (l := l) (x := MAlgOrdered.μ (f a >>= fun b => pure (post b)))).symm)

theorem wp_mono (x : m α) {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    wp x post ≤ wp x post' := by
  unfold wp
  exact MAlgOrdered.μ_bind_mono
    (f := fun a => pure (post a))
    (g := fun a => pure (post' a))
    (fun a => by simpa [MAlgOrdered.μ_pure] using h a)
    x

theorem triple_conseq {pre pre' : l} {x : m α} {post post' : α → l}
    (hpre : pre' ≤ pre) (hpost : ∀ a, post a ≤ post' a) :
    Triple pre x post → Triple pre' x post' := by
  intro h
  exact le_trans hpre (le_trans h (wp_mono x hpost))

theorem triple_bind [LawfulMonad m] {pre : l} {x : m α} {cut : α → l}
    {f : α → m β} {post : β → l}
    (hx : Triple pre x cut) (hf : ∀ a, Triple (cut a) (f a) post) :
    Triple pre (x >>= f) post := by
  unfold Triple at *
  rw [wp_bind]
  exact le_trans hx (wp_mono x hf)

end MAlgOrdered
