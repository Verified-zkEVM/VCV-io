/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Hom
import Mathlib.Logic.Function.Defs

/-!
# Monad equivalences / isomorphisms

This file defines equivalences or isomorphisms between monads, which consists of a pair of monad
morphisms that are inverses of each other.

TODO: extends the hierarchy with type classes such as `{Nat/Pure/Bind/Monad}EquivClass`
-/

universe u v w z

/-- A natural equivalence between two type-level functions (endofunctors).

This represents a natural isomorphism between two type constructors `m` and `n`. It consists
of natural transformations in both directions that are inverses of each other. -/
structure NatEquiv (m : Type u → Type v) (n : Type u → Type w) where
  toFun : {α : Type u} → m α → n α
  invFun : {α : Type u} → n α → m α
  left_inv : ∀ {α}, Function.LeftInverse (@invFun α) (@toFun α) := by
    intros; first | rfl | ext <;> rfl
  right_inv : ∀ {α}, Function.RightInverse (@invFun α) (@toFun α) := by
    intros; first | rfl | ext <;> rfl

namespace NatEquiv

variable {m : Type u → Type v} {n : Type u → Type w} {p : Type u → Type z}

def toNatHom (e : NatEquiv m n) : NatHom m n where
  toFun := e.toFun

def invNatHom (e : NatEquiv m n) : NatHom n m where
  toFun := e.invFun

instance : Coe (NatEquiv m n) (NatHom m n) where
  coe f := f.toNatHom

instance : Coe (NatEquiv m n) (NatHom n m) where
  coe f := f.invNatHom

/-- The identity natural equivalence between `m : Type u → Type v` and itself. -/
def refl (m : Type u → Type v) : NatEquiv m m where
  toFun := id
  invFun := id
  left_inv := by intros; simp [Function.LeftInverse, id]
  right_inv := by intros; simp [Function.RightInverse, Function.LeftInverse, id]

/-- The inverse of a natural equivalence between `m` and `n`. -/
def symm (e : NatEquiv m n) : NatEquiv n m where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- The composition of natural equivalences between `m` and `n` and between `n` and `p`. -/
def trans (e₁ : NatEquiv m n) (e₂ : NatEquiv n p) : NatEquiv m p where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  left_inv := by
    intros α a
    have h₁ := @e₁.left_inv α
    have h₂ := @e₂.left_inv α
    dsimp [Function.LeftInverse] at h₁ h₂
    simp [h₁, h₂]
  right_inv := by
    intros α a
    have h₁ := @e₁.right_inv α
    have h₂ := @e₂.right_inv α
    dsimp [Function.RightInverse, Function.LeftInverse] at h₁ h₂
    simp [h₁, h₂]

end NatEquiv

/-- A natural equivalence that preserves the `pure` operation.

This extends `NatEquiv` with the requirement that the forward transformation commutes with `pure`.
The inverse transformation automatically commutes with `pure` due to the inverse properties. -/
structure PureEquiv (m : Type u → Type v) [Pure m] (n : Type u → Type w) [Pure n]
    extends NatEquiv m n where
  map_pure' {α : Type u} (x : α) : toFun (pure x) = (pure x : n α)

namespace PureEquiv

variable {m : Type u → Type v} [Pure m] {n : Type u → Type w} [Pure n]

instance : Coe (PureEquiv m n) (NatEquiv m n) where
  coe f := f.toNatEquiv

instance : Coe (PureEquiv m n) (PureHom m n) where
  coe f := ⟨f.toNatEquiv, f.map_pure'⟩

@[simp]
lemma map_pure (f : PureEquiv m n) {α : Type u} (x : α) :
    f.toFun (pure x) = (pure x : n α) := f.map_pure' x

@[simp]
lemma map_pure_inv (f : PureEquiv m n) {α : Type u} (x : α) :
    f.invFun (pure x) = (pure x : m α) := by
  have h1 : f.toFun (f.invFun (pure x)) = pure x := f.right_inv (pure x)
  have h2 : f.toFun (pure x) = pure x := f.map_pure' x
  have h3 : f.toFun (f.invFun (pure x)) = f.toFun (pure x) := by rw [h1, h2]
  exact Function.LeftInverse.injective f.left_inv h3

instance : Coe (PureEquiv m n) (PureHom n m) where
  coe f := ⟨f.toNatEquiv, f.map_pure_inv⟩

end PureEquiv

/-- A natural equivalence that preserves the `bind` operation.

This extends `NatEquiv` with the requirement that the forward transformation commutes with `bind`.
The inverse transformation automatically commutes with `bind` due to the inverse properties. -/
structure BindEquiv (m : Type u → Type v) [Bind m] (n : Type u → Type w) [Bind n]
    extends NatEquiv m n where
  map_bind' {α β : Type u} (x : m α) (y : α → m β) :
    toFun (x >>= y) = toFun x >>= (fun a => toFun (y a))

namespace BindEquiv

variable {m : Type u → Type v} [Bind m] {n : Type u → Type w} [Bind n]

instance : Coe (BindEquiv m n) (NatEquiv m n) where
  coe f := f.toNatEquiv

instance : Coe (BindEquiv m n) (BindHom m n) where
  coe f := ⟨f.toNatEquiv, f.map_bind'⟩

@[simp]
lemma map_bind (f : BindEquiv m n) {α β : Type u} (x : m α) (y : α → m β) :
    f.toFun (x >>= y) = f.toFun x >>= (fun a => f.toFun (y a)) := f.map_bind' x y

@[simp]
lemma map_bind_inv (f : BindEquiv m n) {α β : Type u} (x : n α) (y : α → n β) :
    f.invFun (x >>= y) = f.invFun x >>= (fun a => f.invFun (y a)) := by
  -- We'll show f.toFun applied to both sides gives the same result
  have h1 : f.toFun (f.invFun (x >>= y)) = x >>= y := f.right_inv (x >>= y)
  have h2 : f.toFun (f.invFun x >>= (fun a => f.invFun (y a))) =
            f.toFun (f.invFun x) >>= (fun a => f.toFun (f.invFun (y a))) := f.map_bind' _ _
  have h3 : f.toFun (f.invFun x) = x := f.right_inv x
  have h4 : ∀ a, f.toFun (f.invFun (y a)) = y a := fun a => f.right_inv (y a)
  have h5 : f.toFun (f.invFun x >>= (fun a => f.invFun (y a))) = x >>= y := by
    rw [h2, h3]
    congr 1
    ext a
    exact h4 a
  have h6 : f.toFun (f.invFun (x >>= y)) = f.toFun (f.invFun x >>= (fun a => f.invFun (y a))) := by
    rw [h1, h5]
  exact Function.LeftInverse.injective f.left_inv h6

instance : Coe (BindEquiv m n) (BindHom n m) where
  coe f := ⟨f.toNatEquiv, f.map_bind_inv⟩

end BindEquiv

/-- A monad equivalence: a natural equivalence that preserves both `pure` and `bind` operations.

This represents an isomorphism between two monads `m` and `n`. It combines the requirements of
`PureEquiv` and `BindEquiv`, ensuring that the equivalence preserves the entire monadic structure
in both directions.

A `MonadEquiv` demonstrates that two monads are "essentially identical" from the perspective of
monadic computations. -/
structure MonadEquiv (m : Type u → Type v) [Pure m] [Bind m] (n : Type u → Type w) [Pure n] [Bind n]
    extends NatEquiv m n, PureEquiv m n, BindEquiv m n

@[inherit_doc]
infixr:25 " ≃ᵐ " => MonadEquiv

namespace MonadEquiv

variable {m : Type u → Type v} [Pure m] [Bind m]
  {n : Type u → Type w} [Pure n] [Bind n]
  {p : Type u → Type z} [Pure p] [Bind p]

instance : Coe (MonadEquiv m n) (NatEquiv m n) where
  coe f := f.toNatEquiv

instance : Coe (MonadEquiv m n) (MonadHom m n) where
  coe f := ⟨f.toNatHom, f.map_pure, f.map_bind⟩

instance : Coe (MonadEquiv m n) (MonadHom n m) where
  coe f := ⟨f.invNatHom, f.map_pure_inv, f.map_bind_inv⟩

end MonadEquiv
