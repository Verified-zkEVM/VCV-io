/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Control.Monad.Cont
import Mathlib.CategoryTheory.Monad.Basic
import ToMathlib.Control.Monad.Algebra
import ToMathlib.Control.Monad.Relation
import ToMathlib.Control.Monad.Transformer
import Mathlib.Order.Monotone.Basic

/-!
# Ordered monads

This file collects all definitions and basic theorems about adding ordering to monads.

## Main definitions

- `OrderedMonad`
- `OrderedMonadAlgebra`
- `OrderedMonadLift`
- `MonadIdeal`
- `OrderedMonadTransformer`
- Left / right Kan extension of ordered monads

-/

universe u v w

section Prelude

/-- `pointwiseRelation r f g` is the pullback of a relation `r` on `β` to a relation on `α` via `f`
  and `g`. -/
def pointwiseRelation {α β : Type u} (r : β → β → Prop) (f g : α → β) : α → α → Prop :=
  fun a b => r (f a) (g b)

/-- `Proper R m` states that a value `m` respects the relation `R` by being related to itself.
This is useful for expressing that certain operations preserve relationships.

NOTE: this is a direct translation from Coq, the Lean version is essentially `IsRefl` -/
def Proper (A : Type u) (R : A → A → Prop) (m : A) : Prop := R m m

end Prelude

/-- An ordered monad `m` is a monad equipped with a preorder on each type `m α`, such that the bind
    operation preserves the order. -/
class OrderedMonad (m : Type u → Type v) extends Monad m where
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'

export OrderedMonad (monadOrder bind_mono)

instance {m} [OrderedMonad m] {α : Type u} : Preorder (m α) := monadOrder

attribute [simp] bind_mono

/-- Unbundled version of `OrderedMonad`. -/
class Monad.IsOrdered (m : Type u → Type v) [Monad m] where
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'

instance {m} [Monad m] [Monad.IsOrdered m] : OrderedMonad m where
  monadOrder := Monad.IsOrdered.monadOrder
  bind_mono := Monad.IsOrdered.bind_mono

namespace OrderedMonad

/-- The less-than-or-equal relation on an ordered monad `m`. -/
@[reducible] def monadLE {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.le

/-- The less-than relation on an ordered monad `m`. -/
@[reducible] def monadLT {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.lt

@[inherit_doc] scoped infix:50 " ≤ₘ " => OrderedMonad.monadLE
@[inherit_doc] scoped infix:50 " <ₘ " => OrderedMonad.monadLT

macro_rules | `($x ≤ₘ $y)  => `(binrel% OrderedMonad.monadLE $x $y)
macro_rules | `($x <ₘ $y)  => `(binrel% OrderedMonad.monadLT $x $y)

namespace Discrete

/-- Any monad can be given the discrete preorder, where `a ≤ b` if and only if `a = b`.

This is put into the `Discrete` scope in order to avoid conflicts with other instances. This
instance should only be used as a last resort. -/
scoped instance (priority := low) instDiscreteMonad (m) [Monad m] : OrderedMonad m where
  monadOrder := {
    le := (· = ·)
    le_refl _ := rfl
    le_trans _ _ _ _ _ := by simp_all
  }
  bind_mono h hf := by simp_all; rename_i f f'; have : f = f' := funext hf; simp [this]

end Discrete

end OrderedMonad

export OrderedMonad (monadLE monadLT)

open OrderedMonad

-- class OrderedAlgebra (m : Type u → Type u) [Monad m] [MonadAlgebra m] where
--   [carrierOrder {α : Type u} : Preorder α]
--   monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
--     (hm : ma ≤ ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))

class OrderedMonadAlgebra (m : Type u → Type v) [OrderedMonad m] [MonadAlgebra m] where
  [carrierOrder {α : Type u} : Preorder α]
  monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
    (hm : ma ≤ₘ ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))

export OrderedMonadAlgebra (monadAlg_mono)

attribute [simp] monadAlg_mono

section MonadLift

/-- A class that express an ordering for monad lifts. -/
class MonadLift.LE (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [φ : MonadLift m n] [ψ : MonadLift m n] where
  monadLift_le {α} (a : m α) : φ.monadLift a ≤ₘ ψ.monadLift a

/-- If the target monad `n` is ordered, then we have a preorder on the monad lifts from `m` to `n`.
  -/
instance {m n} [Monad m] [OrderedMonad n] : Preorder (MonadLift m n) where
  le := fun φ ψ => ∀ {α : Type u} (a : m α), φ.monadLift a ≤ₘ ψ.monadLift a
  le_refl _ := by intro α a; simp only [ge_iff_le, le_refl]
  le_trans φ₁ φ₂ φ₃ h1 h2 := by simp_all; intro α a; exact le_trans (h1 a) (h2 a)

class OrderedMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLift m n where
  monadLift_mono {α} : Monotone (@monadLift α)

class OrderedMonadLiftT (m : Type u → Type v) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLiftT m n where
  monadLift_mono {α} : Monotone (@monadLift α)

export OrderedMonadLiftT (monadLift_mono)

attribute [simp] monadLift_mono

@[simp] theorem monadLift_mono' {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n]
    {α} {a b : m α} (h : a ≤ₘ b) : monadLift a ≤ₘ (monadLift b : n α) :=
  (monadLift_mono (m := m) (n := n) (α := α)) h

instance {m} [OrderedMonad m] : OrderedMonadLiftT m m where
  monadLift_mono h := by simp only [monadLift_self, h]

-- TODO: fix synthesization order
-- instance (m n o) [Monad m] [Monad n] [Monad o] [OrderedMonadLift n o]
--     [OrderedMonadLiftT m n] : OrderedMonadLiftT m o where
--   monadLift_mono h := by simp

open OrderedMonad Discrete in
/--
Given the (default) discrete preorder on the beginning monad `m`, we can have a preorder on the
monad lifts from `m` to `n`.

This is stated as a definition and not an instance, since oftentimes we want to have another
instance on the monad lift.
-/
def instDiscreteMonadLift {m n} [Monad m] [h : OrderedMonad n] [MonadLift m n] :
    OrderedMonadLift m n where
  monadLift_mono h := by rename_i a b; have : a = b := h; simp only [this, le_refl]

end MonadLift

namespace MonadRelation

class IsUpperClosed (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [MonadRelation m n] where
  monadRel_upper_closed {α} {ma : m α} {na na' : n α} (hr : ma ∼ₘ na) (hn : na ≤ₘ na') : ma ∼ₘ na'

instance {m n} [Monad m] [OrderedMonad n] [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun a b => monadLift a ≤ₘ b

instance {m n} [Monad m] [OrderedMonad n] [MonadLiftT m n] [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftT m n] : LawfulMonadRelation m n where
  monadRel_pure := by
    simp only [monadRel, liftM_pure, ge_iff_le, le_refl, implies_true]
  monadRel_bind ha hb := by
    simp_all only [monadRel, ge_iff_le, liftM_bind, implies_true, bind_mono]

-- TODO: monad morphism also defines a monad ideal

end MonadRelation

class OrderedMonadTransformer (t : (Type u → Type v) → Type u → Type w)
    extends MonadTransformer t where
  mapOrderedMonad {m} [OrderedMonad m] : OrderedMonad (t m)
  liftOf_mono {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n] :
    OrderedMonadLiftT (t m) (t n)

class AssertAssume (α : Type u) [Preorder α] where
  assert : Prop → α → α
  assume : Prop → α → α
  assert_strengthen : ∀ p x, assert p x ≤ x
  assume_weaken : ∀ p x, x ≤ assume p x
  assert_assume_iff : ∀ p x y, assert p x ≤ y ↔ x ≤ assume p y

class Monad.AssertAssume (m : Type u → Type v) [∀ α, Preorder (m α)] where
  assert_assume {α} : _root_.AssertAssume (m α)

section KanExtension
variable {w : Type u → Type v} [Monad w] [OrderedMonad w]

def leftKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : α → w β // p >>= ext ≤ₘ f ∧ (∀ w', p >>= w' ≤ₘ f → ∀ b, w' b ≤ₘ ext b) }

def rightKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : β → w α // f >>= ext ≤ₘ p ∧ (∀ w', f >>= w' ≤ₘ p → ∀ a, w' a ≤ₘ ext a) }

end KanExtension
