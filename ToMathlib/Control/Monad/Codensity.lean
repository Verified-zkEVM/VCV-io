/-
Copyright (c) 2026 Onyeka Obi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Onyeka Obi
-/
module

public import Mathlib.Control.Lawful

/-!
# The codensity monad

For `m : Type u → Type v`, `Codensity m α` is the type of polymorphic continuation
transformers `(β : Type u) → (α → m β) → m β`. It carries a `Monad` structure for an
*arbitrary* `m`, with no `Monad m` hypothesis, because sequencing is deferred into the
continuation. This is the term-level form of the codensity monad `Ranₘ m`, the right Kan
extension of `m` along itself, and the continuation-passing relative of `ContT`.

When `m` is a lawful monad, `Codensity.lift` embeds `m` into `Codensity m` as a monad
morphism and `Codensity.lower` collapses it back, with `Codensity.lower_lift` witnessing
that the embedding is a section. Routing a computation through `Codensity m` and lowering
it reassociates every `bind` to the right, the standard device for avoiding the quadratic
re-traversal incurred when a long left-nested chain of binds is folded out of a free monad,
such as the universal fold `simulateQ` over `OracleComp`.

## Main definitions

* `Codensity m` : the codensity monad of `m`, with `Monad` and `LawfulMonad` instances.
* `Codensity.lift` / `Codensity.lower` : the embedding of `m` and its retraction.

## Main statements

* `Codensity.lower_lift` : `lower (lift x) = x`.
* `Codensity.lift_pure` / `Codensity.lift_bind` : `lift` is a monad morphism, packaged as
  `LawfulMonadLift m (Codensity m)`.
-/

@[expose] public section

universe u v

/-- The codensity monad of `m`: polymorphic continuations `(β) → (α → m β) → m β`.
Carries a monad structure for any `m`, sequencing into the continuation. -/
def Codensity (m : Type u → Type v) (α : Type u) :=
  (β : Type u) → (α → m β) → m β

namespace Codensity

variable {m : Type u → Type v} {α β : Type u}

instance : Monad (Codensity m) where
  pure a := fun _ k => k a
  bind c f := fun γ k => c γ (fun a => f a γ k)

instance : LawfulMonad (Codensity m) :=
  LawfulMonad.mk' _ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- Embed `m` into its codensity monad; the unit of the construction. -/
def lift [Monad m] (x : m α) : Codensity m α :=
  fun _ k => x >>= k

/-- Collapse a codensity computation back into `m` against `pure`. -/
def lower [Monad m] (c : Codensity m α) : m α :=
  c α pure

instance [Monad m] : MonadLift m (Codensity m) where
  monadLift x := lift x

@[simp] theorem lower_lift [Monad m] [LawfulMonad m] (x : m α) :
    lower (lift x) = x := by
  simp [lower, lift]

@[simp] theorem lift_pure [Monad m] [LawfulMonad m] (a : α) :
    lift (pure a : m α) = (pure a : Codensity m α) := by
  funext _ k; exact pure_bind a k

@[simp] theorem lift_bind [Monad m] [LawfulMonad m] (x : m α) (f : α → m β) :
    lift (x >>= f) = (lift x >>= fun a => lift (f a)) := by
  funext _ k; exact bind_assoc x f k

instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (Codensity m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

end Codensity
