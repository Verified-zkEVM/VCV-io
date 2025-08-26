/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import ToMathlib.Control.MonadAlgebra

/-!
# Morphisms Between Monads
-/

universe u v w w'

class IsMonadHom (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n]
    (f : {α : Type u} → m α → n α) where
  map_pure {α} (x : α) : f (pure x) = pure x
  map_bind {α β} (x : m α) (y : α → m β) : f (x >>= y) = f x >>= f ∘ y

/-- Structure to represent a well-behaved mapping between computations in two monads `m` and `n`.
This is similar to `MonadLift` but isn't a type-class but rather an actual object.
This is useful for non-canonical mappings that shouldn't be applied automatically in general.
We also enforce similar laws to `LawfulMonadLift`. -/
@[ext 900] structure MonadHom (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n] where
  toFun {α : Type u} : m α → n α
  toFun_pure' {α : Type u} (x : α) : toFun (pure x) = (pure x : n α)
  toFun_bind' {α β : Type u} (x : m α) (y : α → m β) :
    toFun (x >>= y) = toFun x >>= (fun a => toFun (y a))

infixr:25 " →ᵐ " => MonadHom

instance (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n] (F : m →ᵐ n) :
    IsMonadHom m n F.toFun where
  map_pure := F.toFun_pure'
  map_bind := F.toFun_bind'

/-- View a monad map as a function between computations. Note we can't have a full
`FunLike` instance because the type parameter `α` isn't constrained by the types. -/
instance (m : Type u → Type v) [Pure m] [Bind m] (n : Type u → Type w) [Pure n] [Bind n] :
    CoeFun (m →ᵐ n) (λ _ ↦ {α : Type u} → m α → n α) where
  coe f {_} x := f.toFun x

namespace MonadHom

variable {m : Type u → Type v} [Monad m]
  {n : Type u → Type w} [Monad n]
  {n' : Type u → Type w'} [Monad n']
  {α β γ : Type u}

@[ext] protected def ext' {F G : m →ᵐ n} (h : ∀ α (x : m α), F x = G x) : F = G := by
  ext
  simp [h]

-- Note some potential confusion between `mmap` in applying Hom sense and `Seq.map`
-- This slightly differs from naming conventions of e.g. `map_mul` for `MulHomClass`.

@[simp]
lemma mmap_pure (F : m →ᵐ n) (x : α) :
    F (pure x) = pure x := MonadHom.toFun_pure' F x

@[simp]
lemma mmap_bind (F : m →ᵐ n) (x : m α) (y : α → m β) :
    F (x >>= y) = F x >>= fun x => F (y x) := MonadHom.toFun_bind' F x y

@[simp] -- This doesn't hold without lawful monad
lemma mmap_map [LawfulMonad m] [LawfulMonad n]
    (F : m →ᵐ n) (x : m α) (g : α → β) : F (g <$> x) = g <$> F x := by
  simp [map_eq_bind_pure_comp]

@[simp]
lemma mmap_seq [LawfulMonad m] [LawfulMonad n]
    (F : m →ᵐ n) (x : m (α → β)) (y : m α) : F (x <*> y) = F x <*> F y := by
  simp [seq_eq_bind_map]

@[simp]
lemma mmap_seqLeft [LawfulMonad m] [LawfulMonad n]
    (F : m →ᵐ n) (x : m α) (y : m β) : F (x <* y) = F x <* F y := by
  simp [seqLeft_eq]

@[simp]
lemma mmap_seqRight [LawfulMonad m] [LawfulMonad n]
    (F : m →ᵐ n) (x : m α) (y : m β) : F (x *> y) = F x *> F y := by
  simp [seqRight_eq]

section ofLift

/-- Construct a `MonadHom` from a lawful monad lift. -/
def ofLift (m : Type u → Type v) (n : Type u → Type v) [Monad m] [Monad n]
    [MonadLift m n] [LawfulMonadLift m n] : m →ᵐ n where
  toFun := liftM
  toFun_pure' := liftM_pure
  toFun_bind' := liftM_bind

@[simp]
lemma mmap_ofLift (m : Type u → Type v) (n : Type u → Type v) [Monad m] [Monad n]
    [MonadLift m n] [LawfulMonadLift m n] {α : Type u}
    (x : m α) : ofLift m n x = liftM x := rfl

end ofLift

def id (m : Type u → Type v) [Monad m] : m →ᵐ m where
  toFun mx := mx
  toFun_pure' _ := rfl
  toFun_bind' _ _ := rfl

@[simp] lemma id_apply (mx : m α) : MonadHom.id m mx = mx := rfl

/-- Compose two `MonadHom`s together by applying them in sequence. -/
protected def comp (G : n →ᵐ n') (F : m →ᵐ n) : m →ᵐ n' where
  toFun := G.toFun ∘ F.toFun
  toFun_pure' := by simp
  toFun_bind' := by simp

infixr:90 " ∘ₘ "  => MonadHom.comp

@[simp] lemma comp_apply (G : n →ᵐ n') (F : m →ᵐ n) (x : m α) :
    (G ∘ₘ F) x = G (F x) := rfl

@[simp] lemma comp_id (F : m →ᵐ n) : F.comp (MonadHom.id m) = F := by
  simp [MonadHom.ext'_iff]

@[simp] lemma id_comp (F : m →ᵐ n) : (MonadHom.id n).comp F = F := by
  simp [MonadHom.ext'_iff]

end MonadHom
