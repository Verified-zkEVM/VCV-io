/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import ToMathlib.Control.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Types

/-!
# Morphisms Between Monads

Basic definitions of maps between monads parameterized over any possible output type.
This is implemented with more constrained universes as `m ⟶ n` in mathlib category theory,
but this gives definitions more standardized to a cs context.

TODO: Evaluate more fine-grained `PureHom`/`BintHom`/etc, with `Class` versions as well.
Probably should be in the context of upstreaming things.
-/

universe u v w x y z

variable {m : Type u → Type v} {n : Type u → Type w}

/-- A `NatHom m n` for two functors `m` and `n` is a map `m α → n α` for each possible type `α`.
This is exactly an element of the category `m ⟶ n`, but that has more restricted universes -/
structure NatHom (m : Type u → Type v) (n : Type u → Type w) where
  toFun : (α : Type u) → m α → n α

/-- `f mx` notation for `NatHom m n` applied to an element of `m α`, with implicit `α` inferred. -/
instance : CoeFun (NatHom m n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

-- /-- A natural morphism / transformation that preserves the `pure` operation. -/
-- structure PureHom (m : Type u → Type v) [Pure m] (n : Type u → Type w) [Pure n]
--     extends NatHom m n where
--   toFun_pure' {α : Type u} (x : α) : toFun (pure x) = (pure x : n α)

-- /-- A natural morphism / transformation that preserves the `bind` operation. -/
-- structure BindHom (m : Type u → Type v) [Bind m] (n : Type u → Type w) [Bind n]
--     extends NatHom m n where
--   toFun_bind' {α β : Type u} (x : m α) (y : α → m β) :
--     toFun β (x >>= y) = toFun α x >>= toFun β ∘ y

/-- A `MonadHom m n` bundles a monad map `m ⟶ n` (represented as a `NatHom`) with proofs that
it respects the `bind` and `pure` operations in the underlying monad. -/
@[ext] structure MonadHom (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n] extends NatHom m n where --, PureHom m n, BindHom m n
  toFun_pure' {α} (x : α) : toFun α (pure x) = pure x
  toFun_bind' {α β} (x : m α) (y : α → m β) :
    toFun β (x >>= y) = toFun α x >>= fun x => toFun β (y x)

@[inherit_doc] infixr:25 " →ᵐ " => MonadHom

attribute [simp, grind =] MonadHom.toFun_pure' MonadHom.toFun_bind'

/-- `f mx` notation for `NatHom m n` applied to an element of `m α`, with implicit `α` inferred. -/
instance {m : Type u → Type v} [Pure m] [Bind m] {n : Type u → Type w} [Pure n] [Bind n] :
    CoeFun (m →ᵐ n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

/-- Similar to `AddHomClass` but for `MonadHom`. This becomes more important if we start defining
a hierarchy of these types (e.g. for `AlternativeMonad`s).
Note that getting `FunLike` to work has some `outParam` challenges, may not be workable. -/
class MonadHomClass (F : Type _)
    (m : outParam (Type u → Type v)) [Monad m]
    (n : outParam (Type u → Type w)) [Monad n]
    [hf : (α : Type u) → FunLike F (m α) (n α)] where
  map_pure {α} (x : α) (f : F) : (f : m α → n α) (pure x : m α) = pure x
  map_bind {α β} (x : m α) (y : α → m β) (f : F) :
    (f : m β → n β) (x >>= y) = (f : m α → n α) x >>= f ∘ y

-- namespace MonadHomClass

-- variable {F : Type _}
--   {m : outParam (Type u → Type v)} [Monad m]
--   {n : outParam (Type u → Type w)} [Monad n]
--   [hf : (α : Type u) → FunLike F (m α) (n α)]

-- @[simp] lemma mmap_pure [hf : (α : Type u) → FunLike F (m α) (n α)]
--     (f : F) [@MonadHomClass F m _ n _ hf]
--     (x : α) : F α (pure x) = pure x :=
--   MonadHomClass.map_pure x

-- -- dt: should we be using `F ∘ my`?
-- @[simp] lemma mmap_bind (F : (α : Type u) → m α → n α) [MonadHomClass m n F]
--     (mx : m α) (my : α → m β) : F β (mx >>= my) = F α mx >>= fun x => F β (my x) :=
--   MonadHomClass.map_bind mx my

-- @[simp] lemma mmap_map [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m α) (g : α → β) : F β (g <$> x) = g <$> F α x := by
--   simp [map_eq_bind_pure_comp]

-- @[simp] lemma mmap_seq [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m (α → β)) (y : m α) : F β (x <*> y) = F _ x <*> F α y := by
--   simp [seq_eq_bind_map]

-- @[simp] lemma mmap_seqLeft [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m α) (y : m β) : F α (x <* y) = F α x <* F β y := by
--   simp [seqLeft_eq]

-- @[simp] lemma mmap_seqRight [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m α) (y : m β) : F β (x *> y) = F α x *> F β y := by
--   simp [seqRight_eq]

-- instance ofLawfulMonadLiftT {m n : Type u → Type _} [Monad m] [Monad n]
--     [MonadLiftT m n] [LawfulMonadLiftT m n] : MonadHomClass m n (@liftM m n _) where
--   map_pure := by aesop
--   map_bind := by aesop

-- instance {m : Type u → Type _} [Monad m] : MonadHomClass m m (fun _ => id) where
--   map_pure := by aesop
--   map_bind := by aesop

-- instance {m n n' : Type u → Type _} [Monad m] [Monad n] [Monad n']
--     (f : (α : Type u) → m α → n α) (g : (α : Type u) → n α → n' α)
--     [MonadHomClass m n f] [MonadHomClass n n' g] : MonadHomClass m n' (fun α => g α ∘ f α) where
--   map_pure := by aesop
--   map_bind := by aesop

-- end MonadHomClass

namespace MonadHom

variable {m : Type u → Type v} [Monad m]
  {n : Type u → Type w} [Monad n]
  {n' : Type u → Type x} [Monad n']
  {n'' : Type u → Type y} [Monad n'']
  {α β γ : Type u}

@[ext] protected def ext' {F G : m →ᵐ n}
    (h : ∀ α (x : m α), F x = G x) : F = G := by aesop

@[simp, grind =] lemma mmap_pure (F : m →ᵐ n) (x : α) : F (pure x) = pure x := by grind

-- dt: should we be using `F ∘ my`?
@[simp, grind =] lemma mmap_bind (F : m →ᵐ n) (mx : m α) (my : α → m β) :
    F (mx >>= my) = F mx >>= fun x => F (my x) := by grind

@[simp, grind =] lemma mmap_map [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n)
    (x : m α) (g : α → β) : F (g <$> x) = g <$> F x := by
  simp [map_eq_bind_pure_comp]

@[simp] lemma mmap_seq [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n)
    (x : m (α → β)) (y : m α) : F (x <*> y) = F x <*> F y := by
  simp [seq_eq_bind_map]

@[simp] lemma mmap_seqLeft [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n)
    (x : m α) (y : m β) : F (x <* y) = F x <* F y := by
  simp [seqLeft_eq]

@[simp] lemma mmap_seqRight [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n)
    (x : m α) (y : m β) : F (x *> y) = F x *> F y := by
  simp [seqRight_eq]

/-- Construct a `MonadHom` from a lawful monad lift. -/
def ofLift (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] : m →ᵐ n where
  toFun _ mx := liftM mx
  toFun_pure' := by simp
  toFun_bind' := by simp

@[simp, grind =] lemma ofLift_apply [MonadLiftT m n] [LawfulMonadLiftT m n] {α : Type u} (x : m α) :
    ofLift m n x = liftM x := rfl

/-- The identity morphism between a monad and itself. -/
def id (m : Type u → Type v) [Monad m] : m →ᵐ m where
  toFun _ mx := mx
  toFun_pure' _ := by simp
  toFun_bind' _ _ := by simp

@[simp, grind =] lemma id_apply (mx : m α) : MonadHom.id m mx = mx := rfl

/-- Compose two `MonadHom`s together by applying them in sequence. -/
protected def comp (G : n →ᵐ n') (F : m →ᵐ n) : m →ᵐ n' where
  toFun _ := G.toFun _ ∘ F.toFun _
  toFun_pure' := by simp
  toFun_bind' := by simp

infixr:90 " ∘ₘ "  => MonadHom.comp

@[simp, grind =] lemma comp_apply (G : n →ᵐ n') (F : m →ᵐ n) (x : m α) :
    (G ∘ₘ F) x = G (F x) := rfl

@[simp, grind =] lemma comp_id (F : m →ᵐ n) : F.comp (MonadHom.id m) = F := by aesop

@[simp, grind =] lemma id_comp (F : m →ᵐ n) : (MonadHom.id n).comp F = F := by aesop

@[grind =]
lemma comp_assoc (H : n' →ᵐ n'') (G : n →ᵐ n') (F : m →ᵐ n) :
    (H ∘ₘ G) ∘ₘ F = H ∘ₘ (G ∘ₘ F) := by aesop

/-- `pure`/`return` lawfully embed the `Id` monad into any lawful monad. -/
protected def pure (m) [Monad m] [LawfulMonad m] : Id →ᵐ m where
  toFun _ mx := pure mx.run
  toFun_pure' x := by simp
  toFun_bind' mx my := by simp

@[simp, grind =] lemma pure_apply (m) [Monad m] [LawfulMonad m] (x : Id α) :
    MonadHom.pure m x = pure x.run := rfl

end MonadHom
