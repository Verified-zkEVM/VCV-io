/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Free
import ToMathlib.PFunctor.Free
import Mathlib.Control.Monad.Cont
import Mathlib

universe u v w y z

/-- Church-encoded freer monad transformer, expressed as interpreter for continuation.

When unfolded (recall that `ContT r m α = (α → m r) → m r`), it takes the form:
```
{r : Type u} → (handleEff : {x : Type z} → f x → (x → m r) → m r) → (handlePure : α → m r) → m r
```

Compare this to the inductive definition, which has two constructors:
- `pure : α → FreeMonad f α`
- `roll : f β → (β → FreeMonad f α) → FreeMonad f α`

-/
def FreeContT (f : Type z → Type y) (m : Type u → Type v) (α : Type w) :
    Type (max (u + 1) v w y (z + 1)) :=
  {r : Type u} → ({x : Type z} → f x → ContT r m x) → ContT r m α

/-- Church-encoded freer monad, expressed as interpreter for continuation.

When unfolded, it takes the form:
```
{r : Type u} → (handleEff : {x : Type z} → f x → (x → r) → r) → (handlePure : α → r) → r
```

Compare this to the inductive definition, which has two constructors:
- `pure : α → FreeMonad f α`
- `roll : f β → (β → FreeMonad f α) → FreeMonad f α` -/
def FreeContM (f : Type z → Type y) (α : Type w) : Type (max (u + 1) w y (z + 1)) :=
  FreeContT f Id.{u} α

/-- Church-encoded freer monad transformer from a polynomial functor.
Does not raise universe levels. -/
def PFunctor.FreeContT (P : PFunctor.{z, y}) (m : Type u → Type v) (α : Type w) :
    Type (max (u + 1) v w y z) :=
  {r : Type u} → ((a : P.A) → ContT r m (P.B a)) → ContT r m α

/-- Church-encoded freer monad from a polynomial functor. -/
def PFunctor.FreeContM (P : PFunctor.{z, y}) (α : Type w) : Type _ :=
  FreeContT P Id.{u} α

-- mutual

-- /-- Free monad transformer, defined inductively.
-- -/
-- inductive FreeStepT (F : Type u → Type y) (m : Type u → Type v) (α : Type w)
--     -- Type (max (u + 1) v w y (z + 1)) where
--   | pure (a : α) : FreeStepT F m α
--   | roll {β : Type u} (fx : F β) (k : m β → FreeT F m α) : FreeStepT F m α

-- inductive FreeT (F : Type u → Type y) (m : Type u → Type v) (α : Type w)
--   | lift (mb : FreeStepT F m α) : FreeT F m α

-- end

namespace FreeT

variable {F : Type u → Type y} {m : Type u → Type v} {α β : Type u}

-- def pure [Pure m] (a : α) : FreeT F m α :=
--   FreeT.lift (pure a)

-- def bind [Bind m] (x : FreeT F m α) (f : α → FreeT F m β) : FreeT F m β :=
--   match x with
--   | FreeT.lift ma => by sorry
--   | FreeT.roll fx k => FreeT.roll fx (fun a => f a)

-- instance [Monad m] : Monad (FreeT F m) where
--   pure := FreeT.pure
--   bind := FreeT.bind

end FreeT

-- /-- Free monad transformer from a polynomial functor, defined inductively. -/
-- inductive PFunctor.FreeT (P : PFunctor.{w, u}) (m : Type u → Type v) (α : Type u) :
--     Type (max u v w) where
--   | pure (x : α) : PFunctor.FreeT P m α
--   | lift (a : P.A) (mb : m (P.B a)) (k : P.B a → PFunctor.FreeT P m α) : PFunctor.FreeT P m α
--   | roll (a : P.A) (k : P.B a → PFunctor.FreeT P m α) : PFunctor.FreeT P m α

-- /-- Free monad, defined inductively. -/
-- def FreeM (F : Type z → Type y) (α : Type w) : Type (max (u + 1) w y (z + 1)) :=
--   FreeT F Id.{u} α

-- /-- Free monad from a polynomial functor, defined inductively. -/
-- def PFunctor.FreeM' (P : PFunctor.{w, u}) (α : Type u) : Type (max u w) :=
--   PFunctor.FreeT P Id α

variable {f : Type z → Type y} {m : Type u → Type v} {α β : Type w}

namespace FreeContT

@[simp]
lemma def_eq : FreeContT f m α =
    ({r : Type u} → ({x : Type z} → f x → (x → m r) → m r) → (α → m r) → m r) := rfl

@[simp]
lemma FreeContM.def_eq : FreeContM.{u, w, y, z} f α =
    ({r : Type u} → ({x : Type z} → f x → (x → r) → r) → (α → r) → r) := rfl

inductive FreeM (f : Type v → Type w) (α : Type u) where
  | pure (a : α) : FreeM f α
  | roll {β : Type v} (x : f β) (k : β → FreeM f α) : FreeM f α

/-- `pure` just feeds the value to the pure continuation. -/
@[inline] def pure (a : α) : FreeContT f m α :=
  fun _ handlePure => handlePure a

/-- `bind` runs the first computation; when it produces a value, we run the second computation
    with the *same* effect handler and *same* final continuation. -/
@[inline] def bind (x : FreeContT f m α) (g : α → FreeContT f m β) :
    FreeContT f m β :=
  fun handleEff handlePure => x handleEff (fun a => g a handleEff handlePure)

/-- Lift a monadic computation to the free transformer monad, via sequencing with the pure
  continuation. -/
@[inline] def lift [Bind m] {α : Type u} (x : m α) : FreeContT f m α :=
  fun _ handlePure => x >>= handlePure

/-- `FreeContT f m` is a monad for arbitrary `f` and `m`. -/
instance instMonad : Monad (FreeContT f m) where
  pure := pure
  bind := bind

/-- `FreeContT f m` is a lawful monad for arbitrary `f` and `m`. -/
instance instLawfulMonad : LawfulMonad (FreeContT f m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intros; rfl)

/-- We can always lift a monadic computation to the free transformer monad. -/
instance instMonadLift [Bind m] : MonadLift m (FreeContT f m) where
  monadLift := lift

/-- The lift from `m` to `FreeContT f m` is a lawful monad lift, assuming `m` is a lawful monad. -/
instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (FreeContT f m) where
  monadLift_pure := by
    intro α a
    dsimp [instMonadLift, instMonad]
    funext r a b
    simp [lift, pure]
  monadLift_bind := by
    intros α β ma g
    dsimp [instMonadLift, instMonad]
    funext r a b
    simp [lift, bind]

instance {n : Type u → Type v} [MonadLiftT m n] : MonadLiftT (FreeContT f m) (FreeContT f n) where
  monadLift := fun x => fun handleEff handlePure => by
    dsimp at x
    dsimp [ContT] at handleEff
    sorry

end FreeContT

-- /-- Convert free monad transformers from inductive style to continuation-passing style. -/
-- def FreeT.toFreeContT : FreeT f m α → FreeContT f m α :=
--   fun x => match x with
--     | FreeT.pure a => fun _ handlePure => handlePure a
--     | FreeT.lift mb k => fun handleEff handlePure => sorry
--       -- handleEff mb (fun a => FreeT.toFreeContT (k a) handleEff handlePure)
--     | FreeT.roll fx k => fun handleEff handlePure =>
--       handleEff fx (fun a => FreeT.toFreeContT (k a) handleEff handlePure)

-- def FreeContT.toFreeT : FreeContT f m α → FreeT f m α :=
--   fun x => sorry
--   -- FreeT.lift (x FreeT.roll FreeT.pure) (by simp)

/-- Convert free monads from inductive style to continuation-passing style. -/
def FreeMonad.toFreeContM : FreeMonad f α → FreeContM f α :=
  fun x => match x with
    | FreeMonad.pure a => fun _ handlePure => handlePure a
    | FreeMonad.roll x k => fun handleEff handlePure =>
      handleEff x (fun a => FreeMonad.toFreeContM (k a) handleEff handlePure)

/-- Convert free monads from continuation-passing style to inductive style. -/
def FreeContM.toFreeMonad : FreeContM f α → FreeMonad f α :=
  fun x => x FreeMonad.roll FreeMonad.pure

#print FreeContM.toFreeMonad

@[simp]
lemma FreeMonad.toFreeMonad_toFreeContM (x : FreeMonad f α) :
    FreeContM.toFreeMonad (FreeMonad.toFreeContM x) = x := by
  induction x with
    | pure a => rfl
    | roll x k ih =>
      dsimp [FreeMonad.toFreeContM, FreeContM.toFreeMonad]
      congr
      funext b
      exact ih b

lemma FreeContM.toFreeContM_toFreeMonad (x : FreeContM f α):
    @FreeMonad.toFreeContM f α (FreeContM.toFreeMonad x) = @x := by
  funext r handleEff handlePure
  set y := FreeContM.toFreeMonad x with hy
  induction h : y with
  | pure a =>
    simp [h, toFreeMonad] at hy
    simp [FreeMonad.toFreeContM]
    sorry
  | roll x k ih => sorry
  -- unfold FreeMonad.toFreeContM

/-- Two monad definitions are equivalent. -/
def equivFreeM : FreeMonad f α ≃ FreeContM f α where
  toFun := FreeMonad.toFreeContM
  invFun := FreeContM.toFreeMonad
  left_inv := FreeMonad.toFreeMonad_toFreeContM
  right_inv := FreeContM.toFreeContM_toFreeMonad
