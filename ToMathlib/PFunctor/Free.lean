/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Hom
import ToMathlib.PFunctor.Basic

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), and prove some basic properties.

-/

universe u v uA uB

namespace PFunctor

/-- The free monad on a polynomial functor.
This extends the `W`-type construction with an extra `pure` constructor. -/
inductive FreeM (P : PFunctor.{uA, uB}) : Type v → Type (max uA uB v)
  | pure {α} (x : α) : FreeM P α
  | roll {α} (a : P.A) (r : P.B a → FreeM P α) : FreeM P α
deriving Inhabited

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type v}

/-- Lift an object of the base polynomial functor into the free monad. -/
@[always_inline, inline, reducible]
def lift (x : P.Obj α) : FreeM P α := FreeM.roll x.1 (fun y ↦ FreeM.pure (x.2 y))

/-- Lift a position of the base polynomial functor into the free monad. -/
@[always_inline, inline, reducible]
def liftA (a : P.A) : FreeM P (P.B a) := lift ⟨a, id⟩

instance : MonadLift P (FreeM P) where
  monadLift x := FreeM.lift x

@[simp] lemma lift_ne_pure (x : P α) (y : α) :
    (lift x : FreeM P α) ≠ PFunctor.FreeM.pure y := by simp [lift]

@[simp] lemma pure_ne_lift (x : P α) (y : α) :
    PFunctor.FreeM.pure y ≠ (lift x : FreeM P α) := by simp [lift]

-- @[simp]
lemma monadLift_eq_lift (x : P.Obj α) : (x : FreeM P α) = FreeM.lift x := rfl

/-- Bind operator on `FreeM P` operation used in the monad definition. -/
@[always_inline, inline]
protected def bind : FreeM P α → (α → FreeM P β) → FreeM P β
  | FreeM.pure x, g => g x
  | FreeM.roll x r, g => FreeM.roll x (λ u ↦ FreeM.bind (r u) g)

@[simp]
lemma bind_pure (x : α) (r : α → FreeM P β) :
    FreeM.bind (FreeM.pure x) r = r x := rfl

@[simp]
lemma bind_roll (a : P.A) (r : P.B a → FreeM P β) (g : β → FreeM P γ) :
    FreeM.bind (FreeM.roll a r) g = FreeM.roll a (λ u ↦ FreeM.bind (r u) g) := rfl

@[simp]
lemma bind_lift (x : P.Obj α) (r : α → FreeM P β) :
    FreeM.bind (FreeM.lift x) r = FreeM.roll x.1 (fun a ↦ r (x.2 a)) := rfl

@[simp] lemma bind_eq_pure_iff (x : FreeM P α) (y : α → FreeM P β) (y' : β) :
    FreeM.bind x y = FreeM.pure y' ↔ ∃ x', x = pure x' ∧ y x' = pure y' := by
  cases x <;> simp

@[simp] lemma pure_eq_bind_iff (x : FreeM P α) (y : α → FreeM P β) (y' : β) :
    FreeM.pure y' = FreeM.bind x y ↔ ∃ x', x = pure x' ∧ pure y' = y x' := by
  cases x <;> simp

instance : Monad (FreeM P) where
  pure := FreeM.pure
  bind := FreeM.bind

lemma monad_pure_def (x : α) : (pure x : FreeM P α) = FreeM.pure x := rfl

lemma monad_bind_def (x : FreeM P α) (g : α → FreeM P β) :
    x >>= g = FreeM.bind x g := rfl

instance : LawfulMonad (FreeM P) :=
  LawfulMonad.mk' (FreeM P)
    (λ x ↦ by
      induction x with
      | pure _ => rfl
      | roll a _ h => refine congr_arg (FreeM.roll a) (funext λ i ↦ h i))
    (λ x f ↦ rfl)
    (λ x f g ↦ by
      induction x with
      | pure _ => rfl
      | roll a _ h => refine congr_arg (FreeM.roll a) (funext λ i ↦ h i))

lemma pure_inj (x y : α) : FreeM.pure (P := P) x = FreeM.pure y ↔ x = y := by simp

@[simp] lemma roll_inj (x x' : P.A) (y : P.B x → P.FreeM α) (y' : P.B x' → P.FreeM α) :
    FreeM.roll x y = FreeM.roll x' y' ↔ ∃ h : x = x', h ▸ y = y' := by
  simp
  by_cases hx : x = x'
  · cases hx
    simp
  · simp [hx]

-- @[simp] lemma bind

/-- Proving a predicate `C` of `FreeM P α` requires two cases:
* `pure x` for some `x : α`
* `roll x r h` for some `x : P.A`, `r : P.B x → FreeM P α`, and `h : ∀ y, C (r y)`
Note that we can't use `Sort v` instead of `Prop` due to universe levels.-/
@[elab_as_elim]
protected def inductionOn {C : FreeM P α → Prop}
    (pure : ∀ x, C (pure x))
    (roll : (x : P.A) → (r : P.B x → FreeM P α) → (∀ y, C (r y)) → C (FreeM.roll x r)) :
    (oa : FreeM P α) → C oa
  | FreeM.pure x => pure x
  | FreeM.roll x r => roll x _ (λ u ↦ FreeM.inductionOn pure roll (r u))

section construct

/-- Shoulde be possible to unify with the above-/
@[elab_as_elim]
protected def construct {C : FreeM P α → Type*}
    (pure : (x : α) → C (pure x))
    (roll : (x : P.A) → (r : P.B x → FreeM P α) → ((y : P.B x) → C (r y)) → C (FreeM.roll x r)) :
    (oa : FreeM P α) → C oa
  | .pure x => pure x
  | .roll x r => roll x _ (λ u ↦ FreeM.construct pure roll (r u))

variable {C : FreeM P α → Type*} (h_pure : (x : α) → C (pure x))
  (h_roll : (x : P.A) → (r : P.B x → FreeM P α) → ((y : P.B x) → C (r y)) → C (FreeM.roll x r))

@[simp]
lemma construct_pure (y : α) : FreeM.construct h_pure h_roll (pure y) = h_pure y := rfl

@[simp]
lemma construct_roll (x : P.A) (r : P.B x → FreeM P α) :
    (FreeM.construct h_pure h_roll (FreeM.roll x r) : C (FreeM.roll x r)) =
      (h_roll x r (fun u => FreeM.construct h_pure h_roll (r u))) := rfl

end construct

section mapM

variable {m : Type uB → Type v} {α : Type uB}

/-- Canonical mapping of `FreeM P` into any other monad, given a map `s : (a : P.A) → m (P.B a)`. -/
protected def mapM [Pure m] [Bind m] (s : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .roll a r => (s a) >>= (λ u ↦ (r u).mapM s)

variable [Monad m] (s : (a : P.A) → m (P.B a))

@[simp]
lemma mapM_pure' (x : α) : (FreeM.pure x : FreeM P α).mapM s = Pure.pure x := rfl

@[simp]
lemma mapM_roll (x : P.A) (r : P.B x → FreeM P α) :
    (FreeM.roll x r).mapM s = s x >>= fun u => (r u).mapM s := rfl

@[simp] lemma mapM_pure (x : α) : (Pure.pure x : FreeM P α).mapM s = Pure.pure x := rfl

variable [LawfulMonad m]

@[simp]
lemma mapM_bind {α β} (x : FreeM P α) (y : α → FreeM P β) :
    (FreeM.bind x y).mapM s = x.mapM s >>= fun u => (y u).mapM s := by
  induction x using FreeM.inductionOn with
  | pure _ => simp
  | roll x r h => simp [h]

@[simp]
lemma mapM_bind' {α β} (x : FreeM P α) (y : α → FreeM P β) :
    (x >>= y).mapM s = x.mapM s >>= fun u => (y u).mapM s :=
  mapM_bind _ _ _

@[simp]
lemma mapM_map {α β} (x : FreeM P α) (f : α → β) :
    FreeM.mapM s (f <$> x) = f <$> FreeM.mapM s x := by
  simp [← bind_pure_comp]

@[simp]
lemma mapM_seq {α β}
    (s : (a : P.A) → m (P.B a)) (x : FreeM P (α → β)) (y : FreeM P α) :
    FreeM.mapM s (x <*> y) = (FreeM.mapM s x) <*> (FreeM.mapM s y) := by
  simp [seq_eq_bind_map]

@[simp]
lemma mapM_lift (s : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    FreeM.mapM s (FreeM.lift x) = s x.1 >>= (λ u ↦ (pure (x.2 u)).mapM s) := by
  simp [FreeM.mapM]

@[simp]
lemma mapM_liftA (s : (a : P.A) → m (P.B a)) (x : P.A) :
    FreeM.mapM s (FreeM.liftA x) = s x := by simp [liftA]

/-- `FreeM.mapM` as a monad homomorphism. -/
protected def mapMHom (s : (a : P.A) → m (P.B a)) : FreeM P →ᵐ m where
  toFun _ := FreeM.mapM s
  toFun_pure' x := rfl
  toFun_bind' x y := by
    induction x using FreeM.inductionOn <;> simp [FreeM.mapM, FreeM.monad_bind_def]

@[simp] lemma mapMHom_toFun_eq (s : (a : P.A) → m (P.B a)) :
    ((FreeM.mapMHom s).toFun α) = FreeM.mapM s := rfl

protected def mapMHom' (s : NatHom P.Obj m) : FreeM P →ᵐ m where
  toFun _ := FreeM.mapM (fun t => s ⟨t, id⟩)
  toFun_pure' x := by simp --[FreeM.mapM]
  toFun_bind' x y := by
    induction x using FreeM.inductionOn <;> simp [FreeM.mapM, FreeM.monad_bind_def]

@[simp] lemma mapMHom'_toFun_eq (s : NatHom P.Obj m) :
    (FreeM.mapMHom' s).toFun α = FreeM.mapM (fun t => s ⟨t, id⟩) := rfl

end mapM

end FreeM

end PFunctor
