/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.Control.Monad.Ordered

/-!
# Examples of ordered monads in program verification

We define the following ordered monads:

- The monotone continuation monad `MonoCont`, defined as `WPure` in the paper.
- Extensions thereof via layering on (ordered) monad transformers.

-/

universe u v w

local instance instPreorderId {r} [h : Preorder r] : Preorder (id r) := h

def MonoCont (r : Type v) [Preorder r] : Type u → Type max u v
  | α => {m : Cont r α // ∀ p p' : α → r, (∀ a, p a ≤ p' a) → m p ≤ m p'}

namespace MonoCont

instance {r} [h : Preorder r] : Monad (MonoCont r) where
  pure := fun a => ⟨pure a, fun p p' h => by simp_all only [id_eq, pure]⟩
  bind := fun a f => ⟨a.1 >>= (fun a => (f a).1), fun p p' h => by
    have ha := a.2
    have hf := fun i => (f i).2
    aesop⟩

/-- Everything is `rfl` for this instance since the attached property is a `Prop`. -/
instance {r} [h : Preorder r] : LawfulMonad (MonoCont r) := LawfulMonad.mk' (MonoCont r)
  (id_map := fun x => rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun x f g => rfl)
  (bind_pure_comp := fun x f => rfl)

instance {r α} [h : Preorder r] : Preorder (MonoCont r α) where
  le := fun x y => ∀ p p', (∀ a, p a ≤ p' a) → x.1 p ≤ y.1 p'
  le_refl := fun x => by simp; exact x.2
  le_trans := fun x y z h1 h2 => by
    simp_all
    intro p p' hp
    exact le_trans (h1 p p' hp) (h2 p' p' (fun a => le_refl _))

instance {r} [h : Preorder r] : OrderedMonad (MonoCont r) where
  monadOrder := inferInstance
  bind_mono := fun _ _ => by simp_all only [LE.le, id_eq, bind, implies_true]

end MonoCont

local instance instPreorderProp : Preorder Prop where
  le := fun p q => p → q
  le_refl := fun p => id
  le_trans := fun p q r h1 h2 => h2 ∘ h1

-- `W^Pure` in the paper
def MonoContProp : Type u → Type u := @MonoCont Prop instPreorderProp

@[simp]
theorem MonoContProp_def :
  MonoContProp = fun α => {m : Cont Prop α // ∀ p p', (∀ a, p a → p' a) → m p → m p'} := rfl

instance : Monad MonoContProp := inferInstanceAs (Monad (MonoCont Prop))

instance : LawfulMonad MonoContProp := inferInstanceAs (LawfulMonad (MonoCont Prop))

instance : OrderedMonad MonoContProp := inferInstanceAs (OrderedMonad (MonoCont Prop))

-- Definition STCont S := @MonoCont (S -> Prop) (pointwise_relation S SProp_op_order) _.

-- open scoped OrderedMonad in
-- instance {α} : AssertAssume (MonoContProp α) where
--   assert := fun pre m => ⟨fun p => pre ∧ m.1 p, fun p p' hp ⟨q, mp⟩ => ⟨q, m.2 p p' hp mp⟩⟩
--   assume := fun pre m => ⟨fun p => pre → m.1 p, fun p p' hp q hPre => m.2 p p' hp (q hPre)⟩
--   assert_strengthen := fun pre m p p' hp => by simp_all; intro _ mp; exact m.2 p p' hp mp
--   assume_weaken := fun pre m p p' hp => by simp_all; intro mp _; exact m.2 p p' hp mp
--   assert_assume_iff := fun p m m' => ⟨
--     fun h => by simp_all; sorry,
--     fun h => by simp_all; sorry⟩

/-- The quotient of the state monad, where the preorder on `σ → Prop` is given pointwise,
induced by the preorder `(p ≤ q) ↔ (p → q)` on `Prop`. -/
def MonoStateContProp (σ : Type u) := MonoCont (σ → Prop)

example {σ} : StateT σ (MonoContProp) = fun α => σ → MonoContProp (α × σ) := rfl

-- theorem MonoStateContProp_def {σ} :
--   MonoStateContProp σ = fun α =>
--     {m : α → (σ → Prop) → (σ → Prop) // ∀ p p' :
--     α → (σ → Prop), (∀ s, p s → p' s) → m p ≤ m p'} := rfl

-- TODO: is there a better way to get this to be definitionally equal to
--    `((α × σ) → Prop) → σ → Prop`?

/-! ## Dijkstra monad for free via monad transformers -/

-- /-- The canonical lifting of `Id` into `MonoContProp` -/
-- instance : MonadLift Id MonoContProp := inferInstance

-- /-- The canonical lifting of `Id` into `MonoContProp` is lawful -/
-- instance : LawfulMonadLift Id MonoContProp where
--   monadLift_pure := fun x => by simp only [monadLift, MonadLift.monadLift, pure]
--   monadLift_bind := fun x f => by simp only [monadLift, MonadLift.monadLift, bind]

-- instance {t} [MonadTransformer t] : MonadLift (t Id) (t MonoContProp) where
--   monadLift := fun x => MonadTransformer.liftOf MonoContProp _

-- instance [MonadTrans t] [LawfulMonad t] : LawfulMonadLift (t Id) (t MonoContProp) where
--   monadLift_pure := fun x => by simp only [monadLift, MonadLift.monadLift, pure]
--   monadLift_bind := fun x f => by simp only [monadLift, MonadLift.monadLift, bind]

-- -- `W^St` in the paper
-- noncomputable instance {σ : Type u} : OrderedMonad (StateT σ (Cont Prop)) where
--   monadOrder := {
--     le := fun x y ↦ ∀ p s, x p s → y p s
--     lt := fun x y ↦ monadOrder.le x y ∧ ¬ monadOrder.le y x
--     le_refl := sorry
--     le_trans := sorry
--     lt_iff_le_not_le := by sorry
--   }
--   bind_mono := sorry

-- instance : OrderedMonad (ReaderT σ (Cont Prop)) where
--   le := inferInstance
--   bind_mono := sorry

def effectObserve (m : Type u → Type v) (α : Type u) := m α → (m α → Prop) → Prop

/-!
Hoare triple will have the form `{P} prog {Q}`, where `P Q : m α → Prop` and `prog : m α`,
defined as `P prog → effectObserve prog Q`.
-/
