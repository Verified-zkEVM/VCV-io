/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Hom
import Mathlib

/-!
# Commutative monads
-/

universe u v

namespace Monad

/-- Two monadic actions `ma : m α` and `mb : m β` are commutative if the following holds:
```
(do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))
```
-/
def CommutativeAt (m : Type u → Type v) [Monad m] {α β : Type u} (ma : m α) (mb : m β) : Prop :=
  (do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))

/-- A monad is commutative if any two monadic actions `ma : m α` and `mb : m β` can be applied
  in any order. In other words, the following holds:
```
(do let a ← ma; let b ← mb; pure (a, b)) = (do let b ← mb; let a ← ma; pure (a, b))
```
-/
class Commutative (m : Type u → Type v) [Monad m] where
  bind_comm {α β} (ma : m α) (mb : m β) : CommutativeAt m ma mb

export Monad.Commutative (bind_comm)

attribute [simp] bind_comm

-- Instance for accessing bind_comm directly
instance {m} [Monad m] [Commutative m] {α β} (ma : m α) (mb : m β) :
    CommutativeAt m ma mb := bind_comm ma mb

-- The main commutativity lemma for composed computations
@[simp] theorem bind_comm_comp {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ}
    (ma : m α) (mb : m β) (f : α × β → m γ) :
      (ma >>= fun a => mb >>= fun b => f (a, b)) = (mb >>= fun b => ma >>= fun a => f (a, b)) := by
  -- Use associativity to factor out the pair construction
  have h1 : (ma >>= fun a => mb >>= fun b => f (a, b)) =
           ((ma >>= fun a => mb >>= fun b => pure (a, b)) >>= fun ⟨a, b⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  have h2 : (mb >>= fun b => ma >>= fun a => f (a, b)) =
           ((mb >>= fun b => ma >>= fun a => pure (b, a)) >>= fun ⟨b, a⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  rw [h1, h2]
  -- Apply commutativity
  rw [bind_comm]
  simp_all

alias bind_swap := bind_comm_comp

@[simp] theorem CommutativeAt.bind_comm {m} [Monad m] [LawfulMonad m] {α β}
    (ma : m α) (mb : m β) (h : CommutativeAt m ma mb) :
      (ma >>= fun a => mb >>= fun b => pure (a, b)) =
        (mb >>= fun b => ma >>= fun a => pure (a, b)) :=
  h

-- The main commutativity lemma for composed computations
@[simp] theorem CommutativeAt.bind_comm_comp {m} [Monad m] [LawfulMonad m] {α β γ}
    (ma : m α) (mb : m β) (h : CommutativeAt m ma mb) (f : α × β → m γ) :
      (ma >>= fun a => mb >>= fun b => f (a, b)) = (mb >>= fun b => ma >>= fun a => f (a, b)) := by
  -- Use associativity to factor out the pair construction
  have h1 : (ma >>= fun a => mb >>= fun b => f (a, b)) =
           ((ma >>= fun a => mb >>= fun b => pure (a, b)) >>= fun ⟨a, b⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  have h2 : (mb >>= fun b => ma >>= fun a => f (a, b)) =
           ((mb >>= fun b => ma >>= fun a => pure (b, a)) >>= fun ⟨b, a⟩ => f (a, b)) := by
    simp only [bind_assoc, pure_bind]
  rw [h1, h2]
  -- Apply commutativity
  rw [h]
  simp_all

/-! ### TODO: fix below lemmas & figure out a good naming scheme -/

/-- Commutativity extends to sequences of three operations (swap first two) -/
theorem bind_comm_triple_swap_12 {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (do let a ← ma; let b ← mb; let c ← mc; f (a, b, c)) =
    (do let b ← mb; let a ← ma; let c ← mc; f (a, b, c)) := by
  rw [bind_comm_comp ma mb (fun p => mc >>= fun c => f (p.1, p.2, c))]

/-- Swap second and third elements in a triple of monadic actions -/
theorem bind_comm_triple_swap_23 {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (do let a ← ma; let b ← mb; let c ← mc; f (a, b, c)) =
    (ma >>= fun a => mc >>= fun c => mb >>= fun b => f (a, b, c)) := by
  congr; ext a
  exact bind_comm_comp mb mc (fun p => f (a, p.1, p.2))

-- Quadruple operations: swap first two elements (1,2,3,4) → (2,1,3,4)
theorem bind_comm_quad_swap_12 {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ ε}
    (ma : m α) (mb : m β) (mc : m γ) (md : m δ) (f : α × β × γ × δ → m ε) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => md >>= fun d => f (a, b, c, d)) =
    (mb >>= fun b => ma >>= fun a => mc >>= fun c => md >>= fun d => f (a, b, c, d)) :=
  bind_comm_comp ma mb (fun p => mc >>= fun c => md >>= fun d => f (p.1, p.2, c, d))

-- Swap second and third elements in quadruple (1,2,3,4) → (1,3,2,4)
theorem bind_comm_quad_swap_23 {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ ε}
    (ma : m α) (mb : m β) (mc : m γ) (md : m δ) (f : α × β × γ × δ → m ε) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => md >>= fun d => f (a, b, c, d)) =
    (ma >>= fun a => mc >>= fun c => mb >>= fun b => md >>= fun d => f (a, b, c, d)) := by
  congr; ext a
  exact bind_comm_comp mb mc (fun p => md >>= fun d => f (a, p.1, p.2, d))

-- Swap third and fourth elements in quadruple (1,2,3,4) → (1,2,4,3)
theorem bind_comm_quad_swap_34 {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ ε}
    (ma : m α) (mb : m β) (mc : m γ) (md : m δ) (f : α × β × γ × δ → m ε) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => md >>= fun d => f (a, b, c, d)) =
    (ma >>= fun a => mb >>= fun b => md >>= fun d => mc >>= fun c => f (a, b, c, d)) := by
  congr; ext a; congr; ext b
  exact bind_comm_comp mc md (fun p => f (a, b, p.1, p.2))

-- Swap pairs in quadruple (1,2,3,4) → (3,4,1,2)
theorem bind_comm_quad_swap_pairs {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ ε}
    (ma : m α) (mb : m β) (mc : m γ) (md : m δ) (f : α × β × γ × δ → m ε) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => md >>= fun d => f (a, b, c, d)) =
    (mc >>= fun c => md >>= fun d => ma >>= fun a => mb >>= fun b => f (a, b, c, d)) := by sorry
  -- Use the fact that we can swap the two pairs
  -- exact bind_comm_comp (ma >>= fun a => mb >>= fun b => pure (a, b))
  --                       (mc >>= fun c => md >>= fun d => pure (c, d))
  --                       (fun p => f (p.1.1, p.1.2, p.2.1, p.2.2))

theorem bind_reverse_triple {m} [Monad m] [LawfulMonad m] [Commutative m] {α β γ δ}
    (ma : m α) (mb : m β) (mc : m γ) (f : α × β × γ → m δ) :
    (ma >>= fun a => mb >>= fun b => mc >>= fun c => f (a, b, c)) =
    (mc >>= fun c => mb >>= fun b => ma >>= fun a => f (a, b, c)) := by
  -- First swap a and b
  rw [bind_comm_triple_swap_12]
  sorry
  -- Then swap (b,a) with c by treating (b,a) as a single unit
  -- rw [bind_comm_comp (mb >>= fun b => ma >>= fun a => pure (a, b)) mc
  --     (fun p => f p.1 p.2)]

/-- The identity monad is commutative -/
instance : Commutative Id where
  bind_comm := fun _ _ => rfl

/- Note: `OptionT m` and `ExceptT ε m` are not commutative in general, even if `m` is commutative.
  For example, `OptionT Option` is not commutative. -/

instance : Commutative Option where
  bind_comm := fun ma mb => by cases ma <;> cases mb <;> rfl

instance {ε} [Subsingleton ε] : Commutative (Except ε) where
  bind_comm := fun ma mb => by
    cases ma <;> cases mb <;> simp [CommutativeAt, Bind.bind, Pure.pure, Except.bind, Except.pure]
    exact Subsingleton.elim _ _

/-- The `ReaderT ρ m` monad is commutative if the underlying monad is commutative -/
instance {ρ} {m} [Monad m] [Commutative m] : Commutative (ReaderT ρ m) where
  bind_comm := fun ma mb => by
    dsimp [CommutativeAt, Pure.pure, Bind.bind]
    unfold ReaderT.bind ReaderT.pure
    dsimp only
    funext r
    rw [bind_comm]

/-- The `WriterT` monad is commutative if the underlying monad is commutative and the monoid is
  commutative -/
instance {ω} {m} [Monad m] [LawfulMonad m] [Commutative m] [CommMonoid ω] :
    Commutative (WriterT ω m) where
  bind_comm := fun ma mb => by
    dsimp [CommutativeAt, Pure.pure, Bind.bind]
    unfold WriterT.mk
    sorry

attribute [local instance] Set.monad

/-- The set monad is commutative. This is not registered as an instance similar to how
  `Set.monad` is not registered as an instance. -/
def Set.monadComm : Commutative Set where
  bind_comm := fun ma mb => by
    dsimp [CommutativeAt, Pure.pure, Bind.bind]
    aesop

/-- The `PMF` monad is commutative -/
instance : Commutative PMF where
  bind_comm := fun ma mb => by
    dsimp [CommutativeAt, Pure.pure, Bind.bind, PMF.pure, PMF.bind]
    ext ⟨a, b⟩
    simp [PMF.instFunLike]
    sorry
    -- simp_rw [← Summable.tsum_mul_left]

end Monad
