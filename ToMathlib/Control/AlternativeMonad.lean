/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Batteries.Control.AlternativeMonad

-- These have now made it into batteries, except for a few lemmas

universe u v w

-- Guess this is not always true?
-- theorem pure_orElse [Alternative m] [LawfulAlternative m] {α} (x : α) (y : m α) :
--     (pure x <|> y) = pure x := sorry

variable {m : Type _ → Type _} {n : Type _ → Type _}

section liftM

variable {α β}

@[simp] theorem liftM_failure [Alternative m] [Alternative n] [MonadLift m n]
    [LawfulAlternativeLift m n] : liftM (failure : m α) = (failure : n α) := monadLift_failure

@[simp] theorem liftM_orElse [Alternative m] [Alternative n] [MonadLift m n]
    [LawfulAlternativeLift m n] (x y : m α) : liftM (x <|> y) = (liftM x <|> liftM y : n α) :=
  monadLift_orElse x y

theorem monadLift_guard [AlternativeMonad m] [AlternativeMonad n] [MonadLift m n]
    [LawfulAlternativeLift m n] [LawfulMonadLift m n] (p : Prop) [Decidable p] :
    monadLift (guard p : m Unit) = (guard p : n Unit) := by
  simp only [guard, apply_ite (f := monadLift), liftM_pure, liftM_failure]

@[simp] theorem liftM_guard [AlternativeMonad m] [AlternativeMonad n] [MonadLift m n]
    [LawfulAlternativeLift m n] [LawfulMonadLift m n] (p : Prop) [Decidable p] :
    liftM (guard p : m Unit) = (guard p : n Unit) :=
  monadLift_guard p

theorem monadLift_optional [AlternativeMonad m] [AlternativeMonad n]
    [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [LawfulAlternativeLift m n]
    [LawfulMonadLift m n]
    (x : m α) : monadLift (optional x) = optional (monadLift x : n α) := by
  simp only [optional, liftM_orElse, liftM_map, liftM_pure]

@[simp] theorem liftM_optional [AlternativeMonad m] [AlternativeMonad n]
    [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [LawfulAlternativeLift m n]
    [LawfulMonadLift m n]
    (x : m α) : liftM (optional x) = optional (liftM x : n α) :=
  monadLift_optional x

end liftM

namespace Option

variable {α β}

theorem monadLift_elimM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (x : m (Option α)) (y : m β) (z : α → m β) :
      monadLift (Option.elimM x y z) =
        Option.elimM (monadLift x : n (Option α)) (monadLift y) (fun x => monadLift (z x)) :=
  (monadLift_bind _ _).trans (by congr; funext x; cases x <;> rfl)

@[simp]
theorem liftM_elimM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (x : m (Option α)) (y : m β) (z : α → m β) :
      liftM (Option.elimM x y z) = Option.elimM (x : n (Option α)) (y) (fun x => z x) :=
  monadLift_elimM x y z

end Option
