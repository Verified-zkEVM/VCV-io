/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Control.Monad.Writer
import Batteries.Control.AlternativeMonad

/-!
# Laws for well behaved monadic `failure` operation
-/

universe u v w

/-- Typeclass for instances where `∅` is an identity for `++`. -/
class LawfulAppend (α : Type u)
    [EmptyCollection α] [Append α] where
  empty_append (x : α) : ∅ ++ x = x
  append_empty (x : α) : x ++ ∅ = x
  append_assoc (x y z : α) : x ++ (y ++ z) = x ++ y ++ z

namespace LawfulAppend

attribute [simp] LawfulAppend.empty_append LawfulAppend.append_empty

attribute [grind =] LawfulAppend.empty_append
  LawfulAppend.append_empty LawfulAppend.append_assoc

instance {M : Type u → Type v} {ω : Type u} [Monad M]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] [LawfulMonad M] :
    LawfulMonad (WriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := by simp only [bind, WriterT.mk, pure, map_pure, LawfulAppend.append_empty,
    bind_pure_comp, Functor.map, implies_true])
  (id_map := by simp [Functor.map, WriterT.mk])
  (pure_bind := by simp [Bind.bind, Pure.pure, WriterT.mk])
  (bind_assoc := by simp [Bind.bind, WriterT.mk, LawfulAppend.append_assoc])

instance (α : Type u) : LawfulAppend (List α) where
  empty_append := by simp
  append_empty := by simp
  append_assoc := by grind

end LawfulAppend

namespace WriterT

section basic

variable {m : Type u → Type v} [Monad m] {ω : Type u} {α β γ : Type u}

@[simp]
lemma run_mk {ω : Type u} [LawfulMonad m] (x : m (α × ω)) :
  (WriterT.mk x).run = x := rfl

@[simp]
lemma run_tell (w : ω) : (tell w : WriterT ω m PUnit).run = pure (⟨⟩, w) := rfl

section monoid

variable [Monoid ω]

@[simp]
lemma run_monadLift (x : m α) : (monadLift x : WriterT ω m α).run = (·, 1) <$> x := rfl

lemma liftM_def (x : m α) :
    (liftM x : WriterT ω m α) = WriterT.mk ((·, 1) <$> x) := rfl

lemma monadLift_def (x : m α) :
    (MonadLift.monadLift x : WriterT ω m α) = WriterT.mk ((·, 1) <$> x) := rfl

lemma bind_def (x : WriterT ω m α) (f : α → WriterT ω m β) :
    x >>= f = WriterT.mk (x.run >>= fun (a, w₁) ↦
      (Prod.map id (w₁ * ·)) <$> (f a)) := rfl

@[simp]
lemma run_pure [LawfulMonad m] (x : α) :
    (pure x : WriterT ω m α).run = pure (x, 1) := rfl

@[simp]
lemma run_bind [LawfulMonad m] (x : WriterT ω m α) (f : α → WriterT ω m β) :
    (x >>= f).run = x.run >>= fun (a, w₁) => Prod.map id (w₁ * ·) <$> (f a).run := rfl

@[simp]
lemma run_seqLeft {m : Type u → Type v} [Monad m] {ω : Type u} [Monoid ω] {α β : Type u}
    (x : WriterT ω m α) (y : WriterT ω m β) :
    (x *> y).run = x.run >>= fun z => Prod.map id (z.2 * ·) <$> y.run := rfl

@[simp]
lemma run_map (x : WriterT ω m α) (f : α → β) : (f <$> x).run = Prod.map f id <$> x.run := rfl

end monoid

section append

variable [EmptyCollection ω]

@[simp]
lemma run_monadLift' (x : m α) : (monadLift x : WriterT ω m α).run = (·, ∅) <$> x := rfl

lemma liftM_def' (x : m α) :
    (liftM x : WriterT ω m α) = WriterT.mk ((·, ∅) <$> x) := rfl

lemma monadLift_def' (x : m α) :
    (MonadLift.monadLift x : WriterT ω m α) = WriterT.mk ((·, ∅) <$> x) := rfl

variable [Append ω]

lemma bind_def' (x : WriterT ω m α) (f : α → WriterT ω m β) :
    x >>= f = WriterT.mk (x.run >>= fun (a, w₁) ↦
      (Prod.map id (w₁ ++ ·)) <$> (f a)) := rfl

@[simp]
lemma run_pure' [LawfulMonad m] (x : α) :
    (pure x : WriterT ω m α).run = pure (x, ∅) := rfl

@[simp]
lemma run_bind' [LawfulMonad m] (x : WriterT ω m α) (f : α → WriterT ω m β) :
    (x >>= f).run = x.run >>= fun (a, w₁) => Prod.map id (w₁ ++ ·) <$> (f a).run := rfl

@[simp]
lemma run_seqLeft' {m : Type u → Type v} [Monad m] {ω : Type u} [Monoid ω] {α β : Type u}
    (x : WriterT ω m α) (y : WriterT ω m β) :
    (x *> y).run = x.run >>= fun z => Prod.map id (z.2 * ·) <$> y.run := rfl

@[simp]
lemma run_map' (x : WriterT ω m α) (f : α → β) : (f <$> x).run = Prod.map f id <$> x.run := rfl

end append

end basic

-- @[simp]
-- lemma run_fail [AlternativeMonad m] [LawfulAlternative m] :
--     (failure : WriterT ω m α).run = Failure.fail := by
--   simp [failureOfLift_eq_lift_fail, WriterT.liftM_def]

-- /-- The naturally induced `Failure` on `WriterT` is lawful. -/
-- instance [Monad m] [LawfulMonad m] [Failure m] [LawfulFailure m] :
--     LawfulFailure (WriterT ω m) where
--   fail_bind' {α β} f := by
--     show WriterT.mk _ = WriterT.mk _
--     simp [monadLift_def, map_eq_bind_pure_comp, WriterT.mk, bind_assoc,
--       failureOfLift_eq_lift_fail, liftM_def]

section fail

variable {m : Type u → Type v} [AlternativeMonad m] {ω : Type u} {α β γ : Type u}

@[always_inline, inline]
protected def orElse {α : Type u} (x₁ : WriterT ω m α)
    (x₂ : Unit → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk (x₁.run <|> (x₂ ()).run)

@[always_inline, inline]
protected def failure {α : Type u} : WriterT ω m α := WriterT.mk failure

instance [Monoid ω] : AlternativeMonad (WriterT ω m) where
  failure := WriterT.failure
  orElse  := WriterT.orElse

@[simp]
lemma run_failure [Monoid ω] {α : Type u} : (failure : WriterT ω m α).run = failure := rfl

-- instance [Monoid ω] [LawfulMonad m] [LawfulAlternative m] :
--     LawfulAlternative (WriterT ω m) := sorry
  -- map_failure f := sorry
  -- failure_seq f := sorry
  -- orElse_failure f := sorry
  -- failure_orElse f := sorry
  -- orElse_assoc x y z := sorry
  -- map_orElse f := sorry

instance [Monoid ω] [LawfulMonad m] : LawfulMonadLift m (WriterT ω m) where
  monadLift_pure x := map_pure (·, 1) x
  monadLift_bind {α β} x y := by
    show WriterT.mk _ = WriterT.mk _
    simp [monadLift_def, WriterT.mk]

end fail

end WriterT
