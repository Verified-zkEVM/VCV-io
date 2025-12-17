/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import ToMathlib.Control.Monad.Free
import Batteries.Control.AlternativeMonad
import Batteries.Control.OptionT
import ToMathlib.Control.Monad.Hom
import ToMathlib.General

/-!
# Lemmas about `OptionT`
-/

universe u v w

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w}
  (f : {α : Type u} →  m α → n α) {α β γ : Type u}

@[simp] lemma run_lift {m : Type u → Type v} [Monad m]
    {α : Type u} (x : m α) : (OptionT.lift x).run = x := rfl

-- @[simp]
lemma monad_pure_eq_pure [Monad m] (x : α) :
    (pure x : OptionT m α) = OptionT.pure x := rfl

-- @[simp]
lemma monad_bind_eq_bind [Monad m] (x : OptionT m α) (y : α → OptionT m β) :
    x >>= y = OptionT.bind x y := rfl

-- lemma run_seq {α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
--     (f : OptionT m (α → β)) (x : OptionT m α) :
--     (f <*> x).run = (do let g ← f.run; match g with
--       | some g => Option.map g <$> x.run
--       | none => pure none) := by
--   simp only [seq_eq_bind_map, run_bind, run_map]
--   exact bind_congr fun | some x => rfl | none => rfl

lemma liftM_def {m : Type u → Type v} [Monad m] {α : Type u}
    (x : m α) : (x : OptionT m α) = OptionT.lift x := rfl

section mapM

/-- Canonical lifting of a map from `m α → n α` to one from `OptionT m α → n α`
given an `Alternative n` instance to handle failure. -/
protected def mapM {m : Type u → Type v} {n : Type u → Type w}
    [AlternativeMonad n] (f : {α : Type u} → m α → n α)
    {α : Type u} (x : OptionT m α) : n α :=
  do (← f x.run).getM

-- instance {m : Type u → Type v} {n : Type u → Type w}
--     [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
--     (f : {α : Type u} → m α → n α)
--     [MonadHomClass m n @f] :
--     MonadHomClass (OptionT m) n (@OptionT.mapM m n _ f) where
--   map_pure {α} x := by simp [OptionT.mapM]
--   map_bind {α β} mx my := by
--     simp [OptionT.mapM, Function.comp_def, Option.elimM]
--     refine congr_arg (f mx.run >>= ·) (funext fun x => ?_)
--     cases x <;> simp

/-- Bundled version of `mapM`.
dtumad: we should probably just pick one of these (probably the hom class non-bundled approach)-/
protected def mapM' {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
    (f : m →ᵐ n) : OptionT m →ᵐ n where
  toFun _ x := do match (← f x.run) with
    | some x => return x
    | none => failure
  toFun_pure' x := by
    simp
  toFun_bind' x y := by
    simp [Option.elimM]
    congr 1
    ext x
    cases x
    simp
    simp

@[simp]
lemma mapM'_lift {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
    (f : m →ᵐ n) (x : m α) : OptionT.mapM' f (OptionT.lift x) = f x := by
  simp [OptionT.mapM', OptionT.lift]

@[simp]
lemma mapM'_failure {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
    (f : m →ᵐ n) : OptionT.mapM' f (failure : OptionT m α) = failure := by
  simp [OptionT.mapM']

end mapM

end OptionT
