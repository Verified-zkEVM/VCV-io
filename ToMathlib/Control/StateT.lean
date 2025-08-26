/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.Monad.Free
import ToMathlib.General
import Batteries.Control.Lemmas

/-!
# Lemmas about `StateT`
-/

universe u v w

namespace StateT

variable {m : Type u → Type v} {m' : Type u → Type w}
  {σ α β : Type u}

instance [MonadLift m m'] : MonadLift (StateT σ m) (StateT σ m') where
  monadLift x := StateT.mk fun s => liftM ((x.run) s)

@[simp]
lemma liftM_of_liftM_eq [MonadLift m m'] (x : StateT σ m α) :
    (liftM x : StateT σ m' α) = StateT.mk fun s => liftM (x.run s) := rfl

lemma liftM_def [Monad m] (x : m α) : (liftM x : StateT σ m α) = StateT.lift x := rfl

-- TODO: should this be simp?
lemma monad_pure_def [Monad m] (x : α) :
    (pure x : StateT σ m α) = StateT.pure x := rfl

lemma monad_bind_def [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) :
    x >>= f = StateT.bind x f := rfl

lemma monad_failure_eq [Monad m] [Alternative m] :
    (failure : StateT σ m α) = StateT.failure := rfl

@[simp]
lemma run_failure' [Monad m] [Alternative m] :
    (failure : StateT σ m α).run = fun _ => failure := rfl

@[simp]
lemma mk_pure_eq_pure [Monad m] (x : α) :
  StateT.mk (λ s ↦ pure (x, s)) = (pure x : StateT σ m α) := rfl

end StateT
