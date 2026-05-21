/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Evaluation Semantics for ReaderT

This file provides monad homomorphisms for evaluating `ReaderT ρ m` computations
by fixing the environment parameter.

Unlike `StateT`, `ReaderT` evaluation at a fixed environment is a valid monad homomorphism
because the environment is read-only and doesn't change during computation.

## Main definitions

* `ReaderT.evalAt ρ0`: Monad homomorphism `ReaderT ρ m →ᵐ m` by evaluation at `ρ0`
* `ReaderT.toSPMF ρ0`: Lift `MonadLiftT m SPMF` through `ReaderT` at fixed `ρ0`
* `ReaderT.toPMF ρ0`: Lift `MonadLiftT m PMF` through `ReaderT` at fixed `ρ0`

## Design notes

We do NOT provide global `MonadLift (ReaderT ρ m) SPMF` instances because there's no
canonical choice of environment. Instead, users explicitly provide the environment
when constructing the evaluation homomorphism.

For cryptographic games with random oracles, the typical pattern is:
1. Generate oracle table with some distribution
2. Use `toSPMF`/`toPMF` to evaluate the protocol at that table
3. Compose with the table distribution to get overall game probability

-/

universe u v

variable {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

namespace ReaderT

/-- Evaluate a `ReaderT` computation at a fixed environment `ρ0`.
This is a monad homomorphism because `ReaderT` is read-only. -/
def evalAt (ρ0 : ρ) : ReaderT ρ m →ᵐ m where
  toFun     := fun {α} (mx : ReaderT ρ m α) => mx ρ0
  toFun_pure' := by intros; rfl
  toFun_bind' := by intros; rfl

@[simp] lemma evalAt_apply (ρ0 : ρ) (mx : ReaderT ρ m α) :
    evalAt ρ0 mx = mx ρ0 := rfl

@[simp] lemma evalAt_pure (ρ0 : ρ) (x : α) :
    evalAt (m := m) ρ0 (pure x : ReaderT ρ m α) = pure x := rfl

@[simp] lemma evalAt_bind (ρ0 : ρ) (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    evalAt ρ0 (mx >>= f) = evalAt ρ0 mx >>= fun x => evalAt ρ0 (f x) := rfl

end ReaderT

namespace ReaderT

/-- Lift `m → SPMF` to a homomorphism `ReaderT ρ m →ᵐ SPMF` by fixing `ρ0`.

This allows evaluating reader computations to sub-probability distributions
when the base monad `m` has such an evaluation. -/
noncomputable def toSPMF (ρ0 : ρ) [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    ReaderT ρ m →ᵐ SPMF :=
  MonadHom.ofLift m SPMF ∘ₘ ReaderT.evalAt (m := m) ρ0

/-- Lift `m → PMF` to a homomorphism `ReaderT ρ m →ᵐ PMF` by fixing `ρ0`. -/
noncomputable def toPMF (ρ0 : ρ) [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    ReaderT ρ m →ᵐ PMF :=
  MonadHom.ofLift m PMF ∘ₘ ReaderT.evalAt (m := m) ρ0

section evalDist_lemmas

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (ρ0 : ρ)

/-- Evaluating `pure x` at any environment gives the same result as `pure x` in the base monad. -/
@[simp] lemma toSPMF_pure (x : α) :
    ReaderT.toSPMF ρ0 (pure x : ReaderT ρ m α) = (liftM (pure x : m α) : SPMF α) := by
  change liftM ((ReaderT.evalAt ρ0).toFun α (pure x : ReaderT ρ m α)) = (liftM (pure x : m α)
      : SPMF α)
  rfl

/-- Evaluating a bind distributes through the monad homomorphism. -/
@[simp] lemma toSPMF_bind (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    ReaderT.toSPMF ρ0 (mx >>= f) =
      ReaderT.toSPMF ρ0 mx >>= fun x => ReaderT.toSPMF ρ0 (f x) :=
  (ReaderT.toSPMF ρ0).toFun_bind' mx f

end evalDist_lemmas

section evalPMF_lemmas

variable [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] (ρ0 : ρ)

@[simp] lemma toPMF_pure (x : α) :
    ReaderT.toPMF ρ0 (pure x : ReaderT ρ m α) = (liftM (pure x : m α) : PMF α) := by
  change liftM ((ReaderT.evalAt ρ0).toFun α (pure x : ReaderT ρ m α)) = (liftM (pure x : m α)
      : PMF α)
  rfl

@[simp] lemma toPMF_bind (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    ReaderT.toPMF ρ0 (mx >>= f) =
      ReaderT.toPMF ρ0 mx >>= fun x => ReaderT.toPMF ρ0 (f x) :=
  (ReaderT.toPMF ρ0).toFun_bind' mx f

end evalPMF_lemmas

end ReaderT
