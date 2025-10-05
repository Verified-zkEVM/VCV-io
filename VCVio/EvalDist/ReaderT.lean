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
* `HasEvalSPMF.readerAt ρ0`: Lift `HasEvalSPMF m` through `ReaderT` at fixed `ρ0`
* `HasEvalPMF.readerAt ρ0`: Lift `HasEvalPMF m` through `ReaderT` at fixed `ρ0`

## Design notes

We do NOT provide global `HasEvalSPMF (ReaderT ρ m)` instances because there's no
canonical choice of environment. Instead, users explicitly provide the environment
when constructing the evaluation homomorphism.

For cryptographic games with random oracles, the typical pattern is:
1. Generate oracle table with some distribution
2. Use `readerAt` to evaluate the protocol at that table
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

/-- Lift `HasEvalSPMF m` to a homomorphism `ReaderT ρ m →ᵐ SPMF` by fixing `ρ0`.

This allows evaluating reader computations to sub-probability distributions
when the base monad `m` has such an evaluation. -/
noncomputable def HasEvalSPMF.readerAt (ρ0 : ρ) [HasEvalSPMF m] :
    ReaderT ρ m →ᵐ SPMF :=
  HasEvalSPMF.toSPMF ∘ₘ ReaderT.evalAt (m := m) ρ0

/-- Lift `HasEvalPMF m` to a homomorphism `ReaderT ρ m →ᵐ PMF` by fixing `ρ0`.

This allows evaluating reader computations to probability distributions
when the base monad `m` has such an evaluation. -/
noncomputable def HasEvalPMF.readerAt (ρ0 : ρ) [HasEvalPMF m] :
    ReaderT ρ m →ᵐ PMF :=
  HasEvalPMF.toPMF ∘ₘ ReaderT.evalAt (m := m) ρ0

namespace ReaderT

section evalDist_lemmas

variable [HasEvalSPMF m] (ρ0 : ρ)

/-- Evaluating `pure x` at any environment gives the same result as `pure x` in the base monad. -/
@[simp] lemma evalSPMF_pure (x : α) :
    HasEvalSPMF.readerAt ρ0 (pure x : ReaderT ρ m α) = HasEvalSPMF.toSPMF (pure x : m α) := by
  simp [HasEvalSPMF.readerAt]

/-- Evaluating a bind distributes through the monad homomorphism. -/
@[simp] lemma evalSPMF_bind (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    HasEvalSPMF.readerAt ρ0 (mx >>= f) =
      HasEvalSPMF.readerAt ρ0 mx >>= fun x => HasEvalSPMF.readerAt ρ0 (f x) := by
  simp [HasEvalSPMF.readerAt, MonadHom.comp_apply]

end evalDist_lemmas

section evalPMF_lemmas

variable [HasEvalPMF m] (ρ0 : ρ)

@[simp] lemma evalPMF_pure (x : α) :
    HasEvalPMF.readerAt ρ0 (pure x : ReaderT ρ m α) = HasEvalPMF.toPMF (pure x : m α) := by
  simp [HasEvalPMF.readerAt]

@[simp] lemma evalPMF_bind (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    HasEvalPMF.readerAt ρ0 (mx >>= f) =
      HasEvalPMF.readerAt ρ0 mx >>= fun x => HasEvalPMF.readerAt ρ0 (f x) := by
  simp [HasEvalPMF.readerAt, MonadHom.comp_apply]

end evalPMF_lemmas

end ReaderT

/-! ### Optional: Instances with canonical environments

If you have a canonical choice of environment (e.g., via `[Inhabited ρ]`),
you can uncomment these to get automatic `HasEvalSPMF/PMF` instances.

However, for most cryptographic use cases, it's better to keep the environment
explicit and use the `readerAt` homomorphisms directly.

```lean
noncomputable instance [HasEvalSPMF m] [Inhabited ρ] :
    HasEvalSPMF (ReaderT ρ m) where
  toSPMF := HasEvalSPMF.readerAt (m := m) default

noncomputable instance [HasEvalPMF m] [Inhabited ρ] :
    HasEvalPMF (ReaderT ρ m) where
  toPMF := HasEvalPMF.readerAt (m := m) default
```
-/
