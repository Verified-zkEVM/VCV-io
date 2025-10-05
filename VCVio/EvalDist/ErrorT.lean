/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Instances
import Mathlib.Control.Lawful

/-!
# Evaluation Semantics for ExceptT (ErrorT)

This file provides evaluation semantics for `ExceptT ε m` computations, lifting
`HasEvalPMF m` to `HasEvalSPMF (ExceptT ε m)`.

`ExceptT ε m α` represents computations that can fail with an error of type `ε`
or succeed with a value of type `α`. The underlying type is `m (Except ε α)`.

## Main definitions

* `ExceptT.toSPMF`: Monad homomorphism `ExceptT ε m →ᵐ SPMF` when `m` has `HasEvalPMF`
* Instance `HasEvalSPMF (ExceptT ε m)` when `[HasEvalPMF m]`

## Design notes

Similar to `OptionT`, we lift `HasEvalPMF m` to `HasEvalSPMF (ExceptT ε m)` because
error cases contribute failure mass. We map:
- `Except.ok x` → probability mass at `some x`
- `Except.error e` → failure mass (mapped to `none`)

This means we only support one layer of failure. If you need nested error handling,
you'll need to work with the underlying `m (Except ε α)` type directly.

-/

#check Std.Do.WP

universe u v

variable {ε : Type u} {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace ExceptT

/-- Map `ExceptT ε m` to `SPMF` by treating errors as failure.
This is a monad homomorphism that maps successful computations to `some x`
and errors to `none` (failure mass). -/
noncomputable def toSPMF [HasEvalPMF m] : ExceptT ε m →ᵐ SPMF where
  toFun {α} (mx : ExceptT ε m α) :=
    OptionT.mk (HasEvalPMF.toPMF mx.run >>= fun r =>
      match r with
      | Except.ok x => pure (some x)
      | Except.error _ => pure none)
  toFun_pure' := by
    intro α x
    simp [pure, ExceptT.pure, OptionT.mk]
    sorry
  toFun_bind' := by
    intro α β mx f
    simp [bind, ExceptT.bind, OptionT.mk]
    sorry

end ExceptT

/-- Lift `HasEvalPMF m` to `HasEvalSPMF (ExceptT ε m)`.
Errors contribute to failure mass. -/
noncomputable instance [HasEvalPMF m] : HasEvalSPMF (ExceptT ε m) where
  toSPMF := ExceptT.toSPMF

namespace ExceptT

section lemmas

variable [HasEvalPMF m]

/-- The probability of a successful output `x` in `ExceptT` equals the probability
of getting `Except.ok x` in the underlying computation. -/
lemma probOutput_eq (mx : ExceptT ε m α) (x : α) :
    Pr[= x | mx] = Pr[= Except.ok x | mx.run] := by
  sorry

/-- The probability of an event `p` in `ExceptT` equals the probability
of the event holding on successful values in the underlying computation. -/
lemma probEvent_eq (mx : ExceptT ε m α) (p : α → Prop) :
    Pr[p | mx] = Pr[(fun r => match r with | Except.ok a => p a | Except.error _ => False) | mx.run] := by
  sorry

/-- The failure probability in `ExceptT` equals the probability of getting
any error in the underlying computation. -/
lemma probFailure_eq (mx : ExceptT ε m α) :
    Pr[⊥ | mx] = Pr[(fun r => match r with | Except.error _ => True | Except.ok _ => False) | mx.run] := by
  sorry

/-- Lifting a computation from `m` to `ExceptT ε m` preserves output probabilities. -/
@[simp] lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | (liftM mx : ExceptT ε m α)] = Pr[= x | mx] := by
  sorry

/-- Lifting a computation from `m` to `ExceptT ε m` preserves event probabilities. -/
@[simp] lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | (liftM mx : ExceptT ε m α)] = Pr[p | mx] := by
  sorry

/-- Lifted computations never fail. -/
@[simp] lemma probFailure_lift [LawfulMonad m] (mx : m α) :
    Pr[⊥ | (liftM mx : ExceptT ε m α)] = 0 := by
  sorry

end lemmas

end ExceptT
