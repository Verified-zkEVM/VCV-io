/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Instances
import VCVio.EvalDist.Monad.Map
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

NOTE: this should be a high priority to add for more complex proofs
-/

universe u v

variable {ε : Type u} {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace ExceptT

section HasEvalSet

/-- Standalone `HasEvalSet (ExceptT ε m)` instance under the weaker `[HasEvalSet m]` assumption.

This is deliberately kept separate from the `HasEvalSPMF (ExceptT ε m)` instance below, which
re-exports the same `toSet` to make the resulting typeclass diamond definitionally equal.
Keeping this standalone instance means `support` on `ExceptT ε m` works without requiring a
full `HasEvalSPMF m` — only `HasEvalSet m` is needed (e.g., for `support_liftM`). -/
noncomputable instance (ε : Type u) (m : Type u → Type v) [Monad m] [HasEvalSet m] :
    HasEvalSet (ExceptT ε m) where
  toSet.toFun α mx := Except.ok ⁻¹' (support mx.run)
  toSet.toFun_pure' x := Set.ext fun y => by
    show Except.ok y ∈ support (pure (Except.ok x) : m _) ↔ y = x
    simp
  toSet.toFun_bind' mx f := Set.ext fun x => by
    simp only [Set.mem_preimage, Set.bind_def, Set.mem_iUnion₂]
    show Except.ok x ∈ support (mx.run >>= ExceptT.bindCont f) ↔ _
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨r, hr, hx⟩
      cases r with
      | ok a => exact ⟨a, hr, hx⟩
      | error e => simp [ExceptT.bindCont] at hx
    · rintro ⟨a, ha, hx⟩
      exact ⟨.ok a, ha, hx⟩

variable [HasEvalSet m]

@[aesop unsafe norm, grind =]
lemma support_def (mx : ExceptT ε m α) :
    support mx = Except.ok ⁻¹' (support mx.run) := rfl

@[simp low]
lemma mem_support_iff (mx : ExceptT ε m α) (x : α) :
    x ∈ support mx ↔ Except.ok x ∈ support mx.run := Iff.rfl

omit [HasEvalSet m] in
@[simp]
lemma run_liftM (mx : m α) : (liftM mx : ExceptT ε m α).run = Except.ok <$> mx := rfl

@[simp]
lemma support_liftM [LawfulMonad m] (mx : m α) :
    support (liftM mx : ExceptT ε m α) = support mx := by
  ext x
  simp only [mem_support_iff, run_liftM, support_map, Set.mem_image]
  constructor
  · rintro ⟨a, ha, h⟩; cases h; exact ha
  · exact fun h => ⟨x, h, rfl⟩

end HasEvalSet

section HasEvalFinset

private instance instDecidableEqExcept [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := fun a b => match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else
      isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else
      isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

noncomputable instance (ε : Type u) (m : Type u → Type v) [Monad m]
    [DecidableEq ε] [HasEvalSet m] [HasEvalFinset m] :
    HasEvalFinset (ExceptT ε m) where
  finSupport mx := (finSupport mx.run).preimage Except.ok
    (by intro a b; simp [Except.ok.injEq])
  coe_finSupport mx := by
    ext x; simp

variable [DecidableEq ε] [HasEvalSet m] [HasEvalFinset m]

@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : ExceptT ε m α) :
    finSupport mx = (finSupport mx.run).preimage Except.ok
      (fun a _ => by simp [Except.ok.injEq]) := rfl

@[simp low]
lemma mem_finSupport_iff' [DecidableEq α] (mx : ExceptT ε m α) (x : α) :
    x ∈ finSupport mx ↔ Except.ok x ∈ finSupport mx.run := by
  simp [finSupport_def, Finset.mem_preimage]

@[simp]
lemma finSupport_liftM [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : ExceptT ε m α) = finSupport mx := by
  ext x; simp [mem_finSupport_iff']

end HasEvalFinset

section HasEvalSPMF

/-- Monad homomorphism from `ExceptT ε m` to `SPMF`, treating errors as failure mass.
Given `mx : ExceptT ε m α`, we evaluate the underlying `m (Except ε α)` to an `SPMF`,
then route `Except.ok x` to `pure x` and `Except.error _` to `failure`. -/
noncomputable def toSPMF' [HasEvalPMF m] : ExceptT ε m →ᵐ SPMF where
  toFun {α} (mx : ExceptT ε m α) : SPMF α :=
    HasEvalSPMF.toSPMF mx.run >>= fun r =>
      match r with
      | Except.ok x => pure x
      | Except.error _ => failure
  toFun_pure' x := by simp
  toFun_bind' mx f := by
    show HasEvalSPMF.toSPMF (mx.run >>= ExceptT.bindCont f) >>= _ = _
    simp only [MonadHom.toFun_bind', bind_assoc]
    congr 1; funext r
    cases r with
    | ok a =>
      show HasEvalSPMF.toSPMF (f a).run >>= _ =
        pure a >>= fun b => HasEvalSPMF.toSPMF (f b).run >>= _
      simp
    | error e => simp [ExceptT.bindCont]

private lemma toSPMF'_apply_eq [HasEvalPMF m] (mx : ExceptT ε m α) (x : α) :
    ExceptT.toSPMF' mx x = HasEvalSPMF.toSPMF mx.run (Except.ok x) := by
  rw [show (ExceptT.toSPMF' mx : SPMF α) =
    HasEvalSPMF.toSPMF mx.run >>= fun r =>
      match r with | Except.ok a => pure a | Except.error _ => failure from rfl]
  rw [SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (Except.ok x) fun y hy => ?_).trans ?_
  · cases y with
    | error e => simp
    | ok a =>
        have : x ≠ a := by intro h; subst h; exact hy rfl
        simp [this]
  · simp

/-- Lift `HasEvalPMF m` to `HasEvalSPMF (ExceptT ε m)`.
Errors contribute to failure mass. -/
noncomputable instance (ε : Type u) (m : Type u → Type v) [Monad m] [HasEvalPMF m] :
    HasEvalSPMF (ExceptT ε m) where
  toSPMF := ExceptT.toSPMF'
  support_eq mx := by
    ext x
    rw [ExceptT.mem_support_iff, SPMF.mem_support_iff, toSPMF'_apply_eq]
    change Except.ok x ∈ support mx.run ↔ evalDist mx.run (Except.ok x) ≠ 0
    exact mem_support_iff_evalDist_apply_ne_zero mx.run (Except.ok x)

variable [HasEvalPMF m]

lemma evalDist_eq (mx : ExceptT ε m α) :
    evalDist mx = ExceptT.toSPMF' mx := rfl

@[grind =]
lemma probOutput_eq (mx : ExceptT ε m α) (x : α) :
    Pr[= x | mx] = Pr[= Except.ok x | mx.run] := by
  simp only [probOutput_def]
  exact toSPMF'_apply_eq mx x

@[grind =]
lemma probFailure_eq (mx : ExceptT ε m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] +
      Pr[(fun r => match r with | Except.error _ => True | Except.ok _ => False) | mx.run] := by
  simp only [probFailure_def, probEvent_eq_tsum_indicator, probOutput_def]
  rw [show evalDist mx = (HasEvalSPMF.toSPMF mx.run >>= fun r =>
      match r with | Except.ok a => pure a | Except.error _ => failure : SPMF α) from rfl]
  simp [SPMF.toPMF_bind, Option.elimM, PMF.bind_apply, tsum_option,
    SPMF.apply_eq_toPMF_some, evalDist_def]
  refine tsum_congr fun r => ?_
  cases r <;> simp [SPMF.toPMF_failure, SPMF.toPMF_pure]


lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | (liftM mx : ExceptT ε m α)] = Pr[= x | mx] := by
  rw [probOutput_eq]
  exact probOutput_map_injective mx (fun a b h => by cases h; rfl) x

private lemma evalDist_liftM [LawfulMonad m] (mx : m α) :
    evalDist (liftM mx : ExceptT ε m α) = evalDist mx :=
  SPMF.ext fun x => probOutput_liftM mx x

lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | (liftM mx : ExceptT ε m α)] = Pr[⊥ | mx] := by
  simp only [probFailure_def, evalDist_liftM]

lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | (liftM mx : ExceptT ε m α)] = Pr[p | mx] := by
  simp only [probEvent_def, evalDist_liftM]

end HasEvalSPMF

end ExceptT
