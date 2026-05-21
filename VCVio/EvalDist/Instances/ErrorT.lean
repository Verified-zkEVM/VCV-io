/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Monad.Map
import Mathlib.Control.Lawful

/-!
# Evaluation Semantics for ExceptT (ErrorT)

This file provides evaluation semantics for `ExceptT ε m` computations, lifting
`MonadLiftT m PMF` to `MonadLift (ExceptT ε m) SPMF`.

`ExceptT ε m α` represents computations that can fail with an error of type `ε`
or succeed with a value of type `α`. The underlying type is `m (Except ε α)`.

## Main definitions

* `ExceptT.toSPMF'`: Monad homomorphism `ExceptT ε m →ᵐ SPMF` when `m` lifts into `PMF`
* Instance `MonadLift (ExceptT ε m) SPMF` when `[MonadLiftT m PMF] [LawfulMonadLiftT m PMF]`

## Design notes

Similar to `OptionT`, we lift `MonadLiftT m PMF` to `MonadLift (ExceptT ε m) SPMF` because
error cases contribute failure mass. We map:
- `Except.ok x` → probability mass at `some x`
- `Except.error e` → failure mass (mapped to `none`)

This means we only support one layer of failure. If you need nested error handling,
you'll need to work with the underlying `m (Except ε α)` type directly.
-/

universe u v

variable {ε : Type u} {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace ExceptT

section EvalSet

/-- Standalone `MonadLiftT (ExceptT ε m) SetM` instance under the weaker `[MonadLiftT m SetM]`
assumption. Keeping this standalone means `support` on `ExceptT ε m` works without requiring a
full `MonadLiftT m SPMF` lift — only `MonadLiftT m SetM` is needed. -/
noncomputable instance instMonadLiftTSetM (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] : MonadLiftT (ExceptT ε m) SetM where
  monadLift mx := Except.ok ⁻¹' (support mx.run)

noncomputable instance instLawfulMonadLiftTSetM (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] :
    LawfulMonadLiftT (ExceptT ε m) SetM where
  monadLift_pure x := by
    change Except.ok ⁻¹' (support (pure (Except.ok x) : m _)) = pure x
    ext y
    change Except.ok y ∈ support (pure (Except.ok x) : m _) ↔ y = x
    simp
  monadLift_bind mx f := by
    change (Except.ok ⁻¹' (support (mx >>= f : ExceptT ε m _).run) : SetM _) =
      (Except.ok ⁻¹' (support mx.run) >>=
        fun a => Except.ok ⁻¹' support (f a).run : SetM _)
    ext x
    simp only [Set.mem_preimage]
    change Except.ok x ∈ support (mx.run >>= ExceptT.bindCont f) ↔ _
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨r, hr, hx⟩
      cases r with
      | ok a =>
        change x ∈ ⋃ a ∈ Except.ok ⁻¹' support mx.run, Except.ok ⁻¹' support (f a).run
        exact Set.mem_iUnion₂.mpr ⟨a, hr, hx⟩
      | error e => simp [ExceptT.bindCont] at hx
    · intro h
      have h : x ∈ ⋃ a ∈ Except.ok ⁻¹' support mx.run, Except.ok ⁻¹' support (f a).run := h
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp h
      exact ⟨.ok a, ha, hx⟩

@[simp]
lemma run_liftM_eq_map_ok (mx : m α) :
    (liftM mx : ExceptT ε m α).run = Except.ok <$> mx := rfl

variable [MonadLiftT m SetM]

@[aesop unsafe norm, grind =]
lemma support_def (mx : ExceptT ε m α) :
    support mx = Except.ok ⁻¹' (support mx.run) := rfl

@[simp low]
lemma mem_support_iff (mx : ExceptT ε m α) (x : α) :
    x ∈ support mx ↔ Except.ok x ∈ support mx.run := Iff.rfl

variable [LawfulMonadLiftT m SetM]

@[simp]
lemma support_liftM [LawfulMonad m] (mx : m α) :
    support (liftM mx : ExceptT ε m α) = support mx := by
  ext x
  simp only [mem_support_iff, run_liftM_eq_map_ok, support_map, Set.mem_image]
  constructor
  · rintro ⟨a, ha, h⟩; cases h; exact ha
  · exact fun h => ⟨x, h, rfl⟩

end EvalSet

section EvalFinset

private instance instDecidableEqExcept [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := fun a b => match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else
      isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else
      isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

noncomputable instance (ε : Type u) (m : Type u → Type v) [Monad m]
    [DecidableEq ε] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m] :
    HasEvalFinset (ExceptT ε m) where
  finSupport mx := (finSupport mx.run).preimage Except.ok
    (by intro a b; simp [Except.ok.injEq])
  coe_finSupport mx := by
    ext x; change x ∈ ((finSupport mx.run).preimage Except.ok _ : Set _) ↔
      x ∈ Except.ok ⁻¹' support mx.run
    simp

variable [DecidableEq ε] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]

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
  ext x
  rw [mem_finSupport_iff', mem_finSupport_iff_mem_support, mem_finSupport_iff_mem_support]
  change Except.ok x ∈ support (Except.ok <$> mx) ↔ x ∈ support mx
  simp

end EvalFinset

section EvalSPMF

/-- Monad homomorphism from `ExceptT ε m` to `SPMF`, treating errors as failure mass.
Given `mx : ExceptT ε m α`, we evaluate the underlying `m (Except ε α)` to an `SPMF`,
then route `Except.ok x` to `pure x` and `Except.error _` to `failure`. -/
noncomputable def toSPMF' [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] : ExceptT ε m →ᵐ SPMF where
  toFun {α} (mx : ExceptT ε m α) : SPMF α :=
    (liftM mx.run : SPMF _) >>= fun r =>
      match r with
      | Except.ok x => pure x
      | Except.error _ => failure
  toFun_pure' x := by simp
  toFun_bind' mx f := by
    change (liftM (mx.run >>= ExceptT.bindCont f) : SPMF _) >>= _ = _
    simp only [liftM_bind, monad_norm]
    congr 1; funext r
    cases r with
    | ok a =>
      change (liftM (f a).run : SPMF _) >>= _ =
        pure a >>= fun b => (liftM (f b).run : SPMF _) >>= _
      simp
    | error e => simp [ExceptT.bindCont]

private lemma toSPMF'_apply_eq [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    (mx : ExceptT ε m α) (x : α) :
    ExceptT.toSPMF' mx x = (liftM mx.run : SPMF _) (Except.ok x) := by
  rw [show (ExceptT.toSPMF' mx : SPMF α) =
    (liftM mx.run : SPMF _) >>= fun r =>
      match r with | Except.ok a => pure a | Except.error _ => failure from rfl]
  rw [SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (Except.ok x) fun y hy => ?_).trans ?_
  · cases y with
    | error e => simp
    | ok a =>
        have : x ≠ a := by intro h; subst h; exact hy rfl
        simp [this]
  · simp

/-- Lift `MonadLiftT m PMF` to `MonadLiftT (ExceptT ε m) SPMF`.
Errors contribute to failure mass. -/
noncomputable instance instMonadLiftTSPMF (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    MonadLiftT (ExceptT ε m) SPMF where
  monadLift mx := ExceptT.toSPMF' mx

noncomputable instance instLawfulMonadLiftTSPMF (ε : Type u) (m : Type u → Type v) [Monad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    LawfulMonadLiftT (ExceptT ε m) SPMF where
  monadLift_pure := ExceptT.toSPMF'.toFun_pure'
  monadLift_bind := ExceptT.toSPMF'.toFun_bind'

variable [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]

lemma evalDist_eq (mx : ExceptT ε m α) :
    𝒟[mx] = ExceptT.toSPMF' mx := rfl

@[grind =]
lemma probOutput_eq (mx : ExceptT ε m α) (x : α) :
    Pr[= x | mx] = Pr[= Except.ok x | mx.run] := by
  simp only [probOutput_def]
  exact toSPMF'_apply_eq mx x

@[grind =]
lemma probFailure_eq (mx : ExceptT ε m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] +
      Pr[ (fun r => match r with | Except.error _ => True | Except.ok _ => False) | mx.run] := by
  simp only [probFailure_def, probEvent_eq_tsum_indicator, probOutput_def]
  rw [show 𝒟[mx] = ((liftM mx.run : SPMF _) >>= fun r =>
      match r with | Except.ok a => pure a | Except.error _ => failure : SPMF α) from rfl]
  simp only [SPMF.run_eq_toPMF, SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind,
    PMF.bind_apply, ENNReal.summable, tsum_option, Option.elim_none, PMF.pure_apply, ↓reduceIte,
    mul_one, Option.elim_some, evalDist_def, SPMF.apply_eq_toPMF_some, ne_eq, PMF.apply_ne_top,
    not_false_eq_true, add_right_inj_of_ne_top]
  refine tsum_congr fun r => ?_
  cases r <;> simp [SPMF.toPMF_failure, SPMF.toPMF_pure]

lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | (liftM mx : ExceptT ε m α)] = Pr[= x | mx] := by
  rw [probOutput_eq]
  exact probOutput_map_injective mx (fun a b h => by cases h; rfl) x

private lemma evalDist_liftM [LawfulMonad m] (mx : m α) :
    𝒟[(liftM mx : ExceptT ε m α)] = 𝒟[mx] :=
  SPMF.ext fun x => probOutput_liftM mx x

lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | (liftM mx : ExceptT ε m α)] = Pr[⊥ | mx] := by
  simp only [probFailure_def, evalDist_liftM]

lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[ p | (liftM mx : ExceptT ε m α)] = Pr[ p | mx] := by
  simp only [probEvent_def, evalDist_liftM]

end EvalSPMF

end ExceptT
