/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import ToMathlib.Control.OptionT
import VCVio.EvalDist.Option
import VCVio.EvalDist.Defs.AlternativeMonad
import VCVio.EvalDist.Defs.Instances

/-!
# Probability Distributions on Potentially Failing Computations

This file gives an instance to extend a `evalDist` instance on a monad to one transformed by
the `OptionT` monad transformer.

dt: should add more instances and connecting lemmas
-/

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace OptionT

section HasEvalSet

/-- Standalone `HasEvalSet (OptionT m)` instance under the weaker `[HasEvalSet m]` assumption.

This is deliberately kept separate from the `HasEvalSPMF (OptionT m)` instance below, which
re-exports the same `toSet` to make the resulting typeclass diamond definitionally equal.
Keeping this standalone instance means `support` on `OptionT m` works without requiring a
full `HasEvalSPMF m` — only `HasEvalSet m` is needed (e.g., for `support_liftM`). -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSet m] :
    HasEvalSet (OptionT m) where
  toSet.toFun α mx := some ⁻¹' (support (OptionT.run mx))
  toSet.toFun_pure' mx := Set.ext fun x => by simp
  toSet.toFun_bind' mx my := Set.ext fun x => by simp [Option.elimM, Option.exists]

variable [HasEvalSet m]

@[aesop unsafe norm, grind =]
lemma support_def (mx : OptionT m α) :
    support mx = some ⁻¹' (support mx.run) := rfl

@[simp low]
lemma mem_support_iff (mx : OptionT m α) (x : α) :
    x ∈ support mx ↔ some x ∈ support mx.run := by grind

@[simp]
lemma support_liftM (mx : m α) :
    support (liftM mx : OptionT m α) = support mx := by grind

@[simp]
lemma support_lift (mx : m α) :
    support (OptionT.lift mx) = support mx := by grind

end HasEvalSet

section HasEvalFinset

/-- Lift a `HasEvalFinset` instance to `OptionT`. by just taking preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSet m] [HasEvalFinset m] :
    HasEvalFinset (OptionT m) where
  finSupport mx := (finSupport mx.run).preimage some (by simp)
  coe_finSupport := by aesop

variable [HasEvalSet m] [HasEvalFinset m]

@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : OptionT m α) :
    finSupport mx = (finSupport mx.run).preimage some (by simp) := rfl

@[simp low]
lemma mem_finSupport_iff [DecidableEq α] (mx : OptionT m α) (x : α) :
    x ∈ finSupport mx ↔ some x ∈ finSupport mx.run := by
  simp [finSupport_def, Finset.mem_preimage]

@[simp]
lemma finSupport_liftM [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : OptionT m α) = finSupport mx := by
  grind only [= finSupport_def, = liftM_def, = coe_finSupport, = run_lift,
    = mem_finSupport_iff_mem_support, = support_def, = Set.mem_preimage, = mem_support_bind_iff,
    = support_pure, = Set.mem_singleton_iff]

@[simp]
lemma finSupport_lift [DecidableEq α] (mx : m α) :
    finSupport (OptionT.lift mx) = finSupport mx := by
  grind only [= finSupport_def, = run_lift, = coe_finSupport, = mem_finSupport_iff_mem_support,
    = support_def, = Set.mem_preimage, = mem_support_bind_iff, = support_pure,
    = Set.mem_singleton_iff]

end HasEvalFinset

section HasEvalSPMF

/-- Lift a `HasEvalSPMF m` instance to `HasEvalSPMF (OptionT m)`.
Note: a more specific `HasEvalPMF m → HasEvalSPMF (OptionT m)` path would make explicit
that failure comes solely from `OptionT`, but this general instance subsumes it.

Lean 4 automatically synthesizes `toSet` from the standalone `HasEvalSet (OptionT m)` instance
above, ensuring the diamond is definitionally equal (per Mathlib convention). The `support_eq`
field then serves as the coherence proof between the set-path and distribution-path. -/
noncomputable instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSPMF (OptionT m) where
  toSPMF := OptionT.mapM' HasEvalSPMF.toSPMF
  support_eq mx := by
    ext x
    simp [mem_support_iff, OptionT.mapM']
    constructor
    · simp [mem_support_iff_evalDist_apply_ne_zero]
      refine fun h => ⟨some x, by simpa using h⟩
    · simp [mem_support_iff_evalDist_apply_ne_zero]
      intro x
      cases x <;> aesop

instance (m : Type u → Type v) [Monad m] [HasEvalSPMF m] :
    HasEvalSet.LawfulFailure (OptionT m) where
  support_failure' := by aesop


variable [HasEvalSPMF m]

lemma evalDist_eq (mx : OptionT m α) :
    evalDist mx = OptionT.mapM' HasEvalSPMF.toSPMF mx := rfl

@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  simp only [probOutput_def]
  show (OptionT.mapM' HasEvalSPMF.toSPMF mx) x = HasEvalSPMF.toSPMF mx.run (some x)
  rw [show (OptionT.mapM' HasEvalSPMF.toSPMF mx : SPMF α) =
    HasEvalSPMF.toSPMF mx.run >>= fun y =>
      match y with | some a => pure a | none => failure from rfl]
  rw [SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (some x) fun y hy => ?_).trans (by simp)
  cases y with
  | none => simp
  | some a =>
      have : x ≠ a := by intro h; subst h; exact hy rfl
      simp [this]

@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] + Pr[= none | mx.run] = Pr[fun x => x.all p | mx.run] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_eq]
  rw [add_comm, tsum_option _ ENNReal.summable]
  congr 1
  · simp
  · congr 1; ext a; simp [Set.indicator_apply, decide_eq_true_eq]

@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] + Pr[= none | mx.run] := by
  simp only [probFailure_def, probOutput_def]
  rw [show evalDist mx = (HasEvalSPMF.toSPMF mx.run >>= fun y =>
      match y with | some a => pure a | none => failure : SPMF α) from rfl]
  simp [SPMF.toPMF_bind, Option.elimM, PMF.bind_apply, tsum_option,
    SPMF.toPMF_failure, SPMF.toPMF_pure, SPMF.apply_eq_toPMF_some, evalDist_def]

@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | liftM (n := OptionT m) mx] = Pr[= x | mx] := by simp [probOutput_eq]

@[simp, grind =]
lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | OptionT.lift mx] = Pr[= x | mx] := by simp [probOutput_eq]

@[simp, grind =]
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | liftM (n := OptionT m) mx] = Pr[p | mx] := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_liftM]

@[simp, grind =]
lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[p | OptionT.lift mx] = Pr[p | mx] := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_lift]

@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | liftM (n := OptionT m) mx] = Pr[⊥ | mx] := by
  simp [probFailure_eq]

@[simp, grind =]
lemma probFailure_lift [LawfulMonad m] (mx : m α) :
    Pr[⊥ | OptionT.lift mx] = Pr[⊥ | mx] := by
  simp [probFailure_eq]

/-! ### SubPMF / SPMF bridge

`SubPMF α` is `OptionT PMF α` and `SPMF α` is also `OptionT PMF α`, but they carry
different `HasEvalSPMF` instances. These lemmas equate `probOutput` and `probEvent`
across the two views. -/

lemma probOutput_subpmf_eq_spmf (p : SPMF α) (x : α) :
    @probOutput SubPMF OptionT.instMonad α (instHasEvalSPMF PMF) (p : SubPMF α) x =
      @probOutput SPMF SPMF.instAlternativeMonad.toMonad α SPMF.instHasEvalSPMF p x := by
  rw [probOutput_eq, PMF.probOutput_eq_apply, SPMF.probOutput_eq_apply]
  rfl

lemma probEvent_subpmf_eq_spmf (p : SPMF α) (q : α → Prop) :
    @probEvent SubPMF OptionT.instMonad α (instHasEvalSPMF PMF) (p : SubPMF α) q =
      @probEvent SPMF SPMF.instAlternativeMonad.toMonad α SPMF.instHasEvalSPMF p q := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  by_cases hq : q x <;> simp [hq, probOutput_subpmf_eq_spmf]

end HasEvalSPMF

end OptionT
