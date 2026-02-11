/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import VCVio.Prelude
import Batteries.Control.AlternativeMonad
import ToMathlib.Control.Monad.Hom

/-!
# Sub-Probability Distributions

This file defines a type `SPMF` as a `PMF` extended with the option to fail.
The probability of failure is the missing mass to make the `PMF` sum to `1`.
-/

open ENNReal

attribute [simp] PMF.coe_le_one PMF.apply_ne_top

universe u v w

variable {α β γ : Type u}

/-- A subprobability mass function is a function `α → ℝ≥0∞` such that values have an infinite
sum at most `1` represented by applying an `OptionT` transformer to the `PMF` monad.
The new `failure`/`none` value holds the "missing" mass to reach the total sum of `1`. -/
def SPMF : Type u → Type u := OptionT PMF

/-- View a distribution on `Option α` as a subdistribution on `α`,
where `none` is corresponds to the missing mass. -/
protected def SPMF.mk (p : PMF (Option α)) : SPMF α := OptionT.mk p

/-- View a subdistribution on `α` as a distribution on `Option α`. -/
protected def SPMF.toPMF (p : SPMF α) : PMF (Option α) := OptionT.run p

namespace SPMF

@[simp] lemma run_eq_toPMF (p : SPMF α) : p.run = p.toPMF := rfl

@[simp] lemma toPMF_mk (p : PMF (Option α)) : (SPMF.mk p).toPMF = p := rfl

@[simp] lemma mk_toPMF (p : SPMF α) : SPMF.mk p.toPMF = p := rfl

/-- Expose the induced monad instance on `SPMF`. -/
noncomputable instance : AlternativeMonad SPMF := OptionT.instAlternativeMonadOfMonad PMF
noncomputable instance : LawfulAlternative SPMF := OptionT.instLawfulAlternativeOfLawfulMonad PMF
noncomputable instance : LawfulMonad SPMF := OptionT.instLawfulMonad

/-- Expose the lifting operations from `PMF` to `SPMF` given by `OptionT.lift`-/
noncomputable instance : MonadLift PMF SPMF where monadLift := OptionT.lift
instance : LawfulMonadLift PMF SPMF := OptionT.instLawfulMonadLift

/-- Apply an `SPMF α` to an element of `α`. -/
instance : FunLike (SPMF α) α ENNReal where
  coe p x := OptionT.run p (some x)
  coe_injective' _ _ h := OptionT.ext (PMF.ext_forall_ne none fun | some x, _ => congr_fun h x)

@[aesop norm 100, grind =] -- TODO: decide if this should be a simp
lemma apply_eq_toPMF_some (p : SPMF α) (x : α) : p x = p.toPMF (some x) := rfl

@[grind =]
lemma liftM_eq_map (p : PMF α) : (liftM p : SPMF α) = SPMF.mk (p.map Option.some) := rfl

@[simp, grind =]
lemma lift_pure (x : α) : (liftM (PMF.pure x) : SPMF α) = pure x := by
  simp [← PMF.monad_pure_eq_pure]

@[simp, grind =]
lemma toPMF_liftM (p : PMF α) : (liftM p : SPMF α).toPMF = p := rfl

@[simp, grind =]
lemma liftM_apply (p : PMF α) (x : α) : (liftM p : SPMF α) x = p x := by
  simp [apply_eq_toPMF_some]
  refine (tsum_eq_single x ?_).trans ?_ <;> aesop

@[simp, grind =]
lemma toPMF_pure (x : α) : (pure x : SPMF α).toPMF = PMF.pure (some x) := rfl

lemma failure_eq_mk : (failure : SPMF α) = SPMF.mk (PMF.pure none) := rfl

@[simp, grind =]
lemma toPMF_failure : (failure : SPMF α).toPMF = PMF.pure none := rfl

@[simp, grind =]
lemma failure_apply (x : α) : (failure : SPMF α) x = 0 := by aesop

noncomputable instance : Zero (SPMF α) where zero := failure

lemma zero_def : (0 : SPMF α) = failure := rfl

@[simp, grind =]
lemma toPMF_zero : (0 : SPMF α).toPMF = PMF.pure none := rfl

@[simp, grind =]
lemma toPMF_bind (p : SPMF α) (q : α → SPMF β) :
    (p >>= q).toPMF = Option.elimM p.toPMF (PMF.pure none) (fun x => (q x).toPMF) := by
  simp [← run_eq_toPMF]

@[simp, grind =]
lemma toPMF_map (p : SPMF α) (f : α → β) : (f <$> p).toPMF = Option.map f <$> p.toPMF := by
  simp [← run_eq_toPMF]

@[simp, grind =]
lemma zero_apply (x : α) : (0 : SPMF α) x = 0 := by aesop

@[simp] lemma tsum_toPMF_some_add_toPMF_none (p : SPMF α) :
    (∑' x, p.toPMF (some x)) + p.toPMF none = 1 := by
  rw [add_comm, ← tsum_option _ ENNReal.summable, p.toPMF.tsum_coe]

@[simp] lemma run_none_add_tsum_run_some (p : SPMF α) :
    p.toPMF none + (∑' x, p.toPMF (some x)) = 1 := by
  rw [← tsum_option _ ENNReal.summable, p.toPMF.tsum_coe]

lemma tsum_run_some_eq_one_sub (p : SPMF α) :
    ∑' x, p.toPMF (some x) = 1 - p.toPMF none := by
  rw [← tsum_toPMF_some_add_toPMF_none p]
  refine ENNReal.eq_sub_of_add_eq' ?_ rfl
  simp

@[simp, grind .] lemma apply_ne_top (p : SPMF α) (x : α) : p x ≠ ⊤ := by aesop

@[simp] lemma tsum_run_some_ne_top (p : SPMF α) : ∑' x, p.toPMF (some x) ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (p.tsum_run_some_eq_one_sub ▸ tsub_le_self)

lemma run_none_eq_one_sub (p : SPMF α) :
    p.toPMF none = 1 - ∑' x, p.toPMF (some x) := by
  rw [p.tsum_coe.symm.trans (tsum_option _ ENNReal.summable)]
  refine ENNReal.eq_sub_of_add_eq ?_ rfl
  simp only [ne_eq, tsum_run_some_ne_top, not_false_eq_true]

@[ext]
lemma ext {p q : SPMF α} (h : ∀ x : α, p.toPMF (some x) = q.toPMF (some x)) : p = q :=
  PMF.ext fun
    | some x => h x
    | none =>  calc p.toPMF none
        _ = 1 - ∑' x, p.toPMF (some x) := by rw [run_none_eq_one_sub]
        _ = 1 - ∑' x, q.toPMF (some x) := by simp only [h]
        _ = q.toPMF none := by rw [run_none_eq_one_sub]

open Classical in
lemma eq_liftM_iff_forall (p : SPMF α) (q : PMF α) :
    p = liftM q ↔ ∀ x, p x = q x := by
  simp [SPMF.ext_iff]
  grind

@[simp] lemma pure_apply [DecidableEq α] (x y : α) :
    (pure x : SPMF α) y = if y = x then 1 else 0 := by aesop

@[simp] lemma pure_apply_self (x : α) :
    (pure x : SPMF α) x = 1 := by aesop

@[simp] lemma pure_apply_eq_zero_iff (x y : α) :
    (pure x : SPMF α) y = 0 ↔ y ≠ x := by aesop

@[simp] lemma bind_apply_eq_tsum (p : SPMF α) (q : α → SPMF β) (y : β) :
    (p >>= q) y = ∑' x, p x * q x y := by
  erw [PMF.bind_apply, tsum_option _ ENNReal.summable]
  simp
  rfl

/-- The set of outputs with non-zero probability mass. -/
protected def support {α : Type _} (p : SPMF α) : Set α :=
  Function.support (p : α → ℝ≥0∞)

lemma support_def (p : SPMF α) :
    SPMF.support p = Function.support p := rfl

@[grind =]
lemma support_eq_preimage_some (p : SPMF α) :
    p.support = some ⁻¹' p.toPMF.support := by grind

@[simp, grind =]
lemma mem_support_iff (p : SPMF α) (x : α) : x ∈ p.support ↔ p x ≠ 0 := by aesop

@[simp, grind =]
lemma support_liftM (p : PMF α) : (liftM p : SPMF α).support = p.support := by aesop

@[simp, grind =]
lemma support_pure (x : α) : (pure x : SPMF α).support = {x} := by aesop

@[simp] lemma map_mk (p : PMF (Option α)) (f : α → β) :
    f <$> SPMF.mk p = SPMF.mk (Option.map f <$> p) := by aesop


end SPMF

namespace PMF

/-- Convert a `PMF` to an `SPMF` in the canonical way.
dtumad: this should probably be a bare function with a hom-class instance.  -/
@[reducible] noncomputable def toSPMF' : PMF →ᵐ SPMF where
  toFun _ := fun p ↦ OptionT.mk (p.map some)
  toFun_pure' x := by
    ext y
    refine (tsum_eq_single x ?_).trans ?_ <;> aesop
  toFun_bind' p q := by
    ext y
    simp [← SPMF.run_eq_toPMF]
    simp [PMF.map, Option.elimM]
    refine tsum_congr fun x => congr_arg (_ * ·) ?_
    refine symm ((tsum_eq_single y ?_).trans ?_) <;> aesop

end PMF
