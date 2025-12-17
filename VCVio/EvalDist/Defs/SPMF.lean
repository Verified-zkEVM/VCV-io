/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import ToMathlib.General
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

-- TODO: move this to a base file somewhere
declare_aesop_rule_sets [UnfoldEvalDist]

/-- A subprobability mass function is a function `α → ℝ≥0∞` such that values have an infinite
sum at most `1` represented by applying an `OptionT` transformer to the `PMF` monad.
The new `failure`/`none` value holds the "missing" mass to reach the total sum of `1`. -/
def SPMF : Type u → Type u := OptionT PMF

/-- View a distribution on `α` as a sub-distribution with no missing mass.
This function is applied automatically as a `MonadLift` when needed. -/
protected noncomputable def PMF.toSPMF (p : PMF α) : SPMF α := OptionT.lift p

/-- View a distribution on `Option α` as a subdistribution on `α`. -/
protected def SPMF.mk (p : PMF (Option α)) : SPMF α := OptionT.mk p

/-- View a subdistribution on `α` as a distribution on `Option α`. -/
protected def SPMF.run (p : SPMF α) : PMF (Option α) := OptionT.run p

namespace SPMF

@[simp] lemma run_mk (p : PMF (Option α)) : (SPMF.mk p).run = p := rfl

@[simp] lemma mk_run (p : SPMF α) : SPMF.mk p.run = p := rfl

/-- Expose the induced monad instance on `SPMF`. -/
noncomputable instance : AlternativeMonad SPMF := OptionT.instAlternativeMonadOfMonad PMF
noncomputable instance : LawfulAlternative SPMF := OptionT.instLawfulAlternativeOfLawfulMonad PMF
noncomputable instance : LawfulMonad SPMF := OptionT.instLawfulMonad_batteries PMF

noncomputable instance : MonadLift PMF SPMF where monadLift := PMF.toSPMF

instance : LawfulMonadLift PMF SPMF := OptionT.instLawfulMonadLift

/-- Apply an `SPMF α` to an element of `α`. -/
instance : FunLike (SPMF α) α ENNReal where
  coe p x := OptionT.run p (some x)
  coe_injective' _ _ h := OptionT.ext (PMF.ext_forall_ne none fun | some x, _ => congr_fun h x)

@[aesop norm 100] -- TODO: decide if this should be a simp
lemma apply_eq_run_some (p : SPMF α) (x : α) : p x = p.run (some x) := rfl

lemma liftM_eq_map (p : PMF α) : (liftM p : SPMF α) = SPMF.mk (p.map Option.some) := rfl

@[simp] lemma run_liftM (p : PMF α) : (liftM p : SPMF α).run = p := rfl

@[simp] lemma liftM_apply (p : PMF α) (x : α) :
    (liftM p : SPMF α) x = p x := by
  simp [apply_eq_run_some]
  refine (tsum_eq_single x ?_).trans ?_ <;> aesop

-- instance : MonadHomClass PMF SPMF @PMF.toSPMF := by
--   show MonadHomClass PMF SPMF (@liftM PMF SPMF _)
--   infer_instance

-- instance : MonadHomClass SPMF (OptionT PMF) (@SPMF.run) := by sorry

-- instance : MonadHomClass (OptionT PMF) SPMF (@SPMF.mk) := by sorry

@[simp] lemma run_pure (x : α) : (pure x : SPMF α).run = PMF.pure (some x) := rfl

lemma failure_eq_mk : (failure : SPMF α) = SPMF.mk (PMF.pure none) := rfl

@[simp] lemma run_failure : (failure : SPMF α).run = PMF.pure none := rfl

@[simp] lemma failure_apply (x : α) : (failure : SPMF α) x = 0 := by aesop

noncomputable instance : Zero (SPMF α) where zero := failure

lemma zero_def : (0 : SPMF α) = failure := rfl

@[simp] lemma run_zero : (0 : SPMF α).run = PMF.pure none := rfl

@[simp] lemma zero_apply (x : α) : (0 : SPMF α) x = 0 := by aesop

@[simp] lemma tsum_run_some_add_run_none (p : SPMF α) :
    (∑' x, p.run (some x)) + p.run none = 1 := by
  rw [add_comm, ← tsum_option _ ENNReal.summable, p.run.tsum_coe]

@[simp] lemma run_none_add_tsum_run_some (p : SPMF α) :
    p.run none + (∑' x, p.run (some x)) = 1 := by
  rw [← tsum_option _ ENNReal.summable, p.run.tsum_coe]

lemma tsum_run_some_eq_one_sub (p : SPMF α) :
    ∑' x, p.run (some x) = 1 - p.run none := by
  rw [← tsum_run_some_add_run_none p]
  refine ENNReal.eq_sub_of_add_eq' ?_ rfl
  simp

@[simp] lemma apply_ne_top (p : SPMF α) (x : α) : p x ≠ ⊤ := by aesop

@[simp] lemma tsum_run_some_ne_top (p : SPMF α) : ∑' x, p.run (some x) ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (p.tsum_run_some_eq_one_sub ▸ tsub_le_self)

lemma run_none_eq_one_sub (p : SPMF α) :
    p.run none = 1 - ∑' x, p.run (some x) := by
  rw [p.tsum_coe.symm.trans (tsum_option _ ENNReal.summable)]
  refine ENNReal.eq_sub_of_add_eq ?_ rfl
  simp only [ne_eq, tsum_run_some_ne_top, not_false_eq_true]

@[ext] lemma ext {p q : SPMF α} (h : ∀ x : α, p.run (some x) = q.run (some x)) : p = q :=
  PMF.ext fun
    | some x => h x
    | none =>  calc p.run none
        _ = 1 - ∑' x, p.run (some x) := by rw [run_none_eq_one_sub]
        _ = 1 - ∑' x, q.run (some x) := by simp only [h]
        _ = q.run none := by rw [run_none_eq_one_sub]

open Classical in
lemma eq_liftM_iff_forall (p : SPMF α) (q : PMF α) :
    p = liftM q ↔ ∀ x, p x = q x := by
  simp [SPMF.ext_iff, apply_eq_run_some]

@[simp] lemma pure_apply [DecidableEq α] (x y : α) :
    (pure x : SPMF α) y = if y = x then 1 else 0 := by
  simp [SPMF.apply_eq_run_some]

@[simp] lemma pure_apply_self (x : α) :
    (pure x : SPMF α) x = 1 := by
  simp [SPMF.apply_eq_run_some]

@[simp] lemma bind_apply_eq_tsum (p : SPMF α) (q : α → SPMF β) (y : β) :
    (p >>= q) y = ∑' x, p x * q x y := by
  -- simp [SPMF.apply_eq_run_some, SPMF.run, OptionT.run]
  erw [PMF.bind_apply, tsum_option _ ENNReal.summable]
  simp
  rfl

protected def support : SPMF →ᵐ SetM where
  toFun _ x := Function.support x
  toFun_pure' x := by
    refine Set.ext fun y => ?_
    simp [SPMF.apply_eq_run_some]
  toFun_bind' x y := by
    refine Set.ext fun y => ?_
    simp

@[simp] lemma support_toSPMF (p : PMF α) : (PMF.toSPMF p).support = p.support := by
  sorry

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
    simp [Function.comp_def, SPMF.run]
    simp [PMF.map, Option.elimM]
    refine tsum_congr fun x => congr_arg (_ * ·) ?_
    refine symm ((tsum_eq_single y ?_).trans ?_) <;> aesop

-- instance : MonadHomClass PMF SetM @PMF.support where
--   map_pure := by simp
--   map_bind := by simp

-- @[simp] lemma run_toSPMF_none (p : PMF α) :
--     p.toSPMF.run none = 0 := by simp

end PMF
