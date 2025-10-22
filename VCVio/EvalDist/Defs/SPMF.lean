/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import ToMathlib.General
import Batteries.Control.AlternativeMonad
import ToMathlib.Control.Monad.Hom

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

namespace PMF

attribute [simp] coe_le_one PMF.apply_ne_top

declare_aesop_rule_sets [UnfoldEvalDist]

end PMF

/-- Subprobability distribution.
dt: this should move to mathlib -/
@[reducible] def SPMF : Type u → Type u := OptionT PMF

namespace SPMF

def mk (p : PMF (Option α)) : SPMF α := p

@[simp] lemma run_mk (p : PMF (Option α)) : (mk p).run = p := rfl

@[simp] lemma mk_run (p : SPMF α) : mk p.run = p := rfl

@[simp] lemma liftM_PMF_eq (p : PMF α) :
    (liftM p : SPMF α) = SPMF.mk (p.map Option.some) := rfl

lemma tsum_run_some_eq_one_sub (p : SPMF α) :
    ∑' x, p.run (some x) = 1 - p.run none := by
  rw [p.tsum_coe.symm.trans (tsum_option _ ENNReal.summable)]
  exact (ENNReal.add_sub_cancel_left (PMF.apply_ne_top p none)).symm

@[simp] lemma tsum_run_some_add_run_none (p : SPMF α) :
    (∑' x, p.run (some x)) + p.run none = 1 := by
  rw [tsum_run_some_eq_one_sub, ENNReal.sub_add_eq_add_sub] <;> aesop

@[simp] lemma run_none_add_tsum_run_some (p : SPMF α) :
    p.run none + (∑' x, p.run (some x)) = 1 := by
  simp [tsum_run_some_eq_one_sub]

@[simp] lemma tsum_run_some_ne_top (p : SPMF α) :
    ∑' x, p.run (some x) ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (p.tsum_run_some_eq_one_sub ▸ tsub_le_self)

lemma run_none_eq_one_sub (p : SPMF α) :
    p.run none = 1 - ∑' x, p.run (some x) := by
  rw [p.tsum_coe.symm.trans (tsum_option _ ENNReal.summable)]
  refine ENNReal.eq_sub_of_add_eq ?_ rfl
  simp only [ne_eq, tsum_run_some_ne_top, not_false_eq_true]

@[simp] lemma run_none_ne_top (p : SPMF α) : p.run none ≠ ⊤ := PMF.apply_ne_top p none

@[ext] lemma ext {p q : SPMF α} (h : ∀ x : α, p.run (some x) = q.run (some x)) : p = q :=
  PMF.ext fun
    | some x => h x
    | none =>  calc p.run none
        _ = 1 - ∑' x, p.run (some x) := by rw [run_none_eq_one_sub]
        _ = 1 - ∑' x, q.run (some x) := by simp only [h]
        _ = q.run none := by rw [run_none_eq_one_sub]

-- Should we do it this way or add the instance on `Option α` instead?
instance : FunLike (SPMF α) α ENNReal where
  coe sp x := sp.run (some x)
  coe_injective' p q h := by simpa [SPMF.ext_iff] using congr_fun h

-- dt: is this really what we also want to simplify to?
@[simp] lemma apply_eq_run_some (p : SPMF α) (x : α) : p x = p.run (some x) := rfl

section zero

protected noncomputable def zero (α : Type u) : SPMF α := SPMF.mk (PMF.pure none)

noncomputable instance : Zero (SPMF α) where zero := SPMF.zero α

lemma zero_def : (0 : SPMF α) = SPMF.zero α := rfl

@[simp] lemma zero_apply (x : α) : (0 : SPMF α) x = 0 := by
  simp [zero_def, SPMF.zero]

end zero

protected def support : SPMF →ᵐ SetM where
  toFun x := Function.support x
  toFun_pure' x := by
    refine Set.ext fun y => ?_
    simp
  toFun_bind' x y := by
    refine Set.ext fun y => ?_
    simp [Option.elimM, Function.comp_def]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨z, hz⟩ := h
      cases z with
      | none =>
          simp at hz
      | some z =>
          use z
          simp at hz
          simp [hz]
    · obtain ⟨z, hz⟩ := h
      use some z
      simp [hz]

end SPMF

namespace PMF

/-- Convert a `PMF` to an `SPMF` in the canonical way. -/
@[reducible] noncomputable def toSPMF : PMF →ᵐ SPMF where
  toFun := fun p ↦ OptionT.mk (p.map some)
  toFun_pure' x := by
    ext y
    refine (tsum_eq_single x ?_).trans ?_ <;> aesop
  toFun_bind' p q := by
    ext y
    simp [Function.comp_def]
    simp [PMF.map, Option.elimM]
    refine (tsum_eq_single y ?_).trans ?_
    · aesop
    · simp
      refine tsum_congr fun x => congr_arg (p x * ·) ?_
      refine trans ?_ (tsum_eq_single y ?_).symm <;> aesop

@[simp] lemma run_toSPMF_none (p : PMF α) :
    p.toSPMF.run none = 0 := by simp

end PMF
