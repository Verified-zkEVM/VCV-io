/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
import Batteries.Control.AlternativeMonad
import ToMathlib.Control.Monad.Hom
public import ToMathlib.General

/-!
# Sub-Probability Distributions

This file defines a type `SPMF` as a `PMF` extended with the option to fail.
The probability of failure is the missing mass to make the `PMF` sum to `1`.
-/

@[expose] public section

open ENNReal

attribute [simp] PMF.coe_le_one PMF.apply_ne_top

universe u v w

variable {α β γ : Type u}

namespace PMF

/-- A PMF that is zero at all points except `a` equals `PMF.pure a`. -/
lemma eq_pure_of_forall_ne_eq_zero {γ : Type*} (p : PMF γ) (a : γ)
    (h : ∀ x, x ≠ a → p x = 0) : p = PMF.pure a := by
  ext x; by_cases hx : x = a
  · subst hx; simp only [PMF.pure_apply, if_true]
    rw [← p.tsum_coe]; exact (tsum_eq_single x (fun b hb => h b hb)).symm
  · simp [PMF.pure_apply, hx, h x hx]

/-- `PMF.bind` respects equality on the support. -/
protected lemma bind_congr {γ δ : Type*} (p : PMF γ) (f g : γ → PMF δ)
    (h : ∀ x, p x ≠ 0 → f x = g x) : p.bind f = p.bind g := by
  ext y; simp only [PMF.bind_apply]; congr 1; ext x
  by_cases hx : p x = 0 <;> simp [hx, h x]

/-- If `PMF.map f c = PMF.pure b` and `f a ≠ b`, then `c a = 0`. -/
lemma map_eq_pure_zero {γ δ : Type*} (f : γ → δ) (c : PMF γ) (b : δ)
    (h : PMF.map f c = PMF.pure b) (a : γ) (ha : f a ≠ b) : c a = 0 := by
  have key := congr_fun (congrArg DFunLike.coe h) (f a)
  simp only [map_apply, pure_apply, ha, ↓reduceIte, ENNReal.tsum_eq_zero, ite_eq_right_iff] at key
  exact key a rfl

end PMF

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

/-- Expose the lifting operations from `PMF` to `SPMF` given by `OptionT.lift`. -/
noncomputable instance : MonadLift PMF SPMF where monadLift := OptionT.lift
instance : LawfulMonadLift PMF SPMF := OptionT.instLawfulMonadLift

/-- Apply an `SPMF α` to an element of `α`. -/
instance : FunLike (SPMF α) α ENNReal where
  coe p x := OptionT.run p (some x)
  coe_injective' _ _ h := OptionT.ext (PMF.ext_forall_ne none fun | some x, _ => congr_fun h x)

@[aesop unsafe norm, grind =] -- TODO: decide if this should be a simp
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
  simp only [apply_eq_toPMF_some, toPMF_liftM, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
    PMF.bind_apply, PMF.pure_apply, Option.some.injEq, mul_ite, mul_one, mul_zero]
  refine (tsum_eq_single x ?_).trans ?_ <;> aesop

@[simp, grind =]
lemma toPMF_pure (x : α) : (pure x : SPMF α).toPMF = PMF.pure (some x) := rfl

lemma failure_eq_mk : (failure : SPMF α) = SPMF.mk (PMF.pure none) := rfl

@[simp, grind =]
lemma toPMF_failure : (failure : SPMF α).toPMF = PMF.pure none := rfl

@[simp, grind =]
lemma failure_apply (x : α) : (failure : SPMF α) x = 0 := by aesop

section zero

noncomputable instance : Zero (SPMF α) where zero := failure

lemma zero_def : (0 : SPMF α) = failure := rfl

@[simp, grind =]
lemma toPMF_zero : (0 : SPMF α).toPMF = PMF.pure none := rfl

@[simp, grind =]
lemma zero_apply (x : α) : (0 : SPMF α) x = 0 := by aesop

end zero

@[simp, grind =]
lemma toPMF_bind (p : SPMF α) (q : α → SPMF β) :
    (p >>= q).toPMF = Option.elimM p.toPMF (PMF.pure none) (fun x => (q x).toPMF) := by
  simp [← run_eq_toPMF]

@[simp, grind =]
lemma toPMF_map (p : SPMF α) (f : α → β) : (f <$> p).toPMF = Option.map f <$> p.toPMF := by
  simp [← run_eq_toPMF]

@[simp, grind =]
lemma mk_pure_some (x : α) : SPMF.mk (PMF.pure (some x)) = pure x := rfl

@[simp, grind =]
lemma tsum_toPMF_some_add_toPMF_none (p : SPMF α) :
    (∑' x, p.toPMF (some x)) + p.toPMF none = 1 := by
  rw [add_comm, ← tsum_option _ ENNReal.summable, p.toPMF.tsum_coe]

@[simp, grind =]
lemma run_none_add_tsum_run_some (p : SPMF α) :
    p.toPMF none + (∑' x, p.toPMF (some x)) = 1 := by
  rw [← tsum_option _ ENNReal.summable, p.toPMF.tsum_coe]

lemma tsum_run_some_eq_one_sub (p : SPMF α) :
    ∑' x, p.toPMF (some x) = 1 - p.toPMF none := by
  rw [← tsum_toPMF_some_add_toPMF_none p]
  refine ENNReal.eq_sub_of_add_eq' (by simp) rfl

@[grind =]
lemma toPMF_none_eq_one_sub_tsum (p : SPMF α) :
    p.toPMF none = 1 - ∑' x, p.toPMF (some x) := by
  rw [← run_none_add_tsum_run_some p]
  refine ENNReal.eq_sub_of_add_eq' (by simp) rfl

@[simp, grind .] lemma apply_ne_top (p : SPMF α) (x : α) : p x ≠ ⊤ := by aesop

@[simp] lemma tsum_run_some_ne_top (p : SPMF α) : ∑' x, p.toPMF (some x) ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (p.tsum_run_some_eq_one_sub ▸ tsub_le_self)

@[ext]
lemma ext {p q : SPMF α} (h : ∀ x : α, p x = q x) : p = q := by
  simp only [apply_eq_toPMF_some] at h
  refine PMF.ext fun
    | some x => h x
    | none =>  calc p.toPMF none
        _ = 1 - ∑' x, p.toPMF (some x) := by grind
        _ = 1 - ∑' x, q.toPMF (some x) := by simp [h]
        _ = q.toPMF none := by grind

open Classical in
lemma eq_liftM_iff_forall (p : SPMF α) (q : PMF α) :
    p = liftM q ↔ ∀ x, p x = q x := by
  simp [SPMF.ext_iff]

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

section support

/-- The set of outputs with non-zero probability mass. -/
protected def support {α : Type*} (p : SPMF α) : Set α :=
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

end support

section gap

/-- Gap between the total mass of `p : SPMF` and `1`, so `∑ x, p x + p.gap = 1`.
TODO: use this to simplify the API around failure and needing `toPMF`/`run`. -/
def gap (p : SPMF α) : ℝ≥0∞ := p.toPMF none

@[grind =]
lemma gap_eq_toPMF_none (p : SPMF α) : p.gap = p.toPMF none := rfl

@[grind =]
lemma gap_eq_one_sub_tsum (p : SPMF α) : p.gap = 1 - ∑' x : α, p x := by grind

@[grind =]
lemma toReal_gap_eq_one_sub_sum_toReal [Fintype α] (p : SPMF α) :
    p.gap.toReal = 1 - ∑ x : α, (p x).toReal := by
  simp only [gap_eq_one_sub_tsum, tsum_fintype]
  rw [ENNReal.toReal_sub_of_le]
  · simp only [toReal_one, _root_.sub_right_inj]
    rw [ENNReal.toReal_sum]
    simp
  · refine le_of_le_of_eq ?_ (run_none_add_tsum_run_some p)
    simp [SPMF.apply_eq_toPMF_some]
  · simp

end gap

@[simp] lemma map_mk (p : PMF (Option α)) (f : α → β) :
    f <$> SPMF.mk p = SPMF.mk (Option.map f <$> p) := by aesop

theorem bind_eq_pmf_bind {p : SPMF α} {f : α → SPMF β} :
    (p >>= f) = PMF.bind p (fun a => match a with | some a' => f a' | none => PMF.pure none) := by
  simp [bind, OptionT.bind, PMF.instMonad, OptionT.mk]
  rfl

@[simp] lemma PMF.map_some_apply_some (p : PMF α) (x : α) : (some <$> p) (some x) = p x := by
  simp [PMF.monad_map_eq_map]

/-- `pure a` in `SPMF` equals `PMF.pure (some a)` as a PMF on `Option α`. -/
protected lemma pure_eq_pure_some (a : α) :
    (pure a : SPMF α) = SPMF.mk (PMF.pure (some a)) := by rfl

@[simp, grind =]
lemma toPMF_inj (p q : SPMF α) : p.toPMF = q.toPMF ↔ p = q := by aesop

/-- The functor map for SPMF equals `PMF.map (Option.map f)`. -/
protected lemma fmap_eq_map (f : α → β) (c : SPMF α) :
    (f <$> c : SPMF β) = (PMF.map (Option.map f) c) :=
  show (f <$> c : SPMF β) = SPMF.mk (PMF.map (Option.map f) c.toPMF)
  by rw [← SPMF.toPMF_inj, SPMF.toPMF_map, SPMF.toPMF_mk, PMF.monad_map_eq_map]

end SPMF
