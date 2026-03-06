/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Convex.Basic
import ToMathlib.ProbabilityTheory.Coupling

/-!
# Optimal Couplings

This file provides the topological foundation to show that the space of couplings
between two distributions with finite support is compact, and that continuous
functions (like expected value) attain their supremum on this space.
-/

noncomputable section

open Topology ENNReal NNReal Set

universe u

variable {α β : Type u} [Fintype α] [Fintype β]

-- 1. Space of bounded non-negative real functions
-- 2. Compactness
-- 3. Attaining supremum

/-! ## The space of SubPMFs as a bounded closed subset of `Option (α × β) → ℝ` -/

section Topology

-- To show compactness, we embed `SubPMF (α × β)` into `Option (α × β) → ℝ`.

omit [Fintype α] [Fintype β] in
private lemma spmf_pure_eq (a : α) : (pure a : SubPMF α) = PMF.pure (some a) := by
  have : (pure a : SubPMF α) = liftM (PMF.pure a) := by
    simp [pure, liftM, OptionT.pure, monadLift, MonadLift.monadLift, OptionT.lift, PMF.instMonad]
  rw [this]; change (PMF.pure a).bind (fun x => PMF.pure (some x)) = _; rw [PMF.pure_bind]

omit [Fintype α] [Fintype β] in
private lemma spmf_fmap_eq_map (f : α → β) (c : SubPMF α) :
    (f <$> c : SubPMF β) = PMF.map (Option.map f) c := by
  have : (f <$> c : SubPMF β) =
    PMF.bind c (fun a => match a with
      | some a' => (pure (f a') : SubPMF β) | none => PMF.pure none) := by
    show (c >>= (pure ∘ f)) = _; exact SubPMF.bind_eq_pmf_bind
  rw [this]; apply PMF.ext; intro x
  simp only [PMF.bind_apply, PMF.map_apply]
  congr 1; ext y; cases y with
  | none => cases x <;> simp [PMF.pure_apply]
  | some a => simp only [spmf_pure_eq, PMF.pure_apply]; cases x <;> simp

lemma map_fst_eval (c : SubPMF (α × β)) (a : α) :
    (Prod.fst <$> c) (some a) = ∑ b, c (some (a, b)) := by
  sorry

lemma map_snd_eval (c : SubPMF (α × β)) (b : β) :
    (Prod.snd <$> c) (some b) = ∑ a, c (some (a, b)) := by
  sorry

def couplings_set (p : SubPMF α) (q : SubPMF β) : Set (Option (α × β) → ℝ) :=
  { c | (∀ z, 0 ≤ c z) ∧
        (∀ z, c z ≤ 1) ∧
        (∀ a, ∑ b, c (some (a, b)) = (p (some a)).toReal) ∧
        (∀ b, ∑ a, c (some (a, b)) = (q (some b)).toReal) ∧
        c none = 1 - (∑ z, c (some z)) }

-- 2. Prove this set is closed and bounded
lemma isClosed_couplings_set (p : SubPMF α) (q : SubPMF β) :
    IsClosed (couplings_set p q) := by
  rw [show couplings_set p q =
      {c | ∀ z, 0 ≤ c z} ∩
      {c | ∀ z, c z ≤ 1} ∩
      {c | ∀ a, ∑ b, c (some (a, b)) = (p (some a)).toReal} ∩
      {c | ∀ b, ∑ a, c (some (a, b)) = (q (some b)).toReal} ∩
      {c | c none = 1 - (∑ z, c (some z))} by
    ext x
    simp only [couplings_set, mem_inter_iff, mem_setOf_eq]
    tauto
  ]

  have h1 : IsClosed {c : Option (α × β) → ℝ | ∀ z, 0 ≤ c z} := by
    have : {c : Option (α × β) → ℝ | ∀ z, 0 ≤ c z} = ⋂ z, {c | 0 ≤ c z} := by ext; simp
    rw [this]
    exact isClosed_iInter fun z => isClosed_le continuous_const (continuous_apply z)
  have h2 : IsClosed {c : Option (α × β) → ℝ | ∀ z, c z ≤ 1} := by
    have : {c : Option (α × β) → ℝ | ∀ z, c z ≤ 1} = ⋂ z, {c | c z ≤ 1} := by ext; simp
    rw [this]
    exact isClosed_iInter fun z => isClosed_le (continuous_apply z) continuous_const
  have h3 : IsClosed {c : Option (α × β) → ℝ | ∀ a, ∑ b, c (some (a, b)) = (p (some a)).toReal} := by
    have : {c : Option (α × β) → ℝ | ∀ a, ∑ b, c (some (a, b)) = (p (some a)).toReal} = ⋂ a, {c | ∑ b, c (some (a, b)) = (p (some a)).toReal} := by ext; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_eq (continuous_finset_sum _ (fun b _ => continuous_apply _)) continuous_const
  have h4 : IsClosed {c : Option (α × β) → ℝ | ∀ b, ∑ a, c (some (a, b)) = (q (some b)).toReal} := by
    have : {c : Option (α × β) → ℝ | ∀ b, ∑ a, c (some (a, b)) = (q (some b)).toReal} = ⋂ b, {c | ∑ a, c (some (a, b)) = (q (some b)).toReal} := by ext; simp
    rw [this]
    exact isClosed_iInter fun b => isClosed_eq (continuous_finset_sum _ (fun a _ => continuous_apply _)) continuous_const
  have h5 : IsClosed {c : Option (α × β) → ℝ | c none = 1 - (∑ z, c (some z))} := by
    exact isClosed_eq (continuous_apply _) (continuous_const.sub (continuous_finset_sum _ (fun z _ => continuous_apply _)))

  exact (((h1.inter h2).inter h3).inter h4).inter h5

lemma isBounded_couplings_set (p : SubPMF α) (q : SubPMF β) :
    Bornology.IsBounded (couplings_set p q) := by
  rw [Metric.isBounded_iff]
  use 1
  intro x hx y hy
  rw [dist_pi_le_iff (by norm_num)]
  intro z
  have hx1 : 0 ≤ x z := hx.1 z
  have hx2 : x z ≤ 1 := hx.2.1 z
  have hy1 : 0 ≤ y z := hy.1 z
  have hy2 : y z ≤ 1 := hy.2.1 z
  rw [Real.dist_eq]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

lemma isCompact_couplings_set (p : SubPMF α) (q : SubPMF β) :
    IsCompact (couplings_set p q) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_couplings_set p q) (isBounded_couplings_set p q)

lemma mem_couplings_set_of_isCoupling {p : SubPMF α} {q : SubPMF β} (c : SubPMF (α × β))
    (hc : SubPMF.IsCoupling c p q) :
    (fun z => (c z).toReal) ∈ couplings_set p q := by
  simp only [couplings_set, mem_setOf_eq]
  refine ⟨fun z => ENNReal.toReal_nonneg, ?_, ?_, ?_, ?_⟩
  · intro z; have h := ENNReal.toReal_mono (by exact ENNReal.one_ne_top) (PMF.coe_le_one c z); exact h
  · intro a
    have h_fst : (Prod.fst <$> c) (some a) = p (some a) := by rw [hc.map_fst]
    have h_sum : (Prod.fst <$> c) (some a) = ∑ b, c (some (a, b)) := map_fst_eval c a
    rw [h_sum] at h_fst
    have h_toReal := congrArg ENNReal.toReal h_fst
    have h_sum_toReal : (∑ b, c (some (a, b))).toReal = ∑ b, (c (some (a, b))).toReal := by
      apply ENNReal.toReal_sum
      intro b _
      exact PMF.apply_ne_top c _
    rw [h_sum_toReal] at h_toReal
    exact h_toReal
  · intro b
    have h_snd : (Prod.snd <$> c) (some b) = q (some b) := by rw [hc.map_snd]
    have h_sum : (Prod.snd <$> c) (some b) = ∑ a, c (some (a, b)) := map_snd_eval c b
    rw [h_sum] at h_snd
    have h_toReal := congrArg ENNReal.toReal h_snd
    have h_sum_toReal : (∑ a, c (some (a, b))).toReal = ∑ a, (c (some (a, b))).toReal := by
      apply ENNReal.toReal_sum
      intro a _
      exact PMF.apply_ne_top c _
    rw [h_sum_toReal] at h_toReal
    exact h_toReal
  · have h_sum : (c none).toReal = 1 - ∑ z, (c (some z)).toReal := sorry
    exact h_sum

-- 3. Attaining supremum
lemma SubPMF.exists_max_coupling {p : SubPMF α} {q : SubPMF β}
    (f : Option (α × β) → ℝ≥0∞) (hf : ∀ z, f z ≠ ⊤)
    (h_nonempty : Nonempty (SubPMF.Coupling p q)) :
    ∃ (c : SubPMF.Coupling p q),
      (⨆ c' : SubPMF.Coupling p q, ∑' (z : Option (α × β)), (c'.1.1 z) * f z) = ∑' (z : Option (α × β)), (c.1.1 z) * f z := by
  let F : (Option (α × β) → ℝ) → ℝ := fun c => ∑ z, c z * (f z).toReal
  have hF_cont : Continuous F := continuous_finset_sum _ (fun z _ => (continuous_apply z).mul continuous_const)
  have h_comp := isCompact_couplings_set p q

  -- Show set is nonempty
  obtain ⟨c0⟩ := h_nonempty
  have h_nonempty_set : (couplings_set p q).Nonempty := by
    use fun z => (c0.1.1 z).toReal
    exact mem_couplings_set_of_isCoupling c0.1 c0.2

  -- Using compact max theorem
  have h_exists := h_comp.exists_isMaxOn h_nonempty_set hF_cont.continuousOn
  obtain ⟨c_max, hc_max_in, hc_max_prop⟩ := h_exists

  -- c_max is a function Option (α × β) → ℝ
  -- We need to build a Coupling out of it.
  have h_c_max_nonneg : ∀ z, 0 ≤ c_max z := hc_max_in.1
  have h_c_max_sum : HasSum c_max 1 := sorry

  let c_max_pmf : PMF (Option (α × β)) := ⟨fun z => ENNReal.ofReal (c_max z), sorry⟩
  let c_max_spmf : SubPMF (α × β) := c_max_pmf
  have hc_max_isCoupling : SubPMF.IsCoupling c_max_spmf p q := sorry
  use ⟨c_max_spmf, hc_max_isCoupling⟩

  -- Now show that this c_max_spmf achieves the supremum
  sorry

end Topology
