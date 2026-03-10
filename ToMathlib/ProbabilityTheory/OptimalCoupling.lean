/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Convex.Basic
public import ToMathlib.ProbabilityTheory.Coupling

/-!
# Optimal Couplings

This file provides the topological foundation to show that the space of couplings
between two distributions with finite support is compact, and that continuous
functions (like expected value) attain their supremum on this space.
-/

@[expose] public section

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
  classical
  rw [spmf_fmap_eq_map, PMF.map_apply, tsum_fintype, Fintype.sum_option]
  have hsimp :
      ((if some a = Option.map Prod.fst (none : Option (α × β)) then c none else 0) +
          ∑ x : α × β, if some a = Option.map Prod.fst (some x : Option (α × β)) then c (some x) else 0) =
        ∑ x : α × β, if a = x.1 then c (some x) else 0 := by
    simp
  have hprod :
      (∑ x : α × β, if a = x.1 then c (some x) else (0 : ℝ≥0∞)) =
        ∑ a', ∑ b : β, if a = a' then c (some (a', b)) else (0 : ℝ≥0∞) := by
    simpa using
      (Fintype.sum_prod_type' (f := fun a' b => if a = a' then c (some (a', b)) else (0 : ℝ≥0∞)))
  have hmain : (∑ x : α × β, if a = x.1 then c (some x) else (0 : ℝ≥0∞)) =
      ∑ b : β, c (some (a, b)) := by
    rw [hprod, Finset.sum_eq_single_of_mem a (by simp)]
    · simp
    · intro a' _ ha'
      have ha'' : a ≠ a' := by simpa [eq_comm] using ha'
      simp [ha'']
  simpa [hsimp] using hmain

lemma map_snd_eval (c : SubPMF (α × β)) (b : β) :
    (Prod.snd <$> c) (some b) = ∑ a, c (some (a, b)) := by
  classical
  rw [spmf_fmap_eq_map, PMF.map_apply, tsum_fintype, Fintype.sum_option]
  have hsimp :
      ((if some b = Option.map Prod.snd (none : Option (α × β)) then c none else 0) +
          ∑ x : α × β, if some b = Option.map Prod.snd (some x : Option (α × β)) then c (some x) else 0) =
        ∑ x : α × β, if b = x.2 then c (some x) else 0 := by
    simp
  have hprod :
      (∑ x : α × β, if b = x.2 then c (some x) else (0 : ℝ≥0∞)) =
        ∑ a : α, ∑ b', if b = b' then c (some (a, b')) else (0 : ℝ≥0∞) := by
    simpa using
      (Fintype.sum_prod_type' (f := fun a b' => if b = b' then c (some (a, b')) else (0 : ℝ≥0∞)))
  have hmain : (∑ x : α × β, if b = x.2 then c (some x) else (0 : ℝ≥0∞)) =
      ∑ a : α, c (some (a, b)) := by
    rw [hprod]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Finset.sum_eq_single_of_mem b (by simp)]
    · simp
    · intro b' _ hb'
      have hb'' : b ≠ b' := by simpa [eq_comm] using hb'
      simp [hb'']
  simpa [hsimp] using hmain

omit [Fintype α] [Fintype β] in
private lemma pmf_none_eq {γ : Type u} [Fintype γ] (p : PMF (Option γ)) :
    p none = 1 - ∑ x, p (some x) := by
  have h := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_option] at h
  exact ENNReal.eq_sub_of_add_eq' one_ne_top h

omit [Fintype α] [Fintype β] in
private lemma spmf_ext {γ : Type u} [Fintype γ] {p q : SubPMF γ}
    (h : ∀ x, p (some x) = q (some x)) : p = q := by
  refine PMF.ext fun x => ?_
  cases x with
  | none =>
      rw [pmf_none_eq, pmf_none_eq]
      congr with y
      exact h y
  | some x => exact h x

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
  · have h_total : c none + ∑ z, c (some z) = 1 := by
      simpa [tsum_fintype, Fintype.sum_option] using c.tsum_coe
    have h_some_le_one : ∑ z, c (some z) ≤ 1 := by
      calc
        ∑ z, c (some z) ≤ c none + ∑ z, c (some z) := by
          exact le_add_of_nonneg_left bot_le
        _ = 1 := h_total
    have h_sum : (c none).toReal = 1 - ∑ z, (c (some z)).toReal := by
      rw [pmf_none_eq, ENNReal.toReal_sub_of_le h_some_le_one one_ne_top, ENNReal.toReal_sum]
      · simp
      · intro z _
        exact PMF.apply_ne_top c _
    exact h_sum

omit [Fintype α] [Fintype β] in
private lemma sum_option_eq_one_of_none_eq_sub {γ : Type u} [Fintype γ]
    {c : Option γ → ℝ} (h_nonneg : ∀ z, 0 ≤ c z)
    (h_none : c none = 1 - ∑ z, c (some z)) :
    ∑ z : Option γ, c z = 1 := by
  rw [Fintype.sum_option, h_none]
  have h_some_le_one : ∑ z, c (some z) ≤ 1 := by
    have hnone_nonneg : 0 ≤ c none := h_nonneg none
    rw [h_none] at hnone_nonneg
    linarith
  linarith

private lemma exists_coupling_of_mem_couplings_set {p : SubPMF α} {q : SubPMF β}
    {c : Option (α × β) → ℝ} (hc : c ∈ couplings_set p q) :
    ∃ c' : SubPMF.Coupling p q, ∀ z, (c'.1.1 z).toReal = c z := by
  rcases hc with ⟨h_nonneg, _, h_row, h_col, h_none⟩
  have h_total_real : ∑ z : Option (α × β), c z = 1 := by
    exact sum_option_eq_one_of_none_eq_sub h_nonneg h_none
  have h_total :
      ∑ z : Option (α × β), ENNReal.ofReal (c z) = 1 := by
    calc
      ∑ z : Option (α × β), ENNReal.ofReal (c z)
          = ENNReal.ofReal (∑ z : Option (α × β), c z) := by
              symm
              simpa using
                (ENNReal.ofReal_sum_of_nonneg
                  (s := (Finset.univ : Finset (Option (α × β))))
                  (f := c)
                  (fun z _ => h_nonneg z))
      _ = 1 := by rw [h_total_real, ENNReal.ofReal_one]
  let c_pmf : PMF (Option (α × β)) := PMF.ofFintype (fun z => ENNReal.ofReal (c z)) h_total
  let c_spmf : SubPMF (α × β) := c_pmf
  have h_row_ennreal : ∀ a, ∑ b : β, c_spmf.1 (some (a, b)) = p (some a) := by
    intro a
    calc
      ∑ b : β, c_spmf.1 (some (a, b))
          = ∑ b : β, ENNReal.ofReal (c (some (a, b))) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              change (PMF.ofFintype (fun z => ENNReal.ofReal (c z)) h_total) (some (a, b)) =
                ENNReal.ofReal (c (some (a, b)))
              rfl
      _ = ENNReal.ofReal (∑ b : β, c (some (a, b))) := by
            symm
            simpa using
              (ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset β))
                (f := fun b => c (some (a, b)))
                (fun b _ => h_nonneg (some (a, b))))
      _ = ENNReal.ofReal ((p (some a)).toReal) := by rw [h_row a]
      _ = p (some a) := by rw [ENNReal.ofReal_toReal (PMF.apply_ne_top p _)]
  have h_col_ennreal : ∀ b, ∑ a : α, c_spmf.1 (some (a, b)) = q (some b) := by
    intro b
    calc
      ∑ a : α, c_spmf.1 (some (a, b))
          = ∑ a : α, ENNReal.ofReal (c (some (a, b))) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              change (PMF.ofFintype (fun z => ENNReal.ofReal (c z)) h_total) (some (a, b)) =
                ENNReal.ofReal (c (some (a, b)))
              rfl
      _ = ENNReal.ofReal (∑ a : α, c (some (a, b))) := by
            symm
            simpa using
              (ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset α))
                (f := fun a => c (some (a, b)))
                (fun a _ => h_nonneg (some (a, b))))
      _ = ENNReal.ofReal ((q (some b)).toReal) := by rw [h_col b]
      _ = q (some b) := by rw [ENNReal.ofReal_toReal (PMF.apply_ne_top q _)]
  have hfst_some : ∀ a, (Prod.fst <$> c_spmf) (some a) = p (some a) := by
    intro a
    rw [map_fst_eval]
    exact h_row_ennreal a
  have hsnd_some : ∀ b, (Prod.snd <$> c_spmf) (some b) = q (some b) := by
    intro b
    rw [map_snd_eval]
    exact h_col_ennreal b
  have hcpl : SubPMF.IsCoupling c_spmf p q := ⟨spmf_ext hfst_some, spmf_ext hsnd_some⟩
  refine ⟨⟨c_spmf, hcpl⟩, ?_⟩
  intro z
  change (ENNReal.ofReal (c z)).toReal = c z
  exact ENNReal.toReal_ofReal (h_nonneg z)

private lemma objective_eq_ofReal (c : SubPMF (α × β))
    (f : Option (α × β) → ℝ≥0∞) (hf : ∀ z, f z ≠ ⊤) :
    (∑' z, c.1 z * f z) = ENNReal.ofReal (∑ z, (c.1 z).toReal * (f z).toReal) := by
  rw [tsum_fintype]
  calc
    ∑ z : Option (α × β), c.1 z * f z
        = ∑ z : Option (α × β), ENNReal.ofReal ((c.1 z).toReal * (f z).toReal) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal]
            exact ENNReal.mul_ne_top (PMF.apply_ne_top c z) (hf z)
    _ = ENNReal.ofReal (∑ z : Option (α × β), (c.1 z).toReal * (f z).toReal) := by
          symm
          simpa using
            (ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.univ : Finset (Option (α × β))))
              (f := fun z => (c.1 z).toReal * (f z).toReal)
              (fun z _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))

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
  obtain ⟨c_max_cpl, hc_max_eq⟩ := exists_coupling_of_mem_couplings_set hc_max_in
  use c_max_cpl
  apply le_antisymm
  · refine iSup_le ?_
    intro c'
    have hc'_in : (fun z => (c'.1.1 z).toReal) ∈ couplings_set p q := by
      exact mem_couplings_set_of_isCoupling c'.1 c'.2
    have hmax_real : F (fun z => (c'.1.1 z).toReal) ≤ F c_max := by
      exact (isMaxOn_iff.mp hc_max_prop) _ hc'_in
    have h_obj_left :
        (∑' z, c'.1.1 z * f z) = ENNReal.ofReal (F (fun z => (c'.1.1 z).toReal)) := by
      simpa [F] using (objective_eq_ofReal c'.1 f hf)
    have h_obj_right :
        (∑' z, c_max_cpl.1.1 z * f z) = ENNReal.ofReal (F c_max) := by
      simpa [F, hc_max_eq] using (objective_eq_ofReal c_max_cpl.1 f hf)
    rw [h_obj_left, h_obj_right]
    exact ENNReal.ofReal_le_ofReal hmax_real
  · exact le_iSup (f := fun c' : SubPMF.Coupling p q => ∑' z, c'.1.1 z * f z) c_max_cpl

end Topology
