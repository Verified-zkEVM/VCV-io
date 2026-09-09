/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Bounds
public import ToMathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Uniform table resampling

Finite uniform measures are normalized counting measures. Independently resampling one
coordinate of a uniform table preserves its joint distribution. These laws work directly
with measures and can be used below any computation or random-oracle semantics.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- Integrate a continuation against a finite uniform measure. -/
theorem uniformOn_univ_bind_apply {α β : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] (f : α → Measure β)
    (s : Set β) (hs : MeasurableSet s) :
    ((uniformOn Set.univ : Measure α).bind f) s =
      ∑ a, (Fintype.card α : ENNReal)⁻¹ * f a s := by
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp [uniformOn_univ, mul_comm]

/-- Replace one cell of a uniform table by an independent uniform value. -/
theorem uniformOn_univ_bind_map_update {D R : Type*} [Finite D] [DecidableEq D]
    [Finite R] [Nonempty R] [MeasurableSpace R] [MeasurableSingletonClass R] (t : D) :
    (uniformOn Set.univ : Measure R).bind (fun u =>
      (uniformOn Set.univ : Measure (D → R)).map (fun g => Function.update g t u)) =
      uniformOn Set.univ := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype R := Fintype.ofFinite R
  apply Measure.ext_of_singleton
  intro h
  rw [uniformOn_univ_bind_apply _ _ (MeasurableSet.singleton h)]
  have hinner : ∀ u : R,
      ((uniformOn Set.univ : Measure (D → R)).map (fun g => Function.update g t u)) {h}
        = if u = h t then
            (Fintype.card R : ENNReal) * (Fintype.card (D → R) : ENNReal)⁻¹ else 0 := by
    intro u
    rw [Measure.map_apply .of_discrete (MeasurableSet.singleton h)]
    change (uniformOn Set.univ : Measure (D → R)) {g | Function.update g t u = h} = _
    rw [show {g | Function.update g t u = h} = {g | h = Function.update g t u} by
      ext; exact eq_comm]
    rw [uniformOn_univ_apply_setOf]
    have hcard :
        ((Finset.univ.filter fun g : D → R => h = Function.update g t u).card : ENNReal)
          = if u = h t then (Fintype.card R : ENNReal) else 0 := by
      by_cases hu : u = h t
      · have hset : (Finset.univ.filter fun g : D → R => h = Function.update g t u)
            = Finset.univ.image (fun r : R => Function.update h t r) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hg
            exact ⟨g t, by subst hg; simp⟩
          · rintro ⟨r, rfl⟩
            subst hu; simp
        rw [hset, Finset.card_image_of_injective _
          (fun r₁ r₂ hr => by simpa using congrFun hr t), Finset.card_univ, if_pos hu]
      · rw [if_neg hu, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro g - rfl
        simp at hu
    rw [hcard, ENNReal.div_eq_inv_mul, mul_ite, mul_zero, mul_comm]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (h t), if_pos (Finset.mem_univ _),
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero])
      (ENNReal.natCast_ne_top _), one_mul]
  simp [uniformOn_univ]

/-- A bijection transports a finite uniform measure to the uniform measure on its codomain. -/
theorem uniformOn_univ_map_equiv {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformOn Set.univ : Measure α).map e = (uniformOn Set.univ : Measure β) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.map_apply .of_discrete (MeasurableSet.singleton y)]
  have hpreimage : e ⁻¹' {y} = {e.symm y} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← e.eq_symm_apply]
  rw [hpreimage]
  simp [uniformOn_univ, Fintype.card_congr e]

/-- Restrict a uniform table to an injectively indexed family of cells. -/
theorem uniformOn_univ_map_comp_injective {A B R : Type*} [Finite A] [Finite B] [Finite R]
    [Nonempty R] [MeasurableSpace R] [MeasurableSingletonClass R]
    {e : A → B} (he : Function.Injective e) :
    (uniformOn Set.univ : Measure (B → R)).map (fun g => g ∘ e) =
      (uniformOn Set.univ : Measure (A → R)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype R := Fintype.ofFinite R
  let C := {b : B // b ∉ Set.range e}
  let φ : (B → R) ≃ (A → R) × (C → R) :=
    (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range e)).symm.trans
      ((Equiv.ofInjective e he).symm.sumCongr (Equiv.refl C))) (Equiv.refl R)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have hφ1 : ∀ g : B → R, (φ g).1 = g ∘ e := fun g => funext fun a => by
    simp [φ, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
  calc
    _ = ((uniformOn Set.univ : Measure (B → R)).map φ).map Prod.fst := by
      rw [Measure.map_map .of_discrete .of_discrete]
      simp only [Function.comp_def, hφ1]
    _ = (uniformOn Set.univ : Measure ((A → R) × (C → R))).map Prod.fst := by
      rw [uniformOn_univ_map_equiv]
    _ = _ := by rw [uniformOn_univ_prod, Measure.map_fst_prod, measure_univ, one_smul]

end ProbabilityTheory
