/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Interchanging independent measure-valued draws

Joint measurability of a continuation lets independent s-finite draws commute under
Giry bind. No normalization of the measures is required, so the laws also apply to
subprobability measures and continuations with missing mass.
-/

public section

open MeasureTheory Function

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- Integrating a jointly measurable measure-valued continuation gives a measurable family. -/
theorem measurable_bind_prod_right (ν : Measure β) [SFinite ν]
    {f : α → β → Measure γ} (hf : Measurable (uncurry f)) :
    Measurable fun a => ν.bind (f a) := by
  apply measurable_of_measurable_coe
  intro s hs
  have hfa (a : α) : Measurable (f a) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have heq : (fun a => (ν.bind (f a)) s) = fun a => ∫⁻ b, f a b s ∂ν :=
    funext fun a => bind_apply hs (hfa a).aemeasurable
  rw [heq]
  exact Measurable.lintegral_prod_right (f := fun a b => f a b s)
    ((measurable_coe hs).comp hf)

/-- Two independent s-finite draws commute before a jointly measurable continuation. -/
theorem bind_bind_swap (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {f : α → β → Measure γ} (hf : Measurable (uncurry f)) :
    μ.bind (fun a => ν.bind (f a)) = ν.bind (fun b => μ.bind (fun a => f a b)) := by
  have hfa (a : α) : Measurable (f a) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hfb (b : β) : Measurable fun a => f a b :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hswap : Measurable (uncurry fun b a => f a b) := hf.comp measurable_swap
  ext s hs
  rw [bind_apply hs (measurable_bind_prod_right ν hf).aemeasurable,
    bind_apply hs (measurable_bind_prod_right μ hswap).aemeasurable]
  simp_rw [bind_apply hs (hfa _).aemeasurable, bind_apply hs (hfb _).aemeasurable]
  exact lintegral_lintegral_swap ((measurable_coe hs).comp hf).aemeasurable

/-- Move the third independent draw before the first two, preserving continuation order. -/
theorem bind_bind_bind_rotate (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] {f : α → β → γ → Measure δ}
    (hf : Measurable fun p : α × β × γ => f p.1 p.2.1 p.2.2) :
    μ.bind (fun a => ν.bind (fun b => ρ.bind (f a b))) =
      ρ.bind (fun c => μ.bind (fun a => ν.bind (fun b => f a b c))) := by
  calc
    _ = μ.bind (fun a => ρ.bind (fun c => ν.bind (fun b => f a b c))) := by
      apply bind_congr_right
      exact Filter.Eventually.of_forall fun a =>
        bind_bind_swap ν ρ (hf.comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      apply bind_bind_swap μ ρ
      exact measurable_bind_prod_right ν
        (hf.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)))

end MeasureTheory.Measure
