/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.IndependentDraws

/-!
# Independent draws under measure-valued evaluation

The Giry composition laws transport measure-level independence to computation syntax.
The general interchange theorem requires joint measurability; the three-draw law
specializes to discrete intermediate results and leaves the final result space arbitrary.
-/

public section

open MeasureTheory Function

universe u v

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β γ δ : Type u}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Independent computations commute under a jointly measurable denoted continuation. -/
theorem evalDist_bind_bind_swap (mx : m α) (my : m β) (f : α → β → m γ)
    (hf : Measurable fun p : α × β => 𝒟[f p.1 p.2]) :
    𝒟[mx >>= fun a => my >>= fun b => f a b] =
      𝒟[my >>= fun b => mx >>= fun a => f a b] := by
  have hfa (a : α) : Measurable fun b => 𝒟[f a b] :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hfb (b : β) : Measurable fun a => 𝒟[f a b] :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hleft : Measurable fun a => 𝒟[my >>= f a] := by
    simp_rw [evalDist_bind my _ (hfa _)]
    exact Measure.measurable_bind_prod_right 𝒟[my] hf
  have hright : Measurable fun b => 𝒟[mx >>= fun a => f a b] := by
    simp_rw [evalDist_bind mx _ (hfb _)]
    exact Measure.measurable_bind_prod_right 𝒟[mx] (hf.comp measurable_swap)
  rw [evalDist_bind mx _ hleft, evalDist_bind my _ hright]
  simp_rw [evalDist_bind my _ (hfa _), evalDist_bind mx _ (hfb _)]
  exact Measure.bind_bind_swap _ _ hf

/-- Move the third independent discrete draw to the front of a computation. -/
theorem evalDist_bind_bind_bind_rotate [DiscreteMeasurableSpace α]
    [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    (mx : m α) (my : m β) (mz : m γ) (f : α → β → γ → m δ)
    (hf : Measurable fun p : α × β × γ => 𝒟[f p.1 p.2.1 p.2.2]) :
    𝒟[mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
      𝒟[mz >>= fun c => mx >>= fun a => my >>= fun b => f a b c] := by
  simp only [evalDist_bind_of_discrete]
  exact Measure.bind_bind_bind_rotate _ _ _ hf
