/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.PFunctorMeasure.Core
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Measure-only independent-draw checks

The imports provide direct polynomial-program measure semantics without a discrete
distribution backend. Continuous draws and subprobability continuations exercise
the measurable and potentially lossy forms of interchange.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "measure-only imports unexpectedly include {name}"

namespace VCVioTest.IndependentDraws

example (μ ν ρ : Measure ℝ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    μ.bind (fun a => ν.bind (fun b => ρ.bind (fun c => Measure.dirac (a + b * c)))) =
      ρ.bind (fun c => μ.bind (fun a => ν.bind (fun b => Measure.dirac (a + b * c)))) := by
  apply Measure.bind_bind_bind_rotate
  fun_prop

example :
    (gaussianReal 0 1).bind (fun a => (gaussianReal 1 2).bind
      (fun b => Measure.dirac (a + b))) =
      (gaussianReal 1 2).bind (fun b => (gaussianReal 0 1).bind
        (fun a => Measure.dirac (a + b))) := by
  apply Measure.bind_bind_swap
  fun_prop

example (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    μ.bind (fun a => ν.bind (fun b => (1 / 2 : ENNReal) • Measure.dirac (a + b))) =
      ν.bind (fun b => μ.bind (fun a => (1 / 2 : ENNReal) • Measure.dirac (a + b))) := by
  apply Measure.bind_bind_swap
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable fun p : ℝ × ℝ => (1 / 2 : ENNReal) * Measure.dirac (p.1 + p.2) s
  exact measurable_const.mul ((Measure.measurable_coe hs).comp
    (Measure.measurable_dirac.comp (measurable_fst.add measurable_snd)))

example (ν : Measure ℝ) :
    (0 : Measure ℝ).bind (fun a => ν.bind (fun b => Measure.dirac (a + b))) = 0 := by
  simp

/-- A finite-answer interface whose semantics is a native uniform measure. -/
@[expose, reducible] def coinSpec : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

instance : coinSpec.Fintype where
  fintypeB _ := inferInstance

instance : coinSpec.Inhabited where
  inhabitedB _ := inferInstance

noncomputable instance : coinSpec.IsMeasureSpec :=
  IsMeasureSpec.uniformOfFintypeInhabited _

example (mx : FreeM coinSpec Bool) (my : FreeM coinSpec (Fin 3))
    (mz : FreeM coinSpec Unit) (f : Bool → Fin 3 → Unit → FreeM coinSpec ℝ) :
    𝒟[mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
      𝒟[mz >>= fun c => mx >>= fun a => my >>= fun b => f a b c] := by
  apply evalDist_bind_bind_bind_rotate
  exact Measurable.of_discrete

end VCVioTest.IndependentDraws
