/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.CryptoFoundations.KEMDEM.Measure
public import VCVio.EvalDist.PFunctorMeasure.Core
import Mathlib.Tactic.NormNum

/-!
# Native KEM–DEM and Boolean-bias checks

The native hybrid proof imports no discrete probability backend. A direct free-program
interpretation exercises the whole bound; a lossy branch demonstrates why the hidden-bit
identity needs its totality hypotheses.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native KEM–DEM imports unexpectedly include {name}"

namespace VCVioTest.KEMDEMMeasure

/-- A native fair-coin query interface. -/
@[expose, reducible] def coinSpec : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

instance : coinSpec.Fintype where
  fintypeB _ := inferInstance

instance : coinSpec.Inhabited where
  inhabitedB _ := inferInstance

noncomputable instance : coinSpec.IsMeasureSpec :=
  IsMeasureSpec.uniformOfFintypeInhabited _

example (prepare : FreeM coinSpec Unit) (encaps : Unit → FreeM coinSpec (Bool × Bool))
    (finish : Unit → Bool → Bool → Bool → FreeM coinSpec Bool) :
    (𝒟[KEMDEM.composedGame prepare encaps finish (FreeM.lift ())]).boolBias ≤
      (𝒟[KEMDEM.kemGame prepare encaps finish (FreeM.lift ()) (FreeM.lift ()) true]).boolBias +
      (𝒟[KEMDEM.kemGame prepare encaps finish (FreeM.lift ()) (FreeM.lift ()) false]).boolBias +
      (𝒟[KEMDEM.demGame prepare encaps finish (FreeM.lift ()) (FreeM.lift ())]).boolBias := by
  let (mx : FreeM coinSpec Bool) : IsProbabilityMeasure 𝒟[mx] :=
    FreeM.isProbabilityMeasure_denote mx
  have hcoin (b : Bool) : (uniformOn Set.univ : Measure Bool) {b} = 1 / 2 := by
    rw [uniformOn_univ]
    simp [Fintype.card_bool]
  apply KEMDEM.bias_compose_le
  · rw [FreeM.evalDist_lift (P := coinSpec)]
    exact hcoin _
  · rw [FreeM.evalDist_lift (P := coinSpec)]
    exact hcoin _
  · exact measure_univ
  · intro real side
    have h : ∫⁻ _, (1 : ENNReal)
        ∂𝒟[KEMDEM.hybrid prepare encaps finish (FreeM.lift ()) real side] = 1 := by
      rw [lintegral_one]
      exact measure_univ
    simpa only [lintegral_fintype, Fintype.sum_bool, one_mul] using h

example :
    ((uniformOn Set.univ : Measure Bool).bind fun b =>
      (if b then 0 else Measure.dirac true).bind fun z => Measure.dirac (b == z)).boolBias =
        1 / 2 := by
  have hcoin (b : Bool) : (uniformOn Set.univ : Measure Bool) {b} = 1 / 2 := by
    rw [uniformOn_univ]
    simp [Fintype.card_bool]
  unfold Measure.boolBias
  simp only [Measure.bind_apply (MeasurableSet.singleton _) Measurable.of_discrete.aemeasurable,
    lintegral_fintype, Fintype.sum_bool, hcoin]
  norm_num [Measure.dirac_apply']

example : (0 : Measure Bool).boolDist (Measure.dirac true) = 1 := by
  norm_num [Measure.boolDist, Measure.dirac_apply']

end VCVioTest.KEMDEMMeasure
