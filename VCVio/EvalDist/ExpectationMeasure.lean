/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Expectation

/-!
# `expectedValue` as a Lebesgue integral

`VCVio.EvalDist.Expectation` defines `expectedValue mx g` as `∑' x, Pr[= x | mx] * g x`. This
module identifies that discrete spelling with the `lintegral` against the primary evaluation
measure `𝒟[mx]`, for every semantics that satisfies the façade bridge
`DiscreteEvalDistCompatible`.

`lintegral_evalDist` is stated in the simp direction: on a discrete space an integral against
`𝒟[mx]` *is* the façade expectation, so a measure-side goal reduces into the discrete normal
form, where the existing `simp`/`grind` contract applies. Monotone convergence
(`expectedValue_iSup`) is the first payoff: `lintegral_iSup` becomes available for VCVio
expectations by rewriting once, and there is no `∑'`-shaped lemma for it in the library.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u v

namespace OracleComp.EvalDist

variable {α : Type u} {m : Type u → Type v} [MonadLiftT m SPMF] [EvalDistSemantics m]
  [DiscreteEvalDistCompatible m] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- An integral against the denoted measure is the façade expectation. The priority puts this
rewrite ahead of the generic `lintegral_*` simp lemmas, so an `∫⁻ … ∂𝒟[mx]` leaves the measure
world before they fire. -/
@[simp high]
theorem lintegral_evalDist (mx : m α) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g :=
  DiscreteEvalDistCompatible.lintegral_evalDist mx Measurable.of_discrete

/-- **Monotone convergence** for VCVio expectations. -/
theorem expectedValue_iSup (mx : m α) (g : ℕ → α → ℝ≥0∞) (hg : Monotone g) :
    expectedValue mx (fun x => ⨆ n, g n x) = ⨆ n, expectedValue mx (g n) := by
  simp only [← lintegral_evalDist]
  exact lintegral_iSup (fun _ => Measurable.of_discrete) hg

end OracleComp.EvalDist
