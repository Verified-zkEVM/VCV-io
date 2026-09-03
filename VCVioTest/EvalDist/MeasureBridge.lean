/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio

/-!
# The measure gate

The measure-side counterpart of `VCVioTest/ProbabilityTactics.lean`: goal families about the
primary measure `𝒟[…]`, each closed by one terminal tactic, following the conventions of
`CONTRIBUTING.md` (*Tactic Gate Files*). The contract it pins is that on a discrete carrier the
measure side reduces *into* the discrete façade: singleton, event and total masses become
`Pr[…]`, and an integral against `𝒟[mx]` becomes `expectedValue mx g`, after which the façade's
own `simp`/`grind` contract applies. The Giry laws for `bind`/`map` stay out of default `simp`
on both sides, and the integral form of a bind is an intermediate, not a target.

The same entries run with the compatibility adapter (no measure specification in scope), with
the free-monad fold (a local `IsProbabilitySpec.toMeasureSpec`), and over `OptionT ProbComp`,
where failure mass is visible; all three satisfy `DiscreteEvalDistCompatible`. The total-mass
entries use `Fin 3` rather than `Bool` because Mathlib's `simp` rewrites `(Set.univ : Set Bool)`
to the literal `{false, true}` before any `𝒟`-keyed lemma can see it.
-/

public section

open MeasureTheory OracleComp OracleSpec OracleComp.EvalDist
open scoped ENNReal

namespace VCVioTest.MeasureBridge

/-! ## Adapter side: `ProbComp` with no measure specification -/

example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) (p : Bool → Prop) : 𝒟[mx] {b | p b} = Pr[p | mx] := by simp
example (mx : ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx] := by simp
example (mx : ProbComp Bool) (g : Bool → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g := by simp
example (mx : ProbComp Bool) (c : ℝ≥0∞) :
    ∫⁻ _, c ∂𝒟[mx] = expectedValue mx fun _ => c := by simp

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} = 1 := by simp
example : 𝒟[$ᵗ Bool] {true} = 2⁻¹ := by simp

example (mx : ProbComp (Fin 2)) (my : ProbComp (Fin 3)) (y : Fin 3) :
    𝒟[mx >>= fun _ => my] {y} = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by simp
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

/-- The ladder's finite rung: expanding a bind on a `Fintype` lands on a finite sum through
Mathlib's `tsum_fintype`, with no library lemma involved. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) (y : Fin 3) :
    Pr[= y | mx >>= f] = ∑ x, Pr[= x | mx] * Pr[= y | f x] := by
  simp [probOutput_bind_eq_tsum]

/-- The Giry bind law is a `rw`/`exact` target, not a simp rule, on either side. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) :
    𝒟[mx >>= f] = 𝒟[mx].bind fun x => 𝒟[f x] := by
  fail_if_success simp  -- by design: bind expansion is not default simp
  exact evalDist_bind_of_discrete mx f

/-- The integral form of a bind is an intermediate, not a target: `simp` takes the right-hand
side into the façade instead of meeting it. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) (s : Set (Fin 3)) :
    𝒟[mx >>= f] s = ∫⁻ x, 𝒟[f x] s ∂𝒟[mx] := by
  fail_if_success (simp; done)  -- by design: the integral form is not a normal form
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

/-! ## Free-monad fold: `ProbComp` with a local measure specification -/

section measureSpec

/-- A local measure specification for `unifSpec`, so nothing leaks through the test umbrella. -/
@[instance_reducible]
noncomputable def unifMeasureSpec : unifSpec.toPFunctor.IsMeasureSpec :=
  PFunctor.IsProbabilitySpec.toMeasureSpec _

attribute [local instance] unifMeasureSpec

example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) (p : Bool → Prop) : 𝒟[mx] {b | p b} = Pr[p | mx] := by simp
example (mx : ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx] := by simp
example (mx : ProbComp Bool) (g : Bool → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g := by simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) :
    𝒟[mx >>= f] = 𝒟[mx].bind fun x => 𝒟[f x] :=
  evalDist_bind_of_discrete mx f

end measureSpec

/-! ## `OptionT ProbComp`: failure mass is visible -/

example (mx : OptionT ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = Pr[= x | mx] := by simp
example (mx : OptionT ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx] := by simp
example (mx : OptionT ProbComp Bool) (g : Bool → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g := by simp
example (mx : OptionT ProbComp Bool) (my : OptionT ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

/-! ## Failure is missing mass -/

example : 𝒟[(failure : OptionT ProbComp Bool)] = 0 := by simp
example (mx : OptionT ProbComp Bool) : (𝒟[mx]).withFailure {none} = Pr[⊥ | mx] := by simp
example (mx : OptionT ProbComp Bool) (x : Bool) :
    (𝒟[mx]).withFailure {some x} = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) : IsProbabilityMeasure 𝒟[mx] := inferInstance
example (mx : ProbComp (Fin 3)) (f : Fin 3 → ProbComp (Fin 2)) : 𝒟[mx >>= f] Set.univ = 1 := by
  simp
/-! ## A unit-test program

A coin and a die drawn independently, closed on the measure side by the same calls as the
façade: the point mass is the product of the two uniform masses (the closed form `simp` reaches;
merging `2⁻¹ * 6⁻¹` into `12⁻¹` is `ℝ≥0∞` arithmetic, not a probability rule), an event on one
coordinate needs the bind expanded under `Pr[…]` and `ENNReal.div_self` for the total factor. -/

/-- A coin and a die, drawn independently. -/
def coinDie : ProbComp (Bool × Fin 6) := do
  let b ← $ᵗ Bool
  let d ← $ᵗ (Fin 6)
  pure (b, d)

example : 𝒟[coinDie] {(true, 0)} = 2⁻¹ * 6⁻¹ := by simp [coinDie]
example : 𝒟[coinDie] {z | z.1 = true} = 2⁻¹ := by
  simp [coinDie, probEvent_bind_eq_tsum, ENNReal.div_self]
example (g : Bool × Fin 6 → ℝ≥0∞) : ∫⁻ z, g z ∂𝒟[coinDie] = expectedValue coinDie g := by simp

/-! ## Continuous carriers are untouched -/

/-- Without a discrete carrier the bridge does not fire: `lintegral_evalDist` needs
`DiscreteMeasurableSpace`, which `ℝ` does not have. -/
example (mx : ProbComp ℝ) (g : ℝ → ℝ≥0∞) (h : ∫⁻ x, g x ∂𝒟[mx] = 0) :
    ∫⁻ x, g x ∂𝒟[mx] = 0 := by
  fail_if_success simp only [lintegral_evalDist] at h
  exact h

end VCVioTest.MeasureBridge
