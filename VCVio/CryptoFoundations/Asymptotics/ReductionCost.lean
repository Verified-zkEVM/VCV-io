/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.OracleComp.QueryTracking.ResourceProfile

/-!
# Cost-Aware Security Reductions

This file packages the cost-transform part of a reduction theorem.

`ReductionWithCost` records:

- a reduction `reduce : Adv → Adv'`,
- a monotone transform on asymptotic cost bounds,
- a proof that the reduced adversary's cost profile is bounded by that transform.

This is intentionally abstract in both the choice of efficiency class and the shape of the cost
objects being transformed. Users can instantiate the resulting meta-theorems with scalar costs,
structured resource profiles, interface-profile bounds, or any other preordered asymptotic notion
that is closed under the transform carried by the reduction.
-/

open OracleComp OracleSpec ENNReal Filter

namespace SecurityGame

variable {Adv Adv' Adv'' : Type*}
variable {σ σ' σ'' : Type*}
variable [Preorder σ] [Preorder σ'] [Preorder σ'']

/-- An adversary is efficient for a profile class `isEff` if its concrete cost profile is bounded by
some admissible asymptotic profile in that class. -/
def EfficientFor
    (cost : Adv → ℕ → σ)
    (isEff : (ℕ → σ) → Prop) : Adv → Prop :=
  fun A ↦ ∃ bound, isEff bound ∧ ∀ n, cost A n ≤ bound n

/-- A reduction together with an explicit transform on asymptotic cost bounds. -/
structure ReductionWithCost
    (cost : Adv → ℕ → σ)
    (cost' : Adv' → ℕ → σ') where
  reduce : Adv → Adv'
  transform : ℕ → σ → σ'
  monotone_transform : ∀ n, Monotone (transform n)
  cost_bound : ∀ A n, cost' (reduce A) n ≤ transform n (cost A n)

namespace ReductionWithCost

variable {cost : Adv → ℕ → σ}
variable {cost' : Adv' → ℕ → σ'}
variable {cost'' : Adv'' → ℕ → σ''}

/-- The cost transform of a reduction sends admissible profile bounds on the source adversary to
admissible profile bounds on the reduced adversary. -/
theorem efficientFor_image
    (R : ReductionWithCost cost cost')
    {isEff : (ℕ → σ) → Prop}
    {isEff' : (ℕ → σ') → Prop}
    {A : Adv}
    (hA : EfficientFor cost isEff A)
    (hmap : ∀ bound, isEff bound → isEff' (fun n ↦ R.transform n (bound n))) :
    EfficientFor cost' isEff' (R.reduce A) := by
  rcases hA with ⟨bound, hboundEff, hbound⟩
  refine ⟨fun n ↦ R.transform n (bound n), hmap bound hboundEff, ?_⟩
  intro n
  simpa using le_trans (R.cost_bound A n) ((R.monotone_transform n) (hbound n))

/-- Cost-aware reductions compose by composing both the adversary map and the profile transform. -/
def comp
    (R₁ : ReductionWithCost cost cost')
    (R₂ : ReductionWithCost cost' cost'') :
    ReductionWithCost cost cost'' where
  reduce := R₂.reduce ∘ R₁.reduce
  transform n := R₂.transform n ∘ R₁.transform n
  monotone_transform n := (R₂.monotone_transform n).comp (R₁.monotone_transform n)
  cost_bound A n := by
    simpa using le_trans (R₂.cost_bound (R₁.reduce A) n)
      ((R₂.monotone_transform n) (R₁.cost_bound A n))

end ReductionWithCost

/-- Cost-aware security reduction.

If a reduction preserves advantage, and if the target efficiency class is closed under the
reduction's cost transform, then security of the target game implies security of the source game
for adversaries whose cost profiles lie in the source class. -/
theorem secureAgainst_of_reduction_withCost
    {g : SecurityGame Adv} {g' : SecurityGame Adv'}
    {cost : Adv → ℕ → σ}
    {cost' : Adv' → ℕ → σ'}
    {isEff : (ℕ → σ) → Prop}
    {isEff' : (ℕ → σ') → Prop}
    (R : ReductionWithCost cost cost')
    (hadv : ∀ A n, g.advantage A n ≤ g'.advantage (R.reduce A) n)
    (hmap : ∀ bound, isEff bound → isEff' (fun n ↦ R.transform n (bound n)))
    (hsecure : g'.secureAgainst (EfficientFor cost' isEff')) :
    g.secureAgainst (EfficientFor cost isEff) := by
  intro A hA
  exact negligible_of_le (hadv A)
    (hsecure (R.reduce A) (R.efficientFor_image hA hmap))

end SecurityGame
