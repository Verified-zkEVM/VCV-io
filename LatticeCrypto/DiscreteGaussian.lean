/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Discrete Gaussian Distribution

This file defines the discrete Gaussian distribution `D_{ℤ,σ,μ}` over the integers,
parameterized by a standard deviation `σ > 0` and a center `μ ∈ ℝ`. This distribution is
fundamental to lattice-based cryptography, where it is used for trapdoor sampling (GPV
framework, Falcon) and masking (ML-DSA / Dilithium).

## Main Definitions

- `discreteGaussianWeight σ μ z` — the unnormalized Gaussian weight
  `exp(-(z - μ)² / (2σ²))` at integer `z`.
- `discreteGaussianSum σ μ` — the normalizing constant `∑_{z ∈ ℤ} ρ_{σ,μ}(z)`.
- `discreteGaussianPMF σ μ` — the probability mass function, defined as
  `ρ_{σ,μ}(z) / ∑_z ρ_{σ,μ}(z)`.

## References

- Falcon specification v1.2, Section 3.9.3 (SamplerZ)
- Gentry, Peikert, Vaikuntanathan. STOC 2008.
- Micciancio, Regev. "Lattice-based Cryptography." 2009.
-/


open Real BigOperators

namespace LatticeCrypto

/-- The unnormalized Gaussian weight at integer point `z` with center `μ` and standard
deviation `σ`. -/
noncomputable def discreteGaussianWeight (σ μ : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(↑z - μ) ^ 2 / (2 * σ ^ 2))

/-- The discrete Gaussian weight is strictly positive at every integer point. -/
theorem discreteGaussianWeight_pos (σ μ : ℝ) (z : ℤ) :
    0 < discreteGaussianWeight σ μ z :=
  exp_pos _

/-- The discrete Gaussian weight is nonnegative at every integer point. -/
theorem discreteGaussianWeight_nonneg (σ μ : ℝ) (z : ℤ) :
    0 ≤ discreteGaussianWeight σ μ z :=
  le_of_lt (discreteGaussianWeight_pos σ μ z)

/-- The normalizing constant for the discrete Gaussian: `∑_{z ∈ ℤ} ρ_{σ,μ}(z)`. -/
noncomputable def discreteGaussianSum (σ μ : ℝ) : ℝ :=
  ∑' (z : ℤ), discreteGaussianWeight σ μ z

/-- The discrete Gaussian sum converges for any `σ > 0`. The Gaussian weight decays
exponentially, so the sum over `ℤ` is absolutely convergent. -/
theorem discreteGaussianSum_summable (σ μ : ℝ) (hσ : 0 < σ) :
    Summable (discreteGaussianWeight σ μ) := by
  sorry

/-- The discrete Gaussian normalizing constant is strictly positive when `σ > 0`. -/
theorem discreteGaussianSum_pos (σ μ : ℝ) (hσ : 0 < σ) :
    0 < discreteGaussianSum σ μ := by
  exact (discreteGaussianSum_summable σ μ hσ).tsum_pos
    (fun z => discreteGaussianWeight_nonneg σ μ z) 0
    (discreteGaussianWeight_pos σ μ 0)

/-- The discrete Gaussian probability mass function over `ℤ` with center `μ` and standard
deviation `σ`. Defined as the normalized Gaussian weight:

  `P(z) = exp(-(z - μ)² / (2σ²)) / (∑_{z' ∈ ℤ} exp(-(z' - μ)² / (2σ²)))` -/
noncomputable def discreteGaussianPMF (σ μ : ℝ) : ℤ → ℝ :=
  fun z => discreteGaussianWeight σ μ z / discreteGaussianSum σ μ

/-- The discrete Gaussian PMF is pointwise nonnegative. -/
theorem discreteGaussianPMF_nonneg (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    0 ≤ discreteGaussianPMF σ μ z :=
  div_nonneg (discreteGaussianWeight_nonneg σ μ z)
    (le_of_lt (discreteGaussianSum_pos σ μ hσ))

/-- The discrete Gaussian PMF sums to `1`. -/
theorem discreteGaussianPMF_sum_eq_one (σ μ : ℝ) (hσ : 0 < σ) :
    ∑' (z : ℤ), discreteGaussianPMF σ μ z = 1 := by
  unfold discreteGaussianPMF
  rw [tsum_div_const]
  exact div_self (ne_of_gt (discreteGaussianSum_pos σ μ hσ))

/-- The discrete Gaussian PMF is strictly positive at every integer point. -/
theorem discreteGaussianPMF_pos (σ μ : ℝ) (hσ : 0 < σ) (z : ℤ) :
    0 < discreteGaussianPMF σ μ z :=
  div_pos (discreteGaussianWeight_pos σ μ z) (discreteGaussianSum_pos σ μ hσ)

end LatticeCrypto
