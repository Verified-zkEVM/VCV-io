/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import ToMathlib.Probability.ProbabilityMassFunction.TotalVariation

/-!
# Rényi Divergence for PMFs

This file defines Rényi divergence on probability mass functions, following the
multiplicative convention `R_α(p ‖ q) = (∑ x, p(x)^α · q(x)^(1-α))^(1/(α-1))` used
in the lattice cryptography literature (Falcon, GPV, etc.).

We also define the max-divergence (Rényi divergence of order `∞`) as `⨆ x, p(x) / q(x)`.

## Main Definitions

- `PMF.renyiMGF a p q : ℝ≥0∞` — the Rényi moment generating function (the base quantity
  before exponentiation): `∑ x, p(x)^a * q(x)^(1-a)`
- `PMF.renyiDiv a p q : ℝ≥0∞` — the multiplicative Rényi divergence of order `a > 1`:
  `(renyiMGF a p q)^(1/(a-1))`
- `PMF.maxDiv p q : ℝ≥0∞` — the max-divergence (order `∞`): `⨆ x, p(x) / q(x)`

## Main Results

- `renyiMGF_self` — `M_a(p ‖ p) = 1`
- `renyiDiv_self` — `R_a(p ‖ p) = 1`
- `renyiMGF_map_le` — data processing inequality for deterministic maps
- `renyiDiv_map_le` — data processing inequality for Rényi divergence
- `renyiDiv_prob_bound` — probability preservation bound

## Design Notes

We use `ℝ≥0∞` throughout rather than `ℝ` to avoid partiality issues (Rényi divergence can
be infinite when `q` has zeros that `p` doesn't). The multiplicative form (not the log form)
is used because:

1. The Falcon literature uses `R_α` (multiplicative), not `D_α` (log form).
2. Multiplicative form composes better: `R_α(p₁⊗p₂ ‖ q₁⊗q₂) = R_α(p₁‖q₁) · R_α(p₂‖q₂)`.
3. The probability preservation bound is cleaner: `q(E) ≥ p(E)^{α/(α-1)} / R_α(p‖q)`.

## References

- Rényi, A. "On measures of entropy and information." 1961.
- van Erven, T., Harremoës, P. "Rényi divergence and Kullback-Leibler divergence." 2014.
- Bai, S., et al. "An Improved Compression Technique for Signatures Based on Learning
  with Errors." 2014. (multiplicative convention for lattice crypto)
- Fouque, P.-A., et al. "A closer look at Falcon." ePrint 2024/1769.
-/


noncomputable section

open ENNReal

namespace PMF

variable {α : Type*}

/-! ### Rényi Moment Generating Function -/

/-- The Rényi moment generating function of order `a ∈ ℝ` between two PMFs:
`M_a(p ‖ q) = ∑ x, p(x)^a * q(x)^(1-a)`.
This is the base quantity whose `1/(a-1)` power gives the multiplicative Rényi divergence. -/
protected def renyiMGF (a : ℝ) (p q : PMF α) : ℝ≥0∞ :=
  ∑' x, (p x) ^ a * (q x) ^ (1 - a)

@[simp]
theorem renyiMGF_self (a : ℝ) (p : PMF α) : p.renyiMGF a p = 1 := by
  simp only [PMF.renyiMGF]
  have h : ∀ x, (p x) ^ a * (p x) ^ (1 - a) = p x := fun x => by
    by_cases hx : p x = 0
    · by_cases ha : 0 < a
      · simp [hx, ENNReal.zero_rpow_of_pos ha]
      · push Not at ha
        have h1a : 0 < 1 - a := by linarith
        simp [hx, ENNReal.zero_rpow_of_pos h1a]
    · rw [← ENNReal.rpow_add a (1 - a) hx (PMF.apply_ne_top p x),
        show a + (1 - a) = 1 from by ring, ENNReal.rpow_one]
  simp [h, p.tsum_coe]

/-! ### Multiplicative Rényi Divergence -/

/-- The multiplicative Rényi divergence of order `a > 1` between two PMFs:
`R_a(p ‖ q) = M_a(p ‖ q)^(1/(a-1))`.

When `a ≤ 1`, this returns `1` (the trivial bound). -/
protected def renyiDiv (a : ℝ) (p q : PMF α) : ℝ≥0∞ :=
  if a ≤ 1 then 1 else (p.renyiMGF a q) ^ ((a - 1)⁻¹ : ℝ)

@[simp]
theorem renyiDiv_self (a : ℝ) (p : PMF α) : p.renyiDiv a p = 1 := by
  unfold PMF.renyiDiv
  split
  · rfl
  · simp

theorem renyiDiv_eq_rpow {a : ℝ} (ha : 1 < a) (p q : PMF α) :
    p.renyiDiv a q = (p.renyiMGF a q) ^ ((a - 1)⁻¹ : ℝ) := by
  simp [PMF.renyiDiv, not_le.mpr ha]

/-! ### Max-Divergence (Rényi order ∞) -/

/-- The max-divergence (Rényi divergence of order `∞`): `⨆ x, p(x) / q(x)`.
This bounds the pointwise likelihood ratio. -/
protected def maxDiv (p q : PMF α) : ℝ≥0∞ := ⨆ x, p x / q x

@[simp]
theorem maxDiv_self (p : PMF α) : p.maxDiv p = 1 := by
  sorry

theorem maxDiv_one_le (p q : PMF α) (hq : ∀ x, p x ≠ 0 → q x ≠ 0) :
    1 ≤ p.maxDiv q := by
  sorry

/-! ### Data Processing Inequality -/

section DataProcessing

universe u₀
variable {α' : Type u₀} {β : Type u₀}

/-- Data processing inequality for the Rényi MGF under deterministic maps:
`M_a(f∗p ‖ f∗q) ≤ M_a(p ‖ q)`.
Applying a deterministic function can only decrease the Rényi MGF. -/
theorem renyiMGF_map_le (a : ℝ) (ha : 1 ≤ a) (f : α' → β) (p q : PMF α') :
    (f <$> p).renyiMGF a (f <$> q) ≤ p.renyiMGF a q := by
  sorry

/-- Data processing inequality for the multiplicative Rényi divergence:
`R_a(f∗p ‖ f∗q) ≤ R_a(p ‖ q)`. -/
theorem renyiDiv_map_le (a : ℝ) (ha : 1 < a) (f : α' → β) (p q : PMF α') :
    (f <$> p).renyiDiv a (f <$> q) ≤ p.renyiDiv a q := by
  simp only [renyiDiv_eq_rpow ha]
  exact ENNReal.rpow_le_rpow (renyiMGF_map_le a ha.le f p q)
    (inv_nonneg.mpr (sub_nonneg.mpr ha.le))

/-- Data processing inequality for the Rényi MGF under Markov kernels (post-processing). -/
theorem renyiMGF_bind_right_le (a : ℝ) (ha : 1 ≤ a) (f : α' → PMF β) (p q : PMF α') :
    (p.bind f).renyiMGF a (q.bind f) ≤ p.renyiMGF a q := by
  sorry

/-- Data processing inequality for the Rényi divergence under Markov kernels. -/
theorem renyiDiv_bind_right_le (a : ℝ) (ha : 1 < a) (f : α' → PMF β) (p q : PMF α') :
    (p.bind f).renyiDiv a (q.bind f) ≤ p.renyiDiv a q := by
  simp only [renyiDiv_eq_rpow ha]
  exact ENNReal.rpow_le_rpow (renyiMGF_bind_right_le a ha.le f p q)
    (inv_nonneg.mpr (sub_nonneg.mpr ha.le))

end DataProcessing

/-! ### Multiplicativity (Product Distributions) -/

universe u₁ in
/-- Multiplicativity of the Rényi MGF for independent product distributions:
`M_a(p₁⊗p₂ ‖ q₁⊗q₂) = M_a(p₁ ‖ q₁) · M_a(p₂ ‖ q₂)`. -/
theorem renyiMGF_prod {α' : Type u₁} {β : Type u₁}
    (a : ℝ) (p₁ q₁ : PMF α') (p₂ q₂ : PMF β) :
    (p₁.bind fun x => Prod.mk x <$> p₂).renyiMGF a
        (q₁.bind fun x => Prod.mk x <$> q₂) =
      p₁.renyiMGF a q₁ * p₂.renyiMGF a q₂ := by
  sorry

universe u₁ in
/-- Multiplicativity of the Rényi divergence for independent product distributions:
`R_a(p₁⊗p₂ ‖ q₁⊗q₂) = R_a(p₁ ‖ q₁) · R_a(p₂ ‖ q₂)`. -/
theorem renyiDiv_prod {α' : Type u₁} {β : Type u₁}
    (a : ℝ) (ha : 1 < a) (p₁ q₁ : PMF α') (p₂ q₂ : PMF β) :
    (p₁.bind fun x => Prod.mk x <$> p₂).renyiDiv a
        (q₁.bind fun x => Prod.mk x <$> q₂) =
      p₁.renyiDiv a q₁ * p₂.renyiDiv a q₂ := by
  simp only [renyiDiv_eq_rpow ha, renyiMGF_prod,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr (sub_nonneg.mpr ha.le))]

/-! ### Probability Preservation -/

/-- Probability preservation bound: for any event `E`,
`q(E) ≥ p(E)^{a/(a-1)} / R_a(p ‖ q)`.

This is the key lemma used in security reductions involving Rényi divergence:
if `R_a(p ‖ q)` is small, then events that are likely under `p` remain likely under `q`. -/
theorem renyiDiv_prob_bound (a : ℝ) (ha : 1 < a) (p q : PMF α) (E : α → Prop)
    [DecidablePred E] :
    (∑' x, if E x then p x else 0) ^ (a / (a - 1) : ℝ) / p.renyiDiv a q ≤
      ∑' x, if E x then q x else 0 := by
  sorry

/-! ### From Relative Error to Rényi Divergence -/

/-- If the pointwise relative error between two PMFs is bounded by `δ`,
then the Rényi MGF is bounded. Specifically, if for all `x`,
`p(x) ≤ (1 + δ) · q(x)`, then `M_a(p ‖ q) ≤ (1 + δ)^(a-1)`.

This is used to convert floating-point error bounds into Rényi divergence bounds. -/
theorem renyiMGF_le_of_pointwise_le (a : ℝ) (ha : 1 < a) (p q : PMF α)
    (δ : ℝ≥0∞) (hδ : ∀ x, p x ≤ (1 + δ) * q x) :
    p.renyiMGF a q ≤ (1 + δ) ^ (a - 1) := by
  sorry

/-- Rényi divergence bound from pointwise relative error. -/
theorem renyiDiv_le_of_pointwise_le (a : ℝ) (ha : 1 < a) (p q : PMF α)
    (δ : ℝ≥0∞) (hδ : ∀ x, p x ≤ (1 + δ) * q x) :
    p.renyiDiv a q ≤ 1 + δ := by
  sorry

/-! ### Rényi to TV Distance -/

/-- Rényi divergence bounds TV distance: `‖p - q‖_TV ≤ ...`.
For `a > 1`, TV distance can be bounded in terms of Rényi divergence. -/
theorem etvDist_le_of_renyiDiv (a : ℝ) (ha : 1 < a) (p q : PMF α) :
    p.etvDist q ≤ (1 - (p.renyiDiv a q)⁻¹) := by
  sorry

end PMF
