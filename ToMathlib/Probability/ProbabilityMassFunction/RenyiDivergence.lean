/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import ToMathlib.Analysis.MeanInequalities
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
  apply le_antisymm
  · exact iSup_le fun x => ENNReal.div_self_le_one
  · obtain ⟨x, hx⟩ := p.support_nonempty
    exact le_iSup_of_le x ((ENNReal.div_self hx (PMF.apply_ne_top p x)).ge)

theorem maxDiv_one_le (p q : PMF α) (hq : ∀ x, p x ≠ 0 → q x ≠ 0) :
    1 ≤ p.maxDiv q := by
  unfold PMF.maxDiv
  calc (1 : ℝ≥0∞) = ∑' x, p x := p.tsum_coe.symm
    _ = ∑' x, (p x / q x) * q x := by
        congr 1; ext x
        by_cases hpx : p x = 0
        · simp [hpx]
        · rw [ENNReal.div_mul_cancel (hq x hpx) (PMF.apply_ne_top q x)]
    _ ≤ ∑' x, (⨆ y, p y / q y) * q x :=
        ENNReal.tsum_le_tsum fun x => by
          gcongr; exact le_iSup (fun y => p y / q y) x
    _ = (⨆ y, p y / q y) * ∑' x, q x := ENNReal.tsum_mul_left
    _ = ⨆ y, p y / q y := by rw [q.tsum_coe, mul_one]

/-! ### Data Processing Inequality -/

section DataProcessing

universe u₀
variable {α' : Type u₀} {β : Type u₀}

/-- Data processing inequality for the Rényi MGF under deterministic maps:
`M_a(f∗p ‖ f∗q) ≤ M_a(p ‖ q)`.
Applying a deterministic function can only decrease the Rényi MGF. -/
theorem renyiMGF_map_le (a : ℝ) (ha : 1 ≤ a) (f : α' → β) (p q : PMF α') :
    (f <$> p).renyiMGF a (f <$> q) ≤ p.renyiMGF a q := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [PMF.renyiMGF, sub_self, ENNReal.rpow_zero, mul_one, ENNReal.rpow_one]
    rw [(f <$> p).tsum_coe, p.tsum_coe]
  · classical
    have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha'
    have ham1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha'
    have h1a : (1 : ℝ) - a < 0 := by linarith
    have hconj : a.HolderConjugate (a / (a - 1)) := Real.HolderConjugate.conjExponent ha'
    have hainv : a⁻¹ * a = (1 : ℝ) := inv_mul_cancel₀ ha0.ne'
    have hainv' : a * a⁻¹ = (1 : ℝ) := mul_inv_cancel₀ ha0.ne'
    have hsinv : (a - 1) / a * (a / (a - 1)) = (1 : ℝ) := by field_simp
    simp only [PMF.renyiMGF, PMF.monad_map_eq_map, PMF.map_apply]
    have sum_rearr : ∑' x, (p x) ^ a * (q x) ^ (1 - a) =
        ∑' y, ∑' x, if y = f x then (p x) ^ a * (q x) ^ (1 - a) else 0 := by
      trans ∑' x, ∑' y, if y = f x then (p x) ^ a * (q x) ^ (1 - a) else 0
      · exact tsum_congr fun x =>
          (tsum_ite_eq (f x) (fun _ => (p x) ^ a * (q x) ^ (1 - a))).symm
      · exact ENNReal.tsum_comm
    rw [sum_rearr]
    apply ENNReal.tsum_le_tsum
    intro y
    set P : α' → ℝ≥0∞ := fun x => if y = f x then p x else 0
    set Q : α' → ℝ≥0∞ := fun x => if y = f x then q x else 0
    change (∑' x, P x) ^ a * (∑' x, Q x) ^ (1 - a) ≤
      ∑' x, if y = f x then (p x) ^ a * (q x) ^ (1 - a) else 0
    have hif : ∀ x, P x ^ a * Q x ^ (1 - a) =
        if y = f x then (p x) ^ a * (q x) ^ (1 - a) else 0 := by
      intro x; simp only [P, Q]
      split_ifs with h
      · rfl
      · simp [ENNReal.zero_rpow_of_pos ha0]
    by_cases hac : ∀ x, P x ≠ 0 → Q x ≠ 0
    · by_cases hPsum : ∑' x, P x = 0
      · simp [hPsum, ENNReal.zero_rpow_of_pos ha0]
      · have hQne : ∑' x, Q x ≠ 0 := by
          intro hQsum0
          exact hPsum (ENNReal.tsum_eq_zero.mpr fun x => by
            by_cases hPx : P x = 0
            · exact hPx
            · exact absurd (ENNReal.tsum_eq_zero.mp hQsum0 x) (hac x hPx))
        have hQlt : ∑' x, Q x ≠ ⊤ :=
          ne_top_of_le_ne_top (by rw [q.tsum_coe]; exact one_ne_top)
            (ENNReal.tsum_le_tsum fun x => by
              simp only [Q]; split_ifs <;> [exact le_rfl; exact zero_le _])
        have hpw : ∀ x, ((P x) ^ a * (Q x) ^ (1 - a)) ^ (a⁻¹ : ℝ) *
            (Q x) ^ ((a - 1) / a : ℝ) = P x := by
          intro x
          by_cases hPx : P x = 0
          · simp [hPx, ENNReal.zero_rpow_of_pos ha0,
              ENNReal.zero_rpow_of_pos (inv_pos.mpr ha0)]
          · have hQx : Q x ≠ 0 := hac x hPx
            have hyfx : y = f x := by by_contra h; exact hPx (if_neg h)
            have hPt : P x ≠ ⊤ := by
              change (if y = f x then p x else 0) ≠ ⊤
              rw [if_pos hyfx]; exact PMF.apply_ne_top p _
            have hQt : Q x ≠ ⊤ := by
              change (if y = f x then q x else 0) ≠ ⊤
              rw [if_pos hyfx]; exact PMF.apply_ne_top q _
            rw [ENNReal.mul_rpow_of_ne_top
                  (ENNReal.rpow_ne_top_of_nonneg ha0.le hPt)
                  (ENNReal.rpow_ne_top_of_ne_zero hQx hQt),
                ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hainv', ENNReal.rpow_one, mul_assoc,
                ← ENNReal.rpow_add ((1 - a) * a⁻¹) ((a - 1) / a) hQx hQt,
                show (1 - a) * a⁻¹ + (a - 1) / a = (0 : ℝ) from by field_simp; ring,
                ENNReal.rpow_zero, mul_one]
        have hholder : ∑' x, P x ≤
            (∑' x, P x ^ a * Q x ^ (1 - a)) ^ (a⁻¹ : ℝ) *
            (∑' x, Q x) ^ ((a - 1) / a : ℝ) := by
          have hH := ENNReal.inner_le_Lp_mul_Lq_tsum hconj
            (fun x => ((P x) ^ a * (Q x) ^ (1 - a)) ^ (a⁻¹ : ℝ))
            (fun x => (Q x) ^ ((a - 1) / a : ℝ))
          rw [show ∑' x, ((P x) ^ a * (Q x) ^ (1 - a)) ^ (a⁻¹ : ℝ) *
                (Q x) ^ ((a - 1) / a : ℝ) = ∑' x, P x from tsum_congr hpw] at hH
          refine le_trans hH (mul_le_mul' ?_ (le_of_eq ?_))
          · rw [one_div]
            apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr ha0.le)
            exact ENNReal.tsum_le_tsum fun x => le_of_eq (by
              rw [← ENNReal.rpow_mul, hainv, ENNReal.rpow_one])
          · congr 1
            · exact tsum_congr fun x => by rw [← ENNReal.rpow_mul, hsinv, ENNReal.rpow_one]
            · rw [one_div, inv_div]
        have hpow : (∑' x, P x) ^ a ≤
            (∑' x, P x ^ a * Q x ^ (1 - a)) * (∑' x, Q x) ^ (a - 1 : ℝ) := by
          have := ENNReal.rpow_le_rpow hholder ha0.le
          rwa [ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            hainv, ENNReal.rpow_one,
            show (a - 1) / a * a = a - 1 from by field_simp] at this
        calc (∑' x, P x) ^ a * (∑' x, Q x) ^ (1 - a)
            ≤ (∑' x, P x ^ a * Q x ^ (1 - a)) * (∑' x, Q x) ^ (a - 1) *
              (∑' x, Q x) ^ (1 - a) := mul_le_mul_left hpow _
          _ = (∑' x, P x ^ a * Q x ^ (1 - a)) *
              ((∑' x, Q x) ^ (a - 1) * (∑' x, Q x) ^ (1 - a)) := mul_assoc _ _ _
          _ = (∑' x, P x ^ a * Q x ^ (1 - a)) *
              (∑' x, Q x) ^ ((a - 1) + (1 - a)) := by
              congr 1; exact (ENNReal.rpow_add _ _ hQne hQlt).symm
          _ = (∑' x, P x ^ a * Q x ^ (1 - a)) *
              (∑' x, Q x) ^ (0 : ℝ) := by congr 2; ring
          _ = ∑' x, P x ^ a * Q x ^ (1 - a) := by rw [ENNReal.rpow_zero, mul_one]
          _ = ∑' x, if y = f x then (p x) ^ a * (q x) ^ (1 - a) else 0 := tsum_congr hif
    · push Not at hac
      obtain ⟨x₀, hPx₀, hQx₀⟩ := hac
      have hyfx₀ : y = f x₀ := by by_contra h; exact hPx₀ (if_neg h)
      have hpx₀ : p x₀ ≠ 0 := by
        simp only [P, if_pos hyfx₀] at hPx₀; exact hPx₀
      have hqx₀ : q x₀ = 0 := by simp only [Q, if_pos hyfx₀] at hQx₀; exact hQx₀
      suffices h : (∑' x, if y = f x then (p x) ^ a * (q x) ^ (1 - a) else 0) = ⊤ from
        h ▸ le_top
      apply ENNReal.tsum_eq_top_of_eq_top ⟨x₀, ?_⟩
      rw [if_pos hyfx₀, hqx₀]
      have h0top : (0 : ℝ≥0∞) ^ (1 - a) = ⊤ :=
        ENNReal.rpow_eq_top_iff.mpr (Or.inl ⟨rfl, h1a⟩)
      rw [h0top]
      have hpa_pos : 0 < (p x₀) ^ a :=
        ENNReal.rpow_pos (pos_iff_ne_zero.mpr hpx₀) (PMF.apply_ne_top p x₀)
      exact mul_eq_top.mpr (Or.inl ⟨hpa_pos.ne', rfl⟩)

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
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [PMF.renyiMGF, sub_self, ENNReal.rpow_zero, mul_one, ENNReal.rpow_one]
    rw [(p.bind f).tsum_coe, p.tsum_coe]
  · classical
    have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha'
    have ham1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha'
    have h1a : (1 : ℝ) - a < 0 := by linarith
    have hconj : a.HolderConjugate (a / (a - 1)) := Real.HolderConjugate.conjExponent ha'
    have hainv : a⁻¹ * a = (1 : ℝ) := inv_mul_cancel₀ ha0.ne'
    have hainv' : a * a⁻¹ = (1 : ℝ) := mul_inv_cancel₀ ha0.ne'
    have hsinv : (a - 1) / a * (a / (a - 1)) = (1 : ℝ) := by field_simp
    simp only [PMF.renyiMGF, PMF.bind_apply]
    have hfactor : ∀ (x : α') (y : β),
        (p x * (f x) y) ^ a * (q x * (f x) y) ^ (1 - a) =
        p x ^ a * q x ^ (1 - a) * (f x) y := by
      intro x y
      by_cases hfxy : (f x) y = 0
      · simp only [hfxy, mul_zero, ENNReal.zero_rpow_of_pos ha0, zero_mul, mul_zero]
      · rw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top p x) (PMF.apply_ne_top (f x) y),
            ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top q x) (PMF.apply_ne_top (f x) y),
            mul_mul_mul_comm,
            ← ENNReal.rpow_add a (1 - a) hfxy (PMF.apply_ne_top (f x) y),
            show a + (1 - a) = (1 : ℝ) from by ring, ENNReal.rpow_one]
    suffices per_fiber : ∀ y, (∑' x, p x * (f x) y) ^ a *
        (∑' x, q x * (f x) y) ^ (1 - a) ≤
        ∑' x, (p x * (f x) y) ^ a * (q x * (f x) y) ^ (1 - a) from
      calc ∑' y, (∑' x, p x * (f x) y) ^ a * (∑' x, q x * (f x) y) ^ (1 - a)
          ≤ ∑' y, ∑' x, (p x * (f x) y) ^ a * (q x * (f x) y) ^ (1 - a) :=
              ENNReal.tsum_le_tsum per_fiber
        _ = ∑' y, ∑' x, p x ^ a * q x ^ (1 - a) * (f x) y := by
            congr 1; ext y; congr 1; ext x; exact hfactor x y
        _ = ∑' x, ∑' y, p x ^ a * q x ^ (1 - a) * (f x) y := ENNReal.tsum_comm
        _ = ∑' x, p x ^ a * q x ^ (1 - a) * ∑' y, (f x) y := by
            congr 1; ext x; rw [ENNReal.tsum_mul_left]
        _ = ∑' x, p x ^ a * q x ^ (1 - a) := by
            congr 1; ext x; rw [(f x).tsum_coe, mul_one]
    intro y
    set P : α' → ℝ≥0∞ := fun x => p x * (f x) y
    set Q : α' → ℝ≥0∞ := fun x => q x * (f x) y
    have hPt : ∀ x, P x ≠ ⊤ := fun x =>
      ENNReal.mul_ne_top (PMF.apply_ne_top p x) (PMF.apply_ne_top (f x) y)
    have hQt : ∀ x, Q x ≠ ⊤ := fun x =>
      ENNReal.mul_ne_top (PMF.apply_ne_top q x) (PMF.apply_ne_top (f x) y)
    by_cases hac : ∀ x, P x ≠ 0 → Q x ≠ 0
    · by_cases hPsum : ∑' x, P x = 0
      · simp [hPsum, ENNReal.zero_rpow_of_pos ha0]
      · have hQne : ∑' x, Q x ≠ 0 := by
          intro hQsum0
          exact hPsum (ENNReal.tsum_eq_zero.mpr fun x => by
            by_cases hPx : P x = 0
            · exact hPx
            · exact absurd (ENNReal.tsum_eq_zero.mp hQsum0 x) (hac x hPx))
        have hQlt : ∑' x, Q x ≠ ⊤ :=
          ne_top_of_le_ne_top (by rw [q.tsum_coe]; exact one_ne_top)
            (ENNReal.tsum_le_tsum fun x => by
              exact mul_le_of_le_one_right (zero_le _) (PMF.coe_le_one (f x) y))
        have hpw : ∀ x, ((P x) ^ a * (Q x) ^ (1 - a)) ^ (a⁻¹ : ℝ) *
            (Q x) ^ ((a - 1) / a : ℝ) = P x := by
          intro x
          by_cases hPx : P x = 0
          · simp [hPx, ENNReal.zero_rpow_of_pos ha0,
              ENNReal.zero_rpow_of_pos (inv_pos.mpr ha0)]
          · have hQx : Q x ≠ 0 := hac x hPx
            rw [ENNReal.mul_rpow_of_ne_top
                  (ENNReal.rpow_ne_top_of_nonneg ha0.le (hPt x))
                  (ENNReal.rpow_ne_top_of_ne_zero hQx (hQt x)),
                ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hainv', ENNReal.rpow_one,
                mul_assoc,
                ← ENNReal.rpow_add ((1 - a) * a⁻¹) ((a - 1) / a) hQx (hQt x),
                show (1 - a) * a⁻¹ + (a - 1) / a = (0 : ℝ) from by field_simp; ring,
                ENNReal.rpow_zero, mul_one]
        have hholder : ∑' x, P x ≤
            (∑' x, P x ^ a * Q x ^ (1 - a)) ^ (a⁻¹ : ℝ) *
            (∑' x, Q x) ^ ((a - 1) / a : ℝ) := by
          have hH := ENNReal.inner_le_Lp_mul_Lq_tsum hconj
            (fun x => ((P x) ^ a * (Q x) ^ (1 - a)) ^ (a⁻¹ : ℝ))
            (fun x => (Q x) ^ ((a - 1) / a : ℝ))
          rw [show ∑' x, ((P x) ^ a * (Q x) ^ (1 - a)) ^ (a⁻¹ : ℝ) *
                (Q x) ^ ((a - 1) / a : ℝ) = ∑' x, P x from tsum_congr hpw] at hH
          refine le_trans hH (mul_le_mul' ?_ (le_of_eq ?_))
          · rw [one_div]
            apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr ha0.le)
            exact ENNReal.tsum_le_tsum fun x => le_of_eq (by
              rw [← ENNReal.rpow_mul, hainv, ENNReal.rpow_one])
          · congr 1
            · exact tsum_congr fun x => by
                rw [← ENNReal.rpow_mul, hsinv, ENNReal.rpow_one]
            · rw [one_div, inv_div]
        have hpow : (∑' x, P x) ^ a ≤
            (∑' x, P x ^ a * Q x ^ (1 - a)) * (∑' x, Q x) ^ (a - 1 : ℝ) := by
          have := ENNReal.rpow_le_rpow hholder ha0.le
          rwa [ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, hainv, ENNReal.rpow_one,
            show (a - 1) / a * a = a - 1 from by field_simp] at this
        calc (∑' x, P x) ^ a * (∑' x, Q x) ^ (1 - a)
            ≤ (∑' x, P x ^ a * Q x ^ (1 - a)) * (∑' x, Q x) ^ (a - 1) *
              (∑' x, Q x) ^ (1 - a) := mul_le_mul_left hpow _
          _ = (∑' x, P x ^ a * Q x ^ (1 - a)) *
              ((∑' x, Q x) ^ (a - 1) * (∑' x, Q x) ^ (1 - a)) := mul_assoc _ _ _
          _ = (∑' x, P x ^ a * Q x ^ (1 - a)) *
              (∑' x, Q x) ^ ((a - 1) + (1 - a)) := by
              congr 1; exact (ENNReal.rpow_add _ _ hQne hQlt).symm
          _ = (∑' x, P x ^ a * Q x ^ (1 - a)) *
              (∑' x, Q x) ^ (0 : ℝ) := by congr 2; ring
          _ = ∑' x, P x ^ a * Q x ^ (1 - a) := by rw [ENNReal.rpow_zero, mul_one]
    · push Not at hac
      obtain ⟨x₀, hPx₀, hQx₀⟩ := hac
      suffices h : ∑' x, P x ^ a * Q x ^ (1 - a) = ⊤ from h ▸ le_top
      apply ENNReal.tsum_eq_top_of_eq_top ⟨x₀, ?_⟩
      rw [show Q x₀ = 0 from hQx₀]
      rw [ENNReal.rpow_eq_top_iff.mpr (Or.inl ⟨rfl, h1a⟩), mul_top]
      exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hPx₀) (hPt x₀)).ne'

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
  classical
  have hprod : ∀ (p : PMF α') (q : PMF β) (xy : α' × β),
      (p.bind fun a => Prod.mk a <$> q) xy = p xy.1 * q xy.2 := by
    intro p q ⟨x, y⟩
    simp only [PMF.bind_apply]
    change ∑' a', p a' * ((q.bind (pure ∘ Prod.mk a')) (x, y)) = p x * q y
    simp only [PMF.bind_apply, Function.comp_def, PMF.pure_apply, Prod.mk.injEq]
    have inner : ∀ a', (∑' b, q b * if x = a' ∧ y = b then 1 else 0) =
        if x = a' then q y else 0 := by
      intro a'
      by_cases hax : x = a'
      · subst hax; simp only [true_and, ite_true]
        conv_lhs => arg 1; ext b; rw [show (y = b) = (b = y) from propext eq_comm]
        simp [tsum_ite_eq]
      · simp only [hax, false_and, ite_false, mul_zero]; exact tsum_zero
    simp_rw [inner, mul_ite, mul_zero]
    conv_lhs => arg 1; ext a'; rw [show (x = a') = (a' = x) from propext eq_comm]
    simp [tsum_ite_eq]
  simp only [PMF.renyiMGF, hprod]
  simp_rw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp_rw [mul_mul_mul_comm]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

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

/-- Pointwise probability preservation: for a single element `x`,
`p(x)^{a/(a-1)} / R_a(p ‖ q) ≤ q(x)`.

Proof: from `p(x)^a * q(x)^{1-a} ≤ M_a(p ‖ q)` (one term of the sum)
we get `p(x)^a ≤ M_a * q(x)^{a-1}`, then take `1/(a-1)` powers. -/
theorem renyiDiv_apply_bound (a : ℝ) (ha : 1 < a) (p q : PMF α) (x : α) :
    (p x) ^ (a / (a - 1) : ℝ) / p.renyiDiv a q ≤ q x := by
  rw [renyiDiv_eq_rpow ha]
  by_cases hpx : p x = 0
  · simp [hpx, ENNReal.zero_rpow_of_pos (div_pos (lt_trans zero_lt_one ha) (sub_pos.mpr ha))]
  · by_cases hqx : q x = 0
    · have h1a : 1 - a < 0 := by linarith
      have hqpow : (q x) ^ (1 - a) = ⊤ := by
        rw [ENNReal.rpow_eq_top_iff]; left; exact ⟨hqx, h1a⟩
      have hterm : (p x) ^ a * (q x) ^ (1 - a) = ⊤ := by
        rw [hqpow, mul_top]
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hpx) (PMF.apply_ne_top p x)).ne'
      have hMGF : p.renyiMGF a q = ⊤ := by
        rw [PMF.renyiMGF]
        exact ENNReal.tsum_eq_top_of_eq_top ⟨x, hterm⟩
      have hR : (p.renyiMGF a q) ^ ((a - 1)⁻¹ : ℝ) = ⊤ := by
        rw [hMGF]; exact ENNReal.top_rpow_of_pos (inv_pos.mpr (sub_pos.mpr ha))
      simp [hqx, hR]
    · have ham1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha
      have hqt := PMF.apply_ne_top q x
      have hle_mgf : (p x) ^ a * (q x) ^ (1 - a) ≤ p.renyiMGF a q :=
        ENNReal.le_tsum x
      have hle_rpow : ((p x) ^ a * (q x) ^ (1 - a)) ^ ((a - 1)⁻¹ : ℝ) ≤
          (p.renyiMGF a q) ^ ((a - 1)⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow hle_mgf (inv_nonneg.mpr ham1.le)
      have hlhs : ((p x) ^ a * (q x) ^ (1 - a)) ^ ((a - 1)⁻¹ : ℝ) =
          (p x) ^ (a / (a - 1)) * (q x) ^ ((1 - a) / (a - 1)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr ham1.le),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        simp only [div_eq_mul_inv]
      have hexp : (1 - a) / (a - 1) = (-1 : ℝ) := by field_simp; ring
      rw [hlhs, hexp] at hle_rpow
      rw [ENNReal.rpow_neg_one, mul_comm, ENNReal.inv_mul_le_iff hqx hqt] at hle_rpow
      exact ENNReal.div_le_of_le_mul hle_rpow

/-- Probability preservation bound: for any event `E`,
`q(E) ≥ p(E)^{a/(a-1)} / R_a(p ‖ q)`.

This is the key lemma used in security reductions involving Rényi divergence:
if `R_a(p ‖ q)` is small, then events that are likely under `p` remain likely under `q`. -/
theorem renyiDiv_prob_bound (a : ℝ) (ha : 1 < a) (p q : PMF α) (E : α → Prop)
    [DecidablePred E] :
    (∑' x, if E x then p x else 0) ^ (a / (a - 1) : ℝ) / p.renyiDiv a q ≤
      ∑' x, if E x then q x else 0 := by
  have ham1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have has : (0 : ℝ) < a / (a - 1) := div_pos ha0 ham1
  by_cases hR : p.renyiDiv a q = ⊤
  · rw [hR, ENNReal.div_top]; exact zero_le _
  · rw [renyiDiv_eq_rpow ha] at hR ⊢
    have hM : p.renyiMGF a q ≠ ⊤ := by
      intro hM; exact hR (by rw [hM]; exact ENNReal.top_rpow_of_pos (inv_pos.mpr ham1))
    have hac : ∀ x, p x ≠ 0 → q x ≠ 0 := by
      intro x hpx hqx
      exact hM (ENNReal.tsum_eq_top_of_eq_top ⟨x, by
        rw [ENNReal.rpow_eq_top_iff.mpr (Or.inl ⟨hqx, by linarith⟩), mul_top]
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hpx) (PMF.apply_ne_top p x)).ne'⟩)
    apply ENNReal.div_le_of_le_mul
    set pE := ∑' x, if E x then p x else 0
    set qE := ∑' x, if E x then q x else 0
    set M := p.renyiMGF a q
    have hconj : a.HolderConjugate (a / (a - 1)) := Real.HolderConjugate.conjExponent ha
    have hainv : a⁻¹ * a = (1 : ℝ) := inv_mul_cancel₀ ha0.ne'
    have hainv' : a * a⁻¹ = (1 : ℝ) := mul_inv_cancel₀ ha0.ne'
    have hsinv : (a - 1) / a * (a / (a - 1)) = (1 : ℝ) := by field_simp
    have hexp : a⁻¹ * (a / (a - 1)) = (a - 1)⁻¹ := by field_simp
    -- Pointwise identity: ((p x)^a * (q x)^{1-a})^{1/a} * (q x)^{(a-1)/a} = p x
    have hpw : ∀ x, ((p x) ^ a * (q x) ^ (1 - a)) ^ (a⁻¹ : ℝ) *
        (q x) ^ ((a - 1) / a : ℝ) = p x := by
      intro x
      by_cases hpx : p x = 0
      · simp only [hpx, ENNReal.zero_rpow_of_pos ha0, zero_mul,
          ENNReal.zero_rpow_of_pos (inv_pos.mpr ha0)]
      · have hqx : q x ≠ 0 := hac x hpx
        have hqt := PMF.apply_ne_top q x
        rw [ENNReal.mul_rpow_of_ne_top
              (ENNReal.rpow_ne_top_of_nonneg ha0.le (PMF.apply_ne_top p x))
              (ENNReal.rpow_ne_top_of_ne_zero hqx hqt),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hainv', ENNReal.rpow_one, mul_assoc,
            ← ENNReal.rpow_add ((1 - a) * a⁻¹) ((a - 1) / a) hqx hqt,
            show (1 - a) * a⁻¹ + (a - 1) / a = (0 : ℝ) from by field_simp; ring,
            ENNReal.rpow_zero, mul_one]
    -- Hölder step: pE ≤ M^{1/a} * qE^{(a-1)/a}
    have hholder : pE ≤ M ^ (a⁻¹ : ℝ) * qE ^ ((a - 1) / a : ℝ) := by
      set F : α → ℝ≥0∞ := fun x =>
        if E x then ((p x) ^ a * (q x) ^ (1 - a)) ^ (a⁻¹ : ℝ) else 0
      set G : α → ℝ≥0∞ := fun x =>
        if E x then (q x) ^ ((a - 1) / a : ℝ) else 0
      have hH := ENNReal.inner_le_Lp_mul_Lq_tsum hconj F G
      have hFG : pE = ∑' x, F x * G x :=
        tsum_congr fun x => by
          simp only [F, G]
          split_ifs with hE
          · exact (hpw x).symm
          · simp
      have hFa : (∑' x, F x ^ a) ^ (1 / a : ℝ) ≤ M ^ (a⁻¹ : ℝ) := by
        rw [one_div]; gcongr
        apply ENNReal.tsum_le_tsum; intro x; simp only [F]
        split_ifs with hE
        · rw [← ENNReal.rpow_mul, hainv, ENNReal.rpow_one]
        · rw [ENNReal.zero_rpow_of_pos ha0]; exact zero_le _
      have hGq : (∑' x, G x ^ (a / (a - 1) : ℝ)) ^ (1 / (a / (a - 1)) : ℝ) =
          qE ^ ((a - 1) / a : ℝ) := by
        congr 1
        · exact tsum_congr fun x => by
            simp only [G]
            split_ifs with hE
            · rw [← ENNReal.rpow_mul, hsinv, ENNReal.rpow_one]
            · exact ENNReal.zero_rpow_of_pos has
        · rw [one_div, inv_div]
      rw [hFG]
      exact le_trans hH (mul_le_mul' hFa (le_of_eq hGq))
    -- Raise to a/(a-1) power and simplify
    calc pE ^ (a / (a - 1) : ℝ)
        ≤ (M ^ (a⁻¹ : ℝ) * qE ^ ((a - 1) / a : ℝ)) ^ (a / (a - 1) : ℝ) :=
          ENNReal.rpow_le_rpow hholder has.le
      _ = M ^ ((a - 1)⁻¹ : ℝ) * qE := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ has.le,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hexp, hsinv, ENNReal.rpow_one]
      _ = qE * M ^ ((a - 1)⁻¹ : ℝ) := mul_comm _ _

/-! ### From Relative Error to Rényi Divergence -/

/-- If the pointwise relative error between two PMFs is bounded by `δ`,
then the Rényi MGF is bounded. Specifically, if for all `x`,
`p(x) ≤ (1 + δ) · q(x)`, then `M_a(p ‖ q) ≤ (1 + δ)^(a-1)`.

This is used to convert floating-point error bounds into Rényi divergence bounds. -/
theorem renyiMGF_le_of_pointwise_le (a : ℝ) (ha : 1 < a) (p q : PMF α)
    (δ : ℝ≥0∞) (hδ : ∀ x, p x ≤ (1 + δ) * q x) :
    p.renyiMGF a q ≤ (1 + δ) ^ (a - 1) := by
  unfold PMF.renyiMGF
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have ham1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha
  suffices h : ∀ x, (p x) ^ a * (q x) ^ (1 - a) ≤ (1 + δ) ^ (a - 1) * p x by
    calc ∑' x, (p x) ^ a * (q x) ^ (1 - a)
        ≤ ∑' x, (1 + δ) ^ (a - 1) * p x := ENNReal.tsum_le_tsum h
      _ = (1 + δ) ^ (a - 1) * ∑' x, p x := ENNReal.tsum_mul_left
      _ = (1 + δ) ^ (a - 1) := by rw [p.tsum_coe, mul_one]
  intro x
  by_cases hpx : p x = 0
  · simp [hpx, ENNReal.zero_rpow_of_pos ha0]
  · have hqx : q x ≠ 0 := by
      intro h; exact hpx (le_antisymm (by simpa [h] using hδ x) (zero_le _))
    have hqt := PMF.apply_ne_top q x
    set r := p x / q x with hr_def
    have hrq : r * q x = p x := ENNReal.div_mul_cancel hqx hqt
    have hr_le : r ≤ 1 + δ := ENNReal.div_le_of_le_mul (hδ x)
    calc (p x) ^ a * (q x) ^ (1 - a)
        = (r * q x) ^ a * (q x) ^ (1 - a) := by rw [hrq]
      _ = r ^ a * (q x) ^ a * (q x) ^ (1 - a) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ha0.le]
      _ = r ^ a * ((q x) ^ a * (q x) ^ (1 - a)) := by rw [mul_assoc]
      _ = r ^ a * q x := by
          rw [← ENNReal.rpow_add _ _ hqx hqt]
          simp [show a + (1 - a) = (1 : ℝ) from by ring]
      _ = r ^ (1 + (a - 1)) * q x := by congr 1; congr 1; ring
      _ = (r ^ (1 : ℝ) * r ^ (a - 1)) * q x := by
          rw [ENNReal.rpow_add_of_nonneg _ _ one_pos.le ham1.le]
      _ = r * r ^ (a - 1) * q x := by rw [ENNReal.rpow_one]
      _ ≤ r * (1 + δ) ^ (a - 1) * q x := by gcongr
      _ = (1 + δ) ^ (a - 1) * (r * q x) := by ring
      _ = (1 + δ) ^ (a - 1) * p x := by rw [hrq]

/-- Rényi divergence bound from pointwise relative error. -/
theorem renyiDiv_le_of_pointwise_le (a : ℝ) (ha : 1 < a) (p q : PMF α)
    (δ : ℝ≥0∞) (hδ : ∀ x, p x ≤ (1 + δ) * q x) :
    p.renyiDiv a q ≤ 1 + δ := by
  rw [renyiDiv_eq_rpow ha]
  have ham1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha
  calc (p.renyiMGF a q) ^ ((a - 1)⁻¹ : ℝ)
      ≤ ((1 + δ) ^ (a - 1)) ^ ((a - 1)⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow (renyiMGF_le_of_pointwise_le a ha p q δ hδ)
          (inv_nonneg.mpr ham1.le)
    _ = (1 + δ) ^ ((a - 1) * (a - 1)⁻¹) := by rw [ENNReal.rpow_mul]
    _ = (1 + δ) ^ (1 : ℝ) := by congr 1; exact mul_inv_cancel₀ ham1.ne'
    _ = 1 + δ := ENNReal.rpow_one _

/-! ### Rényi to TV Distance -/

-- The correct Rényi-to-TV bound (van Erven–Harremoës 2014, Theorem 4) is:
--   `TV(P, Q) ≤ sqrt(1 - R_a(P ‖ Q)⁻¹)`
-- The previously stated linear bound `TV ≤ 1 - R_a⁻¹` is false for finite-order
-- Rényi divergence (counterexample: a = 2, P = (0.5,0.5), Q = (0.6,0.4)).
-- Formalizing the correct bound requires `ENNReal.sqrt` infrastructure not yet available.

end PMF
