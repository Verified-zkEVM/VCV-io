/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence
import VCVio.EvalDist.Monad.Map

/-!
# Rényi Divergence for SPMFs and Monadic Computations

This file extends the Rényi divergence from `PMF` (defined in
`ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`) to:

1. `SPMF.renyiDiv` — on sub-probability mass functions (via `toPMF`)
2. `renyiDiv` — on any monad with `HasEvalSPMF` (via `evalDist`)

This mirrors the structure of `VCVio.EvalDist.TVDist`, which performs the same lift for
total variation distance.

## Application

The monadic `renyiDiv` is used to state sampler quality bounds:

```
renyiDiv a (concreteSamplerZ μ σ') (idealSamplerZ μ σ') ≤ 1 + ε
```

where `concreteSamplerZ` uses FPR arithmetic and `idealSamplerZ` samples from the exact
discrete Gaussian. The probability preservation theorem then translates this into a
security loss factor in the Falcon EUF-CMA proof.
-/


noncomputable section

open ENNReal

universe u v

/-! ### SPMF.renyiDiv -/

namespace SPMF

variable {α : Type*}

/-- Rényi MGF on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def renyiMGF (a : ℝ) (p q : SPMF α) : ℝ≥0∞ :=
  p.toPMF.renyiMGF a q.toPMF

/-- Multiplicative Rényi divergence on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def renyiDiv (a : ℝ) (p q : SPMF α) : ℝ≥0∞ :=
  p.toPMF.renyiDiv a q.toPMF

/-- Max-divergence on SPMFs. -/
protected def maxDiv (p q : SPMF α) : ℝ≥0∞ := p.toPMF.maxDiv q.toPMF

@[simp]
theorem renyiDiv_self (a : ℝ) (p : SPMF α) : p.renyiDiv a p = 1 :=
  PMF.renyiDiv_self _ _

universe w in
theorem renyiDiv_map_le (a : ℝ) (ha : 1 < a) {α' : Type w} {β : Type w}
    (f : α' → β) (p q : SPMF α') :
    SPMF.renyiDiv a (f <$> p) (f <$> q) ≤ SPMF.renyiDiv a p q := by
  unfold SPMF.renyiDiv
  rw [SPMF.toPMF_map, SPMF.toPMF_map]
  exact PMF.renyiDiv_map_le a ha (Option.map f) p.toPMF q.toPMF

universe w in
theorem renyiDiv_bind_right_le (a : ℝ) (ha : 1 < a) {α' : Type w} {β : Type w}
    (f : α' → SPMF β) (p q : SPMF α') :
    SPMF.renyiDiv a (p >>= f) (q >>= f) ≤ SPMF.renyiDiv a p q := by
  unfold SPMF.renyiDiv
  rw [SPMF.toPMF_bind, SPMF.toPMF_bind]
  exact PMF.renyiDiv_bind_right_le a ha _ p.toPMF q.toPMF

end SPMF

/-! ### Monadic renyiDiv -/

section monadic

variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] {α : Type u}

/-- Rényi divergence between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def renyiDiv (a : ℝ) (mx my : m α) : ℝ≥0∞ :=
  SPMF.renyiDiv a (𝒟[mx]) (𝒟[my])

@[simp]
theorem renyiDiv_self (a : ℝ) (mx : m α) : renyiDiv a mx mx = 1 :=
  SPMF.renyiDiv_self _ _

theorem renyiDiv_map_le [LawfulMonad m] {β : Type u} (a : ℝ) (ha : 1 < a)
    (f : α → β) (mx my : m α) :
    renyiDiv a (f <$> mx) (f <$> my) ≤ renyiDiv a mx my := by
  simp only [renyiDiv, _root_.evalDist_map]
  exact SPMF.renyiDiv_map_le a ha f _ _

theorem renyiDiv_bind_right_le [LawfulMonad m] {β : Type u} (a : ℝ) (ha : 1 < a)
    (f : α → m β) (mx my : m α) :
    renyiDiv a (mx >>= f) (my >>= f) ≤ renyiDiv a mx my := by
  simp only [renyiDiv, _root_.evalDist_bind]
  exact SPMF.renyiDiv_bind_right_le a ha _ _ _

/-! ### Rényi to Probability Bounds -/

/-- If the Rényi divergence between two computations is at most `R`, then for any
output `x`, `Pr[= x | my] ≥ Pr[= x | mx]^{a/(a-1)} / R`. -/
theorem probOutput_le_of_renyiDiv (a : ℝ) (ha : 1 < a) (mx my : m α)
    (R : ℝ≥0∞) (hR : renyiDiv a mx my ≤ R) (x : α) :
    Pr[= x | mx] ^ (a / (a - 1) : ℝ) / R ≤ Pr[= x | my] := by
  simp only [probOutput, renyiDiv, SPMF.renyiDiv] at *
  rw [SPMF.apply_eq_toPMF_some, SPMF.apply_eq_toPMF_some]
  calc ((𝒟[mx]).toPMF (some x)) ^ (a / (a - 1) : ℝ) / R
      ≤ ((𝒟[mx]).toPMF (some x)) ^ (a / (a - 1) : ℝ) /
          ((𝒟[mx]).toPMF.renyiDiv a (𝒟[my]).toPMF) :=
        ENNReal.div_le_div_left hR _
    _ ≤ (𝒟[my]).toPMF (some x) :=
        PMF.renyiDiv_apply_bound a ha _ _ _

end monadic
