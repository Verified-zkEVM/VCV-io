/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.ProbabilityTheory.TotalVariation
import VCVio.EvalDist.Defs.Basic

/-!
# Total Variation Distance for SPMFs and Monadic Computations

This file extends the TV distance from `PMF` (defined in
`ToMathlib.ProbabilityTheory.TotalVariation`) to:

1. `SPMF.tvDist` — on sub-probability mass functions (via `toPMF`)
2. `tvDist` — on any monad with `HasEvalSPMF` (via `evalDist`)
-/

noncomputable section

universe u v

/-! ### SPMF.tvDist -/

namespace SPMF

variable {α : Type*}

/-- Total variation distance on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def tvDist (p q : SPMF α) : ℝ := p.toPMF.tvDist q.toPMF

@[simp] lemma tvDist_self (p : SPMF α) : p.tvDist p = 0 := PMF.tvDist_self _
lemma tvDist_comm (p q : SPMF α) : p.tvDist q = q.tvDist p := PMF.tvDist_comm _ _
lemma tvDist_nonneg (p q : SPMF α) : 0 ≤ p.tvDist q := PMF.tvDist_nonneg _ _

lemma tvDist_triangle (p q r : SPMF α) :
    p.tvDist r ≤ p.tvDist q + q.tvDist r := PMF.tvDist_triangle _ _ _

lemma tvDist_le_one (p q : SPMF α) : p.tvDist q ≤ 1 := PMF.tvDist_le_one _ _

@[simp] lemma tvDist_eq_zero_iff {p q : SPMF α} : p.tvDist q = 0 ↔ p.toPMF = q.toPMF :=
  PMF.tvDist_eq_zero_iff

end SPMF

/-! ### Monadic tvDist -/

section monadic

variable {m : Type u → Type v} [Monad m] [HasEvalSPMF m] {α : Type u}

/-- Total variation distance between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def tvDist (mx my : m α) : ℝ :=
  SPMF.tvDist (evalDist mx) (evalDist my)

@[simp] lemma tvDist_self (mx : m α) : tvDist mx mx = 0 := SPMF.tvDist_self _

lemma tvDist_comm (mx my : m α) : tvDist mx my = tvDist my mx :=
  SPMF.tvDist_comm _ _

lemma tvDist_nonneg (mx my : m α) : 0 ≤ tvDist mx my := SPMF.tvDist_nonneg _ _

lemma tvDist_triangle (mx my mz : m α) :
    tvDist mx mz ≤ tvDist mx my + tvDist my mz :=
  SPMF.tvDist_triangle _ _ _

lemma tvDist_le_one (mx my : m α) : tvDist mx my ≤ 1 := SPMF.tvDist_le_one _ _

end monadic

end
