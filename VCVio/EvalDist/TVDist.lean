/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.Probability.ProbabilityMassFunction.TotalVariation
import VCVio.EvalDist.Defs.Basic
import VCVio.EvalDist.Defs.NeverFails

/-!
# Total Variation Distance for SPMFs and Monadic Computations

This file extends the TV distance from `PMF` (defined in
`ToMathlib.ProbabilityTheory.TotalVariation`) to:

1. `SPMF.tvDist` — on sub-probability mass functions (via `toPMF`)
2. `tvDist` — on any monad with `HasEvalSPMF` (via `evalDist`)
-/

noncomputable section

open ENNReal

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

universe w in
lemma tvDist_map_le {α' : Type w} {β : Type w} (f : α' → β)
    (p q : SPMF α') : SPMF.tvDist (f <$> p) (f <$> q) ≤ SPMF.tvDist p q := by
  unfold SPMF.tvDist
  rw [SPMF.toPMF_map, SPMF.toPMF_map]
  exact PMF.tvDist_map_le (Option.map f) p.toPMF q.toPMF

universe w in
lemma tvDist_bind_right_le {α' : Type w} {β : Type w} (f : α' → SPMF β)
    (p q : SPMF α') : SPMF.tvDist (p >>= f) (q >>= f) ≤ SPMF.tvDist p q := by
  unfold SPMF.tvDist
  rw [SPMF.toPMF_bind, SPMF.toPMF_bind]
  exact PMF.tvDist_bind_right_le _ p.toPMF q.toPMF

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

lemma tvDist_map_le [LawfulMonad m] {β : Type u} (f : α → β) (mx my : m α) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my := by
  simp only [tvDist, evalDist_def, MonadHom.mmap_map]
  exact SPMF.tvDist_map_le f _ _

lemma tvDist_bind_right_le [LawfulMonad m] {β : Type u} (f : α → m β) (mx my : m α) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my := by
  simp only [tvDist, evalDist_def, MonadHom.mmap_bind]
  exact SPMF.tvDist_bind_right_le _ _ _

/-! ### TV distance bounds -/

lemma tvDist_le_probEvent_of_probOutput_eq_of_not
    {mx my : m α} [NeverFail mx] [NeverFail my]
    (p : α → Prop) [DecidablePred p]
    (h_eq : ∀ x, ¬p x → Pr[= x | mx] = Pr[= x | my])
    (h_event_eq : Pr[p | mx] = Pr[p | my]) :
    tvDist mx my ≤ Pr[p | mx].toReal := by
  rw [tvDist, SPMF.tvDist, PMF.tvDist]
  refine ENNReal.toReal_mono probEvent_ne_top ?_
  rw [PMF.etvDist, tsum_option _ ENNReal.summable]
  have hfailx : (evalDist mx).toPMF none = 0 := by
    rw [← SPMF.run_eq_toPMF (p := evalDist mx), ← probFailure_def (mx := mx)]
    exact probFailure_eq_zero (mx := mx)
  have hfaily : (evalDist my).toPMF none = 0 := by
    rw [← SPMF.run_eq_toPMF (p := evalDist my), ← probFailure_def (mx := my)]
    exact probFailure_eq_zero (mx := my)
  have hsum :
      (∑' x, ENNReal.absDiff ((evalDist mx).toPMF (some x)) ((evalDist my).toPMF (some x))) =
        ∑' x, ENNReal.absDiff (Pr[= x | mx]) (Pr[= x | my]) := by
    refine tsum_congr fun x => ?_
    simp [probOutput_def, SPMF.apply_eq_toPMF_some]
  rw [hfailx, hfaily, ENNReal.absDiff_self, zero_add]
  rw [hsum]
  calc
    (∑' x, ENNReal.absDiff (Pr[= x | mx]) (Pr[= x | my])) / 2
      ≤ (∑' x, if p x then (Pr[= x | mx] + Pr[= x | my]) else 0) / 2 := by
          exact ENNReal.div_le_div_right
            (ENNReal.tsum_le_tsum fun x => by
              by_cases hx : p x
              · simpa [hx] using ENNReal.absDiff_le_add (Pr[= x | mx]) (Pr[= x | my])
              · simp [hx, h_eq x hx, ENNReal.absDiff_self]) _
    _ = (Pr[p | mx] + Pr[p | my]) / 2 := by
        rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
        congr 1
        calc
          (∑' x, if p x then (Pr[= x | mx] + Pr[= x | my]) else 0)
              = (∑' x, ((if p x then Pr[= x | mx] else 0) +
                  (if p x then Pr[= x | my] else 0))) := by
                  refine tsum_congr fun x => ?_
                  by_cases hx : p x <;> simp [hx]
          _ = (∑' x, if p x then Pr[= x | mx] else 0) +
              (∑' x, if p x then Pr[= x | my] else 0) := by
                rw [ENNReal.tsum_add]
    _ = (Pr[p | mx] + Pr[p | mx]) / 2 := by
        rw [← h_event_eq]
    _ = Pr[p | mx] := by
        rw [← two_mul, mul_div_assoc]
        simp [ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top]

end monadic

section bool_tvdist

variable {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- For any `Bool` computation, the difference of `Pr[= true]` values is bounded by
TV distance. -/
lemma abs_probOutput_toReal_sub_le_tvDist
    (game₁ game₂ : m Bool) :
    |Pr[= true | game₁].toReal - Pr[= true | game₂].toReal| ≤ tvDist game₁ game₂ := by
  simp only [probOutput_def, SPMF.apply_eq_toPMF_some, tvDist, SPMF.tvDist, PMF.tvDist]
  have happ : ∀ (p : PMF (Option Bool)),
      ((fun x : Option Bool => if x = some true then some () else none) <$> p) (some ()) =
        p (some true) := fun p => by
    simp [PMF.map_apply_eq, tsum_fintype]
  rw [← ENNReal.absDiff_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  apply ENNReal.toReal_mono (PMF.etvDist_ne_top _ _)
  rw [← happ (evalDist game₁).toPMF, ← happ (evalDist game₂).toPMF,
      ← PMF.etvDist_option_punit]
  exact PMF.etvDist_map_le (fun x : Option Bool => if x = some true then some () else none)
    (evalDist game₁).toPMF (evalDist game₂).toPMF

end bool_tvdist

end
