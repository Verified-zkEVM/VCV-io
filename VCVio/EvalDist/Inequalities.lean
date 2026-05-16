/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.EvalDist.Defs.Basic
import ToMathlib.Data.ENNReal.SumSquares

/-!
# Probability-weighted Cauchy-Schwarz / Jensen inequalities

Inequalities relating per-element bounds and their probabilistic averages, for use in
forking-lemma-style game-hopping arguments where the outermost step marginalizes over a
random key (or, more generally, an arbitrary `MonadLiftT m SPMF` monad output).

The headline lemma is `marginalized_jensen_forking_bound`: given a per-element bound
`acc x · (acc x / q − hinv) ≤ B x` and weights `Pr[= x | mx]` for some monadic computation
`mx`, the marginalized expectation `μ := 𝔼[acc]` satisfies the same shape:

  `μ · (μ / q − hinv) ≤ 𝔼[B]`.

The forking-lemma instantiation is `q := qH + 1`, `hinv := 1/|Chal|`, with `acc x` the
per-pk fork-success probability, `B x` the per-pk extraction-success probability, and
`mx := keygen`. The integration step is genuinely lossy (Cauchy-Schwarz on
`Pr[= · | mx]`), so this lemma sits at the heart of any keygen-marginalized fork-based
extraction bound.
-/

open ENNReal

universe u v

namespace OracleComp.EvalDist

variable {m : Type → Type v} [Monad m] [MonadLiftT m SPMF]

/-- **Marginalized Jensen / Cauchy-Schwarz step for the forking lemma.**

If a per-element bound `acc x · (acc x / q − hinv) ≤ B x` holds for every `x` (with
`acc x ≤ 1`), and we marginalize over the output distribution of any `mx : m X` with
`HasEvalSPMF`, then the marginalized expectation `μ := ∑' x, Pr[= x | mx] · acc x`
satisfies the same forking-bound shape:

  `μ · (μ / q − hinv) ≤ ∑' x, Pr[= x | mx] · B x`.

The proof uses Cauchy-Schwarz `μ² ≤ ∑' x, Pr[= x | mx] · acc x²` (via
`ENNReal.sq_tsum_le_tsum_sq` with weights summing to ≤ 1) and `ENNReal.mul_sub` to
distribute the truncated subtraction across the sum.

**Intended use.** In Pointcheval-Stern / Bellare-Neven style EUF-CMA-to-relation
reductions, instantiate as follows:

* `mx := hr.gen` (key generator),
* `acc (pk, sk) := Pr[fork point exists | run nmaAdv on pk]`,
* `B (pk, sk) := Pr[extraction succeeds | reduction pk]`,
* `q := qH + 1`, `hinv := 1 / |Chal|`.

The per-element hypothesis `hper` is then exactly the conclusion of `replayForkingBound`
(or `seededForkingBound`) at a fixed `pk`, composed with the special-soundness extractor.

This generalizes the obvious `[Fintype X]` Cauchy-Schwarz: the `tsum` form handles the
typical case where `X = Stmt × Wit` (uncountable in general, supported on whatever
keygen reaches). -/
lemma marginalized_jensen_forking_bound
    {X : Type} (mx : m X)
    (acc B : X → ℝ≥0∞) (q hinv : ℝ≥0∞)
    (hinv_ne_top : hinv ≠ ⊤)
    (hacc_le : ∀ x, acc x ≤ 1)
    (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∑' x, Pr[= x | mx] * acc x) *
        ((∑' x, Pr[= x | mx] * acc x) / q - hinv) ≤
      ∑' x, Pr[= x | mx] * B x := by
  classical
  set w : X → ℝ≥0∞ := fun x => Pr[= x | mx] with hw_def
  set μ : ℝ≥0∞ := ∑' x, w x * acc x with hμ_def
  have hw_tsum_le_one : ∑' x, w x ≤ 1 := tsum_probOutput_le_one
  have hμ_le_one : μ ≤ 1 := by
    calc μ = ∑' x, w x * acc x := rfl
      _ ≤ ∑' x, w x * 1 := by gcongr with x; exact hacc_le x
      _ = ∑' x, w x := by simp
      _ ≤ 1 := hw_tsum_le_one
  have hμ_ne_top : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le_one
  have hμ_hinv_ne_top : μ * hinv ≠ ⊤ := ENNReal.mul_ne_top hμ_ne_top hinv_ne_top
  have hCS : μ ^ 2 ≤ ∑' x, w x * acc x ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w acc hw_tsum_le_one
  calc μ * (μ / q - hinv)
      = μ * (μ / q) - μ * hinv :=
        ENNReal.mul_sub (fun _ _ => hμ_ne_top)
    _ = μ ^ 2 / q - μ * hinv := by
        rw [sq, mul_div_assoc]
    _ ≤ (∑' x, w x * acc x ^ 2) / q - μ * hinv := by
        gcongr
    _ = (∑' x, w x * acc x ^ 2 / q) - ∑' x, w x * acc x * hinv := by
        congr 1
        · simp only [div_eq_mul_inv]
          rw [ENNReal.tsum_mul_right]
        · rw [hμ_def, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, (w x * acc x ^ 2 / q - w x * acc x * hinv) := by
        -- Reverse-Jensen: `∑' f - ∑' g ≤ ∑' (f - g)` in ℝ≥0∞ when `∑' g ≠ ⊤`.
        set f : X → ℝ≥0∞ := fun x => w x * acc x ^ 2 / q with hf_def
        set g : X → ℝ≥0∞ := fun x => w x * acc x * hinv with hg_def
        have hg_sum_ne_top : ∑' x, g x ≠ ⊤ := by
          change ∑' x, w x * acc x * hinv ≠ ⊤
          rw [ENNReal.tsum_mul_right]; exact hμ_hinv_ne_top
        have hfg : ∑' x, f x ≤ ∑' x, (f x - g x) + ∑' x, g x := by
          calc ∑' x, f x ≤ ∑' x, ((f x - g x) + g x) :=
                ENNReal.tsum_le_tsum fun _ => le_tsub_add
            _ = ∑' x, (f x - g x) + ∑' x, g x := ENNReal.tsum_add
        exact tsub_le_iff_right.2 hfg
    _ = ∑' x, w x * (acc x ^ 2 / q - acc x * hinv) := by
        refine tsum_congr fun x => ?_
        have hwx_ne_top : w x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
        rw [ENNReal.mul_sub (fun _ _ => hwx_ne_top), mul_div_assoc, mul_assoc]
    _ = ∑' x, w x * (acc x * (acc x / q - hinv)) := by
        refine tsum_congr fun x => ?_
        have hax_ne_top : acc x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (hacc_le x)
        congr 1
        rw [ENNReal.mul_sub (fun _ _ => hax_ne_top), sq, mul_div_assoc]
    _ ≤ ∑' x, w x * B x := by
        gcongr with x
        exact hper x

end OracleComp.EvalDist
