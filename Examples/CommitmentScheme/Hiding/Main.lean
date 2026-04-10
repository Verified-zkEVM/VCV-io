/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Hiding.LoggingBounds

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]
omit [DecidableEq M] [DecidableEq S] [DecidableEq C] [Fintype M] [Inhabited M] in
private lemma tvDist_liftComp_hidingAvgSpec {α : Type}
    (oa ob : OracleComp (CMOracle M S C) α) :
    tvDist
        (OracleComp.liftComp oa (HidingAvgSpec M S C))
        (OracleComp.liftComp ob (HidingAvgSpec M S C)) =
      tvDist oa ob := by
  rw [tvDist, tvDist, evalDist_liftComp, evalDist_liftComp]

omit [Fintype M] [DecidableEq C] in
/-- **Hiding theorem (averaged technical form)**:
The average statistical distance between real and simulated hiding games,
taken over uniformly random salt `s`, is at most `t / |S|`.

For every individual `s`, we have `tvDist(real(s), sim(s)) ≤ Pr[bad(s)]`
(identical-until-bad).  Summing over `s` and dividing by `|S|` gives:
  `𝔼_s[tvDist(real(s), sim(s))] ≤ 𝔼_s[Pr[bad(s)]] ≤ t / |S|`.

The per-salt bound `tvDist ≤ t/|S|` for fixed `s` is FALSE: a trivial adversary
always querying salt `s` makes `Pr[bad] = 1`.  The textbook (Lemma cm-hiding)
implicitly averages over the uniform salt. -/
theorem hiding_bound_avg [Finite M] {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, tvDist (hidingReal A s) (hidingSim A s)) / (Fintype.card S : ℝ) ≤
    (t : ℝ) / (Fintype.card S : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h1 : ∀ s : S, tvDist (hidingReal A s) (hidingSim A s) ≤
      Pr[hidingBad ∘ Prod.snd |
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal :=
    fun s => tvDist_hidingReal_hidingSim_le_probBad A s
  calc ∑ s : S, tvDist (hidingReal A s) (hidingSim A s)
      ≤ ∑ s : S, Pr[hidingBad ∘ Prod.snd |
          (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal :=
        Finset.sum_le_sum fun s _ => h1 s
    _ ≤ (t : ℝ) := by
        have hsum := sum_probEvent_hidingBad_le A
        have hne : ∀ s ∈ Finset.univ, Pr[hidingBad ∘ Prod.snd |
            (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)] ≠ ⊤ :=
          fun _ _ => probEvent_ne_top
        rw [← ENNReal.toReal_sum hne, ← ENNReal.toReal_natCast]
        exact (ENNReal.toReal_le_toReal
          (ne_top_of_le_ne_top ENNReal.coe_ne_top hsum)
          ENNReal.coe_ne_top).mpr hsum

omit [Fintype M] [DecidableEq C] in
/-- **Hiding theorem (Lemma cm-hiding, bounded packaged form)**:
sample the salt uniformly inside the experiment, then compare the resulting real and simulated
hiding games. This is the bounded-query textbook-facing wrapper around `hiding_bound_avg`. -/
theorem hiding_bound_finite [Finite M] {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    tvDist (hidingMixedReal (M := M) (S := S) (C := C) A)
      (hidingMixedSim (M := M) (S := S) (C := C) A) ≤
    (t : ℝ) / (Fintype.card S : ℝ) := by
  have hbind :
      tvDist (hidingMixedReal (M := M) (S := S) (C := C) A)
          (hidingMixedSim (M := M) (S := S) (C := C) A) ≤
        ∑' s : S,
          Pr[= s |
              (query (spec := HidingAvgSpec M S C) (Sum.inl ()) :
                OracleComp (HidingAvgSpec M S C) S)].toReal *
            tvDist
              (OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C))
              (OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C)) := by
    simpa [hidingMixedReal, hidingMixedSim] using
      (_root_.tvDist_bind_left_le
        (mx := (query (spec := HidingAvgSpec M S C) (Sum.inl ()) :
          OracleComp (HidingAvgSpec M S C) S))
        (f := fun s => OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C))
        (g := fun s => OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C)))
  refine le_trans hbind ?_
  calc
    ∑' s : S,
        Pr[= s |
            (query (spec := HidingAvgSpec M S C) (Sum.inl ()) :
              OracleComp (HidingAvgSpec M S C) S)].toReal *
          tvDist
            (OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C))
            (OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C))
      = ∑' s : S,
          Pr[= s |
              (query (spec := HidingAvgSpec M S C) (Sum.inl ()) :
                OracleComp (HidingAvgSpec M S C) S)].toReal *
            tvDist (hidingReal A s) (hidingSim A s) := by
            refine tsum_congr fun s => ?_
            rw [tvDist_liftComp_hidingAvgSpec]
    _ = ∑ s : S, ((Fintype.card S : ℝ≥0∞)⁻¹).toReal * tvDist (hidingReal A s) (hidingSim A s) := by
          rw [tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro s hs
          simp [probOutput_query, HidingAvgSpec]
    _ = (((Fintype.card S : ℝ≥0∞)⁻¹).toReal) *
          ∑ s : S, tvDist (hidingReal A s) (hidingSim A s) := by
          rw [← Finset.mul_sum]
    _ = ((Fintype.card S : ℝ)⁻¹) * ∑ s : S, tvDist (hidingReal A s) (hidingSim A s) := by
          simp [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    _ = (∑ s : S, tvDist (hidingReal A s) (hidingSim A s)) / (Fintype.card S : ℝ) := by
          rw [div_eq_mul_inv, mul_comm]
    _ ≤ (t : ℝ) / (Fintype.card S : ℝ) := hiding_bound_avg (M := M) (S := S) (C := C) A
