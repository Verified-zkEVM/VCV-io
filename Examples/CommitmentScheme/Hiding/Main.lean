/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import Examples.CommitmentScheme.Hiding.LoggingBounds

/-!
# Hiding for the random-oracle commitment scheme — main theorems

The two packaged hiding bounds, both stating that real and simulated
hiding games are `t / |S|`-close in TV distance after the salt is averaged
over `s ← $ᵗ S`.

* `hiding_bound_avg` — per-salt sum, divided by `|S|`. Distance bound:
  `t / |S|`.
* `hiding_bound_finite` — salt sampled inside the experiment via
  `HidingAvgSpec`. Distance bound: `t / |S|`.

`hiding_bound_finite` is the textbook-facing form: sample the salt inside
the experiment, then compare. `hiding_bound_avg` is the underlying
technical form, summing the per-salt TVD bounds and dividing by `|S|`. The
packaging step uses `tvDist_bind_left_le` to push the salt sampling
through the TV distance.

The per-salt bound `tvDist(real(s), sim(s)) ≤ t / |S|` is FALSE: a trivial
adversary always querying salt `s` makes `Pr[bad(s)] = 1`. The averaging
over the uniform salt is essential. -/

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
/-- **Hiding bound (averaged technical form, Lemma cm-hiding).**

For every `t`-query two-phase hiding adversary `A`, the average statistical
distance between real and simulated hiding games, taken over uniformly
random salt `s ← $ᵗ S`, is at most `t / |S|`:

```
(∑ s, tvDist(hidingReal A s, hidingSim A s)) / |S|  ≤  t / |S|.
```

Proof: per-salt identical-until-bad
(`tvDist_hidingReal_hidingSim_le_probBad`) gives
`tvDist(real(s), sim(s)) ≤ Pr[bad(s)]` for every fixed `s`. Summing over
`s` and applying `sum_probEvent_hidingBad_le` (which exchanges the per-salt
bad sum for the adversary's total query bound) yields
`𝔼_s[tvDist(real(s), sim(s))] ≤ 𝔼_s[Pr[bad(s)]] ≤ t / |S|`.

The averaging is essential. The per-salt bound `tvDist ≤ t / |S|` is FALSE
in general: a trivial adversary always querying salt `s` makes
`Pr[bad(s)] = 1`. The textbook lemma silently averages over the uniform
salt, which `hiding_bound_finite` makes explicit by sampling the salt
inside a packaged `HidingAvgSpec` experiment. -/
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
/-- **Hiding bound (Lemma cm-hiding, packaged textbook form).**

For every `t`-query two-phase hiding adversary `A`,

```
tvDist(hidingMixedReal A, hidingMixedSim A)  ≤  t / |S|,
```

where `hidingMixedReal` and `hidingMixedSim` sample the salt
`s ← $ᵗ S` *inside* the experiment (via the `HidingAvgSpec` random-salt
oracle) and then run the corresponding per-salt game.

This is the textbook-facing wrapper around `hiding_bound_avg`: it pushes
the salt sampling through `tvDist_bind_left_le`, leaving the per-salt sum
that `hiding_bound_avg` already controls. -/
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
              ((HidingAvgSpec M S C).query (Sum.inl ()) :
                OracleComp (HidingAvgSpec M S C) S)].toReal *
            tvDist
              (OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C))
              (OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C)) := by
    simpa [hidingMixedReal, hidingMixedSim] using
      (_root_.tvDist_bind_left_le
        (mx := ((HidingAvgSpec M S C).query (Sum.inl ()) :
          OracleComp (HidingAvgSpec M S C) S))
        (f := fun s => OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C))
        (g := fun s => OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C)))
  refine le_trans hbind ?_
  calc
    ∑' s : S,
        Pr[= s |
            ((HidingAvgSpec M S C).query (Sum.inl ()) :
              OracleComp (HidingAvgSpec M S C) S)].toReal *
          tvDist
            (OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C))
            (OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C))
      = ∑' s : S,
          Pr[= s |
              ((HidingAvgSpec M S C).query (Sum.inl ()) :
                OracleComp (HidingAvgSpec M S C) S)].toReal *
            tvDist (hidingReal A s) (hidingSim A s) := by
            simp_rw [tvDist_liftComp_hidingAvgSpec]
    _ = ∑ s : S, ((Fintype.card S : ℝ≥0∞)⁻¹).toReal * tvDist (hidingReal A s) (hidingSim A s) := by
          rw [tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [probOutput_query (spec := HidingAvgSpec M S C) (t := Sum.inl ()) (u := s)]
          congr 1
    _ = (((Fintype.card S : ℝ≥0∞)⁻¹).toReal) *
          ∑ s : S, tvDist (hidingReal A s) (hidingSim A s) := by
          rw [← Finset.mul_sum]
    _ = ((Fintype.card S : ℝ)⁻¹) * ∑ s : S, tvDist (hidingReal A s) (hidingSim A s) := by
          simp [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    _ = (∑ s : S, tvDist (hidingReal A s) (hidingSim A s)) / (Fintype.card S : ℝ) := by
          rw [div_eq_mul_inv, mul_comm]
    _ ≤ (t : ℝ) / (Fintype.card S : ℝ) := hiding_bound_avg (M := M) (S := S) (C := C) A
