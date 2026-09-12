/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Monotone operations and limits of measures

This file supplies two small order-theoretic facts for Mathlib measures. Giry bind is monotone in
a measurable measure-valued continuation, and the lattice supremum of an increasing sequence of
measures is its pointwise supremum on measurable sets.

The second fact is the measure-theoretic basis for interpreting progressively deeper observations
of a potentially nonterminating computation: returned mass grows with fuel, and its limit remains
a measure rather than merely a pointwise set function.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Giry bind is monotone in an almost-everywhere measurable continuation. -/
theorem bind_mono_right {μ : Measure α} {f g : α → Measure β}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    μ.bind f ≤ μ.bind g := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.bind_apply hs hf, Measure.bind_apply hs hg]
  exact lintegral_mono_ae <| hfg.mono fun _ hx => hx s

/-- Giry bind preserves pointwise order of almost-everywhere measurable continuations.
The pointwise hypothesis lets generalized congruence descend into the continuations. -/
@[gcongr]
theorem bind_mono_right_of_forall {μ : Measure α} {f g : α → Measure β}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : ∀ x, f x ≤ g x) :
    μ.bind f ≤ μ.bind g :=
  bind_mono_right hf hg (Filter.Eventually.of_forall hfg)

private theorem iSup_tsum_of_monotone (f : ℕ → ℕ → ENNReal)
    (hf : ∀ i, Monotone fun n => f n i) :
    (⨆ n, ∑' i, f n i) = ∑' i, ⨆ n, f n i := by
  calc
    (⨆ n, ∑' i, f n i) = ⨆ n, ⨆ s : Finset ℕ, ∑ i ∈ s, f n i := by
      simp_rw [ENNReal.tsum_eq_iSup_sum]
    _ = ⨆ s : Finset ℕ, ⨆ n, ∑ i ∈ s, f n i := iSup_comm
    _ = ⨆ s : Finset ℕ, ∑ i ∈ s, ⨆ n, f n i := by
      congr 1
      funext s
      exact (ENNReal.finsetSum_iSup_of_monotone (s := s) hf).symm
    _ = ∑' i, ⨆ n, f n i := ENNReal.tsum_eq_iSup_sum.symm

/-- The measure whose value on a measurable set is the supremum of an increasing sequence. -/
private noncomputable def monotoneLimit (μ : ℕ → Measure α) (hμ : Monotone μ) : Measure α :=
  Measure.ofMeasurable
    (fun s _ => ⨆ n, μ n s)
    (by simp)
    (by
      intro s hs hdisjoint
      simp_rw [measure_iUnion hdisjoint hs]
      exact iSup_tsum_of_monotone (fun n i => μ n (s i)) fun i _ _ hnm => hμ hnm (s i))

private theorem monotoneLimit_apply (μ : ℕ → Measure α) (hμ : Monotone μ)
    (s : Set α) (hs : MeasurableSet s) :
    monotoneLimit μ hμ s = ⨆ n, μ n s :=
  Measure.ofMeasurable_apply s hs

/-- The lattice supremum of an increasing sequence of measures is pointwise on measurable sets. -/
theorem iSup_apply_of_monotone (μ : ℕ → Measure α) (hμ : Monotone μ)
    (s : Set α) (hs : MeasurableSet s) :
    (⨆ n, μ n) s = ⨆ n, μ n s := by
  have hSup : (⨆ n, μ n) = monotoneLimit μ hμ := by
    apply le_antisymm
    · refine iSup_le fun n => Measure.le_iff.mpr fun t ht => ?_
      rw [monotoneLimit_apply μ hμ t ht]
      exact le_iSup (fun k => μ k t) n
    · refine Measure.le_iff.mpr fun t ht => ?_
      rw [monotoneLimit_apply μ hμ t ht]
      exact iSup_le fun n => (le_iSup (fun k => μ k) n) t
  rw [hSup, monotoneLimit_apply μ hμ s hs]

end MeasureTheory.Measure
