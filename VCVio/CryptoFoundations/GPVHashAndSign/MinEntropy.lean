/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.Basic

/-! # GPV Hash-and-Sign: Min-Entropy Bound for the Programmed-Preimage Experiment

In the exact-match experiment `GPVHashAndSign.programmedPreimageExp`, the challenger draws an
honest key pair, a uniform target `y`, and a hidden short preimage `x ← trapdoorSample pk sk y`;
the adversary sees only `(pk, y)` and wins by naming `x` exactly.  Since the hidden draw is
never observed, the best possible strategy is to guess the single most likely preimage, so the
advantage is bounded by the *guessing probability* of the trapdoor sampler — the largest
pointwise output mass it assigns at any honest key and target, i.e. `2^(-H∞)` for the sampler's
min-entropy `H∞`.

* `trapdoorGuessingProbability` — the guessing probability of `psf.trapdoorSample`: the
  supremum of pointwise output masses over honestly generated keys and all targets.
* `programmedPreimageAdvantage_le_trapdoorGuessingProbability` — the generic bound: every
  programmed-preimage adversary's advantage is at most that guessing probability.
* `programmedPreimageAdvantage_le_of_probOutput_trapdoorSample_le` — hypothesis form: a
  uniform pointwise bound `ε` on the sampler's masses at honest keys bounds the advantage
  by `ε`.

For an ideal discrete-Gaussian trapdoor sampler (as in GPV08), the guessing probability is
the maximal mass of the coset Gaussian, which is negligible once the width exceeds the
smoothing parameter of the lattice (GPV08 Lemma 2.10); instantiating `ε` with such a bound
turns the exact-match branch of `GPVHashAndSign.euf_cma_collision_bound` into a concrete
negligible term.
-/

public section

open OracleComp OracleSpec ENNReal

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)

/-- The *guessing probability* of the trapdoor sampler: the supremum, over honestly generated
key pairs and all targets, of the largest pointwise output mass of `psf.trapdoorSample`.  This
is `2^(-H∞)` for the least min-entropy `H∞` the sampler attains at an honest key; it bounds
the chance of naming an unobserved sample exactly
(`programmedPreimageAdvantage_le_trapdoorGuessingProbability`). -/
noncomputable def trapdoorGuessingProbability : ℝ≥0∞ :=
  ⨆ pksk ∈ support hr.gen, ⨆ y : Range, ⨆ x : Domain,
    Pr[= x | psf.trapdoorSample pksk.1 pksk.2 y]

/-- **Guessing-probability bound for the programmed-preimage experiment.**  The hidden
preimage `x ← trapdoorSample pk sk y` is drawn after the adversary's view `(pk, y)` is fixed
and is never revealed, so any adversary's chance of reproducing it exactly is at most the
sampler's largest pointwise mass: `∑ₓ Pr[trap = x] · Pr[adv = x] ≤ (⨆ₓ Pr[trap = x]) · 1`,
averaged over honest keys and targets. -/
theorem programmedPreimageAdvantage_le_trapdoorGuessingProbability [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    programmedPreimageAdvantage (psf := psf) (hr := hr) adversary ≤
      trapdoorGuessingProbability psf hr := by
  classical
  unfold programmedPreimageAdvantage programmedPreimageExp
  rw [← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun pksk hmem => ?_
  obtain ⟨pk, sk⟩ := pksk
  refine probEvent_bind_le_of_forall_le fun y _ => ?_
  have hinner : ∀ x : Domain,
      Pr[ (· = true) | adversary pk y >>= fun x' => pure (decide (x' = x))]
        = Pr[= x | adversary pk y] := by
    intro x
    rw [probEvent_bind_eq_tsum]
    refine (tsum_eq_single x fun x' hx' => ?_).trans (by simp)
    simp [hx']
  calc Pr[ (· = true) | psf.trapdoorSample pk sk y >>= fun x =>
        adversary pk y >>= fun x' => pure (decide (x' = x))]
      = ∑' x : Domain, Pr[= x | psf.trapdoorSample pk sk y] * Pr[= x | adversary pk y] := by
        rw [probEvent_bind_eq_tsum]
        exact tsum_congr fun x => by rw [hinner]
    _ ≤ ∑' x : Domain,
          (⨆ z : Domain, Pr[= z | psf.trapdoorSample pk sk y]) * Pr[= x | adversary pk y] :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul'
          (le_iSup (fun z => Pr[= z | psf.trapdoorSample pk sk y]) x) le_rfl
    _ = (⨆ z : Domain, Pr[= z | psf.trapdoorSample pk sk y])
          * ∑' x : Domain, Pr[= x | adversary pk y] := ENNReal.tsum_mul_left
    _ ≤ (⨆ z : Domain, Pr[= z | psf.trapdoorSample pk sk y]) * 1 :=
        mul_le_mul' le_rfl tsum_probOutput_le_one
    _ = ⨆ z : Domain, Pr[= z | psf.trapdoorSample pk sk y] := mul_one _
    _ ≤ trapdoorGuessingProbability psf hr := by
        unfold trapdoorGuessingProbability
        refine iSup_le fun z => ?_
        exact le_iSup_of_le (pk, sk) (le_iSup_of_le hmem (le_iSup_of_le y
          (le_iSup (fun x => Pr[= x | psf.trapdoorSample pk sk y]) z)))

/-- Hypothesis form of the guessing-probability bound: a uniform pointwise bound `ε` on the
trapdoor sampler's output masses at honestly generated keys bounds every programmed-preimage
adversary's advantage by `ε`.  This is the shape consumed by the exact-match hypothesis
`hMinEntropy` of `euf_cma_collision_bound`. -/
theorem programmedPreimageAdvantage_le_of_probOutput_trapdoorSample_le [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range))
    {ε : ℝ≥0∞}
    (h : ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ (y : Range) (x : Domain),
      Pr[= x | psf.trapdoorSample pk sk y] ≤ ε) :
    programmedPreimageAdvantage (psf := psf) (hr := hr) adversary ≤ ε := by
  refine le_trans
    (programmedPreimageAdvantage_le_trapdoorGuessingProbability psf hr adversary) ?_
  refine iSup_le fun pksk => iSup_le fun hmem => iSup_le fun y => iSup_le fun x => ?_
  exact h pksk.1 pksk.2 hmem y x

end GPVHashAndSign
