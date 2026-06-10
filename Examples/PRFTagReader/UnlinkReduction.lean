/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.MultipleBadCollision

/-!
# Unlinkability PRF Reduction

Top-level PRF reduction for the tag/reader unlinkability game of `Examples.PRFTagReader`. The
unlinkability advantage `unlinkabilityAdvantage` is the gap between the multiple-session world
`unlinkMultipleExp` (all sessions of a tag share one secret) and the single-session world
`unlinkSingleExp` (each session uses an independent secret).

The reduction telescopes three bounds:

* a PRF hop replacing `prfs.evalMultiple` by a lazy random function turns `unlinkMultipleExp` into
  the ideal-PRF world of `unlinkToMultiplePRFReduction`;
* an identical-until-bad coupling bounds the gap between the two random-function worlds by the
  nonce-collision probability `unlinkBadExp`;
* a second PRF hop replacing `prfs.evalSingle` turns `unlinkSingleExp` into the ideal-PRF world of
  `unlinkToSinglePRFReduction`.

The headline `unlinkabilityAdvantage_le_two_prf_plus_collision` bounds the advantage by two PRF
advantages plus `Pr[unlinkBadExp]`. Chaining `unlinkBadExp_le_sessionCollisionBound` then yields
the explicit session-collision bounds in
`unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound` and its uniform-Nonce specialization.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ## Main reduction theorem -/

/-- Unlinkability reduction: the multiple-vs-single advantage is bounded by one PRF advantage for
the multiple-session world, one PRF advantage for the single-session world, the bad-event
probability from the intermediate nonce-collision world, and five unconditional slack terms. The
bound holds for every adversary.

The proof telescopes the three bridge lemmas:
`Pr[Multiple] − Pr[Single]` splits as `(Pr[Multiple] − Pr[MultRF]) + (Pr[MultRF] − Pr[SingleRF])
+ (Pr[SingleRF] − Pr[Single])`, where the first and last differences are absorbed into the two
PRF advantages and the middle difference is bounded by `Pr[unlinkBadExp]` plus the slack terms.
The slacks are unavoidable: the single-session world keys `sessionsPerTag` times more random-oracle
cells than the multiple-session world, an unconditional gap unrelated to nonce collisions. They
comprise the reader-cell slacks `qReader * Fintype.card TagId / Fintype.card Digest` and
`qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest`, the nonce-aliasing slack
`qReader * qTag / Fintype.card Nonce`, and the tag-cell slacks
`qTag * Fintype.card TagId * sessionsPerTag / Fintype.card Digest` and
`qTag * sessionsPerTag / Fintype.card Digest`. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_collision [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
              (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
                ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal +
            ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
            ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) +
            ((qTag * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) +
            ((qTag * sessionsPerTag : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  refine ⟨unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary,
    unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary, ?_⟩
  have h1 := prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp prfs adversary
  have h2 := prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp prfs adversary
  have h3 := unlinkPRFIdeal_gap_le_unlinkBad (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary qReader qTag
    hqReader hqTag
  unfold unlinkabilityAdvantage PRFScheme.prfAdvantage
  rw [h1, h2]
  set M := (Pr[= true | unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal
  set S := (Pr[= true | unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal
  set MR := (Pr[= true | PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) adversary)]).toReal
  set SR := (Pr[= true | PRFScheme.prfIdealExp (unlinkToSinglePRFReduction
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) adversary)]).toReal
  have hA : M - MR ≤ |M - MR| := le_abs_self _
  have hB : SR - S ≤ |S - SR| := (le_abs_self (SR - S)).trans_eq (abs_sub_comm SR S)
  linarith [h3]

/-! ## Explicit session-collision bounds -/

/-- Final unlinkability bound: two PRF advantages, an explicit closed-form bound for the
`multipleBadQueryImpl` collision term, and the chained reader/tag slack terms.

The bad-event collision term is discharged inline via `multipleBad_bad_le_sessionCollisionBound`,
which ports the union-bound induction `simulateQ_unlinkBad_prob_le` to the multiple-bad handler.
The bound is `(sessionsPerTag^2 * |TagId|) * maxNonceProb` (the same shape as
`unlinkBadExp_le_sessionCollisionBound`), plus the five unconditional reader/tag cell and
nonce-aliasing slack terms inherited from `unlinkabilityAdvantage_le_two_prf_plus_collision`. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound
    [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce, (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb +
            ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
            ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) +
            ((qTag * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) +
            ((qTag * sessionsPerTag : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  obtain ⟨multiAdv, singleAdv, hSum⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary qReader qTag hqReader hqTag
  have hbad := multipleBad_bad_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax
  refine ⟨multiAdv, singleAdv, hSum.trans ?_⟩
  linarith

/-- Tightest unlinkability bound: when nonces are sampled uniformly (as enforced by
`SampleableType`), the session-collision term is exactly `sessionsPerTag² · |TagId| / |Nonce|`,
plus the five unconditional reader/tag cell and nonce-aliasing slack terms. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_uniform_sessionCollisionBound
    [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) /
              (Fintype.card Nonce : ℝ) +
            ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
            ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) +
            ((qTag * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) +
            ((qTag * sessionsPerTag : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  -- The uniform-Nonce sampler bounds each `Pr[= nonce | $ᵗ Nonce]` by `(|Nonce|)⁻¹`.
  have hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)]).toReal ≤ ((Fintype.card Nonce : ℝ)⁻¹) := by
    intro nonce
    simp [probOutput_uniformSample, ENNReal.toReal_inv]
  obtain ⟨multiAdv, singleAdv, h⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound prfs adversary qReader qTag
      hqReader hqTag ((Fintype.card Nonce : ℝ)⁻¹) hmax
  exact ⟨multiAdv, singleAdv, by rwa [div_eq_mul_inv]⟩



end UnlinkReduction

end PRFTagReader
