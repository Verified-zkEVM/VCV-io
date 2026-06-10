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
advantages plus the `multipleBadQueryImpl` bad-flag probability (the within-tag nonce-collision
mass) and four unconditional slack terms. Chaining `multipleBad_bad_le_sessionCollisionBound` then
yields the explicit session-collision bounds in
`unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound` and its uniform-Nonce specialization.

The two existential PRF-adversary witnesses are concrete: they are the explicit reductions
`unlinkToMultiplePRFReduction` and `unlinkToSinglePRFReduction` applied to the unlinkability
adversary, so the bounds carry honest reduction content rather than mere existence claims. -/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ## Main reduction theorem -/

omit [Nonempty TagId] in
/-- Unlinkability reduction: the multiple-vs-single advantage is bounded by one PRF advantage for
the multiple-session world, one PRF advantage for the single-session world, the bad-event
probability from the intermediate nonce-collision world, and three unconditional slack terms. The
bound holds for every adversary.

`unlinkabilityAdvantage` is the signed one-sided gap `Pr[Multiple] − Pr[Single]`. The symmetric
bound on `|Pr[Multiple] − Pr[Single]|` follows by applying this theorem to the output-negated
adversary `oa >>= fun b => pure (!b)`, which has the same query bounds; the two directions then
combine into the absolute value.

The proof telescopes the three bridge lemmas:
`Pr[Multiple] − Pr[Single]` splits as `(Pr[Multiple] − Pr[MultRF]) + (Pr[MultRF] − Pr[SingleRF])
+ (Pr[SingleRF] − Pr[Single])`, where the first and last differences are absorbed into the two
PRF advantages and the middle difference is bounded by the `multipleBadQueryImpl` bad-flag
probability plus the slack terms. Each slack is charged by an identified proof step in the
direct coupling: the single-session world keys `sessionsPerTag` times more random-oracle cells
than the multiple-session world, an unconditional cell-count gap unrelated to nonce collisions.
They comprise the reader-cell slacks `qReader * Fintype.card TagId / Fintype.card Digest` and
`qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest` (the latter charged at the
asymmetric-discard reader step via `probEvent_cacheBadReader_uniformSample_le`), and the
nonce-aliasing slack `qReader * qTag / Fintype.card Nonce` (charged at slot-positive tag steps via
the reader-touched-set membership event). There is no tag-side slack: the tag-side cell-count gap
is absorbed by `le_self_add` at every tag step, so removing the reader-nonce distinctness
hypothesis costs zero extra slack compared with the conditional bound. -/
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
              (Fintype.card Digest : ℝ) := by
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

omit [Nonempty TagId] in
/-- Final unlinkability bound: two PRF advantages, an explicit closed-form bound for the
`multipleBadQueryImpl` collision term, and the chained reader/tag slack terms.

The bad-event collision term is discharged inline via `multipleBad_bad_le_sessionCollisionBound`,
which ports the union-bound induction `simulateQ_unlinkBad_prob_le` to the multiple-bad handler.
The bound is `(sessionsPerTag^2 * |TagId|) * maxNonceProb` (the same shape as
`unlinkBadExp_le_sessionCollisionBound`), plus the three unconditional reader-cell and
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
              (Fintype.card Digest : ℝ) := by
  obtain ⟨multiAdv, singleAdv, hSum⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary qReader qTag hqReader hqTag
  have hbad := multipleBad_bad_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax
  refine ⟨multiAdv, singleAdv, hSum.trans ?_⟩
  linarith

omit [Nonempty TagId] in
/-- Tightest unlinkability bound: when nonces are sampled uniformly (as enforced by
`SampleableType`), the session-collision term is exactly `sessionsPerTag² · |TagId| / |Nonce|`,
plus the three unconditional reader-cell and nonce-aliasing slack terms. -/
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
              (Fintype.card Digest : ℝ) := by
  -- The uniform-Nonce sampler bounds each `Pr[= nonce | $ᵗ Nonce]` by `(|Nonce|)⁻¹`.
  have hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)]).toReal ≤ ((Fintype.card Nonce : ℝ)⁻¹) := by
    intro nonce
    simp [probOutput_uniformSample, ENNReal.toReal_inv]
  obtain ⟨multiAdv, singleAdv, h⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound prfs adversary qReader qTag
      hqReader hqTag ((Fintype.card Nonce : ℝ)⁻¹) hmax
  exact ⟨multiAdv, singleAdv, by rwa [div_eq_mul_inv]⟩

/-! ## Absolute unlinkability advantage

The headline `unlinkabilityAdvantage_le_two_prf_plus_collision` is a *signed* bound on the one-sided
gap `Pr[Multiple] − Pr[Single]`. Applying it once more to the output-negated adversary
`adversary >>= fun b => pure (!b)` — which makes the same oracle queries and so inherits the same
query bounds and the same `multipleBadQueryImpl` bad-event mass — flips the sign of the advantage,
provided both experiments are failure-free. Combining the two directions through `abs_le` yields a
symmetric bound on `|Pr[Multiple] − Pr[Single]|`. -/

omit [DecidableEq Nonce] [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Negating the adversary's output bit reflects the multiple-session experiment through `not`. -/
theorem unlinkMultipleExp_not_map
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    unlinkMultipleExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs
      (adversary >>= fun b => pure (!b) :
        OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) =
    (fun b => !b) <$> unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary := by
  have key : (adversary >>= fun b => pure (!b)
      : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) =
      (fun b => !b) <$> adversary := by rw [map_eq_bind_pure_comp]; rfl
  rw [key]
  unfold unlinkMultipleExp
  rw [map_bind]
  refine bind_congr fun k => ?_
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, StateT.run'_eq]
  simp only [Functor.map_map]

omit [DecidableEq Nonce] [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Negating the adversary's output bit reflects the single-session experiment through `not`. -/
theorem unlinkSingleExp_not_map
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    unlinkSingleExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs
      (adversary >>= fun b => pure (!b) :
        OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) =
    (fun b => !b) <$> unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary := by
  have key : (adversary >>= fun b => pure (!b)
      : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) =
      (fun b => !b) <$> adversary := by rw [map_eq_bind_pure_comp]; rfl
  rw [key]
  unfold unlinkSingleExp
  rw [map_bind]
  refine bind_congr fun k => ?_
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, StateT.run'_eq]
  simp only [Functor.map_map]

omit [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The output-negated adversary inherits every predicate-targeted query bound, since appending a
pure continuation makes no additional oracle queries. -/
theorem isQueryBoundP_not_bind
    (adversary : UnlinkAdversary TagId Nonce Digest)
    {p : (UnlinkOracleSpec TagId Nonce Digest).Domain → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP adversary p n) :
    OracleComp.IsQueryBoundP (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) p n := by
  have hmap : (fun b => !b) <$> adversary = (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [← hmap, OracleComp.isQueryBoundP_map_iff]
  exact h

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The `multipleBadQueryImpl` bad-event mass is unchanged by output negation: the bad flag is set
purely by oracle queries, which the trailing `pure (!b)` does not touch. -/
theorem multipleBad_bad_not_bind_eq
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
      (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag))
        (adversary >>= fun b => pure (!b) :
          OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)).run
        ((UnlinkState.init, ∅), UnlinkBadState.init)] =
    Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
      (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag))
        adversary).run ((UnlinkState.init, ∅), UnlinkBadState.init)] := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  rw [probEvent_eq_tsum_ite (p := fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag
    => z.2.2.bad)]
  refine tsum_congr fun z => ?_
  rw [simulateQ_pure, StateT.run_pure]
  simp

omit [DecidableEq Nonce] [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `unlinkabilityAdvantage` is odd under output negation when both experiments are failure-free:
the negated adversary realizes exactly `−unlinkabilityAdvantage`. -/
theorem unlinkabilityAdvantage_not_bind_eq_neg
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (hMnf : NeverFail (unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary))
    (hSnf : NeverFail (unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary)) :
    unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs
      (adversary >>= fun b => pure (!b) :
        OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    = - unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary := by
  unfold unlinkabilityAdvantage
  rw [unlinkMultipleExp_not_map, unlinkSingleExp_not_map,
    probOutput_not_map, probOutput_not_map,
    probOutput_false_eq_sub, probOutput_false_eq_sub,
    hMnf.probFailure_eq_zero, hSnf.probFailure_eq_zero]
  simp only [tsub_zero]
  rw [ENNReal.toReal_sub_of_le probOutput_le_one one_ne_top,
    ENNReal.toReal_sub_of_le probOutput_le_one one_ne_top]
  simp only [ENNReal.toReal_one]
  ring

omit [Nonempty TagId] in
/-- Absolute unlinkability bound: `|Pr[Multiple] − Pr[Single]|` is bounded by four PRF advantages
(two per sign), the `multipleBadQueryImpl` bad-event mass, and the three unconditional slack terms.
The witnesses are the explicit reductions of the adversary and of its output-negated variant; the
two PRF advantages from the negated direction supply the lower-sign bound through `abs_le`, and
since `prfAdvantage` is itself an absolute value all four terms are nonnegative.

The two `NeverFail` hypotheses are necessary: an `UnlinkAdversary` may contain `failure`, in which
case the experiments inherit that failure mass and `unlinkabilityAdvantage` is no longer odd under
output negation. They are dischargeable via `unlinkMultipleExp_neverFail` and
`unlinkSingleExp_neverFail` whenever the adversary does not force a failure in either world. -/
theorem abs_unlinkabilityAdvantage_le_two_prf_plus_collision [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hMnf : NeverFail (unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary))
    (hSnf : NeverFail (unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary)) :
    ∃ multiAdv multiAdv' : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv singleAdv' : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        |unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary| ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv' +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv' +
            (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
              (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
                ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal +
            ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
            ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) := by
  -- Forward direction: the headline bound on the adversary itself.
  obtain ⟨multiAdv, singleAdv, hpos⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary qReader qTag hqReader hqTag
  -- Reverse direction: the headline bound on the output-negated adversary.
  obtain ⟨multiAdv', singleAdv', hneg⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs
      (adversary >>= fun b => pure (!b) :
        OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) qReader qTag
      (isQueryBoundP_not_bind adversary hqReader) (isQueryBoundP_not_bind adversary hqTag)
  rw [unlinkabilityAdvantage_not_bind_eq_neg prfs adversary hMnf hSnf,
    multipleBad_bad_not_bind_eq] at hneg
  refine ⟨multiAdv, multiAdv', singleAdv, singleAdv', ?_⟩
  have hm : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv :=
    abs_nonneg _
  have hs : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv :=
    abs_nonneg _
  have hm' : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv' :=
    abs_nonneg _
  have hs' : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv' :=
    abs_nonneg _
  rw [abs_le]
  constructor
  · linarith
  · linarith

end UnlinkReduction

end PRFTagReader
