/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.UnlinkReduction
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Asymptotic Unlinkability

Paper-shaped packaging of the tag/reader unlinkability bound. For a security-parameter-indexed
family of PRF tag/reader instances whose two derived PRF schemes are asymptotically secure and
whose nonce/digest spaces grow superpolynomially, every polynomial-query adversary family has
negligible unlinkability advantage.

## Framework idiom

The concrete unlinkability quantities (`unlinkabilityAdvantage`, `PRFScheme.prfAdvantage`) are
`ℝ`-valued, while the asymptotic-security vocabulary of
`VCVio.CryptoFoundations.Asymptotics.{Negligible,Security}` is phrased over `ℕ → ℝ≥0∞`. We bridge
the two exactly as the rest of the repository does (see `VCVio/Interaction/UC/Computational.lean`):
an `ℝ`-valued error family `ε : ℕ → ℝ` is *negligible* when `fun λ => ENNReal.ofReal (ε λ)` is
`negligible`, and sums are split with `ENNReal.ofReal_add_le` combined with `negligible_add`. No
parallel framework is introduced; the headline is a plain `negligible` statement over a `ℕ`-indexed
instance family.

## Base bound

The base is the absolute, named-reduction bridge `abs_unlinkabilityAdvantage_reductions` proved
here, an additive restatement of `abs_unlinkabilityAdvantage_le_two_prf_plus_collision` with the
two existential PRF witnesses replaced by the concrete reductions `unlinkToMultiplePRFReduction`
and `unlinkToSinglePRFReduction` (applied to the adversary and to its output-negated variant). The
two `NeverFail` hypotheses are inherited unchanged: they are necessary because an `UnlinkAdversary`
may itself contain `failure`, in which case `unlinkabilityAdvantage` stops being odd under output
negation.

## Hypotheses of the headline

* PRF asymptotic security: the multiple- and single-session PRF advantage of *each* concrete
  reduction family is negligible. The protocol genuinely uses two PRF schemes
  (`multiplePRFScheme`, `singlePRFScheme`), so two independent assumptions are honest.
* Superpolynomial growth of `|Nonce λ|` and `|Digest λ|`, phrased as negligibility of their
  reciprocals.
* Polynomial query / instance bounds: `qReader λ`, `qTag λ`, `|TagId λ|`, and `sessionsPerTag λ`
  are each bounded by a fixed polynomial in `λ`. The cell-count slack
  `qReader · |TagId| · sessionsPerTag / |Digest|` forces the *numerator* to be polynomial, so the
  polynomial bounds on `|TagId λ|` and `sessionsPerTag λ` are real modeling assumptions, surfaced
  explicitly.
-/

open OracleComp OracleSpec ENNReal Filter

namespace PRFTagReader

/-! ## Negligibility helpers -/

/-- A natural-number family bounded by a polynomial times a negligible family is negligible.
The basic closure used to absorb polynomial query / cardinality numerators into a negligible
reciprocal-cardinality factor. -/
theorem negligible_natMul_of_poly_bound {f : ℕ → ℝ≥0∞} (hf : negligible f)
    {g : ℕ → ℕ} {p : Polynomial ℕ} (hg : ∀ n, g n ≤ p.eval n) :
    negligible (fun n => (g n : ℝ≥0∞) * f n) :=
  negligible_of_le (g := fun n => ((p.eval n : ℕ) : ℝ≥0∞) * f n)
    (fun n => mul_le_mul' (by exact_mod_cast hg n) le_rfl)
    (negligible_polynomial_mul hf p)

/-- A slack term `numerator / cardinality` is negligible when the numerator is polynomially bounded
and the reciprocal cardinality is negligible. The `ENNReal.ofReal` wrapper is the framework idiom
for treating an `ℝ`-valued nonnegative error family asymptotically. -/
theorem negligible_ofReal_natDiv_of_poly_bound {C : ℕ → ℕ}
    (hC : negligible (fun n => (C n : ℝ≥0∞)⁻¹))
    {g : ℕ → ℕ} {p : Polynomial ℕ} (hg : ∀ n, g n ≤ p.eval n) :
    negligible (fun n => ENNReal.ofReal ((g n : ℝ) / (C n : ℝ))) :=
  negligible_of_le (g := fun n => (g n : ℝ≥0∞) * (C n : ℝ≥0∞)⁻¹)
    (fun n => by
      refine (ENNReal.ofReal_div_le (by positivity)).trans ?_
      rw [div_eq_mul_inv, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast])
    (negligible_natMul_of_poly_bound hC hg)

section AbsReductions

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [Nonempty TagId] in
/-- Absolute, named-reduction unlinkability bound: `|Pr[Multiple] − Pr[Single]|` is bounded by the
PRF advantages of the concrete reductions `unlinkToMultiplePRFReduction` /
`unlinkToSinglePRFReduction` applied to both the adversary and its output-negated variant, the
`multipleBadQueryImpl` bad-event mass, and the three unconditional slack terms.

This is the additive restatement of `abs_unlinkabilityAdvantage_le_two_prf_plus_collision` with the
existential PRF witnesses replaced by the concrete reductions, so the asymptotic packaging can
state negligibility of the named reduction families directly. The two `NeverFail` hypotheses are
inherited unchanged. -/
theorem abs_unlinkabilityAdvantage_reductions [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hMnf : NeverFail (unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary))
    (hSnf : NeverFail (unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary)) :
    |unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) prfs adversary| ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
          (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary) +
        PRFScheme.prfAdvantage prfs.singlePRFScheme
          (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary) +
        PRFScheme.prfAdvantage prfs.multiplePRFScheme
          (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag)
            (adversary >>= fun b => pure (!b) :
              OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)) +
        PRFScheme.prfAdvantage prfs.singlePRFScheme
          (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag)
            (adversary >>= fun b => pure (!b) :
              OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)) +
        (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
          (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
            ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal +
        ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
        ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
        ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
          (Fintype.card Digest : ℝ) := by
  -- Forward direction: the named-reduction signed bound on the adversary itself.
  have hpos := unlinkabilityAdvantage_le_prfAdvantage_reductions_plus_collision
    prfs adversary qReader qTag hqReader hqTag
  -- Reverse direction: the named-reduction signed bound on the output-negated adversary.
  have hneg := unlinkabilityAdvantage_le_prfAdvantage_reductions_plus_collision prfs
    (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) qReader qTag
    (isQueryBoundP_not_bind adversary hqReader) (isQueryBoundP_not_bind adversary hqTag)
  rw [unlinkabilityAdvantage_not_bind_eq_neg prfs adversary hMnf hSnf,
    multipleBad_bad_not_bind_eq] at hneg
  have hm : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary) := abs_nonneg _
  have hs : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary) := abs_nonneg _
  have hm' : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag)
        (adversary >>= fun b => pure (!b) :
          OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)) := abs_nonneg _
  have hs' : (0 : ℝ) ≤ PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag)
        (adversary >>= fun b => pure (!b) :
          OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)) := abs_nonneg _
  rw [abs_le]
  constructor
  · linarith
  · linarith

end AbsReductions

/-! ## Security-parameter-indexed instance family -/

/-- A security-parameter-indexed family of tag/reader instances. For each `λ` it carries the slot
budget `sessionsPerTag λ` and the keyed-hash packaging `prfs λ` over the per-`λ` carrier types.
The carrier types and their instances are supplied as section variables on the asymptotic theorem;
this structure bundles only the per-`λ` data the concrete unlinkability bound consumes. -/
structure AsymptoticInstance
    (TagId Nonce Digest K : ℕ → Type) (sessionsPerTag : ℕ → ℕ) where
  /-- The keyed-hash packaging at each security parameter. -/
  prfs : (lam : ℕ) → TagReaderPRFs (K lam) (TagId lam) (Nonce lam) (Digest lam) (sessionsPerTag lam)

namespace AsymptoticInstance

variable {TagId Nonce Digest K : ℕ → Type}
  [∀ lam, DecidableEq (TagId lam)] [∀ lam, Fintype (TagId lam)] [∀ lam, Nonempty (TagId lam)]
  [∀ lam, DecidableEq (Nonce lam)] [∀ lam, SampleableType (Nonce lam)] [∀ lam, Fintype (Nonce lam)]
  [∀ lam, DecidableEq (Digest lam)] [∀ lam, SampleableType (Digest lam)]
  [∀ lam, Fintype (Digest lam)]
  {sessionsPerTag : ℕ → ℕ} [∀ lam, NeZero (sessionsPerTag lam)]

omit [∀ lam, Nonempty (TagId lam)] in
/-- **Asymptotic unlinkability.** For a security-parameter-indexed family of PRF tag/reader
instances, suppose:

* both derived PRF families are asymptotically secure — the multiple- and single-session PRF
  advantage of the concrete reduction of the adversary (and of its output-negated variant) is
  negligible;
* the nonce and digest spaces grow superpolynomially — `(|Nonce λ|)⁻¹` and `(|Digest λ|)⁻¹` are
  negligible;
* the adversary is a polynomial-query family and the instance parameters are polynomially bounded —
  `qReader`, `qTag`, `|TagId|`, and `sessionsPerTag` are each bounded by a fixed polynomial in `λ`;
* both experiments are failure-free at every `λ`.

Then the unlinkability advantage `|unlinkabilityAdvantage|` is negligible. -/
theorem negligible_abs_unlinkabilityAdvantage
    (inst : AsymptoticInstance TagId Nonce Digest K sessionsPerTag)
    (adversary : (lam : ℕ) → UnlinkAdversary (TagId lam) (Nonce lam) (Digest lam))
    (qReader qTag : ℕ → ℕ)
    (hqReader : ∀ lam, OracleComp.IsQueryBoundP (adversary lam) (·.isRight) (qReader lam))
    (hqTag : ∀ lam, OracleComp.IsQueryBoundP (adversary lam) (·.isLeft) (qTag lam))
    (hMnf : ∀ lam, NeverFail (unlinkMultipleExp (inst.prfs lam) (adversary lam)))
    (hSnf : ∀ lam, NeverFail (unlinkSingleExp (inst.prfs lam) (adversary lam)))
    -- PRF asymptotic security (multiple + single, adversary + negated adversary):
    (hPRFmulti : negligible (fun lam => ENNReal.ofReal
      (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam)))))
    (hPRFsingle : negligible (fun lam => ENNReal.ofReal
      (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam)))))
    (hPRFmulti' : negligible (fun lam => ENNReal.ofReal
      (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam)
          (adversary lam >>= fun b => pure (!b) :
            OracleComp (UnlinkOracleSpec (TagId lam) (Nonce lam) (Digest lam)) Bool)))))
    (hPRFsingle' : negligible (fun lam => ENNReal.ofReal
      (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam)
          (adversary lam >>= fun b => pure (!b) :
            OracleComp (UnlinkOracleSpec (TagId lam) (Nonce lam) (Digest lam)) Bool)))))
    -- Superpolynomial growth of the nonce and digest spaces:
    (hNonce : negligible (fun lam => (Fintype.card (Nonce lam) : ℝ≥0∞)⁻¹))
    (hDigest : negligible (fun lam => (Fintype.card (Digest lam) : ℝ≥0∞)⁻¹))
    -- Polynomial bounds on the query counts and instance parameters:
    (pReader pTag pTagId pSessions : Polynomial ℕ)
    (hpReader : ∀ lam, qReader lam ≤ pReader.eval lam)
    (hpTag : ∀ lam, qTag lam ≤ pTag.eval lam)
    (hpTagId : ∀ lam, Fintype.card (TagId lam) ≤ pTagId.eval lam)
    (hpSessions : ∀ lam, sessionsPerTag lam ≤ pSessions.eval lam) :
    negligible (fun lam => ENNReal.ofReal
      |unlinkabilityAdvantage (inst.prfs lam) (adversary lam)|) := by
  classical
  -- Negligibility of the collision term: bounded by `sessionsPerTag² · |TagId| / |Nonce|`.
  have hCollision : negligible (fun lam => ENNReal.ofReal
      (Pr[fun z : Bool × MultipleBadState (TagId lam) (Nonce lam) (Digest lam) (sessionsPerTag lam)
          => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId lam) (Nonce := Nonce lam)
          (Digest := Digest lam) (sessionsPerTag := sessionsPerTag lam)) (adversary lam)).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal) := by
    refine negligible_of_le (g := fun lam => ENNReal.ofReal
      (((sessionsPerTag lam ^ 2 * Fintype.card (TagId lam) : ℕ) : ℝ) /
        (Fintype.card (Nonce lam) : ℝ))) (fun lam => ?_)
      (negligible_ofReal_natDiv_of_poly_bound (g := fun lam =>
        sessionsPerTag lam ^ 2 * Fintype.card (TagId lam))
        (p := pSessions ^ 2 * pTagId) hNonce (fun lam => ?_))
    · refine ENNReal.ofReal_le_ofReal ?_
      have hmax : ∀ nonce : Nonce lam,
          (Pr[= nonce | ($ᵗ Nonce lam : ProbComp (Nonce lam))]).toReal ≤
            ((Fintype.card (Nonce lam) : ℝ)⁻¹) := by
        intro nonce; simp [probOutput_uniformSample, ENNReal.toReal_inv]
      have hbad := multipleBad_bad_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag lam)
        (adversary lam) ((Fintype.card (Nonce lam) : ℝ)⁻¹) hmax
      rwa [← div_eq_mul_inv] at hbad
    · rw [Polynomial.eval_mul, Polynomial.eval_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (hpSessions lam) 2) (hpTagId lam)
  -- Negligibility of each unconditional slack term.
  have hSlack1 : negligible (fun lam => ENNReal.ofReal
      (((qReader lam * Fintype.card (TagId lam) : ℕ) : ℝ) / (Fintype.card (Digest lam) : ℝ))) :=
    negligible_ofReal_natDiv_of_poly_bound (p := pReader * pTagId) hDigest (fun lam => by
      rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hpReader lam) (hpTagId lam))
  have hSlack2 : negligible (fun lam => ENNReal.ofReal
      (((qReader lam * qTag lam : ℕ) : ℝ) / (Fintype.card (Nonce lam) : ℝ))) :=
    negligible_ofReal_natDiv_of_poly_bound (p := pReader * pTag) hNonce (fun lam => by
      rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hpReader lam) (hpTag lam))
  have hSlack3 : negligible (fun lam => ENNReal.ofReal
      (((qReader lam * Fintype.card (TagId lam) * sessionsPerTag lam : ℕ) : ℝ) /
        (Fintype.card (Digest lam) : ℝ))) :=
    negligible_ofReal_natDiv_of_poly_bound (p := pReader * pTagId * pSessions) hDigest
      (fun lam => by
        rw [Polynomial.eval_mul, Polynomial.eval_mul]
        exact Nat.mul_le_mul (Nat.mul_le_mul (hpReader lam) (hpTagId lam)) (hpSessions lam))
  -- The pointwise abs bound, transported through `ENNReal.ofReal`.
  refine negligible_of_le (g := fun lam =>
    ENNReal.ofReal (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam))) +
      ENNReal.ofReal (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam))) +
      ENNReal.ofReal (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam)
          (adversary lam >>= fun b => pure (!b) :
            OracleComp (UnlinkOracleSpec (TagId lam) (Nonce lam) (Digest lam)) Bool))) +
      ENNReal.ofReal (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam)
          (adversary lam >>= fun b => pure (!b) :
            OracleComp (UnlinkOracleSpec (TagId lam) (Nonce lam) (Digest lam)) Bool))) +
      ENNReal.ofReal (Pr[fun z : Bool ×
            MultipleBadState (TagId lam) (Nonce lam) (Digest lam) (sessionsPerTag lam) =>
          z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId lam) (Nonce := Nonce lam)
          (Digest := Digest lam) (sessionsPerTag := sessionsPerTag lam)) (adversary lam)).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal +
      ENNReal.ofReal (((qReader lam * Fintype.card (TagId lam) : ℕ) : ℝ) /
        (Fintype.card (Digest lam) : ℝ)) +
      ENNReal.ofReal (((qReader lam * qTag lam : ℕ) : ℝ) / (Fintype.card (Nonce lam) : ℝ)) +
      ENNReal.ofReal (((qReader lam * Fintype.card (TagId lam) * sessionsPerTag lam : ℕ) : ℝ) /
        (Fintype.card (Digest lam) : ℝ))) (fun lam => ?_) ?_
  · -- Pointwise: `ofReal |unlink| ≤ Σ ofReal(termᵢ)`, by the abs bound + `ofReal_add_le`.
    refine (ENNReal.ofReal_le_ofReal (abs_unlinkabilityAdvantage_reductions (inst.prfs lam)
      (adversary lam) (qReader lam) (qTag lam) (hqReader lam) (hqTag lam) (hMnf lam)
      (hSnf lam))).trans ?_
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
    exact ENNReal.ofReal_add_le
  · -- The bounding sum is negligible: nine negligible summands combined additively.
    exact (((((((hPRFmulti.add hPRFsingle).add hPRFmulti').add hPRFsingle').add
      hCollision).add hSlack1).add hSlack2).add hSlack3)

end AsymptoticInstance

end PRFTagReader
