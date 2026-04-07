/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.Schnorr
import VCVio.CryptoFoundations.ForkValues
import VCVio.CryptoFoundations.SigmaExtractorRuntime

/-!
# Fork-Extractor Runtime Bounds for Schnorr

This file specializes the generic runtime bounds from
`VCVio.CryptoFoundations.SigmaExtractorRuntime` to the textbook Schnorr setting.

There are two pieces:

- a concrete extraction-soundness theorem saying that two accepting Schnorr transcripts with
  the same commitment and distinct challenges yield a valid discrete-log witness;
- concrete fork-runtime corollaries for a single challenge family `Unit →ₒ F`, where the
  one-attempt and repeated-rewinding query-work bounds take the familiar forms `2q + 1` and
  `attempts * (2q + 1)`.

The runtime statements intentionally account only for query work, matching the current fork
runtime layer: challenge sampling plus live oracle traffic during replay.
-/

open OracleComp OracleSpec ENNReal

section soundness

variable (F : Type) [Field F]
variable (G : Type) [AddCommGroup G] [Module F G]

/-- The concrete Schnorr extractor formula is sound: from two accepting transcripts with the same
commitment and distinct challenges, the extracted scalar is a valid discrete-log witness. -/
theorem schnorrExtractFormula_sound (g : G) {pk R : G} {c₁ c₂ z₁ z₂ : F} (hc : c₁ ≠ c₂)
    (hv₁ : z₁ • g = R + c₁ • pk)
    (hv₂ : z₂ • g = R + c₂ • pk) :
    (((z₁ - z₂) * (c₁ - c₂)⁻¹ : F) • g) = pk := by
  have h_sub : (z₁ - z₂) • g = (c₁ - c₂) • pk := by
    rw [sub_smul, sub_smul, hv₁, hv₂, add_sub_add_left_eq_sub]
  have h_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hc
  calc
    (((z₁ - z₂) * (c₁ - c₂)⁻¹ : F) • g)
        = (c₁ - c₂)⁻¹ • ((z₁ - z₂) • g) := by rw [mul_comm, mul_smul]
    _ = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • pk) := by rw [h_sub]
    _ = (((c₁ - c₂)⁻¹ * (c₁ - c₂) : F) • pk) := by rw [← mul_smul]
    _ = (1 : F) • pk := by rw [inv_mul_cancel₀ h_ne]
    _ = pk := one_smul F pk

end soundness

section runtime

variable (F : Type) [FinEnum F] [Inhabited F]
variable {α : Type}

/-- The single challenge family used by the Schnorr fork extractor. -/
abbrev schnorrChallengeSpec : OracleSpec Unit := Unit →ₒ F

/-- Structural query budget for the single Schnorr challenge family. -/
abbrev schnorrChallengeBudget (q : ℕ) : QueryCount Unit :=
  SigmaProtocol.singleFamilyBudget () q

private theorem finUniformSample_queryBoundedAboveBy_one
    (n : ℕ) [NeZero n] :
    AddWriterT.QueryBoundedAboveBy
      (simulateQ ((QueryRuntime.oracleCompRuntime (spec := unifSpec)).withUnitCost.impl)
        (uniformSample (Fin n) : ProbComp (Fin n)))
      1 := by
  cases n with
  | zero =>
      cases (NeZero.ne (n := 0) rfl)
  | succ k =>
      change AddWriterT.QueryBoundedAboveBy
        (HasQuery.withUnitCost
          (fun [HasQuery unifSpec (AddWriterT ℕ ProbComp)] =>
            HasQuery.query (spec := unifSpec) (m := AddWriterT ℕ ProbComp) k)
          (QueryRuntime.oracleCompRuntime (spec := unifSpec)))
        1
      exact HasQuery.queryBoundedAboveBy_withUnitCost_query
        (runtime := QueryRuntime.oracleCompRuntime (spec := unifSpec))
        (t := k)

private theorem finUniformSample_queryBoundedBelowBy_one
    (n : ℕ) [NeZero n] :
    AddWriterT.QueryBoundedBelowBy
      (simulateQ ((QueryRuntime.oracleCompRuntime (spec := unifSpec)).withUnitCost.impl)
        (uniformSample (Fin n) : ProbComp (Fin n)))
      1 := by
  cases n with
  | zero =>
      cases (NeZero.ne (n := 0) rfl)
  | succ k =>
      change AddWriterT.QueryBoundedBelowBy
        (HasQuery.withUnitCost
          (fun [HasQuery unifSpec (AddWriterT ℕ ProbComp)] =>
            HasQuery.query (spec := unifSpec) (m := AddWriterT ℕ ProbComp) k)
          (QueryRuntime.oracleCompRuntime (spec := unifSpec)))
        1
      exact HasQuery.queryBoundedBelowBy_withUnitCost_query
        (runtime := QueryRuntime.oracleCompRuntime (spec := unifSpec))
        (t := k)

private theorem schnorrChallengeSample_queryBoundedAboveBy_one :
    AddWriterT.QueryBoundedAboveBy
      (simulateQ ((QueryRuntime.oracleCompRuntime (spec := unifSpec)).withUnitCost.impl)
        ((letI : SampleableType F := FinEnum.SampleableType F
          ($ᵗ F : ProbComp F))))
      1 := by
  letI : SampleableType F := FinEnum.SampleableType F
  haveI : NeZero (FinEnum.card F) := ⟨FinEnum.card_ne_zero (α := F)⟩
  simpa [uniformSample, SampleableType.ofEquiv, FinEnum.SampleableType, simulateQ_map] using
    (AddWriterT.queryBoundedAboveBy_map (FinEnum.equiv (α := F)).symm
      (finUniformSample_queryBoundedAboveBy_one (n := FinEnum.card F)))

private theorem schnorrChallengeSample_queryBoundedBelowBy_one :
    AddWriterT.QueryBoundedBelowBy
      (simulateQ ((QueryRuntime.oracleCompRuntime (spec := unifSpec)).withUnitCost.impl)
        ((letI : SampleableType F := FinEnum.SampleableType F
          ($ᵗ F : ProbComp F))))
      1 := by
  letI : SampleableType F := FinEnum.SampleableType F
  haveI : NeZero (FinEnum.card F) := ⟨FinEnum.card_ne_zero (α := F)⟩
  simpa [uniformSample, SampleableType.ofEquiv, FinEnum.SampleableType, simulateQ_map] using
    (AddWriterT.queryBoundedBelowBy_map (FinEnum.equiv (α := F)).symm
      (finUniformSample_queryBoundedBelowBy_one (n := FinEnum.card F)))

section extractorCandidate

variable [Field F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- Deterministic Schnorr witness extractor applied to the payload returned by
[`OracleComp.forkWithQueryValues`]. It accepts exactly when the fork produced two accepting
transcripts with the same commitment and distinct challenges, and then returns the standard
special-soundness witness formula. -/
def schnorrExtractCandidateFromForkValues (g pk : G) :
    Option ((G × F) × F × (G × F) × F) → Option F
  | none => none
  | some ((R₁, z₁), c₁, (R₂, z₂), c₂) =>
      if _hR : R₁ = R₂ then
        if _hω : c₁ = c₂ then
          none
        else if (schnorrSigma F G g).verify pk R₁ c₁ z₁ = true ∧
            (schnorrSigma F G g).verify pk R₂ c₂ z₂ = true then
          some ((z₁ - z₂) * (c₁ - c₂)⁻¹)
        else
          none
      else
        none

/-- If the deterministic Schnorr extractor postprocessing returns `some sk`, then `sk` is a valid
discrete-log witness for `pk`.

This theorem is phrased only in terms of the fork payload. It is therefore agnostic to the
particular fork wrapper used to obtain that payload, and can be applied equally to seeded replay,
value-carrying fork wrappers, or later Fiat-Shamir specializations. -/
theorem schnorrExtractCandidateFromForkValues_sound (g pk : G)
    {res : Option ((G × F) × F × (G × F) × F)}
    {sk : F}
    (hsk : schnorrExtractCandidateFromForkValues (F := F) (G := G) g pk res = some sk) :
    sk • g = pk := by
  cases res with
  | none =>
      simp [schnorrExtractCandidateFromForkValues] at hsk
  | some data =>
      rcases data with ⟨⟨R₁, z₁⟩, c₁, ⟨R₂, z₂⟩, c₂⟩
      by_cases hR : R₁ = R₂
      · by_cases hω : c₁ = c₂
        · simp [schnorrExtractCandidateFromForkValues, hR, hω] at hsk
        · have hsk' :
              ((schnorrSigma F G g).verify pk R₂ c₁ z₁ = true ∧
                (schnorrSigma F G g).verify pk R₂ c₂ z₂ = true) ∧
              (z₁ - z₂) * (c₁ - c₂)⁻¹ = sk := by
            simpa [schnorrExtractCandidateFromForkValues, hR, hω] using hsk
          rcases hsk' with ⟨hAnd, hskEq⟩
          have hv₁ : z₁ • g = R₂ + c₁ • pk := by
            simpa [schnorrSigma] using hAnd.1
          have hv₂ : z₂ • g = R₂ + c₂ • pk := by
            simpa [schnorrSigma] using hAnd.2
          have hv₁' : z₁ • g = R₁ + c₁ • pk := by
            simpa [hR] using hv₁
          have hv₂' : z₂ • g = R₁ + c₂ • pk := by
            simpa [hR] using hv₂
          have hsound :
              (((z₁ - z₂) * (c₁ - c₂)⁻¹ : F) • g) = pk :=
            schnorrExtractFormula_sound (F := F) (G := G) g (hc := hω) hv₁' hv₂'
          rwa [hskEq] at hsound
      · simp [schnorrExtractCandidateFromForkValues, hR] at hsk

/-- Any witness in the support of the deterministic Schnorr postprocessing is valid.

This support-level version is the right interface for later extractor wrappers: once a forking
construction is known to produce payloads of the expected shape, witness soundness follows by
mapping [`schnorrExtractCandidateFromForkValues`] over that output distribution. -/
theorem schnorrExtractCandidateFromForkValues_sound_of_mem_support
    (g pk : G)
    {m : Type → Type} [Monad m] [LawfulMonad m] [HasEvalSet m]
    {oa : m (Option ((G × F) × F × (G × F) × F))} {sk : F}
    (hsk :
      some sk ∈ support (schnorrExtractCandidateFromForkValues (F := F) (G := G) g pk <$> oa)) :
    sk • g = pk := by
  rw [support_map] at hsk
  rcases hsk with ⟨res, _, hres⟩
  exact schnorrExtractCandidateFromForkValues_sound (F := F) (G := G) g pk (by simpa using hres)

end extractorCandidate

/-- In the standard single-family Schnorr setting, one fork-based extraction attempt has expected
query work at most `2q + 1` whenever the adversary makes at most `q` challenge queries. -/
theorem schnorrSingleRewindExpectedQueryWork_le
    (main : OracleComp (schnorrChallengeSpec F) α) (q : ℕ)
    (cf : α → Option (Fin (schnorrChallengeBudget q () + 1)))
    (hmain : IsPerIndexQueryBound main (schnorrChallengeBudget q)) :
    OracleComp.forkExpectedWrapperAndLiveQueries
      main (schnorrChallengeBudget q) [()] () cf ≤
      (2 * q + 1 : ENNReal) := by
  letI : SampleableType F := FinEnum.SampleableType F
  have hbound :=
    SigmaProtocol.singleRewindExtractorExpectedQueryWork_le_singleFamily
      (main := main) (i := ()) (q := q) (cf := cf) (sampleCost := fun _ => 1)
      (hSampleUpper := fun _ => schnorrChallengeSample_queryBoundedAboveBy_one (F := F))
      (hSampleLower := fun _ => schnorrChallengeSample_queryBoundedBelowBy_one (F := F))
      hmain
  simpa [schnorrChallengeBudget, Nat.mul_one, two_mul, add_assoc, add_left_comm, add_comm] using
    hbound

/-- Repeating the standard Schnorr fork extractor `attempts` times multiplies the one-attempt
bound, giving expected query work at most `attempts * (2q + 1)`. -/
theorem schnorrRewindingExpectedQueryWork_le
    (main : OracleComp (schnorrChallengeSpec F) α) (q attempts : ℕ)
    (cf : α → Option (Fin (schnorrChallengeBudget q () + 1)))
    (hmain : IsPerIndexQueryBound main (schnorrChallengeBudget q)) :
    SigmaProtocol.rewindingExtractorExpectedQueryWork
        main (schnorrChallengeBudget q) [()] () cf attempts ≤
      (attempts : ENNReal) * (2 * q + 1 : ENNReal) := by
  letI : SampleableType F := FinEnum.SampleableType F
  have hbound :=
    SigmaProtocol.rewindingExtractorExpectedQueryWork_le_singleFamily
      (main := main) (i := ()) (q := q) (attempts := attempts)
      (cf := cf) (sampleCost := fun _ => 1)
      (hSampleUpper := fun _ => schnorrChallengeSample_queryBoundedAboveBy_one (F := F))
      (hSampleLower := fun _ => schnorrChallengeSample_queryBoundedBelowBy_one (F := F))
      hmain
  simpa [schnorrChallengeBudget, Nat.mul_one, two_mul, add_assoc, add_left_comm, add_comm] using
    hbound

end runtime
