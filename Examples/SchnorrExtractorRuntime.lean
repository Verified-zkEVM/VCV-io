/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.Schnorr
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
