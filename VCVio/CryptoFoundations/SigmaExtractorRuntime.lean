/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.ForkRuntime
import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Runtime Bounds for Fork-Based Sigma Extractors

This file packages the runtime side of single-rewind and repeated-rewinding extractors built
from the forking wrapper.

The key point is that `ForkRuntime.forkExpectedWrapperAndLiveQueries` already separates the total
query work of one fork attempt into:

- seed-generation sampling cost;
- one fresh replacement sample at the forked challenge family;
- live oracle queries made by the seeded replay core.

For Σ-protocols with special soundness, these are precisely the query-work components of the
usual single-rewind extractor. This file adds two layers on top of that:

- a small correctness helper reducing witness validity to `SigmaProtocol.SpeciallySound`;
- quantitative bounds for one extractor attempt and for `n` repeated rewinding attempts.

The repeated-rewinding bound is stated as a scalar expectation on top of the one-attempt fork
runtime. It is intentionally phrased at the same level of abstraction as
`forkExpectedWrapperAndLiveQueries`, so it can be reused before committing to a concrete
extractor success analysis.
-/

open OracleSpec OracleComp ENNReal

namespace SigmaProtocol

variable {X W PC SC Ω P : Type} {p : X → W → Bool}

section soundness

/-- Special soundness immediately validates any witness returned by the Σ-protocol extractor from
two accepting transcripts with the same statement and commitment and with distinct challenges. -/
theorem extract_sound_of_speciallySoundAt
    (σ : SigmaProtocol X W PC SC Ω P p) {x : X} (hss : σ.SpeciallySoundAt x)
    {pc : PC} {ω₁ ω₂ : Ω} {p₁ p₂ : P} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : W} (hw : w ∈ support (σ.extract ω₁ p₁ ω₂ p₂)) :
    p x w = true :=
  hss pc ω₁ ω₂ p₁ p₂ hω hv₁ hv₂ w hw

/-- Global special soundness is the statement-level uniform version of
[`SigmaProtocol.extract_sound_of_speciallySoundAt`]. -/
theorem extract_sound_of_speciallySound
    (σ : SigmaProtocol X W PC SC Ω P p) (hss : σ.SpeciallySound)
    {x : X} {pc : PC} {ω₁ ω₂ : Ω} {p₁ p₂ : P} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : W} (hw : w ∈ support (σ.extract ω₁ p₁ ω₂ p₂)) :
    p x w = true :=
  extract_sound_of_speciallySoundAt σ (hss x) hω hv₁ hv₂ hw

end soundness

section runtime

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
variable [∀ i, SampleableType (spec.Range i)]
variable [spec.DecidableEq]
variable [Finite ι] [spec.Fintype] [spec.Inhabited]

/-- Query budget concentrated at one distinguished challenge family `i`. -/
def singleFamilyBudget (i : ι) (q : ℕ) : QueryCount ι :=
  Function.update (0 : QueryCount ι) i q

/-- Expected query work of `attempts` independent single-rewind extractor attempts, expressed as
`attempts` copies of the one-attempt fork runtime quantity
[`OracleComp.forkExpectedWrapperAndLiveQueries`]. -/
noncomputable def rewindingExtractorExpectedQueryWork
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (attempts : ℕ) : ENNReal :=
  (attempts : ENNReal) * OracleComp.forkExpectedWrapperAndLiveQueries main qb js i cf

/-- One single-rewind extractor attempt has the same query-work bound as the corresponding fork
wrapper. This theorem is the direct runtime statement for one special-soundness extraction
attempt. -/
theorem singleRewindExtractorExpectedQueryWork_le
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (sampleCost : ι → ℕ)
    (hSampleUpper :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main qb)
    (hjs : SeedListCovers qb js) :
    OracleComp.forkExpectedWrapperAndLiveQueries main qb js i cf ≤
      ((js.map fun j => qb j * sampleCost j).sum + sampleCost i + qb i : ENNReal) :=
  OracleComp.forkExpectedWrapperAndLiveQueries_le
    (main := main) (qb := qb) (js := js) (i := i) (cf := cf)
    (sampleCost := sampleCost) hSampleUpper hmain hjs

/-- Repeating the single-rewind extractor `attempts` times multiplies the one-attempt expected
query-work bound by `attempts`. -/
theorem rewindingExtractorExpectedQueryWork_le
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (attempts : ℕ) (sampleCost : ι → ℕ)
    (hSampleUpper :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main qb)
    (hjs : SeedListCovers qb js) :
    rewindingExtractorExpectedQueryWork main qb js i cf attempts ≤
      (attempts : ENNReal) *
        ((js.map fun j => qb j * sampleCost j).sum + sampleCost i + qb i : ENNReal) := by
  unfold rewindingExtractorExpectedQueryWork
  gcongr
  exact singleRewindExtractorExpectedQueryWork_le
    (main := main) (qb := qb) (js := js) (i := i) (cf := cf)
    (sampleCost := sampleCost) hSampleUpper hmain hjs

/-- Textbook single-family specialization of the fork-based extractor runtime bound.

If all oracle queries are to one distinguished challenge family `i`, each seed sample at that
family costs `sampleCost i`, and `main` makes at most `q` challenge queries, then one
single-rewind extraction attempt has expected query work at most
`q * sampleCost i + sampleCost i + q`. -/
theorem singleRewindExtractorExpectedQueryWork_le_singleFamily
    (main : OracleComp spec α) (i : ι) (q : ℕ)
    (cf : α → Option (Fin (singleFamilyBudget i q i + 1))) (sampleCost : ι → ℕ)
    (hSampleUpper :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main (singleFamilyBudget i q)) :
    OracleComp.forkExpectedWrapperAndLiveQueries
        main (singleFamilyBudget i q) [i] i cf ≤
      (q * sampleCost i + sampleCost i + q : ENNReal) := by
  have hjs : SeedListCovers (singleFamilyBudget i q) [i] := by
    intro t ht
    by_cases hti : t = i
    · simp [hti]
    · simp [singleFamilyBudget, Function.update, hti] at ht
  have hsingle :=
    singleRewindExtractorExpectedQueryWork_le
      (main := main) (qb := singleFamilyBudget i q) (js := [i]) (i := i) (cf := cf)
      (sampleCost := sampleCost) hSampleUpper hmain hjs
  simpa [singleFamilyBudget] using hsingle

/-- Repeating the single-family single-rewind extractor `attempts` times yields the linear
expected-query-work bound `attempts * (q * sampleCost i + sampleCost i + q)`. -/
theorem rewindingExtractorExpectedQueryWork_le_singleFamily
    (main : OracleComp spec α) (i : ι) (q attempts : ℕ)
    (cf : α → Option (Fin (singleFamilyBudget i q i + 1))) (sampleCost : ι → ℕ)
    (hSampleUpper :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main (singleFamilyBudget i q)) :
    rewindingExtractorExpectedQueryWork
        main (singleFamilyBudget i q) [i] i cf attempts ≤
      (attempts : ENNReal) * (q * sampleCost i + sampleCost i + q : ENNReal) := by
  have hjs : SeedListCovers (singleFamilyBudget i q) [i] := by
    intro t ht
    by_cases hti : t = i
    · simp [hti]
    · simp [singleFamilyBudget, Function.update, hti] at ht
  have hrepeat :=
    rewindingExtractorExpectedQueryWork_le
      (main := main) (qb := singleFamilyBudget i q) (js := [i]) (i := i)
      (cf := cf) (attempts := attempts) (sampleCost := sampleCost)
      hSampleUpper hmain hjs
  simpa [singleFamilyBudget] using hrepeat

end runtime

end SigmaProtocol
