/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.Schnorr
import VCVio.CryptoFoundations.Fork

/-!
# Fork-Extractor Soundness and Query-Work Bounds for Schnorr

Specializes the generic fork framework to the textbook Schnorr identification scheme.

## Extraction soundness

`extractFormula_sound` shows that the standard special-soundness formula
`(z₁ - z₂) / (c₁ - c₂)` yields a valid discrete-log witness from two accepting transcripts
with the same commitment and distinct challenges.

`extractCandidate` is a deterministic postprocessor that takes the raw fork output (a pair of
transcripts with their challenge values) and applies this formula when the preconditions hold.
`extractCandidate_sound` proves that any returned witness is valid.

## Query-work bound

`fork_expectedQueryWork_le` shows that one fork-based extraction attempt over a single
challenge oracle `Unit →ₒ F` has expected query work at most `2q + 1`, where `q` is the
adversary's query budget. The three cost components are:
- `q` calls to sample the seed,
- `1` call to sample the replacement challenge,
- at most `q` live queries during the replayed execution.
-/

open OracleComp OracleComp.ProgramLogic OracleSpec ENNReal

namespace Schnorr

section soundness

variable (F : Type) [Field F]
variable (G : Type) [AddCommGroup G] [Module F G]

/-- The concrete Schnorr extractor formula is sound: from two accepting transcripts with the same
commitment and distinct challenges, the extracted scalar is a valid discrete-log witness. -/
theorem extractFormula_sound (g : G) {pk R : G} {c₁ c₂ z₁ z₂ : F} (hc : c₁ ≠ c₂)
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
abbrev challengeSpec : OracleSpec Unit := Unit →ₒ F

/-- Query budget assigning `q` queries to the single challenge oracle `()`. -/
abbrev challengeBudget (q : ℕ) : QueryCount Unit :=
  Function.update 0 () q

/-- Sampling `Fin n` uniformly costs exactly 1 in the unit-cost model. -/
private theorem finUniformSample_queryCostExactly_one
    (n : ℕ) [NeZero n] :
    AddWriterT.QueryCostExactly
      (simulateQ ((QueryRuntime.oracleCompRuntime (spec := unifSpec)).withUnitCost.impl)
        (uniformSample (Fin n) : ProbComp (Fin n)))
      1 := by
  cases n with
  | zero => cases (NeZero.ne (n := 0) rfl)
  | succ k =>
      change AddWriterT.QueryCostExactly
        (HasQuery.withUnitCost
          (fun [HasQuery unifSpec (AddWriterT ℕ ProbComp)] =>
            HasQuery.query (spec := unifSpec) (m := AddWriterT ℕ ProbComp) k)
          (QueryRuntime.oracleCompRuntime (spec := unifSpec)))
        1
      exact HasQuery.queryCostExactly_withUnitCost_query
        (runtime := QueryRuntime.oracleCompRuntime (spec := unifSpec))
        (t := k)

/-- Sampling `F` uniformly (via its `FinEnum` encoding) costs exactly 1 in the unit-cost model. -/
private theorem challengeSample_queryCostExactly_one :
    letI : SampleableType F := FinEnum.SampleableType F
    AddWriterT.QueryCostExactly
      (OracleComp.probCompUnitQueryRun ($ᵗ F : ProbComp F))
      1 := by
  letI : SampleableType F := FinEnum.SampleableType F
  haveI : NeZero (FinEnum.card F) := ⟨FinEnum.card_ne_zero (α := F)⟩
  change AddWriterT.QueryCostExactly (probCompUnitQueryRun
    (FinEnum.equiv (α := F).symm <$> ($ᵗ Fin (FinEnum.card F) : ProbComp _))) 1
  simp only [probCompUnitQueryRun, simulateQ_map]
  exact AddWriterT.queryCostExactly_map (FinEnum.equiv (α := F)).symm
    (finUniformSample_queryCostExactly_one (n := FinEnum.card F))

end runtime

section extractorCandidate

variable (F : Type) [Field F] [DecidableEq F]
variable (G : Type) [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Deterministic Schnorr witness extractor for the fork payload.

The input type `Option ((G × F) × F × (G × F) × F)` represents
`Option ((R₁, z₁), c₁, (R₂, z₂), c₂)` where `Rᵢ` is the commitment, `zᵢ` the response,
and `cᵢ` the challenge from the `i`-th fork run.

Returns `some ((z₁ - z₂) * (c₁ - c₂)⁻¹)` when:
- both commitments match (`R₁ = R₂`),
- the challenges differ (`c₁ ≠ c₂`), and
- both transcripts verify (`zᵢ • g = Rᵢ + cᵢ • pk`).

Returns `none` otherwise. -/
def extractCandidate (g pk : G) :
    Option ((G × F) × F × (G × F) × F) → Option F
  | none => none
  | some ((R₁, z₁), c₁, (R₂, z₂), c₂) =>
      if R₁ = R₂ then
        if c₁ = c₂ then
          none
        else if decide (z₁ • g = R₁ + c₁ • pk) ∧ decide (z₂ • g = R₂ + c₂ • pk) then
          some ((z₁ - z₂) * (c₁ - c₂)⁻¹)
        else
          none
      else
        none

/-- If `extractCandidate` returns `some sk`, then `sk` is a valid discrete-log witness:
`sk • g = pk`. -/
theorem extractCandidate_sound (g pk : G)
    {res : Option ((G × F) × F × (G × F) × F)}
    {sk : F}
    (hsk : extractCandidate (F := F) (G := G) g pk res = some sk) :
    sk • g = pk := by
  cases res with
  | none =>
      simp [extractCandidate] at hsk
  | some data =>
      rcases data with ⟨⟨R₁, z₁⟩, c₁, ⟨R₂, z₂⟩, c₂⟩
      by_cases hR : R₁ = R₂
      · by_cases hω : c₁ = c₂
        · simp [extractCandidate, hR, hω] at hsk
        · have hsk' :
              (decide (z₁ • g = R₂ + c₁ • pk) ∧ decide (z₂ • g = R₂ + c₂ • pk)) ∧
              (z₁ - z₂) * (c₁ - c₂)⁻¹ = sk := by
            simpa [extractCandidate, hR, hω] using hsk
          rcases hsk' with ⟨⟨hv₁, hv₂⟩, hskEq⟩
          have hv₁' : z₁ • g = R₁ + c₁ • pk := by
            simpa [hR] using of_decide_eq_true hv₁
          have hv₂' : z₂ • g = R₁ + c₂ • pk := by
            simpa [hR] using of_decide_eq_true hv₂
          have hsound :
              (((z₁ - z₂) * (c₁ - c₂)⁻¹ : F) • g) = pk :=
            extractFormula_sound (F := F) (G := G) g (hc := hω) hv₁' hv₂'
          rwa [hskEq] at hsound
      · simp [extractCandidate, hR] at hsk

/-- Monadic lifting of `extractCandidate_sound`: if `some sk` is in the support of
`extractCandidate g pk <$> oa`, then `sk • g = pk`. -/
theorem extractCandidate_sound_of_mem_support
    (g pk : G)
    {m : Type → Type} [Monad m] [LawfulMonad m] [HasEvalSet m]
    {oa : m (Option ((G × F) × F × (G × F) × F))} {sk : F}
    (hsk :
      some sk ∈ support (extractCandidate (F := F) (G := G) g pk <$> oa)) :
    sk • g = pk := by
  rw [support_map] at hsk
  rcases hsk with ⟨res, _, hres⟩
  exact extractCandidate_sound (F := F) (G := G) g pk hres

end extractorCandidate

section runtime

variable (F : Type) [FinEnum F] [Inhabited F]
variable {α : Type}

/-- One fork-based extraction attempt has expected query work at most `2q + 1`, where `q` is
the adversary's challenge-query budget. The LHS has three terms:

1. **Seed generation**: `q` uniform samples (cost 1 each) to build the seed = `q`.
2. **Replacement sample**: 1 fresh challenge value = `1`.
3. **Replay queries**: at most `q` live oracle queries during the replayed execution.

Total: `q + 1 + q = 2q + 1`. -/
theorem fork_expectedQueryWork_le
    (main : OracleComp (challengeSpec F) α) (q : ℕ)
    (cf : α → Option (Fin (challengeBudget q () + 1)))
    (hmain : IsPerIndexQueryBound main (challengeBudget q)) :
    letI : SampleableType F := FinEnum.SampleableType F
    AddWriterT.expectedCostNat
        (OracleComp.probCompUnitQueryRun
          (generateSeed (challengeSpec F) (challengeBudget q) [()])) +
      AddWriterT.expectedCostNat
        (OracleComp.probCompUnitQueryRun ($ᵗ F : ProbComp F)) +
      wp (generateSeed (challengeSpec F) (challengeBudget q) [()])
        (fun seed =>
          wp ($ᵗ F : ProbComp F)
            (fun u =>
              expectedCost
                (OracleComp.forkWithSeedValue main (challengeBudget q) () cf seed u)
                CostModel.unit
                (fun n : ℕ ↦ (n : ENNReal))))
      ≤ (2 * q + 1 : ENNReal) := by
  letI : SampleableType F := FinEnum.SampleableType F
  have hjs : OracleComp.SeedListCovers (challengeBudget q) [()] := by
    intro t ht; simp
  have hbound := OracleComp.forkExpectedQueryWork_le
    (main := main) (qb := challengeBudget q) (js := [()]) (i := ()) (cf := cf)
    (sampleCost := fun _ => 1)
    (fun _ => challengeSample_queryCostExactly_one (F := F))
    hmain hjs
  simpa [challengeBudget, Nat.mul_one, two_mul, add_assoc, add_left_comm, add_comm] using
    hbound

end runtime

end Schnorr
