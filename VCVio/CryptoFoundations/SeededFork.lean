/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CostModel
import VCVio.OracleComp.QueryTracking.SeededOracle
import ToMathlib.Data.ENNReal.SumSquares

/-!
# Seed-Based Forking Lemma (Bellare-Neven)

The forking lemma is a key tool in provable security. The *seeded* variant in this file
(`seededFork`) mechanizes the original Bellare-Neven construction (CCS 2006): pre-sample every
oracle response into a `QuerySeed`, run the adversary deterministically against that seed, then
re-run it against a seed that has been modified at the chosen fork point.

`seededFork` returns `OracleComp spec (Option (α × α))` with explicit matching on
success/failure. The seeded replay uses `seededOracle` via `StateT`, and `generateSeed`
produces the initial seed as a `ProbComp` lifted into `spec`.

The companion file `VCVio/CryptoFoundations/ReplayFork.lean` provides the *replay* variant,
which only pre-samples the forked oracle family and answers ambient randomness live; it is the
natural choice for reductions like Fiat-Shamir EUF-CMA whose adversaries make both kinds of
queries.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal Function Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [IsUniformSpec spec]
  {α β γ : Type}

/-- Bundles the inputs to the forking lemma. -/
structure SeededForkInput (spec : OracleSpec ι) (α : Type) where
  main : OracleComp spec α
  queryBound : ι → ℕ
  js : List ι

section forkDef

variable [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]

/-- The forking operation: run `main` with a random seed, then re-run it with the seed modified
at the `s`-th query to oracle `i` (where `s = cf x₁`), checking that both runs agree on `cf`.

Returns `none` (failure) when:
- `cf x₁ = none` (adversary did not choose a fork point)
- the re-sampled oracle response equals the original (no useful fork)
- `cf x₂ ≠ cf x₁` (the second run chose a different fork point) -/
def seededFork (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α)) := do
  let seed ← liftComp (generateSeed spec qb js) spec
  let x₁ ← (simulateQ seededOracle main).run' seed
  match cf x₁ with
  | none => return none
  | some s =>
    let u ← liftComp ($ᵗ spec.Range i) spec
    -- `seed' := take s ++ [u]` replaces the value at index `s` (0-based) when present.
    -- The collision guard must compare against that same index.
    if (seed i)[↑s]? = some u then
      return none
    else
      let seed' := (seed.takeAtIndex i ↑s).addValue i u
      let x₂ ← (simulateQ seededOracle main).run' seed'
      if cf x₂ = some s then
        return some (x₁, x₂)
      else
        return none

/-- The deterministic core of `seededFork` with the random seed and replacement value already fixed.

Runs `main` once against `seed`, checks whether the fork-index selector `cf` fires, and if so
replays `main` against a modified seed where the `(cf x₁)`-th answer to oracle `i` is replaced
by `u`. Returns the pair `(x₁, x₂)` when both runs agree on the fork index.

The only remaining randomness comes from `main`'s own oracle queries that fall outside the
seed (i.e. queries beyond the budget `qb`). -/
def seededForkWithSeedValue (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) (seed : QuerySeed spec)
    (u : spec.Range i) :
    OracleComp spec (Option (α × α)) := do
  let x₁ ← (simulateQ seededOracle main).run' seed
  match cf x₁ with
  | none => return none
  | some s =>
    if (seed i)[↑s]? = some u then
      return none
    else
      let seed' := (seed.takeAtIndex i ↑s).addValue i u
      let x₂ ← (simulateQ seededOracle main).run' seed'
      if cf x₂ = some s then
        return some (x₁, x₂)
      else
        return none

end forkDef

omit [IsUniformSpec spec] in
/-- When the seed has at least `qb t` pre-generated answers for each oracle `t`, running `main`
against the seed makes zero live oracle queries (every query is answered from the seed). -/
theorem isPerIndexQueryBound_firstRun_seeded (main : OracleComp spec α) (qb : ι → ℕ)
    {seed : QuerySeed spec} (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle main).run' seed) 0 :=
  seededOracle.isPerIndexQueryBound_run'_zero
    (oa := main) (qb := qb) (seed := seed) hmain hseed

omit [IsUniformSpec spec] in
/-- After truncating the seed at query index `s` for oracle `i` and inserting a fresh answer `u`,
the replayed run can make at most `qb i - (s + 1)` live queries, all to oracle `i`.
All other oracle families remain fully covered by the seed. -/
theorem isPerIndexQueryBound_replayAfterFork
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    {seed : QuerySeed spec} {u : spec.Range i}
    (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length)
    (s : Fin (qb i + 1)) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u))
      (Function.update 0 i (qb i - (↑s + 1))) :=
  seededOracle.isPerIndexQueryBound_run'_takeAtIndex_addValue
    (oa := main) (qb := qb) (seed := seed) (i := i) hmain hseed s u

omit [IsUniformSpec spec] in
private lemma isPerIndexQueryBound_if_pure
    {p : Prop} [Decidable p]
    {oa : OracleComp spec α} {qb : ι → ℕ} {x : α}
    (h : IsPerIndexQueryBound oa qb) :
    IsPerIndexQueryBound (if p then pure x else oa) qb := by
  split <;> simp [h]

omit [IsUniformSpec spec] in
private lemma isPerIndexQueryBound_seededForkWithSeedValue_replayGuard
    [spec.DecidableEq]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    {seed : QuerySeed spec} {u : spec.Range i}
    (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length)
    (x₁ : α) (s : Fin (qb i + 1)) :
    IsPerIndexQueryBound
      (if (seed i)[↑s]? = some u then
          (pure none : OracleComp spec (Option (α × α)))
        else
          (((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u)) >>=
            fun x₂ => if cf x₂ = some s then pure (some (x₁, x₂)) else pure none))
      (Function.update 0 i (qb i)) := by
  have hreplay :
      IsPerIndexQueryBound
        ((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u))
        (Function.update 0 i (qb i)) :=
    (isPerIndexQueryBound_replayAfterFork (main := main) (qb := qb) (i := i)
        (seed := seed) (u := u) hmain hseed s).mono fun j => by
      by_cases hj : j = i <;> simp [Function.update, hj]
  have hpost : ∀ x₂ : α,
      IsPerIndexQueryBound
        (if cf x₂ = some s then (pure (some (x₁, x₂)) : OracleComp spec (Option (α × α)))
          else pure none) 0 :=
    fun x₂ => by by_cases hx₂ : cf x₂ = some s <;> simp [hx₂]
  have hcont :
      IsPerIndexQueryBound
        (((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u)) >>=
          fun x₂ => if cf x₂ = some s then pure (some (x₁, x₂)) else pure none)
        (Function.update 0 i (qb i)) :=
    isPerIndexQueryBound_bind hreplay hpost
  exact isPerIndexQueryBound_if_pure (x := (none : Option (α × α))) hcont

omit [IsUniformSpec spec] in
/-- `seededForkWithSeedValue` makes at most `qb i` live queries, all to oracle `i`.

The first seeded run is query-free (covered by the seed); the replay after the fork point uses
at most the remaining `i`-budget. The bound holds regardless of which fork index `cf` returns. -/
theorem isPerIndexQueryBound_seededForkWithSeedValue
    [spec.DecidableEq]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    {seed : QuerySeed spec} {u : spec.Range i}
    (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound
      (seededForkWithSeedValue main qb i cf seed u)
      (Function.update 0 i (qb i)) := by
  have hfirst :
      IsPerIndexQueryBound ((simulateQ seededOracle main).run' seed) 0 :=
    isPerIndexQueryBound_firstRun_seeded (main := main) (qb := qb) hmain hseed
  let core : OracleComp spec (Option (α × α)) :=
    ((simulateQ seededOracle main).run' seed) >>= fun x₁ =>
      match cf x₁ with
      | none => pure none
      | some s =>
        if (seed i)[↑s]? = some u then
          pure none
        else
          let seed' := (seed.takeAtIndex i ↑s).addValue i u
          (simulateQ seededOracle main).run' seed' >>= fun x₂ =>
            if cf x₂ = some s then
              pure (some (x₁, x₂))
            else
              pure none
  have hbind :
      IsPerIndexQueryBound
        core
        ((0 : QueryCount ι) + Function.update (0 : QueryCount ι) i (qb i)) := by
    refine isPerIndexQueryBound_bind hfirst fun x₁ => ?_
    cases hcf : cf x₁ with
    | none =>
        exact isPerIndexQueryBound_pure (spec := spec) (x := (none : Option (α × α)))
          (qb := Function.update 0 i (qb i))
    | some s =>
        exact isPerIndexQueryBound_seededForkWithSeedValue_replayGuard
          (main := main) (qb := qb) (i := i) (cf := cf) (seed := seed) (u := u)
          hmain hseed x₁ s
  have hbind' :
      IsPerIndexQueryBound core (Function.update 0 i (qb i)) := by
    simpa [Pi.zero_apply] using hbind
  simpa [seededForkWithSeedValue, core] using hbind'

section generateSeedCoverage

variable [∀ i, SampleableType (spec.Range i)]

omit [IsUniformSpec spec] in
/-- The expected unit-cost query count of `seededForkWithSeedValue`, averaged over the randomly
sampled seed and replacement value, is at most `qb i`. -/
theorem expectedQueryCount_seededForkWithSeedValue_le
    [spec.DecidableEq]
    [Finite ι] [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hmain : IsPerIndexQueryBound main qb)
    (hjs : SeedListCovers qb js) :
    wp (generateSeed spec qb js)
      (fun seed =>
        wp ($ᵗ spec.Range i)
          (fun u =>
            expectedCost
              (seededForkWithSeedValue main qb i cf seed u)
              CostModel.unit
              (fun n : ℕ ↦ (n : ENNReal))))
      ≤ qb i := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [wp_eq_tsum]
  calc
    ∑' seed : QuerySeed spec,
        Pr[= seed | generateSeed spec qb js] *
          wp ($ᵗ spec.Range i)
            (fun u =>
              expectedCost
                (seededForkWithSeedValue main qb i cf seed u)
                CostModel.unit
                (fun n : ℕ ↦ (n : ENNReal)))
      ≤ ∑' seed : QuerySeed spec,
          Pr[= seed | generateSeed spec qb js] * (qb i : ENNReal) := by
            refine ENNReal.tsum_le_tsum ?_
            intro seed
            by_cases hseed : seed ∈ support (generateSeed spec qb js)
            · gcongr
              have hseedCov := generateSeed_covers_queryBound (spec := spec) qb js hjs hseed
              have hwp : wp ($ᵗ spec.Range i) (fun u =>
                    expectedCost (seededForkWithSeedValue main qb i cf seed u)
                      CostModel.unit (fun n : ℕ ↦ (n : ENNReal))) ≤
                  wp ($ᵗ spec.Range i) (fun _ : spec.Range i => (qb i : ENNReal)) := by
                refine wp_mono ($ᵗ spec.Range i) ?_
                intro u
                have hbound := isPerIndexQueryBound_seededForkWithSeedValue
                  (main := main) (qb := qb) (i := i) (cf := cf) (u := u) hmain hseedCov
                simpa [ExpectedCostBound, Finset.sum_update_of_mem (Finset.mem_univ i)] using
                  (WorstCaseCostBound.toExpectedCostBound
                    (IsPerIndexQueryBound.toWorstCaseCostBound_unit_sum hbound)
                    (fun a b hle ↦ by
                      simpa using (Nat.cast_le.mpr hle : (a : ENNReal) ≤ (b : ENNReal))))
              rwa [wp_const] at hwp
            · simp [probOutput_eq_zero_of_not_mem_support hseed]
    _ = qb i := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

section forkRuntime

variable [spec.DecidableEq]
variable [Finite ι]

/-- Total expected query work of one fork attempt. The LHS decomposes as three terms:

1. **Seed generation**: `∑ j in js, qb j * sampleCost j` uniform-oracle calls to build the seed.
2. **Replacement sample**: `sampleCost i` calls to sample one fresh value at the forked oracle `i`.
3. **Replay queries**: at most `qb i` live queries during the replayed execution.

The RHS is their sum: `(∑ j in js, qb j * sampleCost j) + sampleCost i + qb i`. -/
theorem seededForkExpectedQueryWork_le
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (sampleCost : ι → ℕ)
    (hSample :
      ∀ j, AddWriterT.QueryCostExactly
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main qb)
    (hjs : SeedListCovers qb js) :
    AddWriterT.expectedCostNat (probCompUnitQueryRun (generateSeed spec qb js)) +
      AddWriterT.expectedCostNat
        (probCompUnitQueryRun ($ᵗ spec.Range i : ProbComp (spec.Range i))) +
      wp (generateSeed spec qb js)
        (fun seed =>
          wp ($ᵗ spec.Range i)
            (fun u =>
              expectedCost
                (seededForkWithSeedValue main qb i cf seed u)
                CostModel.unit
                (fun n : ℕ ↦ (n : ENNReal)))) ≤
      ((js.map fun j => qb j * sampleCost j).sum + sampleCost i + qb i : ENNReal) := by
  have hgen_le := AddWriterT.expectedCostNat_le_of_queryBoundedAboveBy
    (generateSeed_queryCostExactly (spec := spec) qb js sampleCost hSample).toAbove
  have hi_le := AddWriterT.expectedCostNat_le_of_queryBoundedAboveBy (hSample i).toAbove
  have hcore :=
    expectedQueryCount_seededForkWithSeedValue_le
      (main := main) (qb := qb) (js := js) (i := i) (cf := cf) hmain hjs
  exact add_le_add (add_le_add hgen_le hi_le) hcore

end forkRuntime

end generateSeedCoverage

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
    [unifSpec ˡ⊂ₒ spec]

omit [IsUniformSpec spec] [unifSpec ˡ⊂ₒ spec] in
/-- If `seededFork` succeeds (returns `some`), both runs agree on the fork index. -/
theorem cf_eq_of_mem_support_seededFork (x₁ x₂ : α)
    (h : some (x₁, x₂) ∈ support (seededFork main qb js i cf)) :
      ∃ s, cf x₁ = some s ∧ cf x₂ = some s := by
  simp only [seededFork] at h
  grind

omit [unifSpec ˡ⊂ₒ spec] in
/-- On `seededFork` support, first-projection success equals old pair-style success event. -/
theorem probEvent_seededFork_fst_eq_probEvent_pair (s : Fin (qb i + 1)) :
    Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) | seededFork main qb js i cf] =
      Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) |
          seededFork main qb js i cf] := by
  refine probEvent_ext fun r hr ↦ ?_
  rcases r with _ | ⟨x₁, x₂⟩
  · simp
  · obtain ⟨t, h₁, h₂⟩ := cf_eq_of_mem_support_seededFork (main := main) (qb := qb)
      (js := js) (i := i) (cf := cf) x₁ x₂ (by simpa using hr)
    simp [h₁, h₂]

omit [spec.DecidableEq] [DecidableEq ι] in
private lemma probEvent_uniform_eq_seedSlot_le_inv (s : Fin (qb i + 1))
    (seed : QuerySeed spec) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[ fun u : spec.Range i => (seed i)[↑s]? = some u
      | liftComp ($ᵗ spec.Range i) spec] ≤ h⁻¹ := by
  by_cases hnone : (seed i)[↑s]? = none
  · simp [hnone]
  · rcases Option.ne_none_iff_exists'.mp hnone with ⟨u₀, hu₀⟩
    simp only [hu₀, Option.some.injEq]
    exact le_of_eq (seededOracle.probEvent_liftComp_uniformSample_eq_of_eq u₀)

private lemma probOutput_collision_given_seed_le (s : Fin (qb i + 1))
    (seed : QuerySeed spec) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= (some s : Option (Fin (qb i + 1))) | do
      let x₁ ← (simulateQ seededOracle main).run' seed
      let u ← liftComp ($ᵗ spec.Range i) spec
      if (seed i)[↑s]? = some u then return cf x₁ else return none] ≤
    Pr[= (some s : Option (Fin (qb i + 1))) |
      cf <$> (simulateQ seededOracle main).run' seed] / h := by
  simp only
  rw [probOutput_bind_eq_tsum, probOutput_map_eq_tsum]
  simp_rw [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x₁ => ?_
  have hterm :
      Pr[= (some s : Option (Fin (qb i + 1))) | do
        let u ← liftComp ($ᵗ spec.Range i) spec
        if (seed i)[↑s]? = some u then return cf x₁ else return none] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) |
        (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
        (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
    by_cases hcf : cf x₁ = some s
    · calc
        Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if (seed i)[↑s]? = some u then return cf x₁ else return none]
          = Pr[ fun u : spec.Range i => (seed i)[↑s]? = some u |
              liftComp ($ᵗ spec.Range i) spec] := by
              rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
              refine tsum_congr fun u => ?_
              by_cases hu : (seed i)[↑s]? = some u <;> simp [hcf, hu]
        _ ≤ (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
              simpa using probEvent_uniform_eq_seedSlot_le_inv (s := s) (seed := seed)
        _ = Pr[= (some s : Option (Fin (qb i + 1))) |
              (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
              (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
              simp [hcf]
    · have hcf' : (some s : Option (Fin (qb i + 1))) ≠ cf x₁ := by
        simpa [eq_comm] using hcf
      refine le_of_eq ?_
      calc
        Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if (seed i)[↑s]? = some u then return cf x₁ else return none] = 0 := by
              rw [probOutput_bind_eq_tsum]
              refine ENNReal.tsum_eq_zero.mpr fun u => ?_
              by_cases hu : (seed i)[↑s]? = some u <;> simp [hu, hcf']
        _ = Pr[= (some s : Option (Fin (qb i + 1))) |
              (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
              (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
              simp [hcf']
  rw [mul_assoc]
  exact mul_le_mul' le_rfl hterm

private lemma probOutput_collision_le_main_div (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= (some s : Option (Fin (qb i + 1))) | do
      let seed ← liftComp (generateSeed spec qb js) spec
      let x₁ ← (simulateQ seededOracle main).run' seed
      let u ← liftComp ($ᵗ spec.Range i) spec
      if (seed i)[↑s]? = some u then return cf x₁ else return none] ≤
    Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] / h := by
  simp only
  rw [probOutput_bind_eq_tsum]
  have hStep1 :
      ∑' seed : QuerySeed spec,
        Pr[= seed | liftComp (generateSeed spec qb js) spec] *
          Pr[= (some s : Option (Fin (qb i + 1))) | do
            let x₁ ← (simulateQ seededOracle main).run' seed
            let u ← liftComp ($ᵗ spec.Range i) spec
            if (seed i)[↑s]? = some u then return cf x₁ else return none]
        ≤ ∑' seed : QuerySeed spec,
            Pr[= seed | liftComp (generateSeed spec qb js) spec] *
              (Pr[= (some s : Option (Fin (qb i + 1))) |
                cf <$> (simulateQ seededOracle main).run' seed] /
              ↑(Fintype.card (spec.Range i))) := by
    refine ENNReal.tsum_le_tsum fun seed => mul_le_mul' le_rfl ?_
    exact probOutput_collision_given_seed_le
      (main := main) (qb := qb) (i := i) (cf := cf) (s := s) (seed := seed)
  refine hStep1.trans_eq ?_
  calc ∑' seed : QuerySeed spec,
        Pr[= seed | liftComp (generateSeed spec qb js) spec] *
          (Pr[= (some s : Option (Fin (qb i + 1))) |
            cf <$> (simulateQ seededOracle main).run' seed] /
          ↑(Fintype.card (spec.Range i)))
      = (∑' seed : QuerySeed spec,
          Pr[= seed | liftComp (generateSeed spec qb js) spec] *
            Pr[= (some s : Option (Fin (qb i + 1))) |
              cf <$> (simulateQ seededOracle main).run' seed]) /
            ↑(Fintype.card (spec.Range i)) := by
        simp_rw [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | do
            let seed ← liftComp (generateSeed spec qb js) spec
            cf <$> (simulateQ seededOracle main).run' seed] /
            ↑(Fintype.card (spec.Range i)) := by rw [probOutput_bind_eq_tsum]
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
          ↑(Fintype.card (spec.Range i)) := by
        congr 1
        simpa using seededOracle.probOutput_generateSeed_bind_map_simulateQ
          (qc := qb) (js := js) (oa := main) (f := cf)
          (y := (some s : Option (Fin (qb i + 1))))

omit [spec.DecidableEq] in
private lemma probOutput_main_eq_tsum_seed_weighted (s : Fin (qb i + 1)) :
    (Pr[= s | cf <$> main] : ℝ≥0∞) =
      ∑' σ, Pr[= σ | generateSeed spec qb js] *
        Pr[= (some s : Option (Fin (qb i + 1))) |
          cf <$> (simulateQ seededOracle main).run' σ] := by
  rw [show (Pr[= s | cf <$> main] : ℝ≥0∞) =
    Pr[= (some s : Option (Fin (qb i + 1))) |
      (do let seed ← liftComp (generateSeed spec qb js) spec
          cf <$> (simulateQ seededOracle main).run' seed :
        OracleComp spec (Option (Fin (qb i + 1))))] from by
    simpa using (seededOracle.probOutput_generateSeed_bind_map_simulateQ
      (qc := qb) (js := js) (oa := main) (f := cf)
      (y := (some s : Option (Fin (qb i + 1))))).symm]
  rw [probOutput_bind_eq_tsum]
  simp_rw [probOutput_liftComp]

omit [spec.DecidableEq] in
private lemma probOutput_noGuardComp_eq_tsum_factored (s : Fin (qb i + 1)) :
    Pr[= (some (some s, some s) :
        Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) | do
      let seed ← liftComp (generateSeed spec qb js) spec
      let x₁ ← (simulateQ seededOracle main).run' seed
      let u ← liftComp ($ᵗ spec.Range i) spec
      let x₂ ← (simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u)
      pure (some (cf x₁, cf x₂))] =
      ∑' σ, Pr[= σ | generateSeed spec qb js] *
        (Pr[= (some s : Option (Fin (qb i + 1))) |
          cf <$> (simulateQ seededOracle main).run' σ] *
         Pr[= (some s : Option (Fin (qb i + 1))) |
          cf <$> (simulateQ seededOracle main).run' (σ.takeAtIndex i ↑s)]) := by
  rw [probOutput_bind_eq_tsum]
  simp_rw [probOutput_liftComp]
  congr 1; ext σ; congr 1
  have hcomp : (do let x₁ ← (simulateQ seededOracle main).run' σ
                   let u ← liftComp ($ᵗ spec.Range i) spec
                   let x₂ ← (simulateQ seededOracle main).run'
                     ((σ.takeAtIndex i ↑s).addValue i u)
                   pure (some (cf x₁, cf x₂)) : OracleComp spec _) =
      some <$> (do let x₁ ← (simulateQ seededOracle main).run' σ
                   let x₂ ← (liftComp ($ᵗ spec.Range i) spec >>= fun u =>
                     (simulateQ seededOracle main).run'
                       ((σ.takeAtIndex i ↑s).addValue i u))
                   pure (cf x₁, cf x₂)) := by
    simp only [monad_norm, Function.comp]
  rw [hcomp, probOutput_some_map_some, probOutput_bind_bind_prod_mk_eq_mul']
  congr 1
  have h := seededOracle.evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue
    (σ.takeAtIndex i ↑s) i main
  exact congrFun (congrArg DFunLike.coe (by simp only [evalDist_map, h])) (some s)

omit [spec.DecidableEq] in
private lemma sq_tsum_seed_weighted_le_tsum_factored (s : Fin (qb i + 1)) :
    (∑' σ, Pr[= σ | generateSeed spec qb js] *
      Pr[= (some s : Option (Fin (qb i + 1))) |
        cf <$> (simulateQ seededOracle main).run' σ]) ^ 2 ≤
    ∑' σ, Pr[= σ | generateSeed spec qb js] *
      (Pr[= (some s : Option (Fin (qb i + 1))) |
        cf <$> (simulateQ seededOracle main).run' σ] *
       Pr[= (some s : Option (Fin (qb i + 1))) |
        cf <$> (simulateQ seededOracle main).run' (σ.takeAtIndex i ↑s)]) := by
  have hMainTake : ∑' σ, Pr[= σ | generateSeed spec qb js] *
      Pr[= (some s : Option (Fin (qb i + 1))) |
        cf <$> (simulateQ seededOracle main).run' (σ.takeAtIndex i ↑s)] =
      Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] := by
    have hTake :=
      seededOracle.probOutput_generateSeed_bind_map_simulateQ_takeAtIndex
        (qc := qb) (js := js) (i₀ := i) (k := ↑s) (oa := main) (f := cf)
        (y := (some s : Option (Fin (qb i + 1))))
    rw [probOutput_bind_eq_tsum] at hTake
    simpa only [probOutput_liftComp] using hTake
  have hEq : ∑' σ, Pr[= σ | generateSeed spec qb js] *
      Pr[= (some s : Option (Fin (qb i + 1))) |
        cf <$> (simulateQ seededOracle main).run' σ] =
    ∑' σ, Pr[= σ | generateSeed spec qb js] *
      Pr[= (some s : Option (Fin (qb i + 1))) |
        cf <$> (simulateQ seededOracle main).run' (σ.takeAtIndex i ↑s)] := by
    rw [(probOutput_main_eq_tsum_seed_weighted main qb js i cf s).symm, hMainTake]
  set w : QuerySeed spec → ℝ≥0∞ := fun σ => Pr[= σ | generateSeed spec qb js]
  set Q : QuerySeed spec → ℝ≥0∞ := fun σ =>
    Pr[= (some s : Option (Fin (qb i + 1))) |
      cf <$> (simulateQ seededOracle main).run' (σ.takeAtIndex i ↑s)]
  have hw : ∑' σ, w σ ≤ 1 := tsum_probOutput_le_one
  have hEq2 : ∑' σ, w σ * Q σ ^ 2 =
      ∑' σ, w σ *
        (Pr[= (some s : Option (Fin (qb i + 1))) |
          cf <$> (simulateQ seededOracle main).run' σ] * Q σ) := by
    simp only [sq, Q, w]
    have hSim : ∀ σ', (simulateQ seededOracle (cf <$> main :
        OracleComp spec (Option (Fin (qb i + 1))))).run' σ' =
        cf <$> (simulateQ seededOracle main).run' σ' := by
      intro σ'
      simp only [simulateQ_map]
      change Prod.fst <$> (Prod.map cf id <$> (simulateQ seededOracle main).run σ') =
        cf <$> (Prod.fst <$> (simulateQ seededOracle main).run σ')
      simp [Functor.map_map]
    have hWF := seededOracle.tsum_probOutput_generateSeed_weight_takeAtIndex
      qb js i (↑s) (cf <$> main : OracleComp spec (Option (Fin (qb i + 1))))
      (some s : Option (Fin (qb i + 1)))
      (fun τ => Pr[= (some s : Option (Fin (qb i + 1))) |
        (simulateQ seededOracle (cf <$> main :
          OracleComp spec (Option (Fin (qb i + 1))))).run' τ])
    simp_rw [hSim] at hWF
    exact hWF.symm.trans (by congr 1; ext σ; congr 1; exact mul_comm _ _)
  calc _ = (∑' σ, w σ * Q σ) ^ 2 := by rw [hEq]
    _ ≤ ∑' σ, w σ * Q σ ^ 2 := ENNReal.sq_tsum_le_tsum_sq w Q hw
    _ = _ := hEq2

omit [spec.DecidableEq] in
private lemma sq_probOutput_main_le_noGuardComp (s : Fin (qb i + 1)) :
    let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
    let noGuardComp :
        OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) := do
      let seed ← liftComp (generateSeed spec qb js) spec
      let x₁ ← (simulateQ seededOracle main).run' seed
      let u ← liftComp ($ᵗ spec.Range i) spec
      let seed' := (seed.takeAtIndex i ↑s).addValue i u
      let x₂ ← (simulateQ seededOracle main).run' seed'
      return some (cf x₁, cf x₂)
    Pr[= s | cf <$> main] ^ 2 ≤ Pr[= z | noGuardComp] := by
  simp only
  rw [probOutput_main_eq_tsum_seed_weighted main qb js i cf s]
  exact (sq_tsum_seed_weighted_le_tsum_factored main qb js i cf s).trans_eq
    (probOutput_noGuardComp_eq_tsum_factored main qb js i cf s).symm

omit [∀ i, SampleableType (spec.Range i)] [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] in
private lemma probOutput_noGuardComp_value_step_le_add_aux (s : Fin (qb i + 1))
    (seed : QuerySeed spec) (x₁ : α) (hx₁ : cf x₁ = some s) (u : spec.Range i) :
    let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
    Pr[= z | (fun a ↦ some (some s, cf a.1)) <$>
        (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u)] ≤
      Pr[= z | (fun r ↦ Option.map (Prod.map cf cf) r) <$>
          (if (seed i)[↑s]? = some u then pure none
          else do
            let a₂ ← (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u)
            if cf a₂.1 = some s then pure (some (x₁, a₂.1)) else pure none :
            OracleComp spec (Option (α × α)))] +
        Pr[= (some s : Option (Fin (qb i + 1))) |
          (if (seed i)[↑s]? = some u then pure (some s) else pure none :
            OracleComp spec (Option (Fin (qb i + 1))))] := by
  intro z
  by_cases hu' : (seed i)[↑s]? = some u
  · refine le_trans probOutput_le_one ?_
    simp [hu']
  · refine le_trans ?_ (le_add_of_nonneg_right zero_le)
    have hmono :
        Pr[= z | (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u) >>=
            (fun x => pure (some (some s, cf x.1)))] ≤
        Pr[= z | (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u) >>=
            (fun x => (fun r ↦ Option.map (Prod.map cf cf) r) <$>
              (if cf x.1 = some s then pure (some (x₁, x.1)) else pure none))] := by
      refine probOutput_bind_mono fun x hx => ?_
      by_cases hxs : cf x.1 = some s
      · simp [hxs, hx₁, z]
      · have hxs' : (some s : Option (Fin (qb i + 1))) ≠ cf x.1 := by simpa [eq_comm] using hxs
        simp [hxs, hxs', z]
    rw [if_neg (by simpa using hu')]
    simpa [monad_norm] using hmono

omit [unifSpec ˡ⊂ₒ spec] in
private lemma probOutput_noGuardComp_step_le_add_aux (s : Fin (qb i + 1))
    (seed : QuerySeed spec) (x₁ : α) :
    let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
    Pr[= z | do
        let u ← liftM ($ᵗ spec.Range i)
        (fun a : α × QuerySeed spec ↦ some (cf x₁, cf a.1)) <$>
          (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u)] ≤
      Pr[= z | (fun r ↦ Option.map (Prod.map cf cf) r) <$>
          (match cf x₁ with
            | none => pure none
            | some s => do
              let u ← liftM ($ᵗ spec.Range i)
              if (seed i)[↑s]? = some u then pure none
                else do
                  let a₂ ← (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u)
                  if cf a₂.1 = some s then pure (some (x₁, a₂.1)) else pure none :
            OracleComp spec (Option (α × α)))] +
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let u ← liftM ($ᵗ spec.Range i)
          (if (seed i)[↑s]? = some u then pure (cf x₁) else pure none :
            OracleComp spec (Option (Fin (qb i + 1))))] := by
  intro z
  cases hca : cf x₁ with
  | none =>
      have hL : Pr[= z | do
          let u ← liftM ($ᵗ spec.Range i)
          (fun a₂ : α × QuerySeed spec ↦ some (none, cf a₂.1)) <$>
            (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u)] = 0 := by
        rw [probOutput_eq_zero_iff]
        simp [support_bind, support_map, z]
      simp only [z]
      rw [hL]
      simp
  | some t =>
      by_cases hts : t = s
      · subst hts
        simp only [map_bind, z]
        refine probOutput_bind_congr_le_add
          (mx := (liftComp ($ᵗ spec.Range i) spec : OracleComp spec (spec.Range i)))
          (y := z) (z₁ := z) (z₂ := (some t : Option (Fin (qb i + 1)))) fun u _ => ?_
        simpa [z] using probOutput_noGuardComp_value_step_le_add_aux
          (main := main) (qb := qb) (i := i) (cf := cf) t seed x₁ hca u
      · have hts' : (some t : Option (Fin (qb i + 1))) ≠ some s := by simpa using hts
        have hzero : Pr[= z | do
            let u ← liftM ($ᵗ spec.Range i)
            (fun a₂ : α × QuerySeed spec ↦ some (some t, cf a₂.1)) <$>
              (simulateQ seededOracle main).run ((seed.takeAtIndex i ↑s).addValue i u)] = 0 := by
          rw [probOutput_eq_zero_iff]
          simp [support_bind, support_map, z, hts']
        simp only [z]
        rw [hzero]
        exact zero_le

omit [unifSpec ˡ⊂ₒ spec] in
private lemma probEvent_seededFork_pair_eq_probOutput_map_aux (s : Fin (qb i + 1)) :
    let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
    Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) | seededFork main qb js i cf] =
      Pr[= z | (fun r => r.map (Prod.map cf cf)) <$> seededFork main qb js i cf] := by
  intro z
  calc
    Pr[ fun r => r.map (Prod.map cf cf) = some (some s, some s) | seededFork main qb js i cf]
      = Pr[ fun r => (fun r => r.map (Prod.map cf cf)) r = z | seededFork main qb js i cf] := by
          simp [z]
    _ = Pr[ fun x => x = z | (fun r => r.map (Prod.map cf cf)) <$> seededFork main qb js i cf] := by
          simpa [Function.comp] using (probEvent_map (mx := seededFork main qb js i cf)
            (f := fun r => r.map (Prod.map cf cf)) (q := fun x => x = z)).symm
    _ = Pr[= z | (fun r => r.map (Prod.map cf cf)) <$> seededFork main qb js i cf] := by
          simp [probEvent_eq_eq_probOutput]

omit [unifSpec ˡ⊂ₒ spec] in
private lemma probOutput_noGuardComp_le_seededFork_add_collision_aux (s : Fin (qb i + 1)) :
    let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
    Pr[= z | do
        let seed ← liftComp (generateSeed spec qb js) spec
        let x₁ ← (simulateQ seededOracle main).run' seed
        let u ← liftComp ($ᵗ spec.Range i) spec
        let x₂ ← (simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u)
        return some (cf x₁, cf x₂)] ≤
      Pr[= z | (fun r => r.map (Prod.map cf cf)) <$> seededFork main qb js i cf] +
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let seed ← liftComp (generateSeed spec qb js) spec
          let x₁ ← (simulateQ seededOracle main).run' seed
          let u ← liftComp ($ᵗ spec.Range i) spec
          if (seed i)[↑s]? = some u then return cf x₁ else return none] := by
  intro z
  simp only [liftComp_eq_liftM, StateT.run'_eq, bind_pure_comp, Functor.map_map, bind_map_left,
    seededFork, Fin.getElem?_fin, map_bind, z]
  refine probOutput_bind_congr_le_add
    (mx := (liftComp (generateSeed spec qb js) spec : OracleComp spec (QuerySeed spec)))
    (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1)))) fun seed _ => ?_
  refine probOutput_bind_congr_le_add
    (mx := ((simulateQ seededOracle main).run seed : OracleComp spec (α × QuerySeed spec)))
    (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1)))) fun a _ => ?_
  exact probOutput_noGuardComp_step_le_add_aux
    (main := main) (qb := qb) (i := i) (cf := cf) s seed a.1

/-- Key bound of the forking lemma: the probability that both runs succeed with fork point `s`
is at least `Pr[cf(main) = s]² - Pr[cf(main) = s] / |Range i|`. -/
theorem le_probOutput_seededFork (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h
      ≤ Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) |
            seededFork main qb js i cf] := by
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  rw [probEvent_seededFork_fst_eq_probEvent_pair
        (main := main) (qb := qb) (js := js) (i := i) (cf := cf),
    probEvent_seededFork_pair_eq_probOutput_map_aux
        (main := main) (qb := qb) (js := js) (i := i) (cf := cf) s]
  let collisionComp : OracleComp spec (Option (Fin (qb i + 1))) := do
    let seed ← liftComp (generateSeed spec qb js) spec
    let x₁ ← (simulateQ seededOracle main).run' seed
    let u ← liftComp ($ᵗ spec.Range i) spec
    if (seed i)[↑s]? = some u then return cf x₁ else return none
  have hCollision : Pr[= (some s : Option (Fin (qb i + 1))) | collisionComp] ≤
      Pr[= s | cf <$> main] / h := by
    simpa [h, collisionComp] using
      probOutput_collision_le_main_div (main := main) (qb := qb) (js := js) (i := i) (cf := cf) s
  refine le_trans (tsub_le_tsub_left hCollision _) (le_trans (tsub_le_tsub_right
    (sq_probOutput_main_le_noGuardComp (main := main) (qb := qb) (js := js) (i := i) (cf := cf) s)
    (Pr[= (some s : Option (Fin (qb i + 1))) | collisionComp])) ?_)
  exact tsub_le_iff_right.2 (probOutput_noGuardComp_le_seededFork_add_collision_aux
    (main := main) (qb := qb) (js := js) (i := i) (cf := cf) s)

omit [unifSpec ˡ⊂ₒ spec] in
/-- Sum of disjoint fork-success events is at most the total `some` probability. -/
private lemma sum_probEvent_fork_le_tsum_some :
    ∑ s : Fin (qb i + 1),
      Pr[ fun r ↦ r.map (cf ∘ Prod.fst) = some (some s) | seededFork main qb js i cf]
    ≤ ∑' (p : α × α), Pr[= some p | seededFork main qb js i cf] := by
  simp_rw [probEvent_eq_tsum_ite]
  have hsplit : ∀ s : Fin (qb i + 1),
      (∑' (r : Option (α × α)),
        if r.map (cf ∘ Prod.fst) = some (some s) then Pr[= r | seededFork main qb js i cf] else 0)
      = ∑' (p : α × α), if cf p.1 = some s then
          Pr[= some p | seededFork main qb js i cf] else 0 := fun s ↦ by
    simpa only [Option.map, comp_apply, reduceCtorEq, ite_false, zero_add, Option.some.injEq] using
      tsum_option (fun r : Option (α × α) ↦
        if r.map (cf ∘ Prod.fst) = some (some s) then
          Pr[= r | seededFork main qb js i cf] else 0) ENNReal.summable
  simp_rw [hsplit]
  rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  rw [tsum_fintype (L := .unconditional _)]
  rcases hcf : cf p.1 with _ | s₀
  · simp
  · rw [Finset.sum_eq_single s₀ (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
    simp

omit [DecidableEq ι] [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq]
  [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] in
/-- The standard forking-lemma precondition is itself a valid probability bound. -/
theorem seededFork_precondition_le_one :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤ 1 :=
  ENNReal.mul_tsub_div_le_one (sum_probOutput_some_le_one (mx := cf <$> main)) (by simp)

/-- Main forking lemma: the failure probability is bounded by `1 - acc * (acc / q - 1/h)`. -/
theorem probOutput_none_seededFork_le :
    let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.Range i)
    let q := qb i + 1
    Pr[= none | seededFork main qb js i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  simp only
  set ps : Fin (qb i + 1) → ℝ≥0∞ := fun s ↦ Pr[= (some s : Option _) | cf <$> main]
  set acc := ∑ s, ps s
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hacc_ne_top : acc ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top
      (sum_probOutput_some_le_one (mx := cf <$> main) (α := Fin (qb i + 1)))
  have htotal := probOutput_none_add_tsum_some (mx := seededFork main qb js i cf)
  rw [probFailure_of_liftM_PMF, tsub_zero] at htotal
  have hne_top : (∑' p, Pr[= some p | seededFork main qb js i cf]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (htotal ▸ le_add_self)
  calc Pr[= none | seededFork main qb js i cf]
    _ = 1 - ∑' p, Pr[= some p | seededFork main qb js i cf] :=
        ENNReal.eq_sub_of_add_eq hne_top htotal
    _ ≤ 1 - ∑ s, Pr[ fun r => r.map (cf ∘ Prod.fst) = some (some s) |
            seededFork main qb js i cf] :=
        tsub_le_tsub_left (sum_probEvent_fork_le_tsum_some main qb js i cf) 1
    _ ≤ 1 - ∑ s, (ps s ^ 2 - ps s / h) :=
        tsub_le_tsub_left (Finset.sum_le_sum fun s _ ↦
          le_probOutput_seededFork main qb js i cf s) 1
    _ ≤ 1 - acc * (acc / ↑(qb i + 1) - h⁻¹) := by
        apply tsub_le_tsub_left _ 1
        have hcs := ENNReal.sq_sum_le_card_mul_sum_sq
          (Finset.univ : Finset (Fin (qb i + 1))) ps
        simp only [Finset.card_univ, Fintype.card_fin] at hcs
        calc acc * (acc / ↑(qb i + 1) - h⁻¹)
          _ = acc * (acc / ↑(qb i + 1)) - acc * h⁻¹ :=
              ENNReal.mul_sub (fun _ _ ↦ hacc_ne_top)
          _ = acc ^ 2 / ↑(qb i + 1) - acc / h := by
              rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, sq, div_eq_mul_inv]
          _ ≤ (∑ s, ps s ^ 2) - acc / h := by
              gcongr; rw [div_eq_mul_inv]
              have hn : ((qb i + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
              calc acc ^ 2 * (↑(qb i + 1))⁻¹
                  _ ≤ (↑(qb i + 1) * ∑ s, ps s ^ 2) * (↑(qb i + 1))⁻¹ := by gcongr
                  _ = ∑ s, ps s ^ 2 := by
                      rw [mul_assoc, mul_comm (∑ s, ps s ^ 2) _, ← mul_assoc,
                        ENNReal.mul_inv_cancel hn (by simp), one_mul]
          _ ≤ (∑ s, ps s ^ 2) - ∑ s, ps s / h := by
              gcongr; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
          _ ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
              rw [tsub_le_iff_right]
              calc ∑ s, ps s ^ 2
                ≤ ∑ s, ((ps s ^ 2 - ps s / h) + ps s / h) :=
                    Finset.sum_le_sum fun s _ ↦ le_tsub_add
                _ = ∑ s, (ps s ^ 2 - ps s / h) + ∑ s, ps s / h :=
                    Finset.sum_add_distrib

/-- Forking-lemma lower bound, packaged directly as the success-event probability. -/
theorem le_probEvent_isSome_seededFork :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr[ fun r : Option (α × α) => r.isSome | seededFork main qb js i cf] := by
  rw [probEvent_isSome_eq_one_sub_probOutput_none (mx := seededFork main qb js i cf)]
  have hpre_le_one := seededFork_precondition_le_one (main := main) (qb := qb) (i := i) (cf := cf)
  exact (ENNReal.le_sub_iff_add_le_left
      (ne_top_of_le_ne_top one_ne_top probOutput_le_one) probOutput_le_one).2
    ((ENNReal.le_sub_iff_add_le_right (ne_top_of_le_ne_top one_ne_top hpre_le_one) hpre_le_one).1
      (probOutput_none_seededFork_le (main := main) (qb := qb) (js := js) (i := i) (cf := cf)))

/-- Bellare-Neven seeded forking bound in its canonical `acc² / q − acc / h` shape, where
`acc = ∑ₛ Pr[= some s | cf <$> main]`, `q = qb i + 1`, and `h = |spec.Range i|`.

This is the aggregated bound that appears as Lemma 1 of Bellare-Neven (CCS'06): summing the
per-index lower bound over all fork points and applying Cauchy-Schwarz reshapes the product
form delivered by `le_probEvent_isSome_seededFork` into the familiar ratio form. Algebraically
the two statements are equal (modulo `ENNReal.mul_sub` under the finiteness of `acc`); this
lemma exposes the ratio form as a public API so that downstream callers can match the
textbook presentation directly. -/
theorem le_probEvent_isSome_seededFork_sq :
    ((∑ s, Pr[= some s | cf <$> main]) ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞)
        - (∑ s, Pr[= some s | cf <$> main]) /
            ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞))
      ≤ Pr[ fun r : Option (α × α) => r.isSome | seededFork main qb js i cf] := by
  set acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main] with hacc_eq
  set h : ℝ≥0∞ := ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞)
  have hacc_ne_top : acc ≠ ⊤ := ne_top_of_le_ne_top one_ne_top
    (hacc_eq ▸ sum_probOutput_some_le_one (mx := cf <$> main) (α := Fin (qb i + 1)))
  calc acc ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞) - acc / h
    _ = acc * (acc / ((qb i + 1 : ℕ) : ℝ≥0∞) - h⁻¹) := by
        grind [ENNReal.mul_sub, sq, mul_div_assoc, div_eq_mul_inv]
    _ ≤ Pr[ fun r : Option (α × α) => r.isSome | seededFork main qb js i cf] :=
        le_probEvent_isSome_seededFork
          (main := main) (qb := qb) (js := js) (i := i) (cf := cf)

end OracleComp
