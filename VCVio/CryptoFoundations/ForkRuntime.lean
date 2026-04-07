/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.Fork

/-!
# Runtime Accounting for Forking

This file complements `VCVio.CryptoFoundations.Fork` with query-cost theorems for the fork
wrapper itself.

The core seeded replay theorem in `Fork.lean` isolates the live-oracle cost of the seeded fork
core. Here we add the missing wrapper side: the query cost of sampling the initial seed and the
fresh replacement value. The result is a quantitative statement about the total expected query
work of the fork wrapper, decomposed into:

- expected query cost of `generateSeed`;
- expected query cost of the fresh replacement sample at the forked family;
- expected live-query count of the seeded replay core.

The sampling side is parameterized by a family `sampleCost` so the theorems work uniformly for
nontrivial `SampleableType` instances whose sampling cost is not definitionally `1`.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}

section generateSeedRuntime

variable [∀ i, SampleableType (spec.Range i)]

/-- Unit-cost instrumentation of a `ProbComp`, viewed as an `AddWriterT` computation whose cost
tracks the number of calls to the underlying uniform-selection oracle. -/
abbrev probCompUnitQueryRun {β : Type} (oa : ProbComp β) :
    AddWriterT ℕ ProbComp β :=
  simulateQ ((QueryRuntime.oracleCompRuntime (spec := unifSpec)).withUnitCost.impl) oa

private theorem queryBoundedAboveBy_replicate_probComp
    {β : Type} (oa : ProbComp β) {k : ℕ}
    (h : AddWriterT.QueryBoundedAboveBy (probCompUnitQueryRun oa) k) :
    ∀ n : ℕ, AddWriterT.QueryBoundedAboveBy (probCompUnitQueryRun (oa.replicate n)) (n * k) := by
  intro n
  induction n with
  | zero =>
      simpa using (AddWriterT.queryBoundedAboveBy_pure ([] : List β))
  | succ n ih =>
      simpa [probCompUnitQueryRun, OracleComp.replicate_succ_bind, simulateQ_bind, simulateQ_pure,
        simulateQ_map, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (AddWriterT.queryBoundedAboveBy_bind (n₁ := k) (n₂ := n * k)
          (oa := probCompUnitQueryRun oa)
          (f := fun a => List.cons a <$> probCompUnitQueryRun (oa.replicate n))
          h
          (fun a => AddWriterT.queryBoundedAboveBy_map (List.cons a) ih))

private theorem queryBoundedBelowBy_replicate_probComp
    {β : Type} (oa : ProbComp β) {k : ℕ}
    (h : AddWriterT.QueryBoundedBelowBy (probCompUnitQueryRun oa) k) :
    ∀ n : ℕ, AddWriterT.QueryBoundedBelowBy (probCompUnitQueryRun (oa.replicate n)) (n * k) := by
  intro n
  induction n with
  | zero =>
      simpa using (AddWriterT.queryBoundedBelowBy_pure ([] : List β))
  | succ n ih =>
      simpa [probCompUnitQueryRun, OracleComp.replicate_succ_bind, simulateQ_bind, simulateQ_pure,
        simulateQ_map, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (AddWriterT.queryBoundedBelowBy_bind (n₁ := k) (n₂ := n * k)
          (oa := probCompUnitQueryRun oa)
          (f := fun a => List.cons a <$> probCompUnitQueryRun (oa.replicate n))
          h
          (fun a => AddWriterT.queryBoundedBelowBy_map (List.cons a) ih))

private theorem generateSeed_queryBoundedAboveBy
    (qc : ι → ℕ) (js : List ι) (sampleCost : ι → ℕ)
    (hSample :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j)) :
    AddWriterT.QueryBoundedAboveBy
      (probCompUnitQueryRun (generateSeed spec qc js))
      ((js.map fun j => qc j * sampleCost j).sum) := by
  induction js with
  | nil =>
      simpa [probCompUnitQueryRun] using
        (AddWriterT.queryBoundedAboveBy_pure (∅ : QuerySeed spec))
  | cons j js ih =>
      simpa [probCompUnitQueryRun, OracleComp.generateSeed_cons, simulateQ_bind, simulateQ_pure,
        simulateQ_map, List.sum_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (AddWriterT.queryBoundedAboveBy_bind
          (n₁ := qc j * sampleCost j)
          (n₂ := (js.map fun j => qc j * sampleCost j).sum)
          (oa := probCompUnitQueryRun (replicate (qc j) ($ᵗ spec.Range j)))
          (f := fun xs =>
            (fun rest : QuerySeed spec => rest.prependValues xs) <$>
              probCompUnitQueryRun (generateSeed spec qc js))
          (queryBoundedAboveBy_replicate_probComp ($ᵗ spec.Range j) (hSample j) (qc j))
          (fun xs => AddWriterT.queryBoundedAboveBy_map (fun rest => rest.prependValues xs) ih))

private theorem generateSeed_queryBoundedBelowBy
    (qc : ι → ℕ) (js : List ι) (sampleCost : ι → ℕ)
    (hSample :
      ∀ j, AddWriterT.QueryBoundedBelowBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j)) :
    AddWriterT.QueryBoundedBelowBy
      (probCompUnitQueryRun (generateSeed spec qc js))
      ((js.map fun j => qc j * sampleCost j).sum) := by
  induction js with
  | nil =>
      simpa [probCompUnitQueryRun] using
        (AddWriterT.queryBoundedBelowBy_pure (∅ : QuerySeed spec))
  | cons j js ih =>
      simpa [probCompUnitQueryRun, OracleComp.generateSeed_cons, simulateQ_bind, simulateQ_pure,
        simulateQ_map, List.sum_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (AddWriterT.queryBoundedBelowBy_bind
          (n₁ := qc j * sampleCost j)
          (n₂ := (js.map fun j => qc j * sampleCost j).sum)
          (oa := probCompUnitQueryRun (replicate (qc j) ($ᵗ spec.Range j)))
          (f := fun xs =>
            (fun rest : QuerySeed spec => rest.prependValues xs) <$>
              probCompUnitQueryRun (generateSeed spec qc js))
          (queryBoundedBelowBy_replicate_probComp ($ᵗ spec.Range j) (hSample j) (qc j))
          (fun xs => AddWriterT.queryBoundedBelowBy_map (fun rest => rest.prependValues xs) ih))

/-- Expected query count of `generateSeed spec qc js`, measured in the unit-cost `ProbComp`
runtime, obtained by summing the per-sample query costs over the seed schedule `js`. -/
theorem generateSeed_expectedQueryCount_eq_sum_sampleCost
    (qc : ι → ℕ) (js : List ι) (sampleCost : ι → ℕ)
    (hSampleUpper :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hSampleLower :
      ∀ j, AddWriterT.QueryBoundedBelowBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j)) :
    AddWriterT.expectedCostNat (probCompUnitQueryRun (generateSeed spec qc js)) =
      ((js.map fun j => qc j * sampleCost j).sum : ENNReal) := by
  apply le_antisymm
  · exact AddWriterT.expectedCostNat_le_of_queryBoundedAboveBy
      (generateSeed_queryBoundedAboveBy (spec := spec) qc js sampleCost hSampleUpper)
  · exact AddWriterT.expectedCostNat_ge_of_queryBoundedBelowBy
      (generateSeed_queryBoundedBelowBy (spec := spec) qc js sampleCost hSampleLower)

end generateSeedRuntime

section forkRuntime

variable [∀ i, SampleableType (spec.Range i)]
variable [spec.DecidableEq]
variable [Finite ι] [spec.Fintype] [spec.Inhabited]

/-- Expected query work of the fork wrapper, split into wrapper sampling and seeded-core live
queries.

The first two summands account for the initial seed generation and the one fresh replacement
sample in the unit-cost `ProbComp` runtime. The final summand is the expected live-oracle query
count of the seeded replay core, averaged over the sampled seed and replacement value. -/
noncomputable def forkExpectedWrapperAndLiveQueries
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : ENNReal :=
  AddWriterT.expectedCostNat (probCompUnitQueryRun (generateSeed spec qb js)) +
    AddWriterT.expectedCostNat (probCompUnitQueryRun ($ᵗ spec.Range i : ProbComp (spec.Range i))) +
    wp (generateSeed spec qb js)
      (fun seed =>
        wp ($ᵗ spec.Range i)
          (fun u =>
            expectedCost
              (forkWithSeedValue main qb i cf seed u)
              CostModel.unit
              (fun n : ℕ ↦ (n : ENNReal))))

/-- Total expected query work of the fork wrapper is bounded by:

- the seed-generation cost, computed from the seed schedule `js`;
- the cost of the one fresh replacement sample at the forked family `i`;
- the live-query budget `qb i` of the seeded replay core.

This theorem is the runtime analogue of the seeded fork-core query bound:
it combines wrapper sampling cost with the live-oracle traffic analyzed in
[`wp_generateSeed_uniform_forkWithSeedValue_expectedQueryCount_le`]. -/
theorem forkExpectedWrapperAndLiveQueries_le
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (sampleCost : ι → ℕ)
    (hSampleUpper :
      ∀ j, AddWriterT.QueryBoundedAboveBy
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main qb)
    (hjs : SeedListCovers qb js) :
    forkExpectedWrapperAndLiveQueries main qb js i cf ≤
      ((js.map fun j => qb j * sampleCost j).sum + sampleCost i + qb i : ENNReal) := by
  unfold forkExpectedWrapperAndLiveQueries
  have hgen_le := AddWriterT.expectedCostNat_le_of_queryBoundedAboveBy
    (generateSeed_queryBoundedAboveBy (spec := spec) qb js sampleCost hSampleUpper)
  have hi_le := AddWriterT.expectedCostNat_le_of_queryBoundedAboveBy (hSampleUpper i)
  have hcore :=
    wp_generateSeed_uniform_forkWithSeedValue_expectedQueryCount_le
      (main := main) (qb := qb) (js := js) (i := i) (cf := cf) hmain hjs
  exact add_le_add (add_le_add hgen_le hi_le) hcore

end forkRuntime

end OracleComp
