/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Generating Random Seeds for Oracle Queries

This file defines `generateSeed spec qc js`, which produces a random `QuerySeed` for
oracle specification `spec`, seeding `qc j` values for each oracle `j ∈ js`.

The definition is recursive on the list `js`, making it easy to prove properties by induction.
-/

open OracleSpec OracleComp

namespace OracleComp

/-- Generate a `QuerySeed` uniformly at random. For each oracle `j ∈ js`, generates `qc j`
uniform random values of type `spec.Range j` using `SampleableType`. -/
def generateSeed {ι} [DecidableEq ι] (spec : OracleSpec ι)
    [∀ t : spec.Domain, SampleableType (spec.Range t)]
    (qc : ι → ℕ) : List ι → ProbComp (OracleSpec.QuerySeed spec)
  | [] => return ∅
  | j :: js => do
    let xs ← replicate (qc j) ($ᵗ spec.Range j)
    let rest ← generateSeed spec qc js
    return rest.addValues xs

section lemmas

variable {ι} [DecidableEq ι] (spec : OracleSpec ι)
  [∀ t : spec.Domain, SampleableType (spec.Range t)]
  (qc : ι → ℕ) (j : ι) (js : List ι)

@[simp]
lemma generateSeed_nil : generateSeed spec qc [] = return ∅ := rfl

@[simp]
lemma generateSeed_cons : generateSeed spec qc (j :: js) = do
    let xs ← replicate (qc j) ($ᵗ spec.Range j)
    let rest ← generateSeed spec qc js
    return rest.addValues xs := rfl

@[simp]
lemma generateSeed_zero :
    generateSeed spec 0 js = (return ∅ : ProbComp (OracleSpec.QuerySeed spec)) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [generateSeed, ih]

-- TODO: the following lemmas were removed during remediation.
-- They characterise the support and output probabilities of `generateSeed`.
-- Needed for seeded-oracle proofs (e.g. `Fork.lean`).

-- @[simp] lemma support_generateSeed : (generateSeed spec qc js).support =
--     {seed | ∀ i, (seed i).length = qc i * js.count i} := by
--   sorry

-- @[simp] lemma finSupport_generateSeed_ne_empty [DecidableEq spec.QuerySeed] :
--     (generateSeed spec qc js).finSupport ≠ ∅ := by
--   sorry

-- lemma probOutput_generateSeed [spec.FiniteRange] (seed : QuerySeed spec)
--     (h : seed ∈ (generateSeed spec qc js).support) : [= seed | generateSeed spec qc js] =
--     1 / (js.map (λ j ↦ (Fintype.card (spec.Range j)) ^ qc j)).prod := by
--   sorry

-- lemma probOutput_generateSeed' [spec.FiniteRange]
--     [DecidableEq spec.QuerySeed] (seed : QuerySeed spec)
--     (h : seed ∈ (generateSeed spec qc js).support) : [= seed | generateSeed spec qc js] =
--     ((generateSeed spec qc js).finSupport.card : ℝ≥0∞)⁻¹ := by
--   sorry

end lemmas

end OracleComp
