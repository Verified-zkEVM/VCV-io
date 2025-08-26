/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
-- import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.UniformSelect
import Mathlib.Data.List.Basic
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle spec` for counting the number of queries made
while running the computation. The count is represented by a type `queryCount spec`,
which

-/

-- open OracleSpec BigOperators ENNReal

-- namespace OracleComp

-- variable {ι : Type} [DecidableEq ι]

-- def generateSeedT (spec : OracleSpec ι) [∀ i, SampleableType (spec.range i)]
--     (qc : ι → ℕ) (activeOracles : List ι) :
--     StateT (QuerySeed spec) ProbComp Unit :=
--   for j in activeOracles do
--     modify (QuerySeed.addValues (← ($ᵗ spec.range j).replicate (qc j)))

-- /-- Generate a `QuerySeed` uniformly at random for some set of oracles `spec : OracleSpec ι`,
-- with `qc i : ℕ` values seeded for each index `i ∈ js`. Note that `js` is allowed
-- to contain duplicates, but usually wouldn't in practice. -/
-- def generateSeed (spec : OracleSpec ι) [∀ i, SampleableType (spec.range i)]
--     (qc : ι → ℕ) (js : List ι) : ProbComp (QuerySeed spec) := do
--   let mut seed : QuerySeed spec := ∅
--   for j in js do
--     seed := seed.addValues (← ($ᵗ spec.range j).replicate (qc j))
--   return seed

-- def generateSingleSeed (spec : OracleSpec ι) (i : ι) [SampleableType (spec.range i)]
--     (n : ℕ) : ProbComp (QuerySeed spec) :=
--   QuerySeed.ofList <$> ($ᵗ spec.range i).replicate n

--   -- Prod.snd <$> (generateSeedT spec qc activeOracles).run ∅
-- -- variable (spec : OracleSpec ι) [∀ i, SampleableType (spec.range i)]
-- --   (qc : ι → ℕ) (j : ι) (js : List ι)

-- -- lemma probOutput_generateSeed (spec : OracleSpec ι) [∀ i, SampleableType (spec.range i)]
-- --     (qc : ι → ℕ) (js : List ι) (seed : QuerySeed spec)
-- --     (h : seed ∈ (generateSeed spec qc js).support) :
-- --     [= seed | generateSeed spec qc js] =
-- --       1 / (js.map (λ j ↦ (Fintype.card (spec.range j)) ^ qc j)).prod :=
-- --   sorry

-- -- def generateSeed (spec : OracleSpec ι) [∀ i, SampleableType (spec.range i)]
-- --     (qc : ι → ℕ) (activeOracles : List ι) : ProbComp (QuerySeed spec) :=
-- --   match activeOracles with
-- --   | [] => return ∅
-- --   | j :: js => QuerySeed.addValues <$> generateSeed spec qc js <*>
-- --       (Array.toList <$> Vector.toArray <$> replicate ($ᵗ (spec.range j)) (qc j))

-- variable (spec : OracleSpec ι) [∀ i, SampleableType (spec.range i)]
--   (qc : ι → ℕ) (j : ι) (js : List ι)

-- @[simp]
-- lemma generateSeed_nil : generateSeed spec qc [] = return ∅ := rfl

-- @[simp]
-- lemma generateSeed_cons : generateSeed spec qc (j :: js) =
--     ($ᵗ (spec.range j)).replicate (qc j) >>= λ xs ↦
--       generateSeed spec qc js := by
--   simp [generateSeed, map_eq_bind_pure_comp,
--     seq_eq_bind, bind_assoc]
--   sorry

-- @[simp]
-- lemma generateSeed_zero : generateSeed spec 0 js = return ∅ := by
--   induction js with | nil => rfl | cons j js h => simp [h]

-- @[simp]
-- lemma support_generateSeed : (generateSeed spec qc js).support =
--     {seed | ∀ i, (seed i).length = qc i * js.count i} := by
--   sorry
-- --   induction js with
-- --   | nil => {
-- --     simp [Set.ext_iff, DFunLike.ext_iff]
-- --     intro x
-- --     rfl
-- --   }
-- --   | cons j js h => {
-- --     simp [h, Set.ext_iff]
-- --     intro seed
-- --     refine ⟨λ h i ↦ ?_, λ h ↦ ?_⟩
-- --     · obtain ⟨seed', ⟨h1, ⟨xs, hxs⟩⟩⟩ := h
-- --       by_cases hj : i = j
-- --       · induction hj
-- --         simp [← hxs, h1, mul_add_one]
-- --       · simp [← hxs, h1, hj]
-- --     · refine ⟨seed.takeAtIndex j (qc j * js.count j), λ i ↦ ?_, ?_⟩
-- --       · by_cases hi : i = j
-- --         · induction hi
-- --           simp [h, mul_add_one]
-- --         · simp [hi, h]
-- --       · refine ⟨⟨(seed j).drop (qc j * js.count j), ?_⟩, ?_⟩
-- --         · simp [h, mul_add_one]
-- --         · simp [h]
-- --           rw [QuerySeed.addValues_eq_iff]
-- --           simp [h, mul_add_one]
-- --   }

-- @[simp]
-- lemma finSupport_generateSeed_ne_empty [DecidableEq spec.QuerySeed] :
--     (generateSeed spec qc js).finSupport ≠ ∅ := by
--   sorry

-- lemma probOutput_generateSeed [spec.FiniteRange] (seed : QuerySeed spec)
--     (h : seed ∈ (generateSeed spec qc js).support) : [= seed | generateSeed spec qc js] =
--     1 / (js.map (λ j ↦ (Fintype.card (spec.range j)) ^ qc j)).prod := by
--   revert seed
--   induction js using List.reverseRecOn with
--   | nil => {
--     -- simp at h
--     simp

--   }
--   | append_singleton j js hjs => {
--     intro seed hs
--     simp [generateSeed, List.forIn_eq_foldlM]

--     -- rw [Array.forIn_toList]
--     sorry
--   }

-- lemma probOutput_generateSeed' [spec.FiniteRange]
--     [DecidableEq spec.QuerySeed] (seed : QuerySeed spec)
--     (h : seed ∈ (generateSeed spec qc js).support) : [= seed | generateSeed spec qc js] =
--     ((generateSeed spec qc js).finSupport.card : ℝ≥0∞)⁻¹ := by
--   sorry

--   -- sorry
-- --   revert seed
-- --   induction js with
-- --   | nil => {
-- --     intro seed h
-- --     simp at h
-- --     simp [h]
-- --   }
-- --   | cons j js hjs => {
-- --     intro seed h
-- --     let rec_seed : QuerySeed spec := seed.takeAtIndex j (qc j * js.count j)
-- --     specialize hjs rec_seed _
-- --     · simp [rec_seed]
-- --       rw [support_generateSeed, Set.mem_setOf] at h
-- --       intro k
-- --       by_cases hk : k = j
-- --       · induction hk
-- --         let hk := h k
-- --         rw [List.count_cons_self, mul_add_one] at hk
-- --         simp [rec_seed, QuerySeed.takeAtIndex, hk]
-- --       · simp [rec_seed, QuerySeed.takeAtIndex, hk, h k]
-- --     · rw [generateSeed_cons]
-- --       have : seed = QuerySeed.addValues rec_seed ((seed j).drop <| qc j * js.count j) :=
-- --         funext (λ k ↦ by simp [rec_seed, QuerySeed.takeAtIndex, QuerySeed.addValues])
-- --       refine (probOutput_seq_map_eq_mul _ _ QuerySeed.addValues rec_seed
-- --         (((seed j).drop <| qc j * js.count j)) _ ?_).trans ?_
-- --       · simp
-- --         intro seed' hs' xs
-- --         simp [rec_seed]
-- --         rw [QuerySeed.eq_addValues_iff]
-- --         simp [hs']
-- --       · rw [hjs]
-- --         rw [support_generateSeed, Set.mem_setOf] at h
-- --         specialize h j
-- --         simp only [List.count_cons_self] at h
-- --         simp only [Nat.cast_list_prod, List.map_map, one_div, probOutput_vector_toList,
-- --           List.length_drop, h, mul_add_one, add_tsub_cancel_left, ↓reduceDIte,
--               -- probOutput_replicate,
-- --           probOutput_uniformOfFintype, Vector.toList_mk, List.map_drop, List.map_const',
-- --           List.drop_replicate, List.prod_replicate, List.map_cons, List.prod_cons, Nat.cast_mul,
-- --           Nat.cast_pow]
-- --         rw [mul_comm, ← ENNReal.inv_pow, ENNReal.mul_inv] <;> simp
-- --   }

-- end OracleComp
