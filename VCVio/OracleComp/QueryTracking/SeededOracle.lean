/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.Coercions.SubSpec


/-!
# Pre-computing Results of Oracle Queries

This file defines a function `QueryImpl.withPregen` that modifies a query implementation
to take in a list of pre-chosen outputs to use when answering queries.
Uses `StateT` so that consumed seed values are threaded to subsequent queries.

Note that ordering is subtle, for example `so.withCaching.withPregen` will first check for seeds
and not cache the result if one is found, while `so.withPregen.withCaching` checks the cache first,
and include seed values into the cache after returning them.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq ι]

namespace OracleComp

section generateSeedCounts

variable {ι : Type} [DecidableEq ι] (spec : OracleSpec ι)
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- Generate a `QuerySeed` by explicit per-index counts.

This is a “product” seed generator: for each `i ∈ is` (assumed duplicate-free), it samples
`n i` i.i.d. uniform values of type `spec.Range i` and stores the resulting list at index `i`.
For `i ∉ is`, the seed list is `[]`. -/
def generateSeedCounts (n : ι → ℕ) : List ι → ProbComp (OracleSpec.QuerySeed spec)
  | [] => return ∅
  | i :: is => do
    let xs ← replicate (n i) ($ᵗ spec.Range i)
    let rest ← generateSeedCounts n is
    return Function.update rest i xs

@[simp] lemma generateSeedCounts_nil (n : ι → ℕ) :
    generateSeedCounts (spec := spec) n [] = return ∅ := rfl

@[simp] lemma generateSeedCounts_cons (n : ι → ℕ) (i : ι) (is : List ι) :
    generateSeedCounts (spec := spec) n (i :: is) = do
      let xs ← replicate (n i) ($ᵗ spec.Range i)
      let rest ← generateSeedCounts (spec := spec) n is
      return Function.update rest i xs := rfl

@[simp] lemma support_generateSeedCounts [spec.Fintype] (n : ι → ℕ) (is : List ι) :
    support (generateSeedCounts (spec := spec) n is) =
      {seed : QuerySeed spec | ∀ i, (seed i).length = if i ∈ is then n i else 0} := by
  classical
  induction is with
  | nil =>
    ext seed
    simp [generateSeedCounts]
    constructor
    · intro h
      subst h
      intro i
      simp
    · intro h
      -- if all lists have length 0, the seed is empty
      have hseed : seed = (∅ : QuerySeed spec) := by
        funext i
        have : (seed i).length = 0 := by simpa using h i
        exact List.eq_nil_of_length_eq_zero this
      subst hseed
      simp
  | cons i is ih =>
    ext seed
    simp only [generateSeedCounts_cons, Set.mem_setOf_eq]
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨xs, hxs, hrest⟩
      rw [mem_support_bind_iff] at hrest
      rcases hrest with ⟨rest, hrest, hpure⟩
      have hEq : Function.update rest i xs = seed := by
        simpa [support_pure, Set.mem_singleton_iff] using hpure.symm
      have hlen_xs : xs.length = n i := by
        have hxss : xs.length = n i ∧ ∀ x ∈ xs, x ∈ support ($ᵗ spec.Range i) := by
          simpa [support_replicate (oa := ($ᵗ spec.Range i)) (n := n i)] using hxs
        exact hxss.1
      have hrest_len : ∀ j, (rest j).length = if j ∈ is then n j else 0 := by
        simpa [ih, Set.mem_setOf_eq] using hrest
      intro j
      by_cases hj : j = i
      · cases hj
        have hseed_i : seed i = xs := by
          have := congrArg (fun s => s i) hEq
          simpa using this.symm
        simpa [hseed_i, List.mem_cons, hlen_xs]
      · have hseed_j : seed j = rest j := by
          have := congrArg (fun s => s j) hEq
          simpa [Function.update_of_ne hj] using this.symm
        have hlen_seed_j : (seed j).length = if j ∈ is then n j else 0 := by
          simpa [hseed_j] using hrest_len j
        -- membership in `i :: is` with `j ≠ i`
        simpa [List.mem_cons, hj, hlen_seed_j]
    · intro h
      let xs : List (spec.Range i) := seed i
      let rest : QuerySeed spec :=
        if hi : i ∈ is then seed else Function.update seed i ([] : List (spec.Range i))
      have hxs_len : xs.length = n i := by
        have := h i
        simpa [xs, List.mem_cons] using this
      refine ⟨xs, ?_, ?_⟩
      · -- `xs` is supported by `replicate` just from its length (all outputs are supported)
        rw [support_replicate (oa := ($ᵗ spec.Range i)) (n := n i)]
        refine ⟨hxs_len, ?_⟩
        intro x hx
        simp [support_uniformSample]  -- `support ($ᵗ _) = univ`
      · rw [mem_support_bind_iff]
        refine ⟨rest, ?_, ?_⟩
        · -- rest in support of tail generator
          rw [ih, Set.mem_setOf_eq]
          intro j
          by_cases hj : j = i
          · cases hj
            by_cases hi : i ∈ is
            · -- if `i ∈ is`, then `rest = seed` and we can read the needed length from `h`
              simpa [rest, hi] using (h i)
            · -- if `i ∉ is`, then `rest i = []`
              simp [rest, hi]
          · -- for `j ≠ i`, `rest j = seed j` and we read the length from `h`
            have := h j
            have : (seed j).length = if j ∈ is then n j else 0 := by
              simpa [List.mem_cons, hj] using this
            by_cases hi : i ∈ is
            · simpa [rest, hi, this]
            · simpa [rest, hi, Function.update_of_ne hj, this]
        · -- and the pure update reconstructs `seed`
          rw [support_pure, Set.mem_singleton_iff]
          ext j
          by_cases hj : j = i
          · subst hj
            simp [xs, rest]
          · by_cases hi : i ∈ is
            · simp [rest, hi, Function.update_of_ne hj]
            · simp [rest, hi, Function.update_of_ne hj]

lemma probOutput_generateSeedCounts [spec.Fintype]
    (n : ι → ℕ) (is : List ι) (his : is.Nodup)
    (seed : QuerySeed spec) :
    Pr[= seed | generateSeedCounts (spec := spec) n is] =
      if h : seed ∈ support (generateSeedCounts (spec := spec) n is)
      then 1 / ((is.map (fun i => (Fintype.card (spec.Range i) : ENNReal) ^ (n i))).prod)
      else 0 := by
  classical
  induction is with
  | nil =>
    simp [OracleComp.generateSeedCounts, support_pure]
  | cons i is ih =>
    have his' : is.Nodup := by simpa using his.tail
    have hni : i ∉ is := by simpa using his.not_mem
    by_cases hseed : seed ∈ support (generateSeedCounts (spec := spec) n (i :: is))
    · have hseed_len :
        ∀ j, (seed j).length = if j ∈ (i :: is) then n j else 0 := by
        simpa [support_generateSeedCounts (spec := spec) n (i :: is), Set.mem_setOf_eq] using hseed
      let xs : List (spec.Range i) := seed i
      let rest : QuerySeed spec := Function.update seed i ([] : List (spec.Range i))
      have hxs_len : xs.length = n i := by
        simpa [xs, List.mem_cons] using hseed_len i
      have hrest_mem : rest ∈ support (generateSeedCounts (spec := spec) n is) := by
        rw [support_generateSeedCounts (spec := spec) n is, Set.mem_setOf_eq]
        intro j
        by_cases hj : j = i
        · subst hj
          simp [rest, hni]
        · have := hseed_len j
          have hlen : (seed j).length = if j ∈ is then n j else 0 := by
            simpa [List.mem_cons, hj] using this
          simpa [rest, Function.update_of_ne hj, hlen]
      -- unfold the head step and collapse the two binds to the unique decomposition
      simp only [OracleComp.generateSeedCounts_cons]
      -- pick out the unique `xs = seed i`
      have huniq_xs :
          ∀ xs' ∈ support (replicate (n i) ($ᵗ spec.Range i)),
            seed ∈ support (do
              let rest' ← generateSeedCounts (spec := spec) n is
              return Function.update rest' i xs') → xs' = xs := by
        intro xs' _ hmem
        rcases (mem_support_bind_iff.mp hmem) with ⟨rest', _, hpure⟩
        have hEq : Function.update rest' i xs' = seed := by
          simpa [support_pure, Set.mem_singleton_iff] using hpure.symm
        have : seed i = xs' := by
          have := congrArg (fun s => s i) hEq
          simpa using this
        simpa [xs, this]
      rw [probOutput_bind_eq_mul (mx := replicate (n i) ($ᵗ spec.Range i))
        (my := fun xs' => do
          let rest' ← generateSeedCounts (spec := spec) n is
          return Function.update rest' i xs') (y := seed) xs huniq_xs]
      -- now pick out the unique `rest = update seed i []` (since `i ∉ is`)
      have huniq_rest :
          ∀ rest' ∈ support (generateSeedCounts (spec := spec) n is),
            seed ∈ support (pure (Function.update rest' i xs)) → rest' = rest := by
        intro rest' hrest' hpure
        have hEq : Function.update rest' i xs = seed := by
          simpa [support_pure, Set.mem_singleton_iff] using hpure.symm
        funext j
        by_cases hj : j = i
        · subst hj
          -- `rest' i = []` since `i ∉ is`
          have hlen0 : (rest' i).length = 0 := by
            have hlen :
                ∀ k, (rest' k).length = if k ∈ is then n k else 0 := by
              simpa [support_generateSeedCounts (spec := spec) n is, Set.mem_setOf_eq] using hrest'
            simpa [hni] using (hlen i)
          have : rest' i = ([] : List (spec.Range i)) := List.eq_nil_of_length_eq_zero hlen0
          simp [rest, Function.update_self, this]
        · have : rest' j = seed j := by
            have := congrArg (fun s => s j) hEq
            simpa [Function.update_of_ne hj] using this
          simp [rest, Function.update_of_ne hj, this]
      rw [probOutput_bind_eq_mul (mx := generateSeedCounts (spec := spec) n is)
        (my := fun rest' => pure (Function.update rest' i xs)) (y := seed) rest huniq_rest]
      -- compute the factors
      have hrep :
          Pr[= xs | replicate (n i) ($ᵗ spec.Range i)] =
            1 / ((Fintype.card (spec.Range i) : ENNReal) ^ (n i)) := by
        simpa [hxs_len, xs] using
          (probOutput_replicate_uniformSample (α := spec.Range i) (xs := xs) (n := n i))
      have hih :
          Pr[= rest | generateSeedCounts (spec := spec) n is] =
            1 / ((is.map (fun j => (Fintype.card (spec.Range j) : ENNReal) ^ (n j))).prod) := by
        have : rest ∈ support (generateSeedCounts (spec := spec) n is) := hrest_mem
        simpa [ih (his := his') rest, this] using (ih (his := his') rest)
      have hpure :
          Pr[= seed | pure (Function.update rest i xs)] = 1 := by
        simp [xs, rest, Function.update_update, Function.update_self]
      simp [hseed, hrest_mem, hrep, hih, hpure, xs, rest, List.prod_cons]
    · simp [hseed, probOutput_eq_zero_of_not_mem_support hseed]

end generateSeedCounts

end OracleComp

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a `QueryImpl` to check for pregenerated responses for oracle queries first.
If a seed value is available for the query, it is used and the seed is consumed (the tail
replaces the head). When no seed remains, falls back to the underlying implementation. -/
def withPregen (so : QueryImpl spec m) :
    QueryImpl spec (StateT (QuerySeed spec) m) :=
  fun t => StateT.mk fun seed =>
    match seed t with
    | u :: us => pure (u, Function.update seed t us)
    | [] => (·, seed) <$> so t

@[simp, grind =]
lemma withPregen_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withPregen t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> so t := rfl

end QueryImpl

/-- Use pregenerated oracle responses for queries, falling back to the real oracle
when the seed is exhausted. Seed consumption is tracked via `StateT`. -/
def seededOracle :
    QueryImpl spec (StateT (QuerySeed spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withPregen

namespace seededOracle

@[simp]
lemma apply_eq (t : spec.Domain) :
    seededOracle t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> OracleComp.query t := rfl

-- @[simp] -- proof deferred; removing simp to avoid unsound rewriting
lemma probOutput_generateSeed_bind_simulateQ_bind
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (ob : α → OracleComp spec₀ β) (y : β) :
    Pr[= y | do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
      ob x] = Pr[= y | oa >>= ob] := by
  classical
  -- Main proof is by structural induction on `oa`.
  revert y
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro y
    -- Seed generation is independent of `pure`.
    simp
  | query_bind t mx ih =>
    intro y
    -- Expand the simulated computation at the first query.
    -- (Further steps will use the distributional equivalence of using a pre-generated
    -- uniform head vs. querying the real oracle, threading the remaining seed.)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, seededOracle.apply_eq, StateT.run]
    -- TODO: finish (requires a “head/tail independence” lemma for `generateSeed` at index `t`).
    sorry

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (f : α → β) (y : β) :
    Pr[= y | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> Prod.fst <$> (simulateQ seededOracle oa).run seed : OracleComp spec₀ β)] =
      Pr[= y | f <$> oa] := by
  -- Reduce `map` to `bind` + `pure`, then apply the `bind` lemma.
  simpa [map_eq_bind_pure_comp, Function.comp] using
    (probOutput_generateSeed_bind_simulateQ_bind (qc := qc) (js := js)
      (oa := oa) (ob := fun x => pure (f x)) (y := y))

end seededOracle
