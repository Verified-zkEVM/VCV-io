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
        simp [hseed_i, List.mem_cons, hlen_xs]
      · have hseed_j : seed j = rest j := by
          have := congrArg (fun s => s j) hEq
          simpa [Function.update_of_ne hj] using this.symm
        have hlen_seed_j : (seed j).length = if j ∈ is then n j else 0 := by
          simpa [hseed_j] using hrest_len j
        -- membership in `i :: is` with `j ≠ i`
        simp [List.mem_cons, hj, hlen_seed_j]
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
            · simp [rest, hi, this]
            · simp [rest, hi, Function.update_of_ne hj, this]
        · -- and the pure update reconstructs `seed`
          rw [support_pure, Set.mem_singleton_iff]
          ext j
          by_cases hj : j = i
          · subst hj
            simp [xs, rest]
          · by_cases hi : i ∈ is
            · simp [rest, hi, Function.update_of_ne hj]
            · simp [rest, hi, Function.update_of_ne hj]

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

/-- The probability that a lifted uniform sample equals a fixed value is `(card α)⁻¹`. -/
lemma probEvent_liftComp_uniformSample_eq_of_eq
    {ι : Type} {spec : OracleSpec ι} [DecidableEq ι]
    [(i : ι) → SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [OracleSpec.LawfulSubSpec unifSpec spec]
    [spec.Fintype] [spec.Inhabited]
    {i : ι} (u₀ : spec.Range i) :
    probEvent (liftComp (uniformSample (spec.Range i)) spec)
      (fun u => u₀ = u) =
      (↑(Fintype.card (spec.Range i)) : ENNReal)⁻¹ := by
  rw [probEvent_eq_eq_probOutput', probOutput_liftComp, probOutput_uniformSample]

private lemma evalDist_generateSeed_eq_canonical
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀) :
    evalDist (generateSeed spec₀ qc js) =
      evalDist (generateSeed spec₀ (fun i => qc i * js.count i) js.dedup) := by
  refine OracleComp.evalDist_generateSeed_eq_of_countEq (spec := spec₀)
    (qc := qc) (js := js)
    (qc' := fun i => qc i * js.count i)
    (js' := js.dedup) ?_
  intro i
  by_cases hi : i ∈ js
  · simp [List.count_dedup, hi]
  · simp [hi, List.count_eq_zero_of_not_mem]

@[simp]
lemma apply_eq (t : spec.Domain) :
    seededOracle t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> OracleComp.query t := rfl

lemma run_bind_query_eq_pop {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((seededOracle t) >>= fun u => simulateQ seededOracle (mx u)).run seed) =
      match seed.pop t with
      | none => do
          let u ← liftM (query t)
          (simulateQ seededOracle (mx u)).run seed
      | some (u, seed') =>
          (simulateQ seededOracle (mx u)).run seed' := by
  cases hst : seed t with
  | nil =>
    simp [seededOracle.apply_eq, StateT.run_bind, QuerySeed.pop, hst]
  | cons u us =>
    simp [seededOracle.apply_eq, StateT.run_bind, QuerySeed.pop, hst]

lemma run_bind_query_eq_pop_bindform {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((StateT.mk fun seed =>
        match seed t with
        | u :: us => pure (u, Function.update seed t us)
        | [] => liftM (query t) >>= pure ∘ fun x => (x, seed)) >>=
      fun x => simulateQ seededOracle (mx x)) seed) =
      match seed.pop t with
      | none => do
          let u ← liftM (query t)
          (simulateQ seededOracle (mx u)).run seed
      | some (u, seed') =>
          (simulateQ seededOracle (mx u)).run seed' := by
  simpa [map_eq_bind_pure_comp] using
    (run_bind_query_eq_pop (spec := spec) (t := t) (mx := mx) seed)

private lemma evalDist_liftComp_generateSeed_bind_simulateQ_run'
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α : Type} (oa : OracleComp spec₀ α) :
    evalDist (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' seed : OracleComp spec₀ α) =
    evalDist oa := by
  classical
  revert qc js
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qc js
    apply evalDist_ext; intro a
    simp
  | query_bind t mx ih =>
    intro qc js
    -- Prove at the evalDist level, not pointwise
    -- First establish the run' decomposition
    have hrun' : ∀ s : QuerySeed spec₀,
        (do let u ← seededOracle t; simulateQ seededOracle (mx u) :
          StateT _ (OracleComp spec₀) α).run' s =
        match s.pop t with
        | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' := by
      intro s
      show Prod.fst <$>
        (seededOracle t >>= fun u => simulateQ seededOracle (mx u)).run s = _
      rw [run_bind_query_eq_pop]
      cases s.pop t with
      | none => simp [map_bind]
      | some p => rfl
    -- Use the decomposition to prove evalDist equality
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    apply evalDist_ext; intro x
    simp_rw [hrun']
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_liftComp]
    by_cases hcount : qc t * js.count t = 0
    · -- All seeds have s t = [], pop = none.
      have hpop : ∀ s ∈ support (generateSeed spec₀ qc js), s.pop t = none := by
        intro s hs; rw [QuerySeed.pop_eq_none_iff]
        rw [support_generateSeed (spec := spec₀)] at hs
        have hlen : (s t).length = qc t * js.count t := hs t
        exact List.eq_nil_of_length_eq_zero (hlen.trans hcount)
      -- Replace match with none branch (zero terms vanish)
      have step1 : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | match s.pop t with
              | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'] =
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s] := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · simp [hpop s hs]
        · have h0 : Pr[= s | generateSeed spec₀ qc js] = 0 :=
            (probOutput_eq_zero_iff _ _).2 hs
          simp [h0]
      simp_rw [step1, probOutput_bind_eq_tsum (liftM (query t))]
      -- ∑' s, Pr[=s|gen] * ∑' u, Pr[=u|query t] * Pr[=x|run'(mx u) s]
      -- Distribute and swap
      simp_rw [← ENNReal.tsum_mul_left, mul_left_comm]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      congr 1; ext u; congr 1
      have hih : Pr[= x | (liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' seed)] = Pr[= x | mx u] :=
        congrFun (congrArg DFunLike.coe (ih u qc js)) x
      rw [show Pr[= x | liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' seed] =
        ∑' s, Pr[= s | generateSeed spec₀ qc js] *
          Pr[= x | (simulateQ seededOracle (mx u)).run' s] from by
        rw [probOutput_bind_eq_tsum]; simp_rw [probOutput_liftComp]] at hih
      exact hih
    · push_neg at hcount
      -- All seeds in support have s t ≠ [], so pop = some.
      have hpop_some : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', s.pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs
            (Nat.pos_of_ne_zero (by omega))
        obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨u, Function.update s t us, QuerySeed.pop_eq_some_of_cons s t u us hcons⟩
      -- Replace match with some branch for seeds in support (others are 0)
      have step1 : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | match s.pop t with
              | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'] =
          Pr[= s | generateSeed spec₀ qc js] *
            (match s.pop t with
              | none => 0
              | some (u, s') =>
                  Pr[= x | (simulateQ seededOracle (mx u)).run' s']) := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · obtain ⟨u, s', hpop⟩ := hpop_some s hs; simp [hpop]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step1]
      -- Reparametrize: ∑' s, f(s) = ∑' (u,s'), f(s'.prependValues [u])
      -- using injectivity of prependValues and support ⊆ range
      have h_supp : Function.support (fun s =>
          Pr[=s | generateSeed spec₀ qc js] *
            match s.pop t with
            | none => 0
            | some (u, s') => Pr[=x | (simulateQ seededOracle (mx u)).run' s']) ⊆
          Set.range (fun (p : spec₀.Range t × QuerySeed spec₀) =>
            p.2.prependValues [p.1]) := by
        intro s hs
        simp only [Function.mem_support] at hs
        have hmem : s ∈ support (generateSeed spec₀ qc js) := by
          by_contra h; exact hs (by simp [(probOutput_eq_zero_iff _ _).2 h])
        obtain ⟨u, s', hpop⟩ := hpop_some s hmem
        exact ⟨(u, s'), QuerySeed.eq_prependValues_of_pop_eq_some hpop⟩
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq h_supp]
      simp only [QuerySeed.pop_prependValues_singleton]
      rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
      congr 1; ext u
      -- Goal: ∑' s', Pr[=s'.prependValues [u]|gen] * Pr[=x|run'(mx u) s']
      --     = Pr[=u|liftM (query t)] * Pr[=x|mx u]
      have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by omega)
      have hfact := fun s' => probOutput_generateSeed_prependValues spec₀ qc js u s' hpos
      simp_rw [hfact, mul_assoc]
      rw [ENNReal.tsum_mul_left]
      congr 1
      · exact (probOutput_query t u).symm
      · suffices h : Pr[= x | (do
            let seed ← liftComp (generateSeed spec₀
                (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1))
                js.dedup) spec₀
            (simulateQ seededOracle (mx u)).run' seed)] = Pr[= x | mx u] by
          rw [probOutput_bind_eq_tsum] at h
          simp_rw [probOutput_liftComp] at h
          exact h
        exact congrFun (congrArg DFunLike.coe (ih u _ js.dedup)) x

-- @[simp] -- proof deferred; removing simp to avoid unsound rewriting
lemma probOutput_generateSeed_bind_simulateQ_bind
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (ob : α → OracleComp spec₀ β) (y : β) :
    Pr[= y | do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
      ob x] = Pr[= y | oa >>= ob] := by
  have h := evalDist_liftComp_generateSeed_bind_simulateQ_run' qc js oa
  rw [show (do
    let seed ← liftComp (generateSeed spec₀ qc js) spec₀
    let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
    ob x) = ((do
    let seed ← liftComp (generateSeed spec₀ qc js) spec₀
    (simulateQ seededOracle oa).run' seed) >>= ob) from by simp [bind_assoc]]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1; ext x
  congr 1
  exact congrFun (congrArg DFunLike.coe h) x

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
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
