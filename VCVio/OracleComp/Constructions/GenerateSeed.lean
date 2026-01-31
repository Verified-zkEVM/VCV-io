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

open OracleSpec BigOperators ENNReal

namespace OracleComp

variable {ι : Type} [DecidableEq ι]

def generateSeedT (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
    (qc : ι → ℕ) (activeOracles : List ι) :
    StateT (QuerySeed spec) ProbComp Unit :=
  for j in activeOracles do
    modify (QuerySeed.addValues (← ($ᵗ spec.range j).replicate (qc j)))

/-- Generate a `QuerySeed` uniformly at random for some set of oracles `spec : OracleSpec ι`,
with `qc i : ℕ` values seeded for each index `i ∈ js`. Note that `js` is allowed
to contain duplicates, but usually wouldn't in practice. -/
def generateSeed (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
    (qc : ι → ℕ) (js : List ι) : ProbComp (QuerySeed spec) := do
  let mut seed : QuerySeed spec := ∅
  for j in js do
    seed := seed.addValues (← ($ᵗ spec.range j).replicate (qc j))
  return seed

def generateSingleSeed (spec : OracleSpec ι) (i : ι) [SelectableType (spec.range i)]
    (n : ℕ) : ProbComp (QuerySeed spec) :=
  QuerySeed.ofList <$> ($ᵗ spec.range i).replicate n

-- Prod.snd <$> (generateSeedT spec qc activeOracles).run ∅
-- variable (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
--   (qc : ι → ℕ) (j : ι) (js : List ι)

-- lemma probOutput_generateSeed (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
--     (qc : ι → ℕ) (js : List ι) (seed : QuerySeed spec)
--     (h : seed ∈ (generateSeed spec qc js).support) :
--     [= seed | generateSeed spec qc js] =
--       1 / (js.map (λ j ↦ (Fintype.card (spec.range j)) ^ qc j)).prod :=
--   sorry

-- def generateSeed (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
--     (qc : ι → ℕ) (activeOracles : List ι) : ProbComp (QuerySeed spec) :=
--   match activeOracles with
--   | [] => return ∅
--   | j :: js => QuerySeed.addValues <$> generateSeed spec qc js <*>
--       (Array.toList <$> Vector.toArray <$> replicate ($ᵗ (spec.range j)) (qc j))

variable (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
  (qc : ι → ℕ) (j : ι) (js : List ι)

@[simp]
lemma generateSeed_nil : generateSeed spec qc [] = return ∅ := rfl

@[simp]
lemma generateSeed_cons : generateSeed spec qc (j :: js) =
    ($ᵗ (spec.range j)).replicate (qc j) >>= λ xs ↦
      generateSeed spec qc js := by
  simp [generateSeed, map_eq_bind_pure_comp,
    seq_eq_bind, bind_assoc]
  sorry

@[simp]
lemma generateSeed_zero : generateSeed spec 0 js = return ∅ := by
  induction js <;> simp [*]

/-- The support of the fold used in `generateSeed` consists of seeds that extend the initial seed
by appending lists of the correct length (determined by `qc` and the count of indices in `js`)
for each index. -/
lemma support_foldlM_generateSeed (seed₀ : QuerySeed spec) (js : List ι) :
  (js.foldlM (fun seed j ↦ do
      let values ← ($ᵗ spec.range j).replicate (qc j)
      return QuerySeed.addValues values seed) seed₀).support =
    {seed | ∀ i, ∃ suffix, seed i = seed₀ i ++ suffix ∧ suffix.length = qc i * js.count i} := by
  ext seed
  constructor <;> intro h
  · induction' js using List.reverseRecOn with j js ih generalizing seed₀ seed <;>
      simp_all only [bind_pure_comp, List.foldlM_nil, support_pure, Set.mem_singleton_iff,
        List.count_nil, mul_zero, List.length_eq_zero_iff, exists_eq_right,
        List.append_nil, Set.mem_setOf_eq, implies_true, List.foldlM_append, List.foldlM_cons,
        bind_pure, support_bind, support_map, support_replicate, support_uniformOfFintype,
        Set.mem_univ, and_true, Set.mem_iUnion, Set.mem_image, exists_prop, List.count_append,
        mul_add]
    rcases h with ⟨seed', hseed', x, hx, rfl⟩
    intro i
    specialize ih seed₀ seed' hseed' i
    rcases ih with ⟨suffix, hsuff₁, hsuff₂⟩
    simp_all only [QuerySeed.addValues_apply]
    by_cases hi : i = js <;> simp_all only [List.nodup_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_self, List.mem_cons, or_false,
      List.count_eq_one_of_mem, mul_one, ne_eq, Function.update_of_ne, List.append_cancel_left_eq,
      exists_eq_left', Nat.left_eq_add, mul_eq_zero]
    · subst hi
      use suffix ++ x
      simp_all only [List.append_assoc, Function.update_self, List.length_append, and_self]
    · grind
  · induction' js using List.reverseRecOn with j js ih generalizing seed₀ seed
    · ext i; simp_all
    simp_all only [Set.mem_setOf_eq, bind_pure_comp, List.count_append, List.count_cons,
      List.count_nil, beq_iff_eq, zero_add, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      bind_pure, support_bind, support_map, support_replicate, support_uniformOfFintype,
      Set.mem_univ, implies_true, and_true, Set.mem_iUnion, Set.mem_image, exists_prop]
    obtain ⟨suffix, hsuff₁, hsuff₂⟩ := h js
    refine ⟨?_, ih _ _ ?_, ?_⟩
    · exact fun i ↦ if i = js then
        seed₀ i ++ List.take (qc i * List.count i j)
          (seed i |> List.drop (seed₀ i |> List.length))
        else seed₀ i ++ List.drop (seed₀ i |> List.length) (seed i)
    · intro i
      specialize h i
      aesop
    · refine ⟨List.drop (qc js * List.count js j) suffix, ?_, ?_⟩ <;>
        simp_all only [mul_add, mul_ite, mul_one, mul_zero, ↓reduceIte, List.length_drop,
          add_tsub_cancel_left]
      ext i
      by_cases hi : i = js <;> simp_all only [QuerySeed.addValues_apply, ↓reduceIte,
        List.drop_left', List.append_assoc, List.take_append_drop, ne_eq, not_false_eq_true,
        Function.update_of_ne]
      · subst hi; simp_all only [Function.update_self]
      · cases h i; simp_all only [List.drop_left']

@[simp]
lemma support_generateSeed : (generateSeed spec qc js).support =
    {seed | ∀ i, (seed i).length = qc i * js.count i} := by
  have h_support : (js.foldlM (fun seed j ↦ do
        let values ← ($ᵗ spec.range j).replicate (qc j)
        return QuerySeed.addValues values seed) ∅).support =
      {seed | ∀ i, ∃ suffix, seed i = suffix ∧ suffix.length = qc i * js.count i} :=
    support_foldlM_generateSeed spec qc ∅ js
  convert h_support using 3
  · funext seed
    induction' js with j js ih generalizing qc <;>
      simp only [bind_pure_comp, QuerySeed.instEmptyCollection]
    · have h_foldlM : ∀ (seed₀ : spec.QuerySeed) (js : List ι), (js.foldlM (fun seed j ↦ do
            let values ← ($ᵗ spec.range j).replicate (qc j)
            return QuerySeed.addValues values seed) seed₀) =
          (do let mut seed := seed₀
              for j in js do seed := seed.addValues (← ($ᵗ spec.range j).replicate (qc j))
              return seed) := by
        intro seed₀ js
        induction' js with j js ih generalizing seed₀ <;> simp_all [List.foldlM]
      convert h_foldlM ∅ seed |> Eq.symm using 1
    · induction' seed using List.reverseRecOn with j seed ih
      · simp only [generateSeed_nil, QuerySeed.instEmptyCollection, List.foldlM]
      · simp only [List.foldlM_append, List.foldlM, bind_pure]
        convert ih qc _ using 1
        · induction' j using List.reverseRecOn with x xs _ <;> simp [*, List.foldlM]
        · exact support_foldlM_generateSeed spec qc ∅ js
  · simp_all only [bind_pure_comp, QuerySeed.instEmptyCollection, exists_eq_left']

--   induction js with
--   | nil => {
--     simp [Set.ext_iff, DFunLike.ext_iff]
--     intro x
--     rfl
--   }
--   | cons j js h => {
--     simp [h, Set.ext_iff]
--     intro seed
--     refine ⟨λ h i ↦ ?_, λ h ↦ ?_⟩
--     · obtain ⟨seed', ⟨h1, ⟨xs, hxs⟩⟩⟩ := h
--       by_cases hj : i = j
--       · induction hj
--         simp [← hxs, h1, mul_add_one]
--       · simp [← hxs, h1, hj]
--     · refine ⟨seed.takeAtIndex j (qc j * js.count j), λ i ↦ ?_, ?_⟩
--       · by_cases hi : i = j
--         · induction hi
--           simp [h, mul_add_one]
--         · simp [hi, h]
--       · refine ⟨⟨(seed j).drop (qc j * js.count j), ?_⟩, ?_⟩
--         · simp [h, mul_add_one]
--         · simp [h]
--           rw [QuerySeed.addValues_eq_iff]
--           simp [h, mul_add_one]
--   }

/-- The probability of failure of `generateSeed` is 0. -/
lemma probFailure_generateSeed_eq_zero {ι : Type} [DecidableEq ι]
    (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
    (qc : ι → ℕ) (js : List ι) :
    probFailure (generateSeed spec qc js) = 0 := by
  induction js with
  | nil => exact (probFailure_eq_zero_iff (generateSeed spec qc [])).mpr trivial
  | cons j js ih =>
    simp_all only [generateSeed, QuerySeed.instEmptyCollection, bind_pure_comp,
        map_pure, bind_pure, probFailure_eq_zero_iff, List.forIn_cons, bind_map_left,
        neverFails_bind_iff, support_replicate, support_uniformOfFintype, Set.mem_univ,
        implies_true, and_true, Set.mem_setOf_eq]
    constructor
    · exact neverFails_list_mapM fun _ _ ↦ neverFails_uniformOfFintype _
    · intro _ _
      suffices ∀ (xs : List ι) (x : QuerySeed spec),
          (ForIn.forIn xs x fun j r ↦
            (fun a ↦ ForInStep.yield (QuerySeed.addValues a r)) <$>
              replicate (qc j) ($ᵗspec.range j)).neverFails from this ..
      intro xs x
      induction xs generalizing x with
      | nil => simp only [List.forIn_nil, neverFails_pure]
      | cons head tail tail_ih =>
        simp_all only [List.forIn_cons, bind_map_left, neverFails_bind_iff, support_replicate,
          support_uniformOfFintype, Set.mem_univ, implies_true, and_true, Set.mem_setOf_eq]
        exact neverFails_list_mapM fun _ _ ↦ neverFails_uniformOfFintype _

@[simp]
lemma finSupport_generateSeed_ne_empty [DecidableEq spec.QuerySeed] :
    (generateSeed spec qc js).finSupport ≠ ∅ := by
  intro; simp_all only [Finset.ext_iff, Finset.notMem_empty, iff_false]
  convert tsum_probOutput_eq_one ..
  any_goals exact OracleComp.probFailure_generateSeed_eq_zero spec qc js
  rw [tsum_eq_single ∅]
  · simp_all only [QuerySeed.instEmptyCollection, probOutput_eq_one_iff', probFailure_eq_zero_iff,
      false_iff, not_and]
    intro a_1 a_2
    simp_all only [Finset.mem_singleton, forall_eq]
  · intro b' a_1
    simp_all only [QuerySeed.instEmptyCollection, ne_eq, probOutput_eq_zero_iff', not_false_eq_true]

lemma probOutput_generateSeed [spec.FiniteRange] (seed : QuerySeed spec)
    (h : seed ∈ (generateSeed spec qc js).support) : [= seed | generateSeed spec qc js] =
    1 / (js.map (λ j ↦ (Fintype.card (spec.range j)) ^ qc j)).prod := by
  revert seed
  induction js using List.reverseRecOn with
  | nil => {
    -- simp at h
    simp

  }
  | append_singleton j js hjs => {
    intro seed hs
    simp [generateSeed, List.forIn_eq_foldlM]

    -- rw [Array.forIn_toList]
    sorry
  }

/-- The cardinality of the finite support of `generateSeed` is the product of the number of
possible values for each query. -/
lemma card_finSupport_generateSeed [spec.FiniteRange] [DecidableEq spec.QuerySeed] :
    (generateSeed spec qc js).finSupport.card =
      (js.map (fun j ↦ (Fintype.card (spec.range j)) ^ qc j)).prod := by
  have h_card : (Set.ncard {seed : QuerySeed spec |
      ∀ i, (seed i).length = qc i * js.count i}) = (Finset.prod (js.toFinset)
      (fun i ↦ (Fintype.card (spec.range i)) ^ (qc i * js.count i))) := by
    have h_bij : {seed : spec.QuerySeed | ∀ i, (seed i).length = qc i * List.count i js} ≃
        (Π i ∈ js.toFinset, Fin (qc i * List.count i js) → spec.range i) := by
      refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
      use fun seed i hi j ↦ (seed.val i)[j]!
      · intro seed₁ seed₂ h_eq
        ext i
        by_cases hi : i ∈ js.toFinset <;> simp_all only [Set.mem_setOf_eq, Fin.getElem!_fin,
          List.getElem!_eq_getElem?_getD, funext_iff, List.mem_toFinset]
        · by_cases hi' : ‹ℕ› < List.length (seed₁.val i) <;>
            by_cases hi'' : ‹ℕ› < List.length (seed₂.val i) <;>
            simp_all only [Set.mem_setOf_eq, getElem?_pos, Option.some.injEq,
              not_lt, getElem?_neg, reduceCtorEq, iff_false, false_iff]
          · specialize h_eq i hi ⟨‹_›, by linarith [seed₁.2 i, seed₂.2 i]⟩
            grind
          · grind
          · grind
        · have hlen₁ := seed₁.2 i
          have hlen₂ := seed₂.2 i
          simp_all [List.count_eq_zero_of_not_mem hi]
      · intro f
        refine ⟨⟨fun i ↦ List.ofFn fun j ↦
          if hi : i ∈ js.toFinset then f i hi j else Inhabited.default, ?_⟩, ?_⟩
        · simp_all only [List.mem_toFinset, Set.mem_setOf_eq, List.length_ofFn, implies_true]
        · simp_all only [↓reduceDIte, List.length_ofFn, Fin.is_lt, getElem!_pos,
            Fin.getElem_fin, List.getElem_ofFn, Fin.eta]
    rw [Set.ncard_def, Set.encard, ENat.card_congr h_bij]
    have h_card_prod : ∀ (s : Finset ι), (ENat.card (Π i ∈ s,
        Fin (qc i * List.count i js) → spec.range i)).toNat =
        ∏ i ∈ s, (Fintype.card (spec.range i)) ^ (qc i * List.count i js) := by
      intro s
      have h_card_prod : ENat.card (Π i ∈ s,
          Fin (qc i * List.count i js) → spec.range i) =
          ∏ i ∈ s, ENat.card (Fin (qc i * List.count i js) → spec.range i) := by
        induction s using Finset.induction with
        | empty => simp [ENat.card]
        | insert j t hj ih =>
          rw [Finset.prod_insert hj, ← ih, ← ENat.card_prod]
          exact ENat.card_congr
            (Finset.insertPiProdEquiv (fun i ↦ Fin (qc i * List.count i js) → spec.range i) hj)
      rw [h_card_prod, ENat.toNat_eq_iff] <;> norm_num [Fintype.card_pi]
      exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ pow_ne_zero _ <| Fintype.card_ne_zero
    exact h_card_prod _
  convert h_card using 1
  · rw [← Set.ncard_coe_finset, coe_finSupport, support_generateSeed]
  · simp only [Finset.prod_list_map_count, pow_mul', pow_right_comm]

/- A helper function `generateSeedFrom` that generates a seed starting from a given initial seed. -/
def generateSeedFrom (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
    (qc : ι → ℕ) (js : List ι) (seed : QuerySeed spec) : ProbComp (QuerySeed spec) :=
  js.foldlM (λ seed j ↦ do
    let vals ← ($ᵗ spec.range j).replicate (qc j)
    return seed.addValues vals) seed

/- Recursive step for `generateSeedFrom`. -/
lemma generateSeedFrom_cons (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
    (qc : ι → ℕ) (j : ι) (js : List ι) (seed : QuerySeed spec) :
    generateSeedFrom spec qc (j :: js) seed =
      (($ᵗ spec.range j).replicate (qc j) >>= fun vals ↦
         generateSeedFrom spec qc js (seed.addValues vals)) := by
  simp only [generateSeedFrom, bind_pure_comp, List.foldlM_cons, bind_map_left]

/-- Taking `n` elements after dropping `l1.length` from `l1 ++ l2 ++ l3` returns `l2`
if `l2.length = n`. -/
lemma List.take_drop_append_of_length_eq {α} (l1 l2 l3 : List α) (n : ℕ) (h : l2.length = n) :
    ((l1 ++ l2 ++ l3).drop l1.length).take n = l2 := by
  simp [h]

/-- `ForIn.forIn` on a list with a body that always yields is equivalent to `List.foldlM`. -/
lemma forIn_list_eq_foldlM.{u} {m : Type → Type u} [Monad m] [LawfulMonad m] {α β : Type}
    (l : List α) (init : β) (f : α → β → m β) :
    ForIn.forIn l init (fun a b ↦ f a b >>= fun b' ↦ pure (ForInStep.yield b')) =
      l.foldlM (fun b a ↦ f a b) init := by
  simp

/-- `generateSeed` is equivalent to `generateSeedFrom` with empty initial seed. -/
lemma generateSeed_eq_generateSeedFrom (spec : OracleSpec ι) [∀ i, SelectableType (spec.range i)]
    (qc : ι → ℕ) (js : List ι) :
    generateSeed spec qc js = generateSeedFrom spec qc js ∅ := by
  convert forIn_list_eq_foldlM ..
  · simp only [generateSeed, QuerySeed.instEmptyCollection, bind_pure_comp, map_pure,
      bind_pure, Functor.map_map]
  · exact instLawfulMonad

/-- The support of `generateSeedFrom` consists of seeds that extend the initial seed by the correct
number of elements for each index. -/
lemma support_generateSeedFrom [spec.FiniteRange] (js : List ι) (seed : QuerySeed spec) :
    (generateSeedFrom spec qc js seed).support =
    {s | ∀ i, List.IsPrefix (seed i) (s i) ∧
      (s i).length = (seed i).length + qc i * js.count i} := by
  induction' js using List.reverseRecOn with js j ih generalizing seed
  · ext
    simp only [generateSeedFrom, bind_pure_comp, List.foldlM_nil, support_pure,
      Set.mem_singleton_iff, List.count_nil, mul_zero, add_zero, Set.mem_setOf_eq]
    constructor <;> intro h
    · grind
    · suffices h_eq : ∀ i, seed i = ‹spec.QuerySeed› i by exact (QuerySeed.ext seed _ h_eq).symm
      intro i; specialize h i; obtain ⟨h₁, h₂⟩ := h
      exact h₁.eq_of_length h₂.symm
  · have h_split : generateSeedFrom spec qc (js ++ [j]) seed = do
      let seed' ← generateSeedFrom spec qc js seed
      let vals ← ($ᵗ spec.range j).replicate (qc j)
      return seed'.addValues vals := by
        unfold generateSeedFrom
        simp [List.foldlM_append]
    simp_all only [Set.ext_iff, Set.mem_setOf_eq, bind_pure_comp, support_bind,
      support_map, support_replicate, support_uniformOfFintype, Set.mem_univ, implies_true,
      and_true, List.count_append, Set.mem_iUnion, Set.mem_image, exists_prop]
    intro x; constructor
    · rintro ⟨y, hy, z, hz, rfl⟩ i; specialize hy i
      simp_all only [QuerySeed.addValues_apply, List.count_cons, List.count_nil,
        beq_iff_eq, zero_add]
      by_cases hi : j = i <;> simp_all only [Function.update, ↓reduceDIte, ↓reduceIte] <;> grind
    · intro hx
      refine ⟨?_, ?_, ?_⟩
      · exact fun i ↦
          if i = j then x i |>.take (List.length (seed i) + qc i * List.count i js) else x i
      · grind
      · refine ⟨x j |>.drop (List.length (seed j) + qc j * List.count j js), ?_, ?_⟩
        <;> simp_all only [List.nodup_cons, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_self, List.length_drop, List.mem_cons, or_false,
          List.count_eq_one_of_mem]
        · exact Nat.sub_eq_of_eq_add <| by ring
        · ext i; by_cases hi : i = j <;> simp_all [List.take_append_drop]
          · subst hi; simp_all only [Function.update_self]

/-- If `seed_out` is a possible result of `generateSeedFrom` starting with `seed_in` extended by
`vals`, then `vals` can be recovered from `seed_out`. -/
lemma vals_eq_of_mem_support_generateSeedFrom [spec.FiniteRange]
    (js : List ι) (seed_in : QuerySeed spec) (seed_out : QuerySeed spec)
    (j : ι) (vals : List (spec.range j))
    (h_len : vals.length = qc j)
    (h_support : seed_out ∈ (generateSeedFrom spec qc js (seed_in.addValues vals)).support) :
    vals = ((seed_out j).drop (seed_in j).length).take (qc j) := by
  obtain ⟨k, hk⟩ := (support_generateSeedFrom spec qc js (QuerySeed.addValues vals seed_in)
    |>.subset h_support j).1
  simp_all [← hk]

omit [(i : ι) → SelectableType (spec.range i)] in
/-- If `seed` extended by `vals` is a prefix of `seed'`, then `vals` is determined by
`seed`, `seed'`. -/
lemma vals_eq_of_isPrefix_addValues {i : ι} {seed seed' : QuerySeed spec}
    {vals : List (spec.range i)}
    (h : List.IsPrefix ((seed.addValues vals) i) (seed' i))
    (n : ℕ) (h_len : vals.length = n) :
    vals = ((seed' i).drop (seed i).length).take n := by
  obtain ⟨l, hl⟩ := h
  simp [← hl, h_len]

/-- If `seed_out` is in the support of `generateSeedFrom` starting from `seed_in` extended by
`vals`, then `vals` is determined by `seed_out` and `seed_in`. -/
lemma vals_eq_of_mem_support_generateSeedFrom' [spec.FiniteRange]
    (js : List ι) (seed_in : QuerySeed spec) (seed_out : QuerySeed spec)
    (j : ι) (vals : List (spec.range j))
    (h_len : vals.length = qc j)
    (h_support : seed_out ∈ (generateSeedFrom spec qc js (seed_in.addValues vals)).support) :
    vals = ((seed_out j).drop (seed_in j).length).take (qc j) :=
  vals_eq_of_mem_support_generateSeedFrom spec qc js seed_in seed_out j vals h_len h_support

omit [DecidableEq ι] in
/-- Probability of a list from replicating a uniform distribution. -/
lemma probOutput_replicate_uniformOfFintype [spec.FiniteRange] (j : ι) (n : ℕ)
    (xs : List (spec.range j)) :
    [= xs | ($ᵗ spec.range j).replicate n] =
    if xs.length = n then ((Fintype.card (spec.range j)) ^ n : ℝ≥0∞)⁻¹ else 0 := by
  split_ifs with h <;> simp only [probOutput_replicate, h, ↓reduceIte,
    probOutput_uniformOfFintype, List.map_const', List.prod_replicate, ENNReal.inv_pow]

/-- The probability of a specific seed in `generateSeedFrom` is the inverse of the product of the
cardinalities of the ranges. -/
lemma probOutput_generateSeedFrom [spec.FiniteRange] [DecidableEq spec.QuerySeed]
    (js : List ι) (seed_in : QuerySeed spec) (seed_out : QuerySeed spec)
    (h : seed_out ∈ (generateSeedFrom spec qc js seed_in).support) :
    [= seed_out | generateSeedFrom spec qc js seed_in] =
    ((js.map (fun j ↦ (Fintype.card (spec.range j)) ^ qc j)).prod : ℝ≥0∞)⁻¹ := by
  induction js generalizing seed_in seed_out with
  | nil => simp_all only [generateSeedFrom, bind_pure_comp, List.foldlM_nil, support_pure,
      Set.mem_singleton_iff, probOutput_pure, ↓reduceIte, List.map_nil, List.prod_nil,
      Nat.cast_one, inv_one]
  | cons j js ih =>
    have h_def : generateSeedFrom spec qc (j :: js) seed_in =
        (($ᵗ spec.range j).replicate (qc j) >>= fun vals ↦
          generateSeedFrom spec qc js (seed_in.addValues vals)) :=
      generateSeedFrom_cons spec qc j js seed_in
    have h_bind : [=seed_out|generateSeedFrom spec qc (j :: js) seed_in] =
        ∑' (vals : List (spec.range j)), [=vals|($ᵗ spec.range j).replicate (qc j)] *
          [=seed_out|generateSeedFrom spec qc js (seed_in.addValues vals)] := by
      rw [h_def]
      exact probOutput_bind_eq_tsum (replicate (qc j) ($ᵗspec.range j))
        (fun vals ↦ generateSeedFrom spec qc js (QuerySeed.addValues vals seed_in)) seed_out
    obtain ⟨vals, h_vals⟩ : ∃ vals : List (spec.range j),
        vals.length = qc j ∧
          seed_out ∈ (generateSeedFrom spec qc js (seed_in.addValues vals)).support := by
      contrapose! h_bind
      simp_all
    rw [h_bind, tsum_eq_single vals]
    · rw [probOutput_replicate_uniformOfFintype, if_pos h_vals.1, ih _ _ h_vals.2]
      simp only [Nat.cast_list_prod, List.map_map, List.map_cons, List.prod_cons,
        Nat.cast_mul, Nat.cast_pow]
      rw [ENNReal.mul_inv]
      · left
        exact ENNReal.pow_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_pos.ne') _
      · left
        exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    · intro b' hb'
      by_cases hb'_len : b'.length = qc j
      · by_cases hb'_support :
            seed_out ∈ (generateSeedFrom spec qc js (seed_in.addValues b')).support
        · have hb'_eq := vals_eq_of_mem_support_generateSeedFrom' spec qc js seed_in seed_out j b'
            hb'_len hb'_support
          have hvals_eq := vals_eq_of_mem_support_generateSeedFrom' spec qc js seed_in seed_out j
            vals h_vals.1 h_vals.2
          exact (hb' (hb'_eq.trans hvals_eq.symm)).elim
        · exact mul_eq_zero_of_right _ (by rw [probOutput_eq_zero_iff]; grind)
      · rw [probOutput_replicate_uniformOfFintype, if_neg hb'_len, zero_mul]

lemma probOutput_generateSeed' [spec.FiniteRange]
    [DecidableEq spec.QuerySeed] (seed : QuerySeed spec)
    (h : seed ∈ (generateSeed spec qc js).support) : [= seed | generateSeed spec qc js] =
    ((generateSeed spec qc js).finSupport.card : ℝ≥0∞)⁻¹ := by
  convert probOutput_generateSeedFrom spec qc js ∅ seed _ using 1
  · rw [generateSeed_eq_generateSeedFrom]
  · rw [card_finSupport_generateSeed]
  · exact generateSeed_eq_generateSeedFrom spec qc js ▸ h

end OracleComp
