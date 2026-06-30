/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.QueryTracking.CostModel

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
    return rest.prependValues xs

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
    return rest.prependValues xs := rfl

@[simp]
lemma generateSeed_zero :
    generateSeed spec 0 js = (return ∅ : ProbComp (OracleSpec.QuerySeed spec)) := by
  induction js <;> simp [generateSeed, *]

omit [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- Split a seed whose lengths match the budget for `j :: js` into its leading `qc j` answers at
`j` and the remaining seed for `js`. The leading block has length `qc j`, the remainder matches
the budget for `js`, and prepending the block recovers the original seed. -/
private lemma exists_split_of_length_cons {seed : QuerySeed spec}
    (h : ∀ i, (seed i).length = qc i * (j :: js).count i) :
    ∃ (xs : List (spec.Range j)) (rest : QuerySeed spec), xs.length = qc j ∧
      (∀ i, (rest i).length = qc i * js.count i) ∧ rest.prependValues xs = seed := by
  have hlen_j : (seed j).length = qc j * (js.count j + 1) := by rw [h j, List.count_cons_self]
  refine ⟨(seed j).take (qc j), Function.update seed j ((seed j).drop (qc j)), ?_, fun i => ?_, ?_⟩
  · simp [List.length_take, hlen_j, Nat.mul_add]
  · rcases eq_or_ne i j with rfl | hi
    · simp [Function.update_self, List.length_drop, hlen_j, Nat.mul_add]
    · simp only [Function.update_of_ne hi, h i, List.count_cons_of_ne hi.symm]
  · exact QuerySeed.prependValues_take_drop seed j (qc j)

@[simp] lemma support_generateSeed : support (generateSeed spec qc js) =
    {seed : QuerySeed spec | ∀ i, (seed i).length = qc i * js.count i} := by
  induction js with
  | nil =>
    ext seed
    simp [generateSeed_nil, QuerySeed.ext_iff, QuerySeed.empty_apply]
  | cons j js ih =>
    ext seed
    simp only [generateSeed_cons, mem_support_bind_iff, support_replicate, ih, support_pure,
      Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨xs, ⟨hlen, _⟩, rest, hrest_mem, rfl⟩ i
      rcases eq_or_ne i j with rfl | hi
      · simp [List.length_append, hlen, hrest_mem i, List.count_cons_self, Nat.mul_succ,
          Nat.add_comm]
      · simp [QuerySeed.prependValues_of_ne _ _ hi, List.count_cons_of_ne hi.symm, hrest_mem i]
    · intro h
      obtain ⟨xs, rest, hxs_len, hrest_len, rfl⟩ := exists_split_of_length_cons spec qc j js h
      exact ⟨xs, ⟨hxs_len, fun x _ => by simp⟩, rest, hrest_len, rfl⟩

lemma length_eq_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js)) :
    (seed i).length = qc i * js.count i :=
  (support_generateSeed spec qc js ▸ hseed) i

/-- If the seed-generation list `js` contains every oracle family with positive budget, then any
seed sampled by `generateSeed spec qc js` contains at least `qc i` answers for each oracle `i`.

This is the support-level coverage property needed by seeded replay arguments: one occurrence of
`i` in `js` already contributes `qc i` pre-generated answers to the seed at `i`, and additional
occurrences only increase that supply. -/
lemma le_length_of_mem_support_generateSeed_of_covers
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hcover : ∀ j, 0 < qc j → j ∈ js) :
    qc i ≤ (seed i).length := by
  rw [length_eq_of_mem_support_generateSeed spec qc js seed i hseed]
  rcases Nat.eq_zero_or_pos (qc i) with hq0 | hqpos
  · simp [hq0]
  · exact Nat.le_mul_of_pos_right _ (List.count_pos_iff.mpr (hcover i hqpos))

lemma eq_nil_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlen0 : qc i * js.count i = 0) :
    seed i = [] :=
  List.eq_nil_of_length_eq_zero
    ((length_eq_of_mem_support_generateSeed spec qc js seed i hseed).trans hlen0)

lemma ne_nil_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlenPos : 0 < qc i * js.count i) :
    seed i ≠ [] := by
  intro hnil
  have hlen := length_eq_of_mem_support_generateSeed spec qc js seed i hseed
  rw [hnil, List.length_nil] at hlen
  omega

lemma exists_cons_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlenPos : 0 < qc i * js.count i) :
    ∃ u us, seed i = u :: us :=
  List.exists_cons_of_ne_nil
    (ne_nil_of_mem_support_generateSeed spec qc js seed i hseed hlenPos)

lemma tail_length_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlenPos : 0 < qc i * js.count i) :
    (seed i).tail.length = qc i * js.count i - 1 := by
  have hlen := length_eq_of_mem_support_generateSeed spec qc js seed i hseed
  obtain ⟨u, us, hus⟩ := exists_cons_of_mem_support_generateSeed spec qc js seed i hseed hlenPos
  simp only [hus, List.length_cons, List.tail_cons] at hlen ⊢
  omega

lemma probOutput_pop_none_eq_zero_of_count_pos [IsUniformSpec spec]
    (i : ι) (hpos : 0 < qc i * js.count i) :
    Pr[= none | (fun seed => seed.pop i) <$> generateSeed spec qc js] = 0 := by
  rw [probOutput_eq_zero_iff]
  intro hmem
  simp only [support_map] at hmem
  obtain ⟨seed, hseed, hpop⟩ := hmem
  exact ne_nil_of_mem_support_generateSeed spec qc js seed i hseed hpos
    (by simpa [QuerySeed.pop_eq_none_iff] using hpop)

lemma probOutput_pop_some_eq_probOutput_prepend
    (i : ι) (u : spec.Range i) (rest : QuerySeed spec) :
    Pr[= some (u, rest) | (fun seed => seed.pop i) <$> generateSeed spec qc js] =
      Pr[= rest.prependValues [u] | generateSeed spec qc js] := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [probOutput_bind_eq_mul (rest.prependValues [u]) fun seed' _ hs =>
    (QuerySeed.eq_prependValues_of_pop_eq_some ((mem_support_pure_iff' _ _).mp hs)).symm]
  simp

@[simp] lemma finSupport_generateSeed_ne_empty [DecidableEq (QuerySeed spec)] :
    finSupport (generateSeed spec qc js) ≠ ∅ :=
  (finSupport_nonempty_of_liftM_PMF _).ne_empty

omit [DecidableEq ι] in
/-- The product-of-inverses identity assembling the `j :: js` answer from the `j` and `js`
parts: `(c ^ qc j)⁻¹ * (∏ js)⁻¹ = (∏ (j :: js))⁻¹` over `ℝ≥0∞`, valid because every factor is
a finite natural-number cast. -/
private lemma inv_natCast_pow_mul_inv_list_prod (qc : ι → ℕ) (j : ι) (js : List ι) (f : ι → ℕ) :
    ((↑(f j ^ qc j) : ENNReal))⁻¹ * (↑(js.map (fun j => f j ^ qc j)).prod)⁻¹ =
      (↑((j :: js).map (fun j => f j ^ qc j)).prod)⁻¹ := by
  rw [List.map_cons, List.prod_cons, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Factor the probability of sampling a fixed `seed` for `j :: js` into the probability of its
leading `qc j` answers at `j` times the probability of the remaining seed for `js`. The split
`rest.prependValues xs = seed` is unique because `prependValues` of a length-`qc j` block is
injective, so the outer and inner binds each collapse to a single summand. -/
private lemma probOutput_generateSeed_cons_eq_mul (seed rest : QuerySeed spec)
    (xs : List (spec.Range j)) (hxs_len : xs.length = qc j)
    (hseed_eq : rest.prependValues xs = seed) :
    Pr[= seed | generateSeed spec qc (j :: js)] =
      Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] *
        Pr[= rest | generateSeed spec qc js] := by
  obtain ⟨hxs_eq, hrest_eq⟩ := QuerySeed.eq_of_prependValues_eq seed rest xs hxs_len hseed_eq
  have hinner : Pr[= seed | generateSeed spec qc js >>=
      fun rest' => (return rest'.prependValues xs : ProbComp (QuerySeed spec))] =
      Pr[= rest | generateSeed spec qc js] :=
    (probOutput_bind_eq_mul (y := seed) rest fun rest' _ hs => hrest_eq ▸
      (QuerySeed.eq_of_prependValues_eq seed rest' xs hxs_len
        ((mem_support_pure_iff' (m := ProbComp) _ _).mp hs)).2).trans (by simp [hseed_eq])
  rw [generateSeed_cons, ← hinner]
  refine probOutput_bind_eq_mul (y := seed) xs fun xs' hxs' hseed' => ?_
  obtain ⟨rest', _, hpure⟩ := (mem_support_bind_iff _ _ _).mp hseed'
  exact (QuerySeed.eq_of_prependValues_eq seed rest' xs'
    (support_replicate .. ▸ hxs').1 ((mem_support_pure_iff' (m := ProbComp) _ _).mp hpure)).1.trans
    hxs_eq.symm

lemma probOutput_generateSeed [spec.Fintype] (seed : QuerySeed spec)
    (h : seed ∈ support (generateSeed spec qc js)) :
    Pr[= seed | generateSeed spec qc js] =
      (↑(js.map (fun j => (Fintype.card (spec.Range j)) ^ qc j)).prod)⁻¹ := by
  induction js generalizing seed with
  | nil =>
    obtain rfl : seed = ∅ := by simpa using h
    simp
  | cons j js ih =>
    have hlen : ∀ i, (seed i).length = qc i * (j :: js).count i := by
      rw [support_generateSeed spec qc (j :: js)] at h
      simpa [Set.mem_setOf_eq] using h
    obtain ⟨xs, rest, hxs_len, hrest_len, hseed_eq⟩ :=
      exists_split_of_length_cons spec qc j js hlen
    have hrest_mem : rest ∈ support (generateSeed spec qc js) := by
      simpa [support_generateSeed spec qc js] using hrest_len
    rw [probOutput_generateSeed_cons_eq_mul spec qc j js seed rest xs hxs_len hseed_eq,
      probOutput_replicate_uniformSample hxs_len, ih rest hrest_mem,
      inv_natCast_pow_mul_inv_list_prod qc j js fun j => Fintype.card (spec.Range j)]

lemma probOutput_generateSeed' [spec.Fintype] [DecidableEq (QuerySeed spec)]
    (seed : QuerySeed spec) (h : seed ∈ support (generateSeed spec qc js)) :
    Pr[= seed | generateSeed spec qc js] =
      1 / (finSupport (generateSeed spec qc js)).card := by
  rw [probOutput_generateSeed spec qc js seed h]
  exact probOutput_eq_inv_finSupport_card_of_liftM_PMF fun s hs =>
    probOutput_generateSeed spec qc js s hs

lemma evalDist_generateSeed_eq_of_countEq [IsUniformSpec spec]
    (qc' : ι → ℕ) (js' : List ι)
    (hcount : ∀ i, qc i * js.count i = qc' i * js'.count i) :
    𝒟[generateSeed spec qc js] = 𝒟[generateSeed spec qc' js'] := by
  classical
  have hsupp : support (generateSeed spec qc js) = support (generateSeed spec qc' js') := by
    simp only [support_generateSeed, hcount]
  ext seed
  change Pr[= seed | generateSeed spec qc js] = Pr[= seed | generateSeed spec qc' js']
  by_cases hmem : seed ∈ support (generateSeed spec qc js)
  · have hfin : finSupport (generateSeed spec qc js) = finSupport (generateSeed spec qc' js') :=
      finSupport_eq_of_support_eq_coe (by rw [hsupp, coe_finSupport])
    rw [probOutput_generateSeed' spec qc js seed hmem,
      probOutput_generateSeed' spec qc' js' seed (hsupp ▸ hmem)]
    simp [hfin]
  · rw [(probOutput_eq_zero_iff (generateSeed spec qc js) seed).2 hmem,
      (probOutput_eq_zero_iff (generateSeed spec qc' js') seed).2 (hsupp ▸ hmem)]

/-- Prepending one answer `u` at `t` and decrementing the budget at `t` is a support-preserving
bijection: the seed `s'.prependValues [u]` lies in the support of `generateSeed spec qc js` exactly
when `s'` lies in the support of the count-reduced generator on `js.dedup`. Membership in either
support is the per-oracle length condition, and the two conditions match coordinatewise. -/
private lemma support_prependValues_iff_of_count_pos {t : ι} (u : spec.Range t)
    (s' : QuerySeed spec) (hpos : 0 < qc t * js.count t) :
    s'.prependValues [u] ∈ support (generateSeed spec qc js) ↔
      s' ∈ support (generateSeed spec
        (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1)) js.dedup) := by
  have ht_mem : t ∈ js := by
    by_contra h; simp [List.count_eq_zero_of_not_mem h] at hpos
  simp only [support_generateSeed, Set.mem_setOf_eq]
  constructor <;> intro h i <;> specialize h i <;> rcases eq_or_ne i t with rfl | hi
  · simp only [QuerySeed.prependValues_singleton, List.length_cons, Function.update_self,
      List.count_dedup, ht_mem, ↓reduceIte, mul_one] at h ⊢
    omega
  · simp only [QuerySeed.prependValues_of_ne _ _ hi, Function.update_of_ne hi,
      List.count_dedup] at h ⊢
    by_cases hi_mem : i ∈ js <;> simp_all [List.count_eq_zero_of_not_mem]
  · simp only [QuerySeed.prependValues_singleton, List.length_cons, Function.update_self,
      List.count_dedup, ht_mem, ↓reduceIte, mul_one] at h ⊢
    omega
  · simp only [QuerySeed.prependValues_of_ne _ _ hi, Function.update_of_ne hi,
      List.count_dedup] at h ⊢
    by_cases hi_mem : i ∈ js <;> simp_all [List.count_eq_zero_of_not_mem]

/-- ENNReal product-erase identity behind the prepend formula: for a list `l` containing `t` and
`ℕ`-valued weights `f`, `g` that agree on `l.erase t` with `f t = c * g t`, the inverse products
satisfy `(∏ l.map f)⁻¹ = c⁻¹ * (∏ l.map g)⁻¹`. Splitting off the `t` factor turns the
shared remaining product into the common cofactor, leaving the `c⁻¹` from the `t` block. -/
private lemma inv_natCast_list_prod_map_eq_inv_mul {ι : Type*} [DecidableEq ι]
    (l : List ι) {t : ι} (ht : t ∈ l) (c : ℕ) (f g : ι → ℕ)
    (hft : f t = c * g t) (hfg : ∀ j ∈ l.erase t, f j = g j) :
    ((↑(l.map f).prod : ENNReal))⁻¹ = (↑c)⁻¹ * (↑(l.map g).prod)⁻¹ := by
  have hrest : (l.erase t).map g = (l.erase t).map f :=
    List.map_congr_left fun j hj => (hfg j hj).symm
  rw [← List.prod_map_erase f ht, ← List.prod_map_erase g ht, hrest, hft, mul_assoc,
    Nat.cast_mul, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))) (Or.inl (ENNReal.natCast_ne_top _))]

lemma probOutput_generateSeed_prependValues [IsUniformSpec spec]
    {t : ι} (u : spec.Range t) (s' : QuerySeed spec)
    (hpos : 0 < qc t * js.count t) :
    Pr[= s'.prependValues [u] | generateSeed spec qc js] =
      (↑(Fintype.card (spec.Range t)))⁻¹ *
        Pr[= s' | generateSeed spec
          (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1))
          js.dedup] := by
  set N : ι → ℕ := fun i => qc i * js.count i
  set qc_red := Function.update N t (N t - 1)
  have ht_mem : t ∈ js := List.count_pos_iff.mp (Nat.pos_of_mul_pos_left hpos)
  have supp_iff := support_prependValues_iff_of_count_pos spec qc js u s' hpos
  by_cases hmem : s'.prependValues [u] ∈ support (generateSeed spec qc js)
  · have hmem_red := supp_iff.mp hmem
    have hcount : ∀ i, N i = N i * js.dedup.count i := fun i => by
      by_cases hi : i ∈ js <;> simp [N, List.count_dedup, hi, List.count_eq_zero_of_not_mem]
    have hmem_canon : s'.prependValues [u] ∈ support (generateSeed spec N js.dedup) := by
      rw [support_generateSeed, Set.mem_setOf_eq] at hmem ⊢
      exact fun i => (hmem i).trans (hcount i)
    rw [probOutput_congr rfl (evalDist_generateSeed_eq_of_countEq spec qc js N js.dedup hcount),
      probOutput_generateSeed spec N js.dedup _ hmem_canon,
      probOutput_generateSeed spec qc_red js.dedup _ hmem_red]
    refine inv_natCast_list_prod_map_eq_inv_mul js.dedup
      (List.mem_dedup.mpr ht_mem) _ _ _ ?_ fun j hj => ?_
    · simpa only [qc_red, Function.update_self] using (mul_pow_sub_one hpos.ne' _).symm
    · simp only [qc_red, Function.update_of_ne ((List.nodup_dedup js).mem_erase_iff.mp hj).1]
  · rw [(probOutput_eq_zero_iff _ _).2 hmem,
      (probOutput_eq_zero_iff _ _).2 (mt supp_iff.mpr hmem), mul_zero]

end lemmas

section coverage

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- `SeedListCovers qb js` means that every oracle family with positive query budget appears in
the seed-generation list `js`.

When this holds, any seed sampled from `generateSeed spec qb js` supplies enough pre-generated
answers to cover one full execution of a computation satisfying the structural bound `qb`. -/
def SeedListCovers (qb : ι → ℕ) (js : List ι) : Prop :=
  ∀ t, 0 < qb t → t ∈ js

/-- Any seed sampled from `generateSeed spec qb js` has at least `qb t` entries for each
oracle `t`, provided `js` lists every oracle family with positive budget. -/
lemma generateSeed_covers_queryBound
    (qb : ι → ℕ) (js : List ι) {seed : QuerySeed spec}
    (hjs : SeedListCovers qb js)
    (hseed : seed ∈ support (generateSeed spec qb js)) :
    ∀ t, qb t ≤ (seed t).length :=
  fun t =>
    le_length_of_mem_support_generateSeed_of_covers
      (spec := spec) (qc := qb) (js := js) seed t hseed hjs

end coverage

section unitCost

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

private theorem queryCostExactly_replicate_probComp
    {β : Type} (oa : ProbComp β) {k : ℕ}
    (h : AddWriterT.QueryCostExactly (probCompUnitQueryRun oa) k) :
    ∀ n : ℕ, AddWriterT.QueryCostExactly (probCompUnitQueryRun (oa.replicate n)) (n * k) := by
  intro n
  induction n with
  | zero =>
      simpa using AddWriterT.queryCostExactly_pure ([] : List β)
  | succ n ih =>
      simpa [probCompUnitQueryRun, OracleComp.replicate_succ_bind, simulateQ_bind, simulateQ_pure,
        simulateQ_map, Nat.succ_mul, Nat.add_comm] using
        AddWriterT.queryCostExactly_bind (n₁ := k) (n₂ := n * k)
          (oa := probCompUnitQueryRun oa)
          (f := fun a => List.cons a <$> probCompUnitQueryRun (oa.replicate n)) h
          fun a => AddWriterT.queryCostExactly_map (List.cons a) ih

/-- The number of uniform-oracle calls made by `generateSeed spec qc js` is exactly
`(js.map fun j => qc j * sampleCost j).sum`, with each of the `qc j` samples at oracle
`j` costing `sampleCost j`. -/
theorem generateSeed_queryCostExactly
    (qc : ι → ℕ) (js : List ι) (sampleCost : ι → ℕ)
    (hSample :
      ∀ j, AddWriterT.QueryCostExactly
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j)) :
    AddWriterT.QueryCostExactly
      (probCompUnitQueryRun (generateSeed spec qc js))
      ((js.map fun j => qc j * sampleCost j).sum) := by
  induction js with
  | nil =>
      simpa [probCompUnitQueryRun] using
        (AddWriterT.queryCostExactly_pure (∅ : QuerySeed spec))
  | cons j js ih =>
      simpa [probCompUnitQueryRun, OracleComp.generateSeed_cons, simulateQ_bind, simulateQ_pure,
        simulateQ_map, List.sum_cons, Nat.add_comm] using
        AddWriterT.queryCostExactly_bind (m := ProbComp)
          (n₁ := qc j * sampleCost j)
          (n₂ := (js.map fun j => qc j * sampleCost j).sum)
          (oa := probCompUnitQueryRun (replicate (qc j) ($ᵗ spec.Range j)))
          (f := fun xs =>
            (fun rest : QuerySeed spec => rest.prependValues xs) <$>
              probCompUnitQueryRun (generateSeed spec qc js))
          (queryCostExactly_replicate_probComp ($ᵗ spec.Range j) (hSample j) (qc j))
          fun xs => AddWriterT.queryCostExactly_map (m := ProbComp)
            (fun rest : QuerySeed spec => rest.prependValues xs) ih

open ENNReal in
/-- The expected number of uniform-oracle calls made by `generateSeed spec qc js` equals
`∑ j in js, qc j * sampleCost j`, i.e. each of the `qc j` samples at oracle `j` costs
`sampleCost j`. -/
theorem generateSeed_expectedQueryCount_eq
    (qc : ι → ℕ) (js : List ι) (sampleCost : ι → ℕ)
    (hSample :
      ∀ j, AddWriterT.QueryCostExactly
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j)) :
    AddWriterT.expectedCostNat (probCompUnitQueryRun (generateSeed spec qc js)) =
      ((js.map fun j => qc j * sampleCost j).sum : ENNReal) :=
  AddWriterT.expectedCostNat_eq_of_queryCostExactly
    (generateSeed_queryCostExactly (spec := spec) qc js sampleCost hSample)

end unitCost

end OracleComp
