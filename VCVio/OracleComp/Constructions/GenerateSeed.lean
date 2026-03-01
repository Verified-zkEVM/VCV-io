/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
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
  induction js with
  | nil => rfl
  | cons j js ih => simp [generateSeed, ih]

@[simp] lemma support_generateSeed : support (generateSeed spec qc js) =
    {seed : QuerySeed spec | ∀ i, (seed i).length = qc i * js.count i} := by
  induction js with
  | nil =>
    simp; ext seed; simp
    constructor
    · intro h; rw [h]; simp
    · intro h; funext i; have := h i; simp at this; exact this
  | cons j js ih =>
    ext seed
    simp only [generateSeed_cons, Set.mem_setOf_eq]
    rw [mem_support_bind_iff]
    constructor
    · rintro ⟨xs, hxs, hrest⟩
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest_mem, hpure⟩ := hrest
      rw [support_pure, Set.mem_singleton_iff] at hpure; subst hpure
      rw [ih, Set.mem_setOf_eq] at hrest_mem
      rw [support_replicate] at hxs
      obtain ⟨hlen, _⟩ := hxs
      intro i
      by_cases hi : i = j
      · subst hi
        rw [QuerySeed.prependValues_self, List.length_append, hlen, hrest_mem i,
          List.count_cons_self, Nat.mul_add, Nat.mul_one, Nat.add_comm]
      · rw [QuerySeed.prependValues_of_ne _ _ hi, List.count_cons_of_ne (Ne.symm hi)]
        exact hrest_mem i
    · intro h
      let xs : List (spec.Range j) := (seed j).take (qc j)
      let rest : QuerySeed spec := Function.update seed j ((seed j).drop (qc j))
      have hlen_j : (seed j).length = qc j * (List.count j js + 1) := by
        rw [h j, List.count_cons_self]
      have hxs_len : xs.length = qc j := by
        simp only [xs, List.length_take, hlen_j, Nat.mul_add, Nat.mul_one]
        exact Nat.min_eq_left (Nat.le_add_left _ _)
      have hrest_len : ∀ i, (rest i).length = qc i * List.count i js := by
        intro i
        by_cases hi : i = j
        · subst hi
          simp only [rest, Function.update_self, List.length_drop, hlen_j,
            Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
        · simp only [rest, Function.update_of_ne hi, h i, List.count_cons_of_ne (Ne.symm hi)]
      refine ⟨xs, ?_, ?_⟩
      · rw [support_replicate]
        exact ⟨hxs_len, fun x _ => by simp [support_uniformSample]⟩
      · rw [mem_support_bind_iff]
        refine ⟨rest, ?_, ?_⟩
        · rw [ih, Set.mem_setOf_eq]; exact hrest_len
        · rw [support_pure, Set.mem_singleton_iff]
          ext i
          by_cases hi : i = j
          · subst hi; simp [QuerySeed.prependValues_self, xs, rest, List.take_append_drop]
          · rw [QuerySeed.prependValues_of_ne _ _ hi]; simp [rest, Function.update_of_ne hi]

lemma length_eq_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js)) :
    (seed i).length = qc i * js.count i := by
  have := (support_generateSeed (spec := spec) (qc := qc) (js := js)).symm ▸ hseed
  simpa [Set.mem_setOf_eq] using (this i)

lemma eq_nil_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlen0 : qc i * js.count i = 0) :
    seed i = [] :=
  List.eq_nil_of_length_eq_zero
    ((length_eq_of_mem_support_generateSeed (spec := spec) (qc := qc) (js := js)
      seed i hseed).trans hlen0)

lemma ne_nil_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlenPos : 0 < qc i * js.count i) :
    seed i ≠ [] := by
  intro hnil
  have hlen := length_eq_of_mem_support_generateSeed (spec := spec) (qc := qc) (js := js)
    seed i hseed
  rw [hnil, List.length_nil] at hlen
  exact absurd hlen.symm (ne_of_gt hlenPos)

lemma exists_cons_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlenPos : 0 < qc i * js.count i) :
    ∃ u us, seed i = u :: us :=
  List.exists_cons_of_ne_nil
    (ne_nil_of_mem_support_generateSeed (spec := spec) (qc := qc) (js := js)
      seed i hseed hlenPos)

lemma tail_length_of_mem_support_generateSeed
    (seed : QuerySeed spec) (i : ι)
    (hseed : seed ∈ support (generateSeed spec qc js))
    (hlenPos : 0 < qc i * js.count i) :
    (seed i).tail.length = qc i * js.count i - 1 := by
  have hlen := length_eq_of_mem_support_generateSeed (spec := spec) (qc := qc) (js := js)
    seed i hseed
  rcases exists_cons_of_mem_support_generateSeed (spec := spec) (qc := qc) (js := js)
      seed i hseed hlenPos with ⟨u, us, hus⟩
  rw [hus] at hlen ⊢; simp at hlen ⊢; omega

lemma probOutput_pop_none_eq_zero_of_count_pos [spec.Fintype] [spec.Inhabited]
    (i : ι) (hpos : 0 < qc i * js.count i) :
    Pr[= none | (fun seed => seed.pop i) <$> generateSeed spec qc js] = 0 := by
  rw [probOutput_eq_zero_iff]
  intro hmem
  simp only [support_map] at hmem
  rcases hmem with ⟨seed, hseed, hpop⟩
  have hnil : seed i = [] := by simpa [QuerySeed.pop_eq_none_iff] using hpop
  exact (ne_nil_of_mem_support_generateSeed (spec := spec) (qc := qc) (js := js)
    seed i hseed hpos) hnil

lemma probOutput_pop_some_eq_probOutput_prepend
    (i : ι) (u : spec.Range i) (rest : QuerySeed spec) :
    Pr[= some (u, rest) | (fun seed => seed.pop i) <$> generateSeed spec qc js] =
      Pr[= rest.prependValues [u] | generateSeed spec qc js] := by
  have huniq :
      ∀ seed' ∈ support (generateSeed spec qc js),
        some (u, rest) ∈ support
          (pure (seed'.pop i) : ProbComp (Option (spec.Range i × QuerySeed spec))) →
        seed' = rest.prependValues [u] := by
    intro seed' _ hs
    have hpop : seed'.pop i = some (u, rest) := by
      simpa [support_pure, Set.mem_singleton_iff] using hs.symm
    have hcons : u :: rest i = seed' i :=
      QuerySeed.cons_of_pop_eq_some seed' i u rest hpop
    have hrest : rest = Function.update seed' i ((seed' i).tail) :=
      QuerySeed.rest_eq_update_tail_of_pop_eq_some seed' i u rest hpop
    apply QuerySeed.ext
    intro j
    by_cases hj : j = i
    · subst hj
      calc
        seed' j = u :: rest j := hcons.symm
        _ = (rest.prependValues [u]) j := by simp [QuerySeed.prependValues]
    · have hrestj : rest j = seed' j := by
        exact by
          have := congrArg (fun s => s j) hrest
          simpa [Function.update_of_ne hj] using this
      calc
        seed' j = rest j := hrestj.symm
        _ = (rest.prependValues [u]) j := by simp [QuerySeed.prependValues, Function.update_of_ne hj]
  have hpop_prepend :
      (rest.prependValues [u]).pop i = some (u, rest) := by
    have hcons_pre : (rest.prependValues [u]) i = u :: rest i := by
      simp [QuerySeed.prependValues]
    have hpop' :
        (rest.prependValues [u]).pop i =
          some (u, Function.update (rest.prependValues [u]) i (rest i)) := by
      exact QuerySeed.pop_eq_some_of_cons (seed := rest.prependValues [u]) (i := i) (u := u)
        (us := rest i) hcons_pre
    have hupdate : Function.update (rest.prependValues [u]) i (rest i) = rest := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj, QuerySeed.prependValues]
    simp [hupdate, hpop']
  calc
    Pr[= some (u, rest) | (fun seed => seed.pop i) <$> generateSeed spec qc js]
        = Pr[= some (u, rest) |
            generateSeed spec qc js >>= fun seed =>
              (pure (seed.pop i) : ProbComp (Option (spec.Range i × QuerySeed spec)))] := by
            rfl
    _ = Pr[= rest.prependValues [u] | generateSeed spec qc js] *
          Pr[= some (u, rest) | pure ((rest.prependValues [u]).pop i)] := by
            exact probOutput_bind_eq_mul (mx := generateSeed spec qc js)
              (my := fun seed => (pure (seed.pop i) : ProbComp (Option (spec.Range i × QuerySeed spec))))
              (y := some (u, rest)) (x := rest.prependValues [u]) huniq
    _ = Pr[= rest.prependValues [u] | generateSeed spec qc js] * 1 := by
          simp [hpop_prepend]
    _ = Pr[= rest.prependValues [u] | generateSeed spec qc js] := by simp

@[simp] lemma finSupport_generateSeed_ne_empty [DecidableEq (QuerySeed spec)] :
    finSupport (generateSeed spec qc js) ≠ ∅ := by
  intro h
  have hf : Pr[⊥ | generateSeed spec qc js] = 1 := by
    rw [probFailure_eq_one_iff]
    have := coe_finSupport (mx := generateSeed spec qc js)
    rw [h, Finset.coe_empty] at this
    exact this.symm
  exact zero_ne_one (probFailure_eq_zero (mx := generateSeed spec qc js) ▸ hf)

lemma probOutput_generateSeed [spec.Fintype] (seed : QuerySeed spec)
    (h : seed ∈ support (generateSeed spec qc js)) :
    Pr[= seed | generateSeed spec qc js] =
      (↑(js.map (fun j => (Fintype.card (spec.Range j)) ^ qc j)).prod)⁻¹ := by
  classical
  induction js generalizing seed with
  | nil =>
    have hseed : seed = (∅ : QuerySeed spec) := by simpa using h
    subst hseed; simp
  | cons j js ih =>
    have hlen : ∀ i, (seed i).length = qc i * List.count i (j :: js) := by
      have h' := h
      rw [support_generateSeed (spec := spec) (qc := qc) (js := (j :: js))] at h'
      simpa [Set.mem_setOf_eq] using h'
    let xs : List (spec.Range j) := (seed j).take (qc j)
    let rest : QuerySeed spec := Function.update seed j ((seed j).drop (qc j))
    have hxs_len : xs.length = qc j := by
      have hlen_j : (seed j).length = qc j * (List.count j js + 1) := by
        simpa [List.count_cons_self] using hlen j
      have hqc_le : qc j ≤ (seed j).length := by
        rw [hlen_j]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      simp [xs, List.length_take, Nat.min_eq_left hqc_le]
    have hrest_len : ∀ i, (rest i).length = qc i * List.count i js := by
      intro i
      by_cases hi : i = j
      · cases hi
        have hlen_j : (seed j).length = qc j * (List.count j js + 1) := by
          simpa [List.count_cons_self] using hlen j
        simp [rest, List.length_drop, hlen_j, Nat.mul_add]
      · have := hlen i
        simpa [rest, Function.update_of_ne hi, List.count_cons_of_ne (Ne.symm hi)] using this
    have hrest_mem : rest ∈ support (generateSeed spec qc js) := by
      simpa [support_generateSeed (spec := spec) (qc := qc) (js := js)] using hrest_len
    have hseed_eq : rest.prependValues xs = seed :=
      QuerySeed.prependValues_take_drop seed j (qc j)
    -- Uniqueness: any (xs', rest') satisfying rest'.prependValues xs' = seed must equal (xs, rest)
    have hxs_unique :
        ∀ xs' ∈ support (replicate (qc j) ($ᵗ spec.Range j)),
          seed ∈ support (do
            let rest' ← generateSeed spec qc js
            return rest'.prependValues xs') → xs' = xs := by
      intro xs' hxs' hseed'
      rw [mem_support_bind_iff] at hseed'
      obtain ⟨rest', _, hpure⟩ := hseed'
      have hEq : rest'.prependValues xs' = seed := by
        simpa [support_pure, Set.mem_singleton_iff] using hpure.symm
      have hlen_xs' : xs'.length = qc j := by
        rw [support_replicate] at hxs'; exact hxs'.1
      exact (QuerySeed.eq_of_prependValues_eq seed rest' xs' hlen_xs' hEq).1 ▸ rfl
    have hrest_unique :
        ∀ rest' ∈ support (generateSeed spec qc js),
          seed ∈ support (return rest'.prependValues xs : ProbComp (QuerySeed spec)) → rest' = rest := by
      intro rest' _ hseed'
      have hEq : rest'.prependValues xs = seed := by
        simpa [support_pure, Set.mem_singleton_iff] using hseed'.symm
      exact (QuerySeed.eq_of_prependValues_eq seed rest' xs hxs_len hEq).2
    -- Factor probability via probOutput_bind_eq_mul
    have houter :
        Pr[= seed | generateSeed spec qc (j :: js)] =
          Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] *
            Pr[= seed | (do
              let rest' ← generateSeed spec qc js
              return rest'.prependValues xs)] := by
      simpa [generateSeed_cons] using
        probOutput_bind_eq_mul (mx := replicate (qc j) ($ᵗ spec.Range j))
          (my := fun xs' => do let rest' ← generateSeed spec qc js; return rest'.prependValues xs')
          (y := seed) xs hxs_unique
    have hinner :
        Pr[= seed | (do
          let rest' ← generateSeed spec qc js
          return rest'.prependValues xs)] =
        Pr[= rest | generateSeed spec qc js] := by
      have := probOutput_bind_eq_mul
        (mx := generateSeed spec qc js)
        (my := fun rest' => (return rest'.prependValues xs : ProbComp (QuerySeed spec)))
        (y := seed) rest hrest_unique
      simpa [hseed_eq, mul_one] using this
    -- Assemble final result
    calc
      Pr[= seed | generateSeed spec qc (j :: js)]
          = Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] *
              Pr[= rest | generateSeed spec qc js] := by rw [houter, hinner]
      _ = (↑(Fintype.card (spec.Range j) ^ qc j) : ENNReal)⁻¹ *
            (↑(js.map (fun j => Fintype.card (spec.Range j) ^ qc j)).prod)⁻¹ := by
            rw [probOutput_replicate_uniformSample hxs_len, ih rest hrest_mem]
      _ = (↑((j :: js).map (fun j => Fintype.card (spec.Range j) ^ qc j)).prod)⁻¹ := by
            simp only [List.map, List.prod_cons, Nat.cast_mul]
            have ha : ((↑(Fintype.card (spec.Range j)) : ENNReal) ^ qc j) ≠ ⊤ :=
              ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
            have hb : (List.map (Nat.cast ∘ fun j => Fintype.card (spec.Range j) ^ qc j) js).prod ≠ ⊤ :=
              ENNReal.list_prod_natCast_ne_top _ js
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (ENNReal.mul_inv (a := (↑(Fintype.card (spec.Range j)) : ENNReal) ^ qc j)
                (b := (List.map (Nat.cast ∘ fun j => Fintype.card (spec.Range j) ^ qc j) js).prod)
                (ha := Or.inr hb) (hb := Or.inl ha)).symm

lemma probOutput_generateSeed' [spec.Fintype]
    [DecidableEq (QuerySeed spec)] (seed : QuerySeed spec)
    (h : seed ∈ support (generateSeed spec qc js)) :
    Pr[= seed | generateSeed spec qc js] =
      1 / (finSupport (generateSeed spec qc js)).card := by
  classical
  rw [probOutput_generateSeed spec qc js seed h]
  exact HasEvalPMF.probOutput_eq_inv_finSupport_card fun s hs =>
    probOutput_generateSeed spec qc js s hs

lemma evalDist_generateSeed_eq_of_countEq [spec.Fintype] [spec.Inhabited]
    (qc' : ι → ℕ) (js' : List ι)
    (hcount : ∀ i, qc i * js.count i = qc' i * js'.count i) :
    evalDist (generateSeed spec qc js) = evalDist (generateSeed spec qc' js') := by
  classical
  ext seed
  change Pr[= seed | generateSeed spec qc js] = Pr[= seed | generateSeed spec qc' js']
  by_cases hmem : seed ∈ support (generateSeed spec qc js)
  · have hsupp : ∀ i, (seed i).length = qc i * js.count i := by
      simpa [Set.mem_setOf_eq, support_generateSeed (spec := spec) (qc := qc) (js := js)] using hmem
    have hmem' : seed ∈ support (generateSeed spec qc' js') := by
      rw [support_generateSeed (spec := spec) (qc := qc') (js := js'), Set.mem_setOf_eq]
      intro i
      exact (hsupp i).trans (hcount i)
    have hsupportEq :
        support (generateSeed spec qc js) = support (generateSeed spec qc' js') := by
      ext s
      constructor
      · intro hs
        rw [support_generateSeed (spec := spec) (qc := qc') (js := js'), Set.mem_setOf_eq]
        have hs0 : ∀ i, (s i).length = qc i * js.count i := by
          simpa [Set.mem_setOf_eq, support_generateSeed (spec := spec) (qc := qc) (js := js)] using hs
        intro i
        exact (hs0 i).trans (hcount i)
      · intro hs
        rw [support_generateSeed (spec := spec) (qc := qc) (js := js), Set.mem_setOf_eq]
        have hs0 : ∀ i, (s i).length = qc' i * js'.count i := by
          simpa [Set.mem_setOf_eq, support_generateSeed (spec := spec) (qc := qc') (js := js')] using hs
        intro i
        exact (hs0 i).trans ((hcount i).symm)
    have hfin :
        finSupport (generateSeed spec qc js) = finSupport (generateSeed spec qc' js') := by
      apply finSupport_eq_of_support_eq_coe
      rw [hsupportEq, coe_finSupport]
    rw [probOutput_generateSeed' (spec := spec) (qc := qc) (js := js) seed hmem,
      probOutput_generateSeed' (spec := spec) (qc := qc') (js := js') seed hmem']
    simp [hfin]
  · have hsupp : seed ∉ support (generateSeed spec qc' js') := by
      intro hmem'
      apply hmem
      rw [support_generateSeed (spec := spec) (qc := qc) (js := js), Set.mem_setOf_eq]
      have hs0 : ∀ i, (seed i).length = qc' i * js'.count i := by
        simpa [Set.mem_setOf_eq, support_generateSeed (spec := spec) (qc := qc') (js := js')] using hmem'
      intro i
      exact (hs0 i).trans ((hcount i).symm)
    have hzero : Pr[= seed | generateSeed spec qc js] = 0 :=
      (probOutput_eq_zero_iff (generateSeed spec qc js) seed).2 hmem
    have hzero' : Pr[= seed | generateSeed spec qc' js'] = 0 :=
      (probOutput_eq_zero_iff (generateSeed spec qc' js') seed).2 hsupp
    rw [hzero, hzero']

lemma probOutput_generateSeed_prependValues [spec.Fintype] [spec.Inhabited]
    {t : ι} (u : spec.Range t) (s' : QuerySeed spec)
    (hpos : 0 < qc t * js.count t) :
    Pr[= s'.prependValues [u] | generateSeed spec qc js] =
      (↑(Fintype.card (spec.Range t)))⁻¹ *
        Pr[= s' | generateSeed spec
          (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1))
          js.dedup] := by
  classical
  set N : ι → ℕ := fun i => qc i * js.count i
  set qc_red := Function.update N t (N t - 1)
  have ht_pos : 0 < N t := hpos
  have ht_mem : t ∈ js := by
    by_contra h; simp [List.count_eq_zero_of_not_mem h] at hpos
  have ht_dedup : t ∈ js.dedup := List.mem_dedup.mpr ht_mem
  have supp_iff : s'.prependValues [u] ∈ support (generateSeed spec qc js) ↔
      s' ∈ support (generateSeed spec qc_red js.dedup) := by
    simp only [support_generateSeed, Set.mem_setOf_eq]
    constructor <;> intro h <;> intro i <;> specialize h i
    · by_cases hi : i = t
      · subst hi
        simp only [QuerySeed.prependValues_singleton, List.length_cons] at h
        simp only [qc_red, Function.update_self, List.count_dedup, ht_mem, ↓reduceIte, N]
        omega
      · simp only [QuerySeed.prependValues_of_ne _ _ hi] at h
        simp only [qc_red, Function.update_of_ne hi]
        by_cases hi_mem : i ∈ js
        · rw [List.count_dedup, if_pos hi_mem, mul_one]; exact h
        · rw [List.count_eq_zero_of_not_mem hi_mem, mul_zero] at h
          rw [List.count_dedup, if_neg hi_mem, mul_zero]; exact h
    · by_cases hi : i = t
      · subst hi
        simp only [qc_red, Function.update_self, List.count_dedup, ht_mem, ↓reduceIte,
          mul_one, N] at h
        simp only [QuerySeed.prependValues_singleton, List.length_cons, h]; omega
      · simp only [qc_red, Function.update_of_ne hi] at h
        simp only [QuerySeed.prependValues_of_ne _ _ hi]
        by_cases hi_mem : i ∈ js
        · rw [List.count_dedup, if_pos hi_mem, mul_one] at h; exact h
        · rw [List.count_dedup, if_neg hi_mem, mul_zero] at h
          rw [List.count_eq_zero_of_not_mem hi_mem, mul_zero]
          exact h
  by_cases hmem : s'.prependValues [u] ∈ support (generateSeed spec qc js)
  · have hmem_red := supp_iff.mp hmem
    have hmem_canon : s'.prependValues [u] ∈ support (generateSeed spec N js.dedup) := by
      rw [support_generateSeed, Set.mem_setOf_eq]; intro i
      rw [support_generateSeed, Set.mem_setOf_eq] at hmem
      by_cases hi_mem : i ∈ js
      · rw [List.count_dedup, if_pos hi_mem, mul_one]; exact hmem i
      · rw [List.count_dedup, if_neg hi_mem, mul_zero]
        have h := hmem i; rw [List.count_eq_zero_of_not_mem hi_mem, mul_zero] at h; exact h
    have hLHS : Pr[= s'.prependValues [u] | generateSeed spec qc js] =
        Pr[= s'.prependValues [u] | generateSeed spec N js.dedup] :=
      congrFun (congrArg DFunLike.coe (evalDist_generateSeed_eq_of_countEq spec qc js N js.dedup
        (fun i => by
          simp only [N]
          by_cases hi : i ∈ js
          · rw [List.count_dedup, if_pos hi]; ring
          · rw [List.count_dedup, if_neg hi,
              List.count_eq_zero_of_not_mem hi]; simp))) _
    rw [hLHS,
      probOutput_generateSeed spec N js.dedup _ hmem_canon,
      probOutput_generateSeed spec qc_red js.dedup _ hmem_red]
    set f := fun j => Fintype.card (spec.Range j) ^ N j
    set g := fun j => Fintype.card (spec.Range j) ^ qc_red j
    have hperm := List.perm_cons_erase ht_dedup
    have hprod_f : (js.dedup.map f).prod = f t * ((js.dedup.erase t).map f).prod := by
      conv_lhs => rw [(hperm.map f).prod_eq]; simp [List.map_cons, List.prod_cons]
    have hprod_g : (js.dedup.map g).prod = g t * ((js.dedup.erase t).map g).prod := by
      conv_lhs => rw [(hperm.map g).prod_eq]; simp [List.map_cons, List.prod_cons]
    have hne_of_mem_erase : ∀ j, j ∈ js.dedup.erase t → j ≠ t := by
      intro j hj heq
      rw [heq] at hj
      have h1 : js.dedup.count t ≤ 1 :=
        List.nodup_iff_count_le_one.mp (List.nodup_dedup js) t
      have h2 : 0 < (js.dedup.erase t).count t := List.count_pos_iff.mpr hj
      have h3 := List.count_erase_self (a := t) (l := js.dedup)
      omega
    have hrest : (js.dedup.erase t).map g = (js.dedup.erase t).map f := by
      apply List.map_congr_left; intro j hj
      simp only [f, g, qc_red, Function.update_of_ne (hne_of_mem_erase j hj)]
    have hft : f t = Fintype.card (spec.Range t) * g t := by
      simp only [f, g, qc_red, Function.update_self]
      conv_lhs => rw [show N t = (N t - 1) + 1 from by omega]
      rw [pow_succ, mul_comm]
    rw [hprod_f, hprod_g, hrest, hft]
    simp only [Nat.cast_mul, mul_assoc]
    rw [ENNReal.mul_inv
      (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)))
      (Or.inl (ENNReal.natCast_ne_top _)),
      ENNReal.mul_inv
      (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  · have hmem_red : s' ∉ support (generateSeed spec qc_red js.dedup) := mt supp_iff.mpr hmem
    simp [(probOutput_eq_zero_iff _ _).2 hmem, (probOutput_eq_zero_iff _ _).2 hmem_red]

end lemmas

end OracleComp
