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

end lemmas

end OracleComp
