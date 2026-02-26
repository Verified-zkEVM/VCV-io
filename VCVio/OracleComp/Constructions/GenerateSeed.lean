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
  sorry

lemma probOutput_generateSeed' [spec.Fintype]
    [DecidableEq (QuerySeed spec)] (seed : QuerySeed spec)
    (h : seed ∈ support (generateSeed spec qc js)) :
    Pr[= seed | generateSeed spec qc js] =
      1 / (finSupport (generateSeed spec qc js)).card := by
  sorry

end lemmas

end OracleComp
