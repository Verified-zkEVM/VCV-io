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
    have hseed : seed = (∅ : QuerySeed spec) := by
      simpa using h
    subst hseed
    simp
  | cons j js ih =>
    -- Decompose `seed` into the first `qc j` outputs at index `j`,
    -- and the remaining seed (which lives in the support for the tail list).
    have hlen : ∀ i, (seed i).length = qc i * List.count i (j :: js) := by
      -- Avoid `simp` unfolding `generateSeed_cons`; rewrite using the already-proved support lemma.
      have h' := h
      rw [support_generateSeed (spec := spec) (qc := qc) (js := (j :: js))] at h'
      simpa [Set.mem_setOf_eq] using h'
    let xs : List (spec.Range j) := (seed j).take (qc j)
    let rest : QuerySeed spec := Function.update seed j ((seed j).drop (qc j))
    have hxs_len : xs.length = qc j := by
      have hlen_j : (seed j).length = qc j * (List.count j js + 1) := by
        simpa [List.count_cons_self] using hlen j
      have hqc_le : qc j ≤ (seed j).length := by
        rw [hlen_j]
        exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
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
    have hseed_eq : rest.prependValues xs = seed := by
      ext i
      by_cases hi : i = j
      · subst hi
        simp [QuerySeed.prependValues_self, xs, rest, List.take_append_drop]
      · simp [QuerySeed.prependValues_of_ne _ _ hi, rest, Function.update_of_ne hi]
    -- Use support-uniqueness to collapse the outer bind to the unique `xs`.
    have hxs_unique :
        ∀ xs' ∈ support (replicate (qc j) ($ᵗ spec.Range j)),
          seed ∈ support (do
            let rest' ← generateSeed spec qc js
            return rest'.prependValues xs') → xs' = xs := by
      intro xs' hxs' hseed'
      rw [mem_support_bind_iff] at hseed'
      rcases hseed' with ⟨rest', hrest', hpure⟩
      have hEq : rest'.prependValues xs' = seed := by
        -- `seed ∈ support (pure z)` iff `seed = z`
        simpa [support_pure, Set.mem_singleton_iff] using hpure.symm
      have hlen_xs' : xs'.length = qc j := by
        have hxss : xs'.length = qc j ∧ ∀ x ∈ xs', x ∈ support ($ᵗ spec.Range j) := by
          simpa [support_replicate (oa := ($ᵗ spec.Range j)) (n := qc j)] using hxs'
        exact hxss.1
      have htake : xs' = (seed j).take (qc j) := by
        have hEqj : (rest'.prependValues xs') j = seed j := congrArg (fun s => s j) hEq
        -- rewrite `(rest'.prependValues xs') j` as `xs' ++ rest' j`
        have : xs' ++ rest' j = seed j := by simpa [QuerySeed.prependValues_self] using hEqj
        have hseedj : seed j = xs' ++ rest' j := by simpa using this.symm
        -- take `qc j` elements from both sides
        have : (seed j).take (qc j) = xs' := by
          rw [hseedj]
          simp [hlen_xs']
        exact this.symm
      simpa [xs] using htake
    have houter :
        Pr[= seed | generateSeed spec qc (j :: js)] =
          Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] *
            Pr[= seed | (do
              let rest' ← generateSeed spec qc js
              return rest'.prependValues xs)] := by
      -- `probOutput_bind_eq_mul` collapses the outer sum to the unique `xs`
      simpa [generateSeed_cons] using
        (probOutput_bind_eq_mul (mx := replicate (qc j) ($ᵗ spec.Range j))
          (my := fun xs' => do
            let rest' ← generateSeed spec qc js
            return rest'.prependValues xs')
          (y := seed) xs hxs_unique)
    -- Collapse the inner bind to the unique `rest`.
    have hrest_unique :
        ∀ rest' ∈ support (generateSeed spec qc js),
          seed ∈ support (return rest'.prependValues xs : ProbComp (QuerySeed spec)) → rest' = rest := by
      intro rest' hrest' hseed'
      have hEq : rest'.prependValues xs = seed := by
        simpa [support_pure, Set.mem_singleton_iff] using hseed'.symm
      apply QuerySeed.ext
      intro i
      by_cases hi : i = j
      · cases hi
        have hEqj : (rest'.prependValues xs) j = seed j := congrArg (fun s => s j) hEq
        have : xs ++ rest' j = seed j := by simpa [QuerySeed.prependValues_self] using hEqj
        -- drop the `qc j` prefix to recover `rest' j`
        have hdrop : rest' j = (seed j).drop (qc j) := by
          calc
            rest' j = (xs ++ rest' j).drop (xs.length) := by simp
            _ = (xs ++ rest' j).drop (qc j) := by simp [hxs_len]
            _ = (seed j).drop (qc j) := by simp [this]
        simp [rest, hdrop]
      · have hEqi : (rest'.prependValues xs) i = seed i := congrArg (fun s => s i) hEq
        -- `prependValues` does not affect indices `i ≠ j`.
        have : rest' i = seed i := by
          simpa [QuerySeed.prependValues_of_ne _ _ hi] using hEqi
        simp [rest, Function.update_of_ne hi, this]
    have hinner :
        Pr[= seed | (do
          let rest' ← generateSeed spec qc js
          return rest'.prependValues xs)] =
        Pr[= rest | generateSeed spec qc js] := by
      have hseed_pure : Pr[= seed | (return rest.prependValues xs : ProbComp (QuerySeed spec))] = 1 := by
        simp [hseed_eq]
      -- `probOutput_bind_eq_mul` collapses the inner sum to the unique `rest`.
      have := probOutput_bind_eq_mul
        (mx := generateSeed spec qc js)
        (my := fun rest' => (return rest'.prependValues xs : ProbComp (QuerySeed spec)))
        (y := seed) rest hrest_unique
      simpa [hseed_pure, mul_one] using this
    -- Compute the probability of selecting the prefix `xs` from the replicate.
    have hxs_prob :
        Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] =
          (↑((Fintype.card (spec.Range j)) ^ qc j) : ENNReal)⁻¹ := by
      -- Reduce to a product of uniform probabilities.
      have hrep :
          Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] =
            (xs.map (Pr[= · | ($ᵗ spec.Range j)])).prod := by
        simp [probOutput_replicate (oa := ($ᵗ spec.Range j)) (n := qc j), hxs_len]
      rw [hrep]
      simp [probOutput_uniformSample]
      -- Compute the product of a constant explicitly.
      have hprod_const (c : ENNReal) (xs : List (spec.Range j)) :
          (xs.map (fun _ => c)).prod = c ^ xs.length := by
        induction xs with
        | nil => simp
        | cons x xs ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ, mul_comm]
      -- Finish by rewriting in terms of `card` and `qc j`.
      have :
          ((Fintype.card (spec.Range j) : ENNReal)⁻¹) ^ (qc j) =
            (↑((Fintype.card (spec.Range j)) ^ qc j) : ENNReal)⁻¹ := by
        -- `inv_pow` + `Nat.cast_pow`
        simpa [Nat.cast_pow] using
          (ENNReal.inv_pow (a := (Fintype.card (spec.Range j) : ENNReal)) (n := qc j)).symm
      -- Use `hxs_len` to replace `xs.length` with `qc j`.
      simpa [hprod_const, hxs_len] using this
    -- Combine everything and apply the IH to `rest`.
    have hrest_prob :
        Pr[= rest | generateSeed spec qc js] =
          (↑(js.map (fun j => (Fintype.card (spec.Range j)) ^ qc j)).prod)⁻¹ :=
      ih (seed := rest) hrest_mem
    -- Put the pieces together and normalize the final product.
    calc
      Pr[= seed | generateSeed spec qc (j :: js)]
          = Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] *
              Pr[= seed | do
                let rest' ← generateSeed spec qc js
                pure (rest'.prependValues xs)] := by
              exact houter
      _ = Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] *
            Pr[= rest | generateSeed spec qc js] := by
            exact congrArg (fun p => Pr[= xs | replicate (qc j) ($ᵗ spec.Range j)] * p) hinner
      _ = (↑((Fintype.card (spec.Range j)) ^ qc j) : ENNReal)⁻¹ *
            (↑(js.map (fun j => (Fintype.card (spec.Range j)) ^ qc j)).prod)⁻¹ := by
            simp [hxs_prob, hrest_prob]
      _ = (↑((j :: js).map (fun j => (Fintype.card (spec.Range j)) ^ qc j)).prod)⁻¹ := by
            -- `List.prod_cons` plus `ENNReal.mul_inv` (all values are finite).
            simp only [List.map, List.prod_cons, Nat.cast_mul]
            -- reduce `a⁻¹ * b⁻¹` into `(a * b)⁻¹`
            have ha_top :
                ((↑(Fintype.card (spec.Range j)) : ENNReal) ^ qc j) ≠ (⊤ : ENNReal) :=
              ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
            have hb_top :
                (List.map (Nat.cast ∘ fun j => Fintype.card (spec.Range j) ^ qc j) js).prod ≠
                  (⊤ : ENNReal) := by
              -- `Nat.cast` is a monoid hom, so this list product is a `Nat.cast` of a `Nat` product.
              let f : ι → ℕ := fun j => Fintype.card (spec.Range j) ^ qc j
              have hb_eq :
                  (List.map (Nat.cast ∘ f) js).prod = (↑((js.map f).prod) : ENNReal) := by
                -- `List.prod_map_hom` handles the cast-through-product fact.
                simp [f]
              -- A nat-cast is never `⊤`.
              have hnat : (↑((js.map f).prod) : ENNReal) ≠ (⊤ : ENNReal) :=
                ENNReal.natCast_ne_top _
              intro hb
              have hb' := hb
              -- rewrite the product into a nat-cast, then contradict `hnat`
              rw [hb_eq] at hb'
              exact hnat hb'
            -- Apply the multiplicativity of inverse for finite ENNReals.
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (ENNReal.mul_inv (a := (↑(Fintype.card (spec.Range j)) : ENNReal) ^ qc j)
                (b := (List.map (Nat.cast ∘ fun j => Fintype.card (spec.Range j) ^ qc j) js).prod)
                (ha := Or.inr hb_top) (hb := Or.inl ha_top)).symm

lemma probOutput_generateSeed' [spec.Fintype]
    [DecidableEq (QuerySeed spec)] (seed : QuerySeed spec)
    (h : seed ∈ support (generateSeed spec qc js)) :
    Pr[= seed | generateSeed spec qc js] =
      1 / (finSupport (generateSeed spec qc js)).card := by
  classical
  -- Let `c` be the (explicit) common probability for any seed in the support.
  set c : ENNReal :=
    (↑(js.map (fun j => (Fintype.card (spec.Range j)) ^ qc j)).prod)⁻¹ with hc
  have hseedc : Pr[= seed | generateSeed spec qc js] = c := by
    simpa [hc] using (probOutput_generateSeed (spec := spec) (qc := qc) (js := js) seed h)
  -- All elements of `finSupport` are in `support`, so they all have probability `c`.
  have hconst : ∀ s ∈ finSupport (generateSeed spec qc js),
      Pr[= s | generateSeed spec qc js] = c := by
    intro s hs
    have hs' : s ∈ support (generateSeed spec qc js) := by
      exact mem_support_of_mem_finSupport hs
    simpa [hc] using (probOutput_generateSeed (spec := spec) (qc := qc) (js := js) s hs')
  have hsum :
      ∑ s ∈ finSupport (generateSeed spec qc js), Pr[= s | generateSeed spec qc js] = 1 :=
    HasEvalPMF.sum_finSupport_probOutput_eq_one (m := ProbComp) (mx := generateSeed spec qc js)
  -- Rewrite the finset-sum by replacing each term with `c`.
  have hsum_c :
      ∑ s ∈ finSupport (generateSeed spec qc js), c = 1 := by
    have hsum' :
        (∑ s ∈ finSupport (generateSeed spec qc js),
            Pr[= s | generateSeed spec qc js]) =
          ∑ s ∈ finSupport (generateSeed spec qc js), c := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      simp [hconst s hs]
    simpa [hsum'] using hsum
  have hcard_mul : ((finSupport (generateSeed spec qc js)).card : ENNReal) * c = 1 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum_c
  have hc_inv : c = ((finSupport (generateSeed spec qc js)).card : ENNReal)⁻¹ := by
    -- Convert `card * c = 1` into `c * card = 1`, then apply `eq_inv_of_mul_eq_one_left`.
    have : c * ((finSupport (generateSeed spec qc js)).card : ENNReal) = 1 := by
      simpa [mul_comm] using hcard_mul
    exact ENNReal.eq_inv_of_mul_eq_one_left this
  -- Finish by rewriting `Pr[= seed | ...]` to `c`.
  calc
    Pr[= seed | generateSeed spec qc js] = c := hseedc
    _ = ((finSupport (generateSeed spec qc js)).card : ENNReal)⁻¹ := hc_inv
    _ = 1 / (finSupport (generateSeed spec qc js)).card := by simp [one_div]

end lemmas

end OracleComp
