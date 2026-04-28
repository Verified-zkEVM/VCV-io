/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.ProgramLogic.Tactics.Relational

/-!
# Information-Theoretic Private Information Retrieval (PIR)

This file defines a simple 2-server PIR protocol and proves:
1. **Correctness**: the protocol always returns the correct database entry `a[i₀]`.
2. **Privacy**: the distribution of each query set is independent of the queried index.

## Protocol

The user wants to retrieve `a[i₀]` from a database `a : Fin N → W` without
revealing `i₀` to either server. The "word type" `W` must be an additive group
where `x + x = 0` for all `x` (i.e., addition is XOR / characteristic 2).

**Query generation** (via `foldlM` over `List.finRange N`):
- For each index `j`:
  - If `j = i₀`: flip a coin; add `j` to `s` (heads) or `s'` (tails).
  - If `j ≠ i₀`: flip a coin; add `j` to both `s` and `s'` (heads) or neither (tails).

**Response**: server 1 computes `⊕_{j ∈ s} a[j]`, server 2 computes `⊕_{j ∈ s'} a[j]`.
**Reconstruction**: the user XORs (adds) the two responses to recover `a[i₀]`.

**Privacy**: for any `j`, the probability of `j ∈ s` is exactly `1/2`,
regardless of `i₀`. So the distribution of `s` alone reveals nothing about `i₀`.

## References

Port of EasyCrypt's `PIR.ec`.
-/

open OracleComp OracleSpec ENNReal

/-! ## Query generation -/

variable {N : ℕ}

/-- Imperative-style PIR query generation using `for` / `let mut` syntax. -/
def pirQuery' (i₀ : Fin N) : ProbComp (List (Fin N) × List (Fin N)) := do
  let mut s  : List (Fin N) := []
  let mut s' : List (Fin N) := []
  for j in List.finRange N do
    let b ← $ᵗ Bool
    if j = i₀ then
      if b then s := j :: s else s' := j :: s'
    else
      if b then
        s := j :: s
        s' := j :: s'
  return (s, s')

/-- PIR query generation: build two index sets `s, s'` whose "symmetric difference"
is `{i₀}`. Uses `foldlM` over `List.finRange N` with a random coin per index. -/
def pirQuery (i₀ : Fin N) : ProbComp (List (Fin N) × List (Fin N)) :=
  (List.finRange N).foldlM (fun (acc : List (Fin N) × List (Fin N)) (j : Fin N) => do
    let b ← $ᵗ Bool
    if j = i₀ then
      return if b then (j :: acc.1, acc.2) else (acc.1, j :: acc.2)
    else
      return if b then (j :: acc.1, j :: acc.2) else acc
  ) ([], [])

/-- The imperative-style `pirQuery'` (using `for`/`let mut`) and the functional-style
`pirQuery` (using `List.foldlM`) compute exactly the same oracle computation.

Uses the general `List.forIn_mprod_yield_eq_foldlM` bridge from `ToMathlib.General`
to convert the `for`/`let mut` desugaring (which uses `forIn` + `MProd` state +
`ForInStep.yield`) into the direct `foldlM` formulation. The only proof obligation
is showing that each branch of the loop body wraps its result in `ForInStep.yield`. -/
theorem pirQuery'_eq_pirQuery (i₀ : Fin N) : pirQuery' i₀ = pirQuery i₀ := by
  simp only [pirQuery', pirQuery, pure_bind]
  exact List.forIn_mprod_yield_eq_foldlM _ _ _ _ _ (fun j b c => by
    simp only [bind_assoc]
    congr 1; ext b₁
    split <;> split <;> simp)

/-! ## Response computation and main protocol -/

variable {W : Type} [AddCommGroup W]

/-- Compute the XOR (additive sum) of database entries at the given indices.
Uses `+` as the group operation; for correctness we will need `x + x = 0`. -/
def pirResponse (a : Fin N → W) (s : List (Fin N)) : W :=
  s.foldl (fun acc j => acc + a j) 0

/-- Full PIR protocol: generate queries, compute responses, XOR (add) them. -/
def pirMain (a : Fin N → W) (i₀ : Fin N) : ProbComp W := do
  let (s, s') ← pirQuery i₀
  return (pirResponse a s + pirResponse a s')

/-! ## Correctness -/

private lemma foldl_add_shift {β : Type*} (g : β → W) (c : W) (l : List β) :
    l.foldl (fun acc x => acc + g x) c = c + l.foldl (fun acc x => acc + g x) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons x t ih => simp only [List.foldl_cons]; rw [ih, ih (0 + g x), zero_add, add_assoc]

private lemma pirResponse_cons (a : Fin N → W) (j : Fin N) (s : List (Fin N)) :
    pirResponse a (j :: s) = a j + pirResponse a s := by
  simp only [pirResponse, List.foldl_cons, zero_add]; exact foldl_add_shift _ (a j) s

/-- For any output in the support of the foldlM, the sum of responses accumulates `a i₀`
exactly when `i₀` appears in the fold list. -/
private lemma pirQuery_foldl_support
    (hchar : ∀ x : W, x + x = 0) (a : Fin N → W) (i₀ : Fin N)
    (l : List (Fin N)) (hl : l.Nodup)
    (init ss : List (Fin N) × List (Fin N))
    (hss : ss ∈ support (l.foldlM (fun acc j => do
      let b ← $ᵗ Bool
      if j = i₀ then
        return if b then (j :: acc.1, acc.2) else (acc.1, j :: acc.2)
      else
        return if b then (j :: acc.1, j :: acc.2) else acc) init)) :
    pirResponse a ss.1 + pirResponse a ss.2 =
      pirResponse a init.1 + pirResponse a init.2 + if i₀ ∈ l then a i₀ else 0 := by
  induction l generalizing init with
  | nil => simp only [List.foldlM, support_pure, Set.mem_singleton_iff] at hss; subst hss; simp
  | cons j rest ih =>
    rw [List.foldlM_cons] at hss
    rw [mem_support_bind_iff] at hss
    obtain ⟨mid, hmid, hss⟩ := hss
    have hnodup := hl
    rw [List.nodup_cons] at hnodup
    have := ih hnodup.2 mid hss
    rw [this]; clear this
    -- Now show: mid response sum = init response sum + (if j = i₀ then a i₀ else 0)
    -- and combine with the rest-of-list contribution
    simp only [support_bind, Set.mem_iUnion] at hmid
    obtain ⟨b, _, hmid⟩ := hmid
    by_cases hj : j = i₀
    · subst hj
      simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hmid
      simp only [hnodup.1, ↓reduceIte, add_zero, List.mem_cons, or_false]
      -- mid is either (j :: init.1, init.2) or (init.1, j :: init.2)
      rcases b with _ | _  <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmid
        <;> subst hmid <;> simp [pirResponse_cons] <;> abel
    · have hij : i₀ ≠ j := Ne.symm hj
      simp only [hj, hij, ↓reduceIte, false_or, List.mem_cons] at hmid ⊢
      rcases b with _ | _
      · -- b = false: mid = init, unchanged
        simp only [Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hmid
        subst hmid; rfl
      · -- b = true: mid = (j :: init.1, j :: init.2)
        simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hmid
        subst hmid; simp only [pirResponse_cons]; congr 1
        have h := hchar (a j)
        calc _ = (a j + a j) + (pirResponse a init.1 + pirResponse a init.2) := by abel
          _ = 0 + _ := by rw [h]
          _ = _ := by rw [zero_add]

/-- Correctness: the PIR protocol always returns `a[i₀]`, assuming `W` has
characteristic 2 (i.e. `x + x = 0` for all `x`). This ensures that database
entries appearing in both query sets cancel out.

The proof uses a loop invariant: after processing index `j`, the XOR of entries
in `s` plus the XOR of entries in `s'` equals the sum of `a[k]` for all
`k ≤ j` in the symmetric difference of `s` and `s'`, which is `{i₀} ∩ {0..j}`. -/
theorem pir_correct (hchar : ∀ x : W, x + x = 0)
    (a : Fin N → W) (i₀ : Fin N) :
    Pr[= a i₀ | pirMain a i₀] = 1 := by
  -- Every output of pirMain a i₀ equals a i₀
  have huniq : ∀ y ∈ support (pirMain a i₀), y = a i₀ := by
    intro y hy
    rw [pirMain, pirQuery] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨ss, hss, hy⟩ := hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    have h := pirQuery_foldl_support hchar a i₀ (List.finRange N)
      (List.nodup_finRange N) ([], []) ss hss
    simp only [pirResponse, List.foldl_nil, add_zero, List.mem_finRange, ↓reduceIte, zero_add] at h
    exact hy.trans h
  -- All outputs other than a i₀ have probability 0
  have hnot : ∀ y ≠ a i₀, Pr[= y | pirMain a i₀] = 0 :=
    fun y hy => (probOutput_eq_zero_iff _ _).mpr (fun hmem => hy (huniq y hmem))
  -- The total probability collapses to Pr[= a i₀ | ...]
  have hsum : ∑' x, Pr[= x | pirMain a i₀] = Pr[= a i₀ | pirMain a i₀] :=
    tsum_eq_single (a i₀) hnot
  -- ProbComp never fails; combine with total probability = 1
  have htot := probFailure_add_tsum_probOutput (pirMain a i₀)
  rw [NeverFail.probFailure_eq_zero, hsum, zero_add] at htot
  exact htot

/-- Privacy of the first server view: the distribution of the first query set `s`
is independent of which index is being queried. Intuitively, each index `j` appears in `s` with
probability 1/2 regardless of whether `j = i₀` or not:
- If `j = i₀`: `j ∈ s` iff coin is heads (prob 1/2)
- If `j ≠ i₀`: `j ∈ s` iff coin is heads (prob 1/2)

This is one half of the information-theoretic privacy guarantee; the second
server view is handled by `pir_private_snd`. -/
theorem pir_private (i₁ i₂ : Fin N) :
    evalDist (Prod.fst <$> pirQuery i₁) =
    evalDist (Prod.fst <$> pirQuery i₂) := by
  simp only [pirQuery]
  by_equiv
  rvcstep -- handle map
  rvcstep -- handle foldlM
  · rfl -- initial states: ([], []).1 = ([], []).1
  · intro j acc₁ acc₂ hS
    simp only [ProgramLogic.Relational.EqRel] at hS
    rvcstep using (fun b : Bool => b)
    · simp only [ProgramLogic.Relational.relTriple_iff_relWP,
        ProgramLogic.Relational.relWP_iff_couplingPost]
      split <;> split <;> split <;>
        apply ProgramLogic.Relational.relTriple_pure_pure <;>
        simp [ProgramLogic.Relational.EqRel, hS]
    · exact Function.bijective_id

/-- Privacy of the second server view: the distribution of the second query set `s'`
is independent of which index is being queried. Intuitively, each index `j` appears in `s'` with
probability 1/2 regardless of whether `j = i₀` or not:
- If `j = i₀`: `j ∈ s'` iff coin is tails (prob 1/2)
- If `j ≠ i₀`: `j ∈ s'` iff coin is heads (prob 1/2)

This is the other half of the information-theoretic privacy guarantee (see `pir_private`).
The proof uses a coupling argument with four cases depending on whether `j` equals `i₁`, `i₂`,
both, or neither. When `j` equals exactly one of them, the coupling negates the coin (`b ↦ !b`),
exploiting the symmetry of the uniform distribution on `Bool`. -/
theorem pir_private_snd (i₁ i₂ : Fin N) :
    evalDist (Prod.snd <$> pirQuery i₁) =
    evalDist (Prod.snd <$> pirQuery i₂) := by
  simp only [pirQuery]
  by_equiv
  rvcstep -- handle map
  rvcstep -- handle foldlM
  · rfl
  · intro j acc₁ acc₂ hS
    simp only [ProgramLogic.Relational.EqRel] at hS
    by_cases h₁ : j = i₁ <;> by_cases h₂ : j = i₂
    -- Case 1: j = i₁ ∧ j = i₂ — identical, identity coupling
    · subst h₁; subst h₂
      rvcstep using (fun b : Bool => b)
      · simp [ProgramLogic.Relational.EqRel, hS]
        split <;> rfl
      · exact Function.bijective_id
    -- Case 2: j = i₁ ∧ j ≠ i₂ — negation coupling
    · subst h₁
      rvcstep using (fun b : Bool => !b)
      · simp [h₂]
        split_ifs <;> simp [ProgramLogic.Relational.EqRel, hS] at * <;>
          cases ‹Bool› <;> simp at *
      · exact Bool.involutive_not.bijective
    -- Case 3: j ≠ i₁ ∧ j = i₂ — negation coupling
    · subst h₂
      rvcstep using (fun b : Bool => !b)
      · simp [h₁]
        split_ifs <;> simp [ProgramLogic.Relational.EqRel, hS] at * <;>
          cases ‹Bool› <;> simp at *
      · exact Bool.involutive_not.bijective
    -- Case 4: j ≠ i₁ ∧ j ≠ i₂ — identity coupling
    · rvcstep using (fun b : Bool => b)
      · simp [h₁, h₂]
        split_ifs <;> simp [ProgramLogic.Relational.EqRel, hS] at *
      · exact Function.bijective_id
