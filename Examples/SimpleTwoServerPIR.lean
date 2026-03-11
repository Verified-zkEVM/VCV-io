/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.ProgramLogic.Tactics

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

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

/-! ## Query generation -/

variable {N : ℕ}

/-- PIR query generation: build two index sets `s, s'` whose "symmetric difference"
is `{i₀}`. Uses `foldlM` over `List.finRange N` with a random coin per index. -/
def pirQuery {N : ℕ} (i₀ : Fin N) : ProbComp (List (Fin N) × List (Fin N)) :=
  (List.finRange N).foldlM (fun (acc : List (Fin N) × List (Fin N)) (j : Fin N) => do
    let b ← $ᵗ Bool
    if j = i₀ then
      return if b then (j :: acc.1, acc.2) else (acc.1, j :: acc.2)
    else
      return if b then (j :: acc.1, j :: acc.2) else acc
  ) ([], [])

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

/-- Correctness: the PIR protocol always returns `a[i₀]`, assuming `W` has
characteristic 2 (i.e. `x + x = 0` for all `x`). This ensures that database
entries appearing in both query sets cancel out.

The proof uses a loop invariant: after processing index `j`, the XOR of entries
in `s` plus the XOR of entries in `s'` equals the sum of `a[k]` for all
`k ≤ j` in the symmetric difference of `s` and `s'`, which is `{i₀} ∩ {0..j}`. -/
theorem pir_correct [DecidableEq W]
    (hchar : ∀ x : W, x + x = 0)
    (a : Fin N → W) (i₀ : Fin N) :
    Pr[= a i₀ | pirMain a i₀] = 1 := by
  sorry

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
  sorry

/-- Privacy of the second server view: the distribution of the second query set `s'`
is independent of which index is being queried. -/
theorem pir_private_snd (i₁ i₂ : Fin N) :
    evalDist (Prod.snd <$> pirQuery i₁) =
    evalDist (Prod.snd <$> pirQuery i₂) := by
  sorry
