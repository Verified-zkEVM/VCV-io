/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.SampleableType

/-!
# One-Way Functions and Trapdoor Permutations

This file defines one-way functions (OWFs) and one-way trapdoor permutations (OW-TDPs),
along with their security experiments.

## One-Way Functions

A function `f : X → Y` is one-way if no efficient adversary, given `f(x)` for a random `x`,
can find any preimage `x'` with `f(x') = f(x)`.

## Trapdoor Permutations

A trapdoor permutation has a key generation algorithm that produces a public key `pk`
and a secret key `sk`. The forward direction `f(pk, ·)` is a permutation that is hard to
invert given only `pk`; the secret key enables efficient inversion via `f⁻¹(sk, ·)`.

## Main Definitions

- `OWFAdversary X Y` — an adversary trying to invert `f`.
- `owfExp` — the one-wayness experiment.
- `TrapdoorPermutation PK SK X` — a trapdoor permutation scheme.
- `TDPAdversary PK X` — an adversary trying to invert the TDP.
- `tdpExp` — the TDP inversion experiment.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace OneWay

variable {X Y : Type}

/-! ## One-Way Functions -/

/-- An OWF adversary receives `f(x)` and tries to find a preimage. -/
def OWFAdversary (X Y : Type) := Y → ProbComp X

/-- One-wayness experiment: sample `x` uniformly, give the adversary `f(x)`,
and check whether the adversary's output is a valid preimage. -/
def owfExp [SampleableType X] [DecidableEq Y]
    (f : X → Y) (adversary : OWFAdversary X Y) : ProbComp Bool := do
  let x ← $ᵗ X
  let x' ← adversary (f x)
  return decide (f x' = f x)

/-- OWF advantage: the probability of successfully inverting `f`. -/
noncomputable def owfAdvantage [SampleableType X] [DecidableEq Y]
    (f : X → Y) (adversary : OWFAdversary X Y) : ℝ≥0∞ :=
  Pr[= true | owfExp f adversary]

/-! ## Trapdoor Permutations -/

variable {PK SK : Type}

/-- A trapdoor permutation with key spaces `PK`/`SK` and domain `X`.
The forward direction is a permutation computable from the public key;
the inverse requires the secret key (the trapdoor). -/
structure TrapdoorPermutation (PK SK X : Type) where
  keygen : ProbComp (PK × SK)
  forward : PK → X → X
  inverse : SK → X → X

/-- A trapdoor permutation is correct if inversion recovers the original input
for all honestly generated key pairs. -/
def TrapdoorPermutation.Correct (tdp : TrapdoorPermutation PK SK X) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support tdp.keygen →
    ∀ x, tdp.inverse sk (tdp.forward pk x) = x

/-- A TDP adversary receives the public key and a challenge `y = f(pk, x)`,
and tries to find a valid preimage of `y`. -/
def TDPAdversary (PK X : Type) := PK → X → ProbComp X

/-- TDP inversion experiment: generate keys, sample `x` uniformly,
and check whether the adversary outputs a valid preimage of `f(pk, x)`. -/
def tdpExp [SampleableType X] [DecidableEq X]
    (tdp : TrapdoorPermutation PK SK X) (adversary : TDPAdversary PK X) :
    ProbComp Bool := do
  let (pk, _) ← tdp.keygen
  let x ← $ᵗ X
  let x' ← adversary pk (tdp.forward pk x)
  return decide (tdp.forward pk x' = tdp.forward pk x)

/-- TDP advantage: the probability of successfully producing a valid preimage
without the trapdoor. -/
noncomputable def tdpAdvantage [SampleableType X] [DecidableEq X]
    (tdp : TrapdoorPermutation PK SK X) (adversary : TDPAdversary PK X) : ℝ≥0∞ :=
  Pr[= true | tdpExp tdp adversary]

end OneWay
