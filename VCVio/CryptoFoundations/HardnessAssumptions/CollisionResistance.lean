/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Collision-Resistant Hash Functions

This file defines collision resistance for unkeyed hash functions and for
keyed hash function families, together with their security experiments.

## Collision Resistance

A function `f : X → Y` is collision-resistant if no efficient adversary can
find two distinct inputs `x ≠ x'` with `f x = f x'`.

## Keyed Hash Function Families

A keyed hash family samples a public key `k : K` and the adversary must find
a collision under `f k`. This is the form used in practical constructions and
in the Merkle-tree / FRI commitment-scheme setting where the hash key is a
protocol parameter.

## Main Definitions

- `CRAdversary X` — an adversary outputting a candidate collision pair.
- `crExp` — the collision-resistance experiment.
- `crAdvantage` — the advantage of a CR adversary.
- `KeyedHashFamily K X Y` — a keyed hash family.
- `KeyedCRAdversary K X` — an adversary for the keyed variant.
- `keyedCRExp` — the keyed collision-resistance experiment.
- `keyedCRAdvantage` — the advantage of a keyed CR adversary.
-/


open OracleComp OracleSpec ENNReal

namespace CollisionResistance

variable {X Y : Type}

/-! ## Unkeyed Collision Resistance -/

/-- A collision-resistance adversary outputs a candidate pair of inputs
that it hopes form a collision under the target hash function. -/
def CRAdversary (X : Type) := ProbComp (X × X)

/-- Collision-resistance experiment: the adversary proposes a pair `(x, x')`,
and the experiment returns `true` iff the two inputs are distinct and map to
the same image under `f`. -/
def crExp [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (adversary : CRAdversary X) : ProbComp Bool := do
  let (x, x') ← adversary
  return decide (x ≠ x' ∧ f x = f x')

/-- Collision-resistance advantage: the probability that the adversary
produces a valid collision for `f`. -/
noncomputable def crAdvantage [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (adversary : CRAdversary X) : ℝ≥0∞ :=
  Pr[= true | crExp f adversary]

/-! ## Keyed Hash Function Families -/

variable {K : Type}

/-- A keyed hash family with key space `K`, domain `X`, and range `Y`.
The key-sampling algorithm is probabilistic; the hash itself is a
deterministic function of the key and input. -/
structure KeyedHashFamily (K X Y : Type) where
  keygen : ProbComp K
  hash : K → X → Y

/-- A keyed CR adversary receives the public key and outputs a candidate
collision pair. -/
def KeyedCRAdversary (K X : Type) := K → ProbComp (X × X)

/-- Keyed collision-resistance experiment: sample a key, run the adversary on
the key, and return `true` iff the adversary's pair is a valid collision
under `H.hash k`. -/
def keyedCRExp [DecidableEq X] [DecidableEq Y]
    (H : KeyedHashFamily K X Y) (adversary : KeyedCRAdversary K X) :
    ProbComp Bool := do
  let k ← H.keygen
  let (x, x') ← adversary k
  return decide (x ≠ x' ∧ H.hash k x = H.hash k x')

/-- Keyed collision-resistance advantage: the probability of producing a
valid collision under the sampled key. -/
noncomputable def keyedCRAdvantage [DecidableEq X] [DecidableEq Y]
    (H : KeyedHashFamily K X Y) (adversary : KeyedCRAdversary K X) : ℝ≥0∞ :=
  Pr[= true | keyedCRExp H adversary]

end CollisionResistance
