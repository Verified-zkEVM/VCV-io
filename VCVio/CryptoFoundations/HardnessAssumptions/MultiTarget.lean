/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Multi-Target Hash Assumptions (SM-PRE, SM-TCR)

The single-function multi-target preimage (SM-PRE) and target-collision (SM-TCR) resistance
notions that hash-based signatures such as SLH-DSA / SPHINCS+ reduce to. Unlike plain
one-wayness (`HardnessAssumptions.OneWay`) or collision resistance
(`HardnessAssumptions.CollisionResistance`), the SPHINCS+ analysis crucially uses
*single-function multi-target* hardness: the adversary is given `p` targets and wins by breaking
*any one* of them. The `p`-fold loss relative to the single-target notions is intended to be
recorded by separate bridge lemmas (future work), not baked into the advantage here.

The packaging mirrors `LatticeCrypto.HardnessAssumptions.ShortIntegerSolution` (the
`Problem`/`Adversary`/`experiment`/`advantage` shape). The assumptions are stated over plain
functions so that a (seed-fixed) `TweakableHash` can be plugged in.

## References

- Bernstein et al., SPHINCS+ (the multi-target preimage / target-collision treatment)
- Hülsing, Rijneveld, Song, Schwabe, "Mitigating Multi-Target Attacks in Hash-Based Signatures"
-/

open OracleComp ENNReal

namespace MultiTarget

/-! ### Single-function multi-target preimage resistance (SM-PRE) -/

/-- An SM-PRE problem for a fixed function `f : X → Y`: the challenger samples `numTargets`
preimages (via `sampleInputs`) and exposes their images; the adversary must invert one. -/
structure PreimageProblem (X Y : Type) where
  /-- The fixed function whose preimage resistance is in question. -/
  f : X → Y
  /-- The number of targets the adversary is challenged on. -/
  numTargets : ℕ
  /-- Sample all `numTargets` preimages at once. -/
  sampleInputs : ProbComp (Fin numTargets → X)

variable {X Y : Type}

/-- An SM-PRE adversary: given the `numTargets` images, return an index and a preimage. -/
structure PreimageAdversary (prob : PreimageProblem X Y) where
  /-- Given the target images, produce `(i, x')` aiming for `f x' = yᵢ`. -/
  run : (Fin prob.numTargets → Y) → ProbComp (Fin prob.numTargets × X)

/-- The SM-PRE experiment: sample the preimages, run the adversary on their images, and check
that the returned preimage hits the chosen target. -/
def preimageExperiment {prob : PreimageProblem X Y} [DecidableEq Y]
    (adv : PreimageAdversary prob) : ProbComp Bool := do
  let xs ← prob.sampleInputs
  let (i, x') ← adv.run fun i => prob.f (xs i)
  return decide (prob.f x' = prob.f (xs i))

/-- The SM-PRE advantage of an adversary. -/
noncomputable def preimageAdvantage {prob : PreimageProblem X Y} [DecidableEq Y]
    (adv : PreimageAdversary prob) : ℝ≥0∞ :=
  Pr[= true | preimageExperiment adv]

/-! ### Single-function multi-target target-collision resistance (SM-TCR) -/

/-- An SM-TCR problem for a fixed tweakable function `f : Tweak → M → Y`: the adversary commits
`numTargets` target pairs `(tweak, message)`, then must find, for one of them, a *different*
message hashing (under the same tweak) to the same value. -/
structure TcrProblem (Tweak M Y : Type) where
  /-- The fixed tweakable function whose target-collision resistance is in question. -/
  f : Tweak → M → Y
  /-- The number of targets the adversary commits to. -/
  numTargets : ℕ

variable {Tweak M Y : Type}

/-- An SM-TCR adversary: a `choose` phase committing the target `(tweak, message)` pairs (with
private state), and a `forge` phase producing a colliding message for one committed target. -/
structure TcrAdversary (prob : TcrProblem Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Commit the `numTargets` target `(tweak, message)` pairs. -/
  choose : ProbComp ((Fin prob.numTargets → Tweak × M) × State)
  /-- Given the committed targets' hash values, produce `(j, m')` aiming for a collision at
  target `j`. -/
  forge : State → (Fin prob.numTargets → Y) → ProbComp (Fin prob.numTargets × M)

/-- The SM-TCR experiment: commit the targets, run the forge phase on their hashes, and check
that the forged message differs from the committed one yet collides under the same tweak. -/
def tcrExperiment {prob : TcrProblem Tweak M Y} [DecidableEq M] [DecidableEq Y]
    (adv : TcrAdversary prob) : ProbComp Bool := do
  let (targets, st) ← adv.choose
  let (j, m') ← adv.forge st fun i => prob.f (targets i).1 (targets i).2
  let (tweak, m) := targets j
  return decide (m' ≠ m ∧ prob.f tweak m' = prob.f tweak m)

/-- The SM-TCR advantage of an adversary. -/
noncomputable def tcrAdvantage {prob : TcrProblem Tweak M Y} [DecidableEq M] [DecidableEq Y]
    (adv : TcrAdversary prob) : ℝ≥0∞ :=
  Pr[= true | tcrExperiment adv]

end MultiTarget
