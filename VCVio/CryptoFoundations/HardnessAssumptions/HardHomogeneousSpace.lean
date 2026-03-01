/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle
/-!
# Hard Homogeneous Spaces

This file builds up the definition of security experiments for hard homogeneous spaces.
We represent these spaces as an `AddTorsor G P`, i.e. a group `G` acting freely and transitively
(equivalently bijectively) on the underlying set of points `P`.

If the `AddTorsor` is the action of exponention on a finite field these reduce to
classical discrete log based assumptions.
-/

open OracleComp OracleSpec ENNReal

variable {G P : Type} [AddCommGroup G] [AddTorsor G P]
    [SampleableType P] [SampleableType G]

def vectorizationAdversary (G P : Type) := P → P → ProbComp G

/-- Adversary tries to determine a vector between the two points.
Generalization of discrete log problem where the vector is the exponent.

Note: the old version used `guard` which requires `OptionT` in the current API.
We return `Bool` instead so the experiment lives in `ProbComp`. -/
def vectorizationExp [DecidableEq G]
    (adversary : vectorizationAdversary G P) : ProbComp Bool := do
  let p₁ ← $ᵗ P; let p₂ ← $ᵗ P
  let g ← adversary p₁ p₂
  return decide (p₂ -ᵥ p₁ = g)

def parallelizationAdversary (_G P : Type) := P → P → P → ProbComp P

/-- Adversary tries to determine a point completing a parallelogram in point space.
Analogue of the Diffie-Hellman problem. -/
def parallelizationExp [DecidableEq P]
    (adversary : parallelizationAdversary G P) : ProbComp Bool := do
  let x ← $ᵗ P; let g₁ ← $ᵗ G; let g₂ ← $ᵗ G
  let x₁ := g₁ +ᵥ x
  let x₂ := g₂ +ᵥ x
  let x₃ ← adversary x x₁ x₂
  return decide (x₃ = g₁ +ᵥ g₂ +ᵥ x)

def parallelTestingAdversary (_G P : Type) := P → P → P → P → ProbComp Bool

/-- Adversary tries to tell if a set of points form a parallelogram in point space.
Analogue of the decisional Diffie-Hellman problem. -/
def parallelTesting_experiment [DecidableEq G]
    (adversary : parallelTestingAdversary G P) : ProbComp Bool := do
  let x ← $ᵗ P; let g₁ ← $ᵗ G; let g₂ ← $ᵗ G
  let x₁ := g₁ +ᵥ x
  let x₂ := g₂ +ᵥ x
  let b ← $ᵗ Bool
  let x₃ ← if b then pure (g₂ +ᵥ g₁ +ᵥ x) else $ᵗ P
  let b' ← adversary x x₁ x₂ x₃
  return (b == b')

noncomputable def parallelTestingAdvantage [SampleableType P] [SampleableType G] [DecidableEq G]
    (adversary : parallelTestingAdversary G P) : ℝ≥0∞ :=
  Pr[= true | parallelTesting_experiment adversary] - 1 / 2
