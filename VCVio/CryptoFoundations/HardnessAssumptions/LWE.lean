/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Learning With Errors

This file defines the decisional and search LWE problems, parameterized by:
- `n`: the dimension of the secret
- `m`: the number of samples
- `p`: the modulus
- `errSamp`: a probabilistic sampling algorithm for the error distribution

To stay faithful to the standard formulation, this file uses `ZMod p` directly.
Sampling is available from the `SampleableType (ZMod p)` instance (for `[NeZero p]`).
-/

open OracleComp OracleSpec ENNReal Matrix

/-- Sample an IID vector: independently sample each coordinate from `samp`. -/
def sampleIID {α : Type} (k : ℕ) (samp : ProbComp α) : ProbComp (Fin k → α) :=
  Fin.mOfFn k fun _ => samp

namespace LWE

/-- The LWE distribution `(A, s * A + e)` in row-vector form. -/
def Distr (n m p : ℕ) [NeZero p] (errSamp : ProbComp (ZMod p)) :
    ProbComp (Matrix (Fin n) (Fin m) (ZMod p) × (Fin m → ZMod p)) := do
  let A ← $ᵗ Matrix (Fin n) (Fin m) (ZMod p)
  let s ← $ᵗ (Fin n → ZMod p)
  let e ← sampleIID m errSamp
  return (A, vecMul s A + e)

/-- The uniform distribution: `(A, u)` with `u` uniformly random. -/
def UniformDistr (n m p : ℕ) [NeZero p] :
    ProbComp (Matrix (Fin n) (Fin m) (ZMod p) × (Fin m → ZMod p)) := do
  let A ← $ᵗ Matrix (Fin n) (Fin m) (ZMod p)
  let u ← $ᵗ (Fin m → ZMod p)
  return (A, u)

/-- An adversary for the decisional LWE problem. -/
abbrev Adversary (n m p : ℕ) :=
  Matrix (Fin n) (Fin m) (ZMod p) × (Fin m → ZMod p) → ProbComp Bool

/-- The decisional LWE experiment: flip `b`, give the adversary either LWE or uniform,
check if the adversary guesses `b` correctly. -/
def Experiment (n m p : ℕ) [NeZero p] (errSamp : ProbComp (ZMod p))
    (adv : Adversary n m p) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let distr ← if b then Distr n m p errSamp else UniformDistr n m p
  let b' ← adv distr
  return (b == b')

noncomputable def Advantage (n m p : ℕ) [NeZero p] (errSamp : ProbComp (ZMod p))
    (adv : Adversary n m p) : ℝ :=
  (Experiment n m p errSamp adv).boolBiasAdvantage

/-- Game 0: adversary sees an LWE sample. -/
def Game_0 (n m p : ℕ) [NeZero p] (errSamp : ProbComp (ZMod p))
    (adv : Adversary n m p) : ProbComp Bool := do
  adv (← Distr n m p errSamp)

/-- Game 1: adversary sees a uniform sample. -/
def Game_1 (n m p : ℕ) [NeZero p] (adv : Adversary n m p) : ProbComp Bool := do
  adv (← UniformDistr n m p)

/-- An adversary for the search LWE problem. -/
abbrev SearchAdversary (n m p : ℕ) :=
  Matrix (Fin n) (Fin m) (ZMod p) × (Fin m → ZMod p) → ProbComp (Fin n → ZMod p)

/-- The search LWE experiment: adversary must recover the secret `s`. -/
def SearchExperiment (n m p : ℕ) [NeZero p] (errSamp : ProbComp (ZMod p))
    (adv : SearchAdversary n m p) : ProbComp Bool := do
  let A ← $ᵗ Matrix (Fin n) (Fin m) (ZMod p)
  let s ← $ᵗ (Fin n → ZMod p)
  let e ← sampleIID m errSamp
  let s' ← adv (A, vecMul s A + e)
  return decide (s' = s)

noncomputable def SearchAdvantage (n m p : ℕ) [NeZero p] (errSamp : ProbComp (ZMod p))
    (adv : SearchAdversary n m p) : ℝ :=
  (SearchExperiment n m p errSamp adv).boolBiasAdvantage

end LWE
