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
- `p`: a natural number; the modulus is `p + 1` (always positive, giving `SampleableType`)
- `errSamp`: a probabilistic sampling algorithm for the error distribution

We use `ZMod (p + 1)` for ring elements (which has `CommRing` from Mathlib),
and `Fin k → ZMod (p + 1)` for vectors (which has `SampleableType` from VCVio).
-/

open OracleComp OracleSpec ENNReal Matrix

/-- Sample an IID vector: independently sample each coordinate from `samp`. -/
def sampleIID {α : Type} (k : ℕ) (samp : ProbComp α) : ProbComp (Fin k → α) :=
  match k with
  | 0 => return Fin.elim0
  | k + 1 => do
    let x ← samp
    let rest ← sampleIID k samp
    return Fin.cons x rest

namespace LWE

/-- The LWE distribution: `(A, mulVec A s + e)`. -/
def Distr (n m p : ℕ) (errSamp : ProbComp (ZMod (p + 1))) :
    ProbComp (Matrix (Fin m) (Fin n) (ZMod (p + 1)) × (Fin m → ZMod (p + 1))) := do
  let A ← $ᵗ Matrix (Fin m) (Fin n) (ZMod (p + 1))
  let s ← $ᵗ (Fin n → ZMod (p + 1))
  let e ← sampleIID m errSamp
  return (A, mulVec A s + e)

/-- The uniform distribution: `(A, u)` with `u` uniformly random. -/
def UniformDistr (n m p : ℕ) :
    ProbComp (Matrix (Fin m) (Fin n) (ZMod (p + 1)) × (Fin m → ZMod (p + 1))) := do
  let A ← $ᵗ Matrix (Fin m) (Fin n) (ZMod (p + 1))
  let u ← $ᵗ (Fin m → ZMod (p + 1))
  return (A, u)

/-- An adversary for the decisional LWE problem. -/
abbrev Adversary (n m p : ℕ) :=
  Matrix (Fin m) (Fin n) (ZMod (p + 1)) × (Fin m → ZMod (p + 1)) → ProbComp Bool

/-- The decisional LWE experiment: flip `b`, give the adversary either LWE or uniform,
check if the adversary guesses `b` correctly. -/
def Experiment (n m p : ℕ) (errSamp : ProbComp (ZMod (p + 1)))
    (adv : Adversary n m p) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let distr ← if b then Distr n m p errSamp else UniformDistr n m p
  let b' ← adv distr
  return (b == b')

noncomputable def Advantage (n m p : ℕ) (errSamp : ProbComp (ZMod (p + 1)))
    (adv : Adversary n m p) : ℝ :=
  (Experiment n m p errSamp adv).advantage'

/-- Game 0: adversary sees an LWE sample. -/
def Game_0 (n m p : ℕ) (errSamp : ProbComp (ZMod (p + 1)))
    (adv : Adversary n m p) : ProbComp Bool := do
  adv (← Distr n m p errSamp)

/-- Game 1: adversary sees a uniform sample. -/
def Game_1 (n m p : ℕ) (adv : Adversary n m p) : ProbComp Bool := do
  adv (← UniformDistr n m p)

/-- An adversary for the search LWE problem. -/
abbrev SearchAdversary (n m p : ℕ) :=
  Matrix (Fin m) (Fin n) (ZMod (p + 1)) × (Fin m → ZMod (p + 1)) →
    ProbComp (Fin n → ZMod (p + 1))

/-- The search LWE experiment: adversary must recover the secret `s`. -/
def SearchExperiment (n m p : ℕ) (errSamp : ProbComp (ZMod (p + 1)))
    (adv : SearchAdversary n m p) : ProbComp Bool := do
  let A ← $ᵗ Matrix (Fin m) (Fin n) (ZMod (p + 1))
  let s ← $ᵗ (Fin n → ZMod (p + 1))
  let e ← sampleIID m errSamp
  let s' ← adv (A, mulVec A s + e)
  return decide (s' = s)

noncomputable def SearchAdvantage (n m p : ℕ) (errSamp : ProbComp (ZMod (p + 1)))
    (adv : SearchAdversary n m p) : ℝ :=
  (SearchExperiment n m p errSamp adv).advantage'

end LWE

/-! ## Old commented code (for reference)

-- variable (n m p : ℕ) [NeZero p] (errSamp : ProbComp (Fin p))

-- def LWE_Distr : ProbComp (Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) := do
--   let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
--   let s ←$ᵗ Vector (Fin p) n
--   let e ← (Vector.Range m).mapM (fun _ ↦ errSamp)
--   let u := A.vecMul s.get + e.get
--   return (A, Vector.ofFn u)

-- (... rest of old LWE code preserved in git history ...)
-/
