/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Learning With Errors

This file packages generic LWE-style experiments together with the standard matrix-based
instantiation. The generic interface is intentionally broad enough to cover both:

- ordinary LWE over `ZMod p`;
- module-LWE variants over a finite coefficient ring such as the ring used by ML-KEM.

The first phase only introduces definitions and executable experiments; no security proofs are
attempted here.
-/


open OracleComp OracleSpec ENNReal Matrix

namespace LearningWithErrors

/-- A generic LWE-style problem instance.

`Sample` is the public challenge data (e.g. a matrix), `Secret` is the hidden secret, and
`Output` is the noisy linear output given to the adversary. The same shape covers standard LWE and
module-LWE once the appropriate coefficient type is chosen. -/
structure Problem (Sample Secret Output : Type) where
  sampleChallenge : ProbComp Sample
  sampleSecret : ProbComp Secret
  sampleError : ProbComp Output
  noiseless : Secret → Sample → Output
  sampleUniform : ProbComp Output

section Generic

variable {Sample Secret Output : Type}

/-- The real LWE-style distribution `(A, signal + error)`. -/
def distr [Add Output] (problem : Problem Sample Secret Output) :
    ProbComp (Sample × Output) := do
  let challenge ← problem.sampleChallenge
  let secret ← problem.sampleSecret
  let error ← problem.sampleError
  return (challenge, problem.noiseless secret challenge + error)

/-- The matching uniform distribution `(A, u)`. -/
def uniformDistr (problem : Problem Sample Secret Output) :
    ProbComp (Sample × Output) := do
  let challenge ← problem.sampleChallenge
  let uniform ← problem.sampleUniform
  return (challenge, uniform)

/-- A decisional adversary for an LWE-style problem. -/
abbrev Adversary (_problem : Problem Sample Secret Output) :=
  Sample × Output → ProbComp Bool

/-- The decisional LWE experiment: flip `b`, give the adversary either the real distribution or the
matching uniform one, then check whether the guess matches `b`. -/
def experiment [Add Output] (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sample ← if b then distr problem else uniformDistr problem
  let b' ← adv sample
  return (b == b')

/-- Distinguishing advantage for the generic LWE experiment. -/
noncomputable def advantage [Add Output] (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ℝ :=
  (experiment problem adv).boolBiasAdvantage

/-- Game 0: the adversary sees a sample from the real LWE-style distribution. -/
def game0 [Add Output] (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ProbComp Bool := do
  adv (← distr problem)

/-- Game 1: the adversary sees a sample from the matching uniform distribution. -/
def game1 (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ProbComp Bool := do
  adv (← uniformDistr problem)

/-- A search adversary for an LWE-style problem. -/
abbrev SearchAdversary (_problem : Problem Sample Secret Output) :=
  Sample × Output → ProbComp Secret

/-- The search LWE experiment: the adversary must recover the sampled secret. -/
def searchExperiment [Add Output] [DecidableEq Secret]
    (problem : Problem Sample Secret Output) (adv : SearchAdversary problem) :
    ProbComp Bool := do
  let challenge ← problem.sampleChallenge
  let secret ← problem.sampleSecret
  let error ← problem.sampleError
  let secret' ← adv (challenge, problem.noiseless secret challenge + error)
  return decide (secret' = secret)

/-- Search advantage for the generic LWE experiment. -/
noncomputable def searchAdvantage [Add Output] [DecidableEq Secret]
    (problem : Problem Sample Secret Output) (adv : SearchAdversary problem) : ℝ :=
  (Pr[= true | searchExperiment problem adv]).toReal

end Generic

section MatrixProblems

variable {α : Type}

/-- The standard matrix-based LWE constructor. Choosing `α = ZMod p` recovers ordinary LWE, while
choosing a finite coefficient ring `α` gives the corresponding module-LWE-style experiment. -/
def matrixProblem (n m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (errSamp : ProbComp α) :
    Problem (Matrix (Fin n) (Fin m) α) (Fin n → α) (Fin m → α) where
  sampleChallenge := $ᵗ Matrix (Fin n) (Fin m) α
  sampleSecret := $ᵗ (Fin n → α)
  sampleError := ProbComp.sampleIID m errSamp
  noiseless := fun secret challenge => vecMul secret challenge
  sampleUniform := $ᵗ (Fin m → α)

/-- Ordinary LWE over `ZMod p` as a special case of `matrixProblem`. -/
def zmodMatrixProblem (n m p : ℕ) [NeZero p]
    (errSamp : ProbComp (ZMod p)) :
    Problem (Matrix (Fin n) (Fin m) (ZMod p)) (Fin n → ZMod p) (Fin m → ZMod p) :=
  matrixProblem (α := ZMod p) n m errSamp

/-- Module-LWE-style problems use the same experiment shape as ordinary LWE; only the coefficient
ring changes. This alias is provided to make that intended instantiation explicit at call sites. -/
def moduleMatrixProblem (n m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (errSamp : ProbComp α) :
    Problem (Matrix (Fin n) (Fin m) α) (Fin n → α) (Fin m → α) :=
  matrixProblem (α := α) n m errSamp

end MatrixProblems

end LearningWithErrors
