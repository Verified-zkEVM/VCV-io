/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.SimSemantics.Append

/-!
# Pseudorandom Functions (PRFs)

This file defines pseudorandom functions and their security game.

A PRF adversary gets oracle access to uniform sampling plus a function `D → R` and tries to distinguish
the real function `PRF.eval k` (for a random key `k`) from a truly random function
(modeled as a lazy random oracle with consistent responses).

## Main Definitions

- `PRFScheme K D R` — a PRF with key space `K`, domain `D`, and range `R`.
- `PRFAdversary D R` — a distinguisher with oracle access to `D →ₒ R`.
- `prfRealExp` — the real experiment (adversary queries `PRF.eval k`).
- `prfIdealExp` — the ideal experiment (adversary queries a random oracle).
- `prfAdvantage` — distinguishing advantage.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

/-- A pseudorandom function with key space `K`, domain `D`, and range `R`.
Key generation is probabilistic; evaluation is deterministic given a key. -/
structure PRFScheme (K D R : Type) where
  keygen : ProbComp K
  eval : K → D → R

namespace PRFScheme

variable {K D R : Type}

/-- Oracle interface for PRF distinguishers: unrestricted access to uniform sampling plus
oracle access to the candidate function. -/
def PRFOracleSpec (_D R : Type) := unifSpec + (_D →ₒ R)

/-- A PRF adversary gets oracle access to uniform sampling and a function `D → R`,
and outputs a boolean guess (`true` = "real PRF", `false` = "random function"). -/
abbrev PRFAdversary (D R : Type) := OracleComp (PRFOracleSpec D R) Bool

/-- A PRF has uniform key generation when its keygen algorithm is exactly uniform sampling. -/
def UniformKey [SampleableType K] (prf : PRFScheme K D R) : Prop :=
  prf.keygen = ($ᵗ K : ProbComp K)

/-- Query implementation for the real PRF experiment. Uniform-sampling queries are handled
by the ambient `unifSpec`; function queries are answered by `prf.eval k`. -/
def prfRealQueryImpl (prf : PRFScheme K D R) (k : K) :
    QueryImpl (PRFOracleSpec D R) ProbComp :=
  let so : QueryImpl (D →ₒ R) ProbComp := fun d => pure (prf.eval k d)
  (QueryImpl.ofLift unifSpec ProbComp) + so

/-- Query implementation for the ideal PRF experiment. Uniform-sampling queries are handled
by the ambient `unifSpec`; function queries are answered by a lazy random oracle. -/
def prfIdealQueryImpl [DecidableEq D] [SampleableType R] :
    QueryImpl (PRFOracleSpec D R) (StateT ((D →ₒ R).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT ((D →ₒ R).QueryCache) ProbComp) +
    randomOracle (spec := (D →ₒ R))

/-- Real PRF experiment: sample a key, let the adversary query `prf.eval k`. -/
def prfRealExp (prf : PRFScheme K D R) (adversary : PRFAdversary D R) :
    ProbComp Bool := do
  let k ← prf.keygen
  simulateQ (prfRealQueryImpl prf k) adversary

/-- Ideal PRF experiment: let the adversary query a lazy random oracle
(consistent random function). The oracle caches responses so that
the same input always yields the same output. -/
def prfIdealExp [DecidableEq D] [SampleableType R]
    (adversary : PRFAdversary D R) : ProbComp Bool :=
  (simulateQ (prfIdealQueryImpl (D := D) (R := R)) adversary).run' ∅

/-- PRF advantage: how well the adversary distinguishes the real PRF from
a random function. -/
noncomputable def prfAdvantage [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adversary : PRFAdversary D R) : ℝ :=
  |(Pr[= true | prf.prfRealExp adversary]).toReal -
    (Pr[= true | prfIdealExp adversary]).toReal|

end PRFScheme
