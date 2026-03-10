/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.RandomOracle

/-!
# Pseudorandom Functions (PRFs)

This file defines pseudorandom functions and their security game.

A PRF adversary gets oracle access to a function `D → R` and tries to distinguish
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

/-- A PRF adversary gets oracle access to a function `D → R` and outputs a
boolean guess (`true` = "real PRF", `false` = "random function"). -/
def PRFAdversary (D R : Type) := OracleComp (D →ₒ R) Bool

/-- Real PRF experiment: sample a key, let the adversary query `prf.eval k`. -/
def prfRealExp (prf : PRFScheme K D R) (adversary : PRFAdversary D R) :
    ProbComp Bool := do
  let k ← prf.keygen
  simulateQ (fun d => pure (prf.eval k d) : QueryImpl (D →ₒ R) ProbComp) adversary

/-- Ideal PRF experiment: let the adversary query a lazy random oracle
(consistent random function). The oracle caches responses so that
the same input always yields the same output. -/
def prfIdealExp [DecidableEq D] [SampleableType R]
    (adversary : PRFAdversary D R) : ProbComp Bool :=
  (simulateQ (randomOracle (spec := (D →ₒ R))) adversary).run' ∅

/-- PRF advantage: how well the adversary distinguishes the real PRF from
a random function. -/
noncomputable def prfAdvantage [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adversary : PRFAdversary D R) : ℝ :=
  |(Pr[= true | prf.prfRealExp adversary]).toReal -
    (Pr[= true | prfIdealExp adversary]).toReal|

end PRFScheme
