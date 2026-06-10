/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append

/-!
# Pseudorandom Functions (PRFs)

This file defines pseudorandom functions and their security game.

A PRF adversary gets oracle access to uniform sampling plus a function `D → R` and tries to
distinguish the real function `PRF.eval k` (for a random key `k`) from a truly random function
(modeled as a lazy random oracle with consistent responses).

## Main Definitions

- `PRFScheme K D R` — a PRF with key space `K`, domain `D`, and range `R`.
- `PRFAdversary D R` — a distinguisher with oracle access to `D →ₒ R`.
- `prfRealExp` — the real experiment (adversary queries `PRF.eval k`).
- `prfIdealExp` — the ideal experiment (adversary queries a random oracle).
- `prfAdvantage` — distinguishing advantage.
-/

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
@[reducible] def PRFOracleSpec (_D R : Type) := unifSpec + (_D →ₒ R)

/-- A PRF adversary gets oracle access to uniform sampling and a function `D → R`,
and outputs a boolean guess (`true` = "real PRF", `false` = "random function"). -/
abbrev PRFAdversary (D R : Type) := OracleComp (PRFOracleSpec D R) Bool

/-- A PRF has uniform key generation when its keygen algorithm is exactly uniform sampling. -/
def UniformKey [SampleableType K] (prf : PRFScheme K D R) : Prop :=
  prf.keygen = ($ᵗ K)

/-- Query implementation for the real PRF experiment. Uniform-sampling queries are handled
by the ambient `unifSpec`; function queries are answered by `prf.eval k`. -/
def prfRealQueryImpl (prf : PRFScheme K D R) (k : K) :
    QueryImpl (PRFOracleSpec D R) ProbComp :=
  let so : QueryImpl (D →ₒ R) ProbComp := fun d => pure (prf.eval k d)
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) + so

/-- Query implementation for the ideal PRF experiment. Uniform-sampling queries are handled
by the ambient `unifSpec`; function queries are answered by a lazy random oracle. -/
def prfIdealQueryImpl [DecidableEq D] [SampleableType R] :
    QueryImpl (PRFOracleSpec D R) (StateT ((D →ₒ R).QueryCache) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((D →ₒ R).QueryCache) ProbComp) +
    (D →ₒ R).randomOracle

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

/-! ## Forwarding lemmas for the PRF query implementations

How `prfRealQueryImpl`/`prfIdealQueryImpl` act on a computation lifted in from the ambient
`unifSpec` (their identity-handled left summand) and on a function (`Sum.inr`) query. These are the
facts a PRF distinguisher reduction needs when it forwards its own uniform sampling / oracle access
through the PRF experiment: the `unifSpec` side is transparent, and an `inr` query is exactly the
candidate function (real: `prf.eval k`; ideal: the lazy random oracle). -/

/-- The real PRF handler is transparent on a computation lifted in from `unifSpec`: its
`unifSpec` side is the identity handler and the function oracle is never consulted. -/
@[simp] lemma simulateQ_prfRealQueryImpl_liftComp (prf : PRFScheme K D R) (k : K)
    {β : Type} (ob : OracleComp unifSpec β) :
    simulateQ (prf.prfRealQueryImpl k) (OracleComp.liftComp ob (PRFOracleSpec D R)) = ob := by
  unfold prfRealQueryImpl
  rw [QueryImpl.simulateQ_add_liftComp_left, HasQuery.toQueryImpl_eq_id', simulateQ_id']

/-- The ideal (lazy random oracle) PRF handler is transparent on a computation lifted in from
`unifSpec`, threading the cache: the result is just `ob` lifted into the cache state monad. -/
@[simp] lemma simulateQ_prfIdealQueryImpl_liftComp [DecidableEq D] [SampleableType R]
    {β : Type} (ob : OracleComp unifSpec β) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R)) (OracleComp.liftComp ob (PRFOracleSpec D R))
      = (liftM ob : StateT ((D →ₒ R).QueryCache) ProbComp β) := by
  unfold prfIdealQueryImpl
  rw [QueryImpl.simulateQ_add_liftComp_left, HasQuery.toQueryImpl_eq_id',
      simulateQ_liftTarget, simulateQ_id']

/-- A function query (`Sum.inr`) under the real PRF handler evaluates the PRF. -/
@[simp] lemma simulateQ_prfRealQueryImpl_inr (prf : PRFScheme K D R) (k : K) (d : D) :
    simulateQ (prf.prfRealQueryImpl k)
        (liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R))
      = pure (prf.eval k d) := by
  simp only [prfRealQueryImpl, simulateQ_spec_query, QueryImpl.add_apply_inr]

/-- A function query (`Sum.inr`) under the ideal PRF handler is the lazy random oracle at that
point. -/
@[simp] lemma simulateQ_prfIdealQueryImpl_inr [DecidableEq D] [SampleableType R] (q : D) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R))
        (liftM (OracleSpec.query (Sum.inr q) : OracleQuery (PRFOracleSpec D R) R))
      = (D →ₒ R).randomOracle q := by
  simp only [prfIdealQueryImpl, simulateQ_spec_query, QueryImpl.add_apply_inr]

end PRFScheme
