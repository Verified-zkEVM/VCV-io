/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.Basic
public import VCVio.ProgramLogic.Relational.SimulateQ.Epsilon
public import VCVio.ProgramLogic.Relational.SimulateQ.StateDependent
public import VCVio.ProgramLogic.Relational.SimulateQ.Resource

/-!
# Relational `simulateQ` Rules

This file provides the highest-leverage theorems for game-hopping proofs: relational coupling
through oracle simulation, the "identical until bad" fundamental lemma together with its
ε-perturbed refinements, and accumulators that bound the bad-flag mass itself rather than
carrying it as an unbounded remainder.

## Main definitions

- `expectedQuerySlack`: the expected total per-query slack accumulated over the charged queries
  a computation fires, defined by recursion on the free monad. It supports state-dependent
  per-step gaps through a slack function rather than a single uniform `ε`.
- `expectedQuerySlackStep`: the single `query_bind` step of `expectedQuerySlack`.
- `avgBadM`: the bad-flag mass of a run averaged against a bare state measure, with the
  telescoping helpers `postStepJointM` and `postStepOutM`.

## Main results

- `relTriple_simulateQ_run`: if two stateful oracle implementations are related by a state
  invariant and produce equal outputs, then simulating a computation with either implementation
  preserves the invariant and output equality. `relTriple_simulateQ_run_mono` drops the
  equal-outputs requirement in exchange for a per-branch recoupling hypothesis, and
  `relTriple_simulateQ_run'` projects onto output equality alone.
- `relTriple_simulateQ_run_writerT`: the `WriterT` analogue, transporting a monoid congruence
  on accumulated logs through the whole simulation.
- `tvDist_simulateQ_le_probEvent_bad`: "identical until bad" — if two oracle implementations
  agree whenever a "bad" flag is unset, the TV distance between their simulations is bounded by
  the probability of bad being set. `tvDist_simulateQ_le_probEvent_output_bad` is the variant
  whose flag lives in the output, and `identical_until_bad_with_flag` packages the common
  `σ × Bool` shape.
- `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad` and
  `tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad`: ε-perturbed refinements, where
  the two implementations may differ by up to `ε` on each (charged) query.
- `ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad`: the state-dependent
  refinement, where the per-step gap is `ε s` and the bound is `expectedQuerySlack`.
- `probEvent_bad_simulateQ_run_le_expectedQuerySlack`: a single-world accumulator bounding the
  bad-flag mass directly by a resource-weighted query slack.
-/
