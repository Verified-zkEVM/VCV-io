/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR

/-! # ITSR source-game canaries -/

public section

open OracleComp KeyedHash

namespace ITSRTest

def parityProblem : ITSRProblem Bool Nat Bool Nat where
  khf := { keygen := $ᵗ Bool, hash := fun k x => k == decide (x % 2 = 0) }
  indices := fun y => if y then [0] else [1]

def constantIndexProblem : ITSRProblem Bool Nat Unit Nat where
  khf := { keygen := $ᵗ Bool, hash := fun _ _ => () }
  indices := fun _ => [0]

def deterministicCoveredProblem : ITSRProblem Unit Nat Unit Nat where
  khf := { keygen := pure (), hash := fun _ _ => () }
  indices := fun _ => [0]

def deterministicIndexedProblem : ITSRProblem Unit Nat Nat Nat where
  khf := { keygen := pure (), hash := fun _ x => x }
  indices := fun y => [y]

def targetUnit (x : Nat) : OracleComp (unifSpec + ITSRTargetSpec Nat Unit) Unit :=
  liftM ((unifSpec + ITSRTargetSpec Nat Unit).query (.inr x))

def coveredFresh : ITSRAdversary deterministicCoveredProblem where
  main := targetUnit 1 *> pure ((), 2)

def repeatedPair : ITSRAdversary deterministicCoveredProblem where
  main := targetUnit 1 *> pure ((), 1)

def uncoveredIndex : ITSRAdversary deterministicIndexedProblem where
  main := targetUnit 1 *> pure ((), 2)

/-- The candidate pair must be fresh even when its semantic index is covered. -/
theorem repeated_pair_relation_canary :
    ¬parityProblem.Wins [(true, 2)] (true, 2) := by
  decide

/-- Pair freshness permits reusing a target key at a fresh input. -/
theorem reused_key_relation_canary :
    constantIndexProblem.Wins [(true, 1)] (true, 2) := by
  decide

/-- Pair freshness also permits reusing a target input under a fresh key. -/
theorem reused_input_relation_canary :
    constantIndexProblem.Wins [(true, 1)] (false, 1) := by
  decide

/-- A fresh pair loses when its selected index is not covered by the transcript. -/
theorem uncovered_index_relation_canary :
    ¬parityProblem.Wins [(true, 2)] (true, 3) := by
  decide

/-- The exact experiment distinguishes covered fresh pairs from the two near misses: repeating the
recorded pair and selecting an uncovered semantic index. -/
theorem exact_experiment_canary :
    ITSRExperiment coveredFresh = pure true ∧
      ITSRExperiment repeatedPair = pure false ∧
      ITSRExperiment uncoveredIndex = pure false := by
  simp [ITSRExperiment, coveredFresh, repeatedPair, uncoveredIndex, targetUnit,
    ITSROracles, ITSRTargetOracle, ITSRProblem.Wins, ITSRProblem.indexSet,
    ITSRProblem.targetIndexSet, deterministicCoveredProblem, deterministicIndexedProblem]

/-- The target oracle's state theorem pins append-in-issue-order semantics. -/
theorem target_history_canary (x : Nat) (targets : ITSRTranscript Bool Nat) :
    (ITSRTargetOracle constantIndexProblem x).run targets =
      constantIndexProblem.khf.keygen >>= fun k => pure (k, targets ++ [(k, x)]) :=
  ITSRTargetOracle_run constantIndexProblem x targets

end ITSRTest
