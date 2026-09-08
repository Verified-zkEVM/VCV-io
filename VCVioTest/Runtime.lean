/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Runtime
public import VCVio.EvalDist.MaterializeMissingMass

/-! # Stateful runtime producer regressions

The counter starts at seven; each query adds its argument and returns the new state.
Two distinct queries distinguish state reset, reversed logs, and incorrect output pairing.
-/

public section

-- Ordinary imports must not expose a split-projection artifact constructor.
#check_failure RuntimeArtifact.mk

namespace VCVioTest.Runtime

open OracleSpec OracleComp

abbrev counter : OracleRuntime (fun _ : Empty => PUnit) (fun _ : Nat => Nat) where
  State := Nat
  setup := pure 7
  handler := fun n => fun s => pure (s + n, s + n)

@[expose] def program : OracleComp (fun _ : Nat => Nat) (Nat × Nat) := do
  let a ← (query (spec := fun _ : Nat => Nat) 2)
  let b ← (query (spec := fun _ : Nat => Nat) 3)
  pure (a, b)

/-- The observations must come from the same stateful run in query order. -/
theorem counter_observations :
    (fun a => (a.output, a.state, a.trace)) <$> counter.runArtifact program =
    pure ((9, 12), 12, [⟨2, 9⟩, ⟨3, 12⟩]) := by
  rw [OracleRuntime.runArtifact_eq]
  simp only [counter, pure_bind]
  rw [OracleRuntime.runFrom_observe]
  simp [program,
    QueryImpl.Stateful.runState, OracleComp.withQueryLog, monad_norm]
  rfl

end VCVioTest.Runtime
