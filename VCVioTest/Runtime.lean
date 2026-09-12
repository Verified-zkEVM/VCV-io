/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Runtime
public import VCVio.EvalDist.WithFailure
public import VCVio.EvalDist.FailureMeasure

/-! # Stateful runtime producer regressions

The counter starts at seven; each query adds its argument and returns the new state.
Two distinct queries distinguish state reset, reversed logs, and incorrect output pairing.
-/

public section

-- Ordinary imports must not expose a split-projection run-result constructor.
#check_failure RunResult.mk

namespace VCVioTest.Runtime

open OracleSpec OracleComp

variable {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    {Γ : OracleRuntime Import Surface} {α : Type}

/-- Ordinary imports can introduce the runtime's provenance predicate from support membership. -/
example (program : OracleComp Surface α) (result : RunResult Γ α)
    (h : result ∈ support (Γ.run program)) : Γ.GeneratedBy program result :=
  (OracleRuntime.generatedBy_iff_mem_support Γ program result).2 h

/-- Ordinary imports can eliminate the runtime's provenance predicate to support membership. -/
example (program : OracleComp Surface α) (result : RunResult Γ α)
    (h : Γ.GeneratedBy program result) : result ∈ support (Γ.run program) :=
  (OracleRuntime.generatedBy_iff_mem_support Γ program result).1 h

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
    (fun a => (a.output, a.state, a.trace)) <$> counter.run program =
    pure ((9, 12), 12, [⟨2, 9⟩, ⟨3, 12⟩]) := by
  rw [OracleRuntime.run_eq]
  simp only [counter, pure_bind]
  rw [OracleRuntime.runFrom_observe]
  simp [program,
    QueryImpl.Stateful.runState, OracleComp.withQueryLog, monad_norm]
  rfl

/-- Returning `none` is a successful return, distinct from missing runtime mass. -/
theorem returnedNone_is_not_runtimeFailure :
    evalDistWithFailure (pure none : SPMF (Option Bool)) {some none} = 1 ∧
      evalDistWithFailure (pure none : SPMF (Option Bool)) {none} = 0 := by
  simp [evalDistWithFailure_some, evalDistWithFailure_none, evalDist_pure]

/-- Runtime failure does not masquerade as a successfully returned `none`. -/
theorem runtimeFailure_has_no_returnedValue :
    evalDistWithFailure (failure : SPMF (Option Bool)) {some none} = 0 ∧
      evalDistWithFailure (failure : SPMF (Option Bool)) {none} = 1 := by
  simp [evalDistWithFailure_some, evalDistWithFailure_none, evalDist_failure]

end VCVioTest.Runtime
