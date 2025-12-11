/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
-- import VCVio.OracleComp.Constructions.Replicate
-- import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Executing Computations

This file defines a function `runIO` for executing a computation via the `IO` monad.

The semantics mirror `evalDist` in that the oracle will respond uniformly at random,
however we need to limit the oracle set to `unifSpec` to get computability of the function.
In particular we can't choose randomly from arbitrary types.
Usually it's possible to reduce to this anyway using `SelectableType` instances (see `unifOracle`).

NOTE: `OracleComp.failure` could instead be an error to allow error msg propogation.
-/

open OracleSpec

namespace OracleComp

/-- Represent an `OracleComp` via the `IO` monad, allowing actual execution.
NOTE: `OracleComp` as currently defined doesn't allow specialized error messaging.
Changing this would just require adding a `String` to the `failure` constructor -/
protected def runIO {α : Type} (oa : ProbComp α) : IO α :=
  oa.mapM (fail := throw (IO.userError "Computation failed during execution"))
    -- Problem with bump to v4.22.0-rc2: `IO.rand` returns `Nat` instead of `Fin`
    (query_map := λ ⟨i, _⟩ ↦ (Fin.ofNat (i + 1)) <$> IO.rand 0 i) -- Queries become random selection

-- protected def runIO' {α : Type} (oa : OracleComp probSpec α) : IO α :=
--   oa.mapM (fail := throw (IO.userError "Computation failed during execution"))
--     (query_map := fun (query m n) => IO.rand n m) -- Queries become random selection

/-- Automatic lifting of probabalistic computations into `IO`. -/
instance : MonadLift ProbComp IO where
  monadLift := OracleComp.runIO

def test : IO (ℕ × ℕ) := do
  let x ← IO.rand 0 1618
  let y ← IO.rand 0 3141
  let z := x + y
  IO.println z
  return (x, y)

#print test

-- #eval Nat.add <$> $[0..10] <*> $[0..10]

end OracleComp
