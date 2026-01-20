/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ProbComp
import Batteries.Lean.LawfulMonad

/-!
# Executing Computations

This file defines a function `runIO` for executing a `ProbComp` in the `IO` monad.
We add this embedding as a `MonadLift` instance, so `#eval` notation works.
-/

open OracleSpec

namespace OracleComp

/-- Represent a `ProbComp` via the `IO` monad, allowing actual execution. -/
protected def runIO {α : Type} (oa : ProbComp α) : IO α :=
  simulateQ (spec := unifSpec) (fun n => Fin.ofNat (n + 1) <$> (IO.rand 0 n).toIO) oa

/-- Automatic lifting of probabalistic computations into `IO`. -/
instance : MonadLift ProbComp IO where monadLift := OracleComp.runIO

def test1 : ProbComp (ℕ × ℕ × ℕ) := do
  let x ← $[0..1618]
  let y ← $[0..3141]
  return (x, y, x + y)

def test2 (n : ℕ) : ProbComp (List ℕ) := do
  match n with
  | 0 => return []
  | n + 1 => return (← $[0..100]) :: (← test2 n)

def test3 (n : ℕ) : ProbComp (List ℕ) := do
  let mut xs := []
  for _ in List.range n do
    xs := (← $[0..100]) :: xs
  return xs

def test4 (n : ℕ) : ProbComp (List ℕ) := do
  (List.replicate n ()).mapM (fun () => Fin.val <$> ($[0..100]))

-- #eval test1
-- #eval test2 100
-- #eval test3 100
-- #eval test4 100

end OracleComp
