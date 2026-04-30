/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Data.Options

open Lean

namespace Loom

public register_option vcgen.time : Bool := {
  defValue := false
  descr := "When true, report cumulative time spent in internalizeAll and grind solving"
}

/-- Cumulative timing data for `internalizeAll` and `grind` calls. -/
public structure VCGen.TimingData where
  internalizeAllNs : UInt64 := 0
  grindSolveNs     : UInt64 := 0
  deriving Inhabited

public initialize vcgenTimingRef : IO.Ref VCGen.TimingData ← IO.mkRef {}

public def timeNs [Monad m] [MonadLiftT BaseIO m] (k : m α) : m (α × UInt64) := do
  let start ← IO.monoNanosNow
  let a ← k
  let stop ← IO.monoNanosNow
  return (a, (stop - start).toUInt64)

public def addInternalizeTime (ns : UInt64) : IO Unit :=
  vcgenTimingRef.modify fun d => { d with internalizeAllNs := d.internalizeAllNs + ns }

public def addGrindSolveTime (ns : UInt64) : IO Unit :=
  vcgenTimingRef.modify fun d => { d with grindSolveNs := d.grindSolveNs + ns }

end Loom
