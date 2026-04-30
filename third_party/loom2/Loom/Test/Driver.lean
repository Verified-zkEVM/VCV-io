/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Meta
-- import Lean.Meta.InstMVarsAll
import Lean.Elab
import Loom.Tactic.VCGenTime


open Lean Parser Meta Elab Tactic Sym Loom

def timeItMs (k : MetaM α) : MetaM (α × UInt64) := do
  let startTime ← IO.monoNanosNow
  let a ← k
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  return (a, ms.toUInt64)

/-- Helper function for executing a tactic `k` for solving `$(goal) n`. -/
def driver (goal : Name) (unfold : List Name) (n : Nat) (discharge : MetaM (TSyntax `tactic)) (k : MVarId → MetaM (List MVarId)) : MetaM Unit := do
  let mvar ← mkFreshExprMVar (mkApp (mkConst goal) (mkNatLit n))
  let (mvarId, _unfoldMs) ← timeItMs do SymM.run do
    let mvarId ← preprocessMVar mvar.mvarId!
    let eqnss ← unfold.toArray
      |>.push goal
      |>.mapM fun n => getEqnsFor? n
    let thms := eqnss.flatMap (fun o => o.getD #[])
    match (← Sym.simpGoal mvarId (← Sym.mkMethods thms)) with
    | .goal mvarId => return mvarId
    | .noProgress => throwError "No progress when simping {mvarId}!"
    | .closed => throwError "Simp closed goal {mvarId}"
  IO.println s!"time spent unfolding: {_unfoldMs} ms"
  vcgenTimingRef.set {}
  let (mvarIds, ms) ← withOptions (fun o => vcgen.time.set o true) do
    timeItMs do k mvarId
  -- Read vcgen.time data (internalizeAll + grind accumulated during tactic execution)
  let timing ← vcgenTimingRef.get
  let intMs := (timing.internalizeAllNs.toFloat / 1000000.0).toUInt64
  let grindMs := (timing.grindSolveNs.toFloat / 1000000.0).toUInt64
  let grindTotalMs := intMs + grindMs
  -- Subtract grind time from vcgen time to get pure VC generation time
  let vcgenMs := ms - grindTotalMs
  let discharge ← discharge
  let dischargePp ← PrettyPrinter.ppTactic discharge
  let dischargeMs? ← OptionT.run <| do
    guard !mvarIds.isEmpty
    Prod.snd <$> timeItMs do
      for mvarId in mvarIds do
        let ([], _) ← Lean.Elab.runTactic mvarId discharge.raw {} {}
          | throwError "{dischargePp} failed to solve {mvarId}"
  let (expr, instMs) ← timeItMs (instantiateMVars mvar)
  let proofSize ← expr.numObjs
  -- Emulate the shareCommonPreDefs step before sending the term to the kernel.
  -- If we don't do this, kernel checking time balloons.
  let (expr, shareMs) ← timeItMs fun _ => do
    return ShareCommon.shareCommon' expr
  let proofSizeShared ← expr.numObjs
  trace[Loom.Tactic.vcgen] "expr: {expr}"
  let (_, kernelMs) ← timeItMs (checkWithKernel expr)
  let mut msg := s!"goal_{n}: {vcgenMs} ms"
  if let some dischargeMs := dischargeMs? then
    -- Add grind time (internalize + solve) to discharge time
    let totalDischargeMs := dischargeMs + grindTotalMs
    msg := msg ++ s!", {mvarIds.length} VCs by {dischargePp}: {totalDischargeMs} ms"
  else
    msg := msg ++ s!", {mvarIds.length} VCs"
  msg := msg ++ s!", internalize: {intMs} ms"
  msg := msg ++ s!", grind: {grindMs} ms"
  msg := msg ++ s!", instantiate: {instMs} ms"
  msg := msg ++ s!", shareCommon: {shareMs} ms"
  msg := msg ++ s!", kernel: {kernelMs} ms"
  msg := msg ++ s!", proofSize: {proofSize}"
  msg := msg ++ s!", proofSizeShared: {proofSizeShared}"
  IO.println msg

def solveUsingTactic (goal : Name) (unfold : List Name) (n : Nat) (solve : MetaM (TSyntax `tactic)) (discharge : MetaM (TSyntax `tactic)) (check := true) : MetaM Unit := do
  driver goal unfold n discharge fun mvarId => do
    let (mvarIds, _) ← Lean.Elab.runTactic mvarId (← solve).raw {} {}
    return mvarIds

/--
Solves a goal of the form `goal n` using the given tactic, where `n` ranges over `sizes`.
`unfold` is a list of `simp` lemmas to apply in order to unfold `goal n`.
For many benchmarks, this is `[step, loop]`.
-/
public def runBenchUsingTactic (goal : Name) (unfold : List Name) (solve : MetaM (TSyntax `tactic)) (discharge : MetaM (TSyntax `tactic)) (sizes : List Nat) : MetaM Unit := do
  IO.println s!"--- {(← getEnv).mainModule} ---"
  for n in sizes do
    solveUsingTactic goal unfold n solve discharge

def solveUsingSym (goal : Name) (unfold : List Name) (n : Nat) (solve : MVarId → SymM (List MVarId)) (discharge : MetaM (TSyntax `tactic)) (check := true) : MetaM Unit := do
  driver goal unfold n discharge fun mvarId => SymM.run do solve mvarId

/--
Solves a goal of the form `goal n` using a `SymM` procedure, where `n` ranges over `sizes`.
`unfold` is a list of `simp` lemmas to apply in order to unfold `goal n``.
For many benchmarks, this is `[step, loop]`.
-/
public def runBenchUsingSym (goal : Name) (unfold : List Name) (solve : MVarId → SymM (List MVarId)) (discharge : MetaM (TSyntax `tactic)) (sizes : List Nat) : MetaM Unit := do
  for n in sizes do
    solveUsingSym goal unfold n solve discharge
