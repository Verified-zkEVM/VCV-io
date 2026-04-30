/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Lean
public meta import Lean.Meta.Sym.AlphaShareBuilder
public meta import Lean.Meta.Sym.InstantiateS
public meta import Lean.Meta.Sym.LooseBVarsS
public meta import Lean.Meta.Sym.Grind
public meta import Loom.Tactic.VCGenTime

public section

open Lean Parser Meta Elab Tactic Sym Lean.Order

initialize registerTraceClass `Loom.Tactic.vcgen.grind

open Sym Sym.Internal

namespace Loom

/--
Returns `true` if `declName` is the name of a grind helper declaration that
should not be unfolded by `unfoldReducible`.
-/
def isGrindGadget (declName : Name) : Bool :=
  declName == ``Grind.EqMatch

/-
Auxiliary function for implementing `unfoldReducible` and `unfoldReducibleSimproc`.
Performs a single step.
-/
def unfoldReducibleStepEta (e : Expr) : MetaM TransformStep := do
  let .const declName _ := e.getAppFn | return .continue
  unless (← isReducible declName) do return .continue
  if isGrindGadget declName then return .continue
  -- See comment at isUnfoldReducibleTarget.
  if (← getEnv).isProjectionFn declName then return .continue
  let some v ← unfoldDefinition? e | return .continue
  return .visit v

def isUnfoldReducibleTargetEta (e : Expr) : CoreM Bool := do
  let env ← getEnv
  return Option.isSome <| e.find? fun e => Id.run do
    let .const declName _ := e | return false
    if getReducibilityStatusCore env declName matches .reducible then
      -- Remark: it is wasteful to unfold projection functions since
      -- kernel projections are folded again in the `foldProjs` preprocessing step.
      return !isGrindGadget declName && !env.isProjectionFn declName
    else
      return false

/--
Unfolds all `reducible` declarations occurring in `e`.
This is meant as a preprocessing step. It does **not** guarantee maximally shared terms
-/
public def unfoldReducibleEta (e : Expr) : MetaM Expr := do
  if !(← isUnfoldReducibleTargetEta e) then return e
  Meta.transform e (pre := unfoldReducibleStepEta)

/--
Instantiates metavariables, unfold reducible, and applies `shareCommon`.
-/
def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducibleEta (← instantiateMVars e))

end Loom

open Lean Meta Grind in
/-- Like `internalizeAll`, but records timing when `vcgen.time` is set. -/
public meta def Lean.Meta.Grind.Goal.timedInternalizeAll (goal : Grind.Goal) : GrindM Grind.Goal := do
  let g ← if Loom.vcgen.time.get (← getOptions) then do
    let (g, ns) ← Loom.timeNs goal.internalizeAll
    Loom.addInternalizeTime ns
    pure g
  else
    goal.internalizeAll
  pure g

open Lean Meta Grind in
/-- Like `grind`, but records timing when `vcgen.time` is set. -/
public meta def Lean.Meta.Grind.Goal.timedGrind (goal : Grind.Goal) : GrindM GrindResult := do
  if Loom.vcgen.time.get (← getOptions) then
    let (res, ns) ← Loom.timeNs goal.grind
    Loom.addGrindSolveTime ns
    trace[Loom.Tactic.vcgen.grind] "takes {ns / 1000000} ms for goal {goal.mvarId}"
    pure res
  else
    goal.grind

open Lean Meta Grind in
/-- Try to discharge `goal` with grind. `internalizeAll` reassigns the goal's
    mvar to a fresh metavar; if grind fails we restore the MCtx so the
    proof term built by the caller stays intact.
    Returns `none` if grind closed the goal, or `some mvarId` for the unsolved goal. -/
public meta def Lean.Meta.Grind.Goal.timedTryGrind (goal : Grind.Goal) : GrindM (Option MVarId) := do
  let savedMCtx ← getMCtx
  let goal ← goal.timedInternalizeAll
  match ← goal.timedGrind with
  | .closed => return none
  | .failed .. =>
    setMCtx savedMCtx
    return some goal.mvarId

end -- public section
