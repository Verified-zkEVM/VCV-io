/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic
import Lean.Meta.Match.MatcherApp
import VCVio.OracleComp.Constructions.Replicate
import VCVio.ProgramLogic.NotationCore

/-!
# VCGen Planner Core

Shared planning infrastructure for the unary and relational VCGen tactics.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

register_option vcvio.vcgen.maxPasses : Nat := {
  defValue := 64
  descr := "Maximum number of exhaustive vcgen/rvcgen passes before requiring manual stepping."
}

register_option vcvio.vcgen.traceSteps : Bool := {
  defValue := false
  descr := "Emit opt-in trace messages for chosen vcgen/rvcgen planned steps."
}

register_option vcvio.vcgen.time : Bool := {
  defValue := false
  descr := "Emit cumulative timing for internal vcgen/rvcgen planner phases."
}

structure VCGenTimingData where
  previewNs : UInt64 := 0
  structuralNs : UInt64 := 0
  wpStepNs : UInt64 := 0
  probPlannerNs : UInt64 := 0
  localHintNs : UInt64 := 0
  registeredNs : UInt64 := 0
  closeNs : UInt64 := 0
  passNs : UInt64 := 0
  finishNs : UInt64 := 0
  deriving Inhabited

initialize vcGenTimingRef : IO.Ref VCGenTimingData ← IO.mkRef {}

def timeNs {m : Type → Type} {α : Type} [Monad m] [MonadLiftT BaseIO m]
    (k : m α) : m (α × UInt64) := do
  let start ← IO.monoNanosNow
  let a ← k
  let stop ← IO.monoNanosNow
  return (a, (stop - start).toUInt64)

private def addVCGenTiming (f : VCGenTimingData → VCGenTimingData) : BaseIO Unit :=
  vcGenTimingRef.modify f

private def addPreviewTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with previewNs := d.previewNs + ns }

private def addStructuralTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with structuralNs := d.structuralNs + ns }

private def addWpStepTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with wpStepNs := d.wpStepNs + ns }

private def addProbPlannerTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with probPlannerNs := d.probPlannerNs + ns }

private def addLocalHintTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with localHintNs := d.localHintNs + ns }

private def addRegisteredTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with registeredNs := d.registeredNs + ns }

private def addCloseTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with closeNs := d.closeNs + ns }

private def addPassTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with passNs := d.passNs + ns }

private def addFinishTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with finishNs := d.finishNs + ns }

def withVCGenTiming {α : Type} (add : UInt64 → BaseIO Unit) (k : TacticM α) : TacticM α := do
  if vcvio.vcgen.time.get (← getOptions) then
    let (a, ns) ← timeNs k
    add ns
    return a
  else
    k

def withVCGenPreviewTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addPreviewTime k

def withVCGenStructuralTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addStructuralTime k

def withVCGenWpStepTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addWpStepTime k

def withVCGenProbPlannerTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addProbPlannerTime k

def withVCGenLocalHintTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addLocalHintTime k

def withVCGenRegisteredTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addRegisteredTime k

def withVCGenCloseTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addCloseTime k

def withVCGenPassTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addPassTime k

def withVCGenFinishTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addFinishTime k

def resetVCGenTimingIfEnabled : TacticM Unit := do
  if vcvio.vcgen.time.get (← getOptions) then
    vcGenTimingRef.set {}

private def formatNsMs (ns : UInt64) : String :=
  s!"{ns / 1000000}ms"

def logVCGenTimingIfEnabled (label : String) : TacticM Unit := do
  if vcvio.vcgen.time.get (← getOptions) then
    let d ← vcGenTimingRef.get
    logInfo m!"[{label} timing] preview={formatNsMs d.previewNs}, \
      structural={formatNsMs d.structuralNs}, wpStep={formatNsMs d.wpStepNs}, \
      probPlanner={formatNsMs d.probPlannerNs}, localHints={formatNsMs d.localHintNs}, \
      registered={formatNsMs d.registeredNs}, close={formatNsMs d.closeNs}, \
      passes={formatNsMs d.passNs}, finish={formatNsMs d.finishNs}"

def withVCGenRunTiming {α : Type} (label : String) (k : TacticM α) : TacticM α := do
  resetVCGenTimingIfEnabled
  let a ← k
  logVCGenTimingIfEnabled label
  return a

structure PlannedStep where
  label : String
  replayText : String
  run : TacticM Bool
  notes : List String := []

structure PreviewResult where
  ok : Bool
  goalCount : Nat

def withStepNotes (step : PlannedStep) (notes : List String) : PlannedStep :=
  { step with notes := step.notes ++ notes }

def formatCandidateNames (names : Array Name) : String :=
  String.intercalate ", " <| names.toList.map fun name => s!"`{name}`"

def previewAction (action : TacticM Bool) : TacticM Bool := do
  let saved ← saveState
  let ok ← withVCGenPreviewTiming action
  saved.restore
  return ok

def previewActionWithGoals (action : TacticM Bool) : TacticM PreviewResult := do
  let saved ← saveState
  let ok ← withVCGenPreviewTiming action
  let goalCount := (← getGoals).length
  saved.restore
  return { ok, goalCount }

def previewPlannedStep (step : PlannedStep) : TacticM Bool :=
  previewAction step.run

def previewPlannedStepWithGoals (step : PlannedStep) : TacticM PreviewResult :=
  previewActionWithGoals step.run

def renderPlannedStepPreview (step : PlannedStep) (preview : PreviewResult) : String :=
  s!"{step.replayText} -> {preview.goalCount} goal(s)"

def attachPlannerChoiceNotes
    (step : PlannedStep) (preview : PreviewResult) (alternatives : Array String) : PlannedStep :=
  withStepNotes step <|
    [s!"planner preview leaves {preview.goalCount} goal(s)"] ++
      if alternatives.isEmpty then
        []
      else
        [s!"alternatives: {String.intercalate "; " alternatives.toList}"]

def chooseBestPlannedStepCandidate? (steps : Array PlannedStep) :
    TacticM (Option (PlannedStep × PreviewResult)) := do
  let traceSteps := vcvio.vcgen.traceSteps.get (← getOptions)
  let mut best? : Option (PlannedStep × PreviewResult) := none
  let mut accepted : Array String := #[]
  for step in steps do
    let preview ← previewPlannedStepWithGoals step
    if preview.ok then
      if traceSteps then
        accepted := accepted.push (renderPlannedStepPreview step preview)
      match best? with
      | none => best? := some (step, preview)
      | some (_, bestPreview) =>
          if preview.goalCount < bestPreview.goalCount then
            best? := some (step, preview)
      if !traceSteps && preview.goalCount == 0 then
        return some (step, preview)
  match best? with
  | none => return none
  | some (step, preview) =>
      if traceSteps then
        let alternatives := accepted.filter (· != renderPlannedStepPreview step preview)
        return some (attachPlannerChoiceNotes step preview alternatives, preview)
      return some (step, preview)

def logPlannedStep (step : PlannedStep) (beforeGoals afterGoals : Nat) : TacticM Unit := do
  if vcvio.vcgen.traceSteps.get (← getOptions) then
    logInfo m!"[{step.label}] {step.replayText} (goals {beforeGoals} -> {afterGoals})"
    for note in step.notes do
      logInfo m!"  {note}"

def executePlannedStep (step : PlannedStep) : TacticM Bool := do
  let beforeGoals := (← getGoals).length
  let ok ← step.run
  if ok then
    let afterGoals := (← getGoals).length
    logPlannedStep step beforeGoals afterGoals
  return ok

def renderPassReplayLine (steps : Array PlannedStep) : Option String :=
  if steps.isEmpty then
    none
  else
    let body := String.intercalate " | " <| steps.toList.map (·.replayText)
    some s!"all_goals first | {body} | skip"

def whnfReducible (e : Expr) : MetaM Expr :=
  withReducible <| whnf e

def headConstName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

def trailingArgs? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.consumeMData.getAppArgs
  if _h : n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none

def findAppWithHead? (head : Name) (e : Expr) : Option Expr :=
  (e.find? fun e' => e'.consumeMData.getAppFn.isConstOf head).map Expr.consumeMData

def relTripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  if let some app := findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelTriple target then
    let args ← trailingArgs? app 3
    let #[oa, ob, post] := args | none
    some (oa, ob, post)
  else
    let app ← findAppWithHead? ``Std.Do'.RelTriple target
    let args ← trailingArgs? app 6
    let #[_pre, oa, ob, post, _epost₁, _epost₂] := args | none
    some (oa, ob, post)

def relWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelWP target
  let args ← trailingArgs? app 3
  let #[oa, ob, post] := args | none
  some (oa, ob, post)

def stdDoRelTripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``Std.Do'.RelTriple target
  let args ← trailingArgs? app 6
  let #[pre, oa, ob, post, _epost₁, _epost₂] := args | none
  some (pre, oa, ob, post)

private def findWpApp? (target : Expr) : Option (Expr × Nat) := do
  if let some app := findAppWithHead? ``OracleComp.ProgramLogic.wp target then
    some (app, 2)
  else if let some app := findAppWithHead? ``Std.Do'.wp target then
    some (app, 3)
  else
    none

def wpGoalComp? (target : Expr) : Option Expr := do
  let (app, k) ← findWpApp? target
  let args ← trailingArgs? app k
  some args[0]!

def wpGoalParts? (target : Expr) : Option (Expr × Expr) := do
  let (app, k) ← findWpApp? target
  let args ← trailingArgs? app k
  some (args[0]!, args[1]!)

def rawWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let target := target.consumeMData
  if target.isAppOfArity ``LE.le 4 then
    let pre := target.getArg! 2
    let rhs := target.getArg! 3
    let (oa, post) ← wpGoalParts? rhs
    some (pre, oa, post)
  else
    none

private def findTripleApp? (target : Expr) : Option (Expr × Nat) := do
  if let some app := findAppWithHead? ``OracleComp.ProgramLogic.Triple target then
    some (app, 3)
  else if let some app := findAppWithHead? ``Std.Do'.Triple target then
    some (app, 4)
  else
    none

def tripleGoalComp? (target : Expr) : Option Expr := do
  let (app, k) ← findTripleApp? target
  let args ← trailingArgs? app k
  some args[1]!

def tripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let (app, k) ← findTripleApp? target
  let args ← trailingArgs? app k
  some (args[0]!, args[1]!, args[2]!)

def isSimulateQAction (e : Expr) : Bool :=
  (findAppWithHead? ``simulateQ e).isSome

def hasStateTRunExpr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run e).isSome

def hasStateTRun'Expr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run' e).isSome

def hasStateTRunLike (e : Expr) : Bool :=
  hasStateTRunExpr e || hasStateTRun'Expr e

def hasSimulateQRunLike (e : Expr) : Bool :=
  isSimulateQAction e && hasStateTRunLike e

def isEqRelPost (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.ProgramLogic.Relational.EqRel e).isSome

def isBindExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Bind.bind

def isPureExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Pure.pure

def isIfExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``ite || e.consumeMData.getAppFn.isConstOf ``dite

def isMapExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Functor.map

def isReplicateExpr (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.replicate e).isSome

def isListMapMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.mapM e).isSome

def isListFoldlMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.foldlM e).isSome

def isReplicateHead (e : Expr) : Bool :=
  (headConstName? e) == some ``OracleComp.replicate

def isListMapMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.mapM

def isListFoldlMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.foldlM

def isGameEquivGoal (target : Expr) : Bool :=
  target.consumeMData.getAppFn.isConstOf ``OracleComp.ProgramLogic.GameEquiv

def isEvalDistEqGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getArg! 1
    let rhs := target.getArg! 2
    (findAppWithHead? ``evalDist lhs).isSome && (findAppWithHead? ``evalDist rhs).isSome
  else
    false

/-- Check if a goal is an equality with probability expressions on both sides. -/
def isProbEqGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getArg! 1
    let rhs := target.getArg! 2
    let lhsHasProb := (findAppWithHead? ``probEvent lhs).isSome ||
                       (findAppWithHead? ``probOutput lhs).isSome
    let rhsHasProb := (findAppWithHead? ``probEvent rhs).isSome ||
                       (findAppWithHead? ``probOutput rhs).isSome
    lhsHasProb && rhsHasProb
  else
    false

def tryEvalTacticSyntax (stx : Syntax) : TacticM Bool :=
  (evalTactic stx *> pure true) <|> pure false

def focusFirstGoalSatisfying (pred : Expr → Bool) : TacticM Bool := do
  let goals ← getGoals
  let mut matched? : Option MVarId := none
  let mut rest : Array MVarId := #[]
  for goal in goals do
    let target ← instantiateMVars (← goal.getType)
    if matched?.isNone && pred target then
      matched? := some goal
    else
      rest := rest.push goal
  match matched? with
  | none => return false
  | some goal =>
      setGoals (goal :: rest.toList)
      return true

def runBoundedPasses (label : String) (step : TacticM Bool) : TacticM Nat := do
  let maxPasses := vcvio.vcgen.maxPasses.get (← getOptions)
  let mut passes := 0
  while passes < maxPasses do
    if ← withVCGenPassTiming step then
      passes := passes + 1
    else
      return passes
  let saved ← saveState
  let more ← withVCGenPassTiming step
  saved.restore
  if more then
    throwError m!
      "{label}: exhausted the configured pass budget ({maxPasses}).\n\
      Increase `set_option vcvio.vcgen.maxPasses <n>` or keep stepping manually."
  return passes

def runBoundedPassesCollect {α : Type} (label : String)
    (step : TacticM (Array α)) : TacticM (Array (Array α)) := do
  let maxPasses := vcvio.vcgen.maxPasses.get (← getOptions)
  let mut passes := 0
  let mut batches := #[]
  while passes < maxPasses do
    let batch ← withVCGenPassTiming step
    if batch.isEmpty then
      return batches
    passes := passes + 1
    batches := batches.push batch
  let saved ← saveState
  let more ← withVCGenPassTiming step
  saved.restore
  if !more.isEmpty then
    throwError m!
      "{label}: exhausted the configured pass budget ({maxPasses}).\n\
      Increase `set_option vcvio.vcgen.maxPasses <n>` or keep stepping manually."
  return batches

end OracleComp.ProgramLogic
