/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic
import Lean.Meta.Match.MatcherApp
import VCVio.OracleComp.Constructions.Replicate
import VCVio.ProgramLogic.Notation

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

register_option vcvio.vcgen.maxPasses : Nat := {
  defValue := 64
  descr := "Maximum number of exhaustive qvcgen/rvcgen passes before requiring manual stepping."
}

register_option vcvio.vcgen.traceSteps : Bool := {
  defValue := false
  descr := "Emit opt-in trace messages for chosen qvcgen/rvcgen planned steps."
}

structure PlannedStep where
  label : String
  replayText : String
  run : TacticM Bool

structure PreviewResult where
  ok : Bool
  goalCount : Nat

def previewAction (action : TacticM Bool) : TacticM Bool := do
  let saved ← saveState
  let ok ← action
  saved.restore
  return ok

def previewActionWithGoals (action : TacticM Bool) : TacticM PreviewResult := do
  let saved ← saveState
  let ok ← action
  let goalCount := (← getGoals).length
  saved.restore
  return { ok, goalCount }

def previewPlannedStep (step : PlannedStep) : TacticM Bool :=
  previewAction step.run

def previewPlannedStepWithGoals (step : PlannedStep) : TacticM PreviewResult :=
  previewActionWithGoals step.run

def logPlannedStep (step : PlannedStep) : TacticM Unit := do
  if vcvio.vcgen.traceSteps.get (← getOptions) then
    logInfo m!"[{step.label}] {step.replayText}"

def executePlannedStep (step : PlannedStep) : TacticM Bool := do
  let ok ← step.run
  if ok then
    logPlannedStep step
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
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelTriple target
  let args ← trailingArgs? app 3
  let #[oa, ob, post] := args | none
  some (oa, ob, post)

def wpGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.wp target
  let args ← trailingArgs? app 2
  let #[oa, _post] := args | none
  some oa

def tripleGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Triple target
  let args ← trailingArgs? app 3
  let #[_pre, oa, _post] := args | none
  some oa

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

def runBoundedPasses (label : String) (step : TacticM Bool) : TacticM Nat := do
  let maxPasses := vcvio.vcgen.maxPasses.get (← getOptions)
  let mut passes := 0
  while passes < maxPasses do
    if ← step then
      passes := passes + 1
    else
      return passes
  let saved ← saveState
  let more ← step
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
    let batch ← step
    if batch.isEmpty then
      return batches
    passes := passes + 1
    batches := batches.push batch
  let saved ← saveState
  let more ← step
  saved.restore
  if !more.isEmpty then
    throwError m!
      "{label}: exhausted the configured pass budget ({maxPasses}).\n\
      Increase `set_option vcvio.vcgen.maxPasses <n>` or keep stepping manually."
  return batches

def runWpStepRules : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_bind])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_pure])) <||>
    tryEvalTacticSyntax (← `(tactic| simp only [OracleComp.ProgramLogic.wp_pure])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_replicate_zero])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_replicate_succ])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_mapM_nil])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_mapM_cons])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_foldlM_nil])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_foldlM_cons])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_query])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_ite])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_dite])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_uniformSample])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_map])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_simulateQ_eq])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_simulateQ_run'_eq])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_liftComp]))

end OracleComp.ProgramLogic
