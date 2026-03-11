/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Relational

private def mkRVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }

def tryCloseRelGoalImmediate : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption))

def tryCloseLeadingRelGoalImmediate : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => pure ()
  | goal :: rest =>
      setGoals [goal]
      if ← tryCloseRelGoalImmediate then
        let solvedPrefix ← getGoals
        setGoals (solvedPrefix ++ rest)
      else
        setGoals goals

def reorderRelBindGoals : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | first :: second :: rest =>
      setGoals ([second, first] ++ rest)
  | _ => pure ()

def tryLowerRelGoal : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if relTripleGoalParts? target |>.isSome then
    return false
  if isGameEquivGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.GameEquiv.of_relTriple))
  else if isEvalDistEqGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel))
  else
    return false

def runRelBindRule : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_)) then
    reorderRelBindGoals
    tryCloseLeadingRelGoalImmediate
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_)) then
    reorderRelBindGoals
    tryCloseLeadingRelGoalImmediate
    return true
  return false

def runRelBindRuleUsing (R : TSyntax `term) : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_)) then
    reorderRelBindGoals
    tryCloseLeadingRelGoalImmediate
    return true
  return false

def runRelMapRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_map))

def runRelReplicateRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate))

def runRelMapMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))

def runRelMapMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := $R) ?_ ?_))

def runRelFoldlMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same))

def runRelFoldlMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
      (Rin := $R) ?_ ?_ ?_))

def runRelRndRuleUsing (f : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f) <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f) <;> skip))

def runRelRndRuleWithContextBijection : TacticM Bool := withMainContext do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if let some app := findAppWithHead? ``Function.Bijective type then
        if let some args := trailingArgs? app 1 then
          let fStx ← PrettyPrinter.delab args[0]!
          if ← runRelRndRuleUsing fStx then
            return true
  return false

def runRelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_query _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  runRelRndRuleWithContextBijection <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij <;> skip))

def runRelCondRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    (simp only [game_rule]
     apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _)))

def runByUptoRule (bad : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
      (bad := $bad)))

def runRelSimRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, _) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) then
        return false
      if hasStateTRun'Expr oa && hasStateTRun'Expr ob then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run' (R_state := Eq))) <||>
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run')) <||>
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run))
      else
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run))
  | none => return false

def runRelSimRuleUsing (R : TSyntax `term) : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, _) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) then
        return false
      if hasStateTRun'Expr oa && hasStateTRun'Expr ob then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run' (R_state := $R))) <||>
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run (R_state := $R)))
      else
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run (R_state := $R)))
  | none => return false

def runRelSimDistRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, post) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) || !isEqRelPost post then
        return false
      tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_impl_evalDist_eq))
  | none => return false

def runRVCGenCore : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | none => return false
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if ← tryCloseRelGoalImmediate then
        return true
      if isIfExpr oa && isIfExpr ob then
        if ← runRelCondRule then
          return true
      if hasStateTRun'Expr oa && hasStateTRun'Expr ob && hasSimulateQRunLike oa &&
          hasSimulateQRunLike ob && isEqRelPost post then
        if ← runRelSimDistRule then
          return true
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        if ← runRelSimRule then
          return true
      if isMapExpr oa && isMapExpr ob then
        if ← runRelMapRule then
          return true
      if isReplicateExpr oa || isReplicateExpr ob then
        if ← runRelReplicateRule then
          return true
      if isListMapMExpr oa || isListMapMExpr ob then
        if ← runRelMapMRule then
          return true
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        if ← runRelFoldlMRule then
          return true
      if isBindExpr oa && isBindExpr ob then
        if ← runRelBindRule then
          return true
      runRelRndRule

def runRVCGenCoreUsing (hint : TSyntax `term) : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | none => return false
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob &&
          !(hasStateTRun'Expr oa && hasStateTRun'Expr ob && isEqRelPost post) then
        if ← runRelSimRuleUsing hint then
          return true
      if isListMapMExpr oa || isListMapMExpr ob then
        if ← runRelMapMRuleUsing hint then
          return true
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        if ← runRelFoldlMRuleUsing hint then
          return true
      if isBindExpr oa && isBindExpr ob then
        if ← runRelBindRuleUsing hint then
          return true
      if ← runRelRndRuleUsing hint then
        return true
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        runRelSimRuleUsing hint
      else
        return false

/-- Find the unique local hypothesis that works as a relational `using` hint.
Returns `none` if there are 0 or ≥ 2 viable hints (keeping ambiguity explicit). -/
def findUniqueRelHint? : TacticM (Option Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless relTripleGoalParts? target |>.isSome do return none
  let mut found : Option Name := none
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let name := localDecl.userName
      if isUsableBinderName name then
        let type ← instantiateMVars localDecl.type
        unless type.isSort do
          unless ← isProp type do
            let whnfType ← whnfReducible type
            if whnfType.isForall then
              let saved ← saveState
              let hint := mkIdent name
              let ok ← runRVCGenCoreUsing hint
              saved.restore
              if ok then
                if found.isSome then
                  return none
                found := some name
  return found

private def runRVCGenExplicitHintStep (hint : TSyntax `term) : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    if ← introMainGoalNames names then
      progress := true
  if ← runRVCGenCoreUsing hint then
    return true
  return progress

def runRVCGenStepUsingWithNames (hint : TSyntax `term) (names : Array Name) : TacticM Bool := do
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    if ← introMainGoalNames names then
      progress := true
  if ← runRVCGenCoreUsing hint then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return progress

/-- Structural/default relational VCGen step, excluding explicit `using`-hint fallbacks. -/
def runRVCGenStructuralCore : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  if ← runRVCGenCore then
    return true
  return progress

/-- Choose one relational VCGen step and remember how to replay it explicitly. -/
def planRVCGenStep? : TacticM (Option PlannedStep) := do
  if (← getGoals).isEmpty then
    return none
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    let introStep :=
      mkRVCGenPlannedStep
        "rvcgen intro"
        s!"rvcgen_step{renderAsClause names}"
        (introMainGoalNames names)
    if ← previewPlannedStep introStep then
      return some introStep
  let structuralStep :=
    mkRVCGenPlannedStep
      "rvcgen structural step"
      "rvcgen_step"
      runRVCGenStructuralCore
  let structuralPreview ← previewPlannedStepWithGoals structuralStep
  if let some hintName ← findUniqueRelHint? then
    if !(structuralPreview.ok && structuralPreview.goalCount = 0) then
      if let some (oa, ob, _) := relTripleGoalParts? target then
        let oa ← whnfReducible (← instantiateMVars oa)
        let ob ← whnfReducible (← instantiateMVars ob)
        if isBindExpr oa && isBindExpr ob then
          let names ← getRelBindNames
          let namedHintStep :=
            mkRVCGenPlannedStep
              "rvcgen explicit hint with names"
              s!"rvcgen_step using {hintName}{renderAsClause names}"
              (runRVCGenStepUsingWithNames (mkIdent hintName) names)
          if ← previewPlannedStep namedHintStep then
            return some namedHintStep
      let hintStep :=
        mkRVCGenPlannedStep
          "rvcgen explicit hint"
          s!"rvcgen_step using {hintName}"
          (runRVCGenExplicitHintStep (mkIdent hintName))
      if ← previewPlannedStep hintStep then
        return some hintStep
  if structuralPreview.ok then
    return some structuralStep
  return none

/-- Execute one planned relational VCGen step, returning the chosen step for replay/trace. -/
def runRVCGenPlannedStep? : TacticM (Option PlannedStep) := do
  let some step ← planRVCGenStep?
    | return none
  if ← executePlannedStep step then
    return some step
  return none

/-- One step of relational VCGen. -/
def runRVCGenStep : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    if ← introMainGoalNames names then
      progress := true
  if let some hintName ← findUniqueRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if ← runRVCGenCore then
    return true
  return progress

def runRVCGenStepUsing (hint : TSyntax `term) : TacticM Bool := do
  runRVCGenExplicitHintStep hint

def runRVCGenPassPlanned : TacticM (Array PlannedStep) := do
  let goals ← getGoals
  if goals.isEmpty then
    return #[]
  let mut newGoals : List MVarId := []
  let mut steps := #[]
  for goal in goals do
    setGoals [goal]
    if let some step ← runRVCGenPlannedStep? then
      steps := steps.push step
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return steps

def runRVCGenPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← runRVCGenStep then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress

def throwRVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rvcgen_step: failed to lower the `GameEquiv` goal into relational proof mode."
  if isEvalDistEqGoal target then
    throwError "rvcgen_step: failed to lower the `evalDist` equality into a `RelTriple` goal."
  match relTripleGoalParts? target with
  | none =>
      throwError m!
        "rvcgen_step: expected a `GameEquiv`, `evalDist` equality, or `RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        throwError m!
          "rvcgen_step: found a `simulateQ` relational goal but no simulation rule applied.\n\
          If the proof needs a state invariant, try `rvcgen_step using R_state`.\n\
          If the goal is an output-only `run'` equality coupling, `rvcgen_step` also tries the \
          exact-distribution specialization automatically.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListMapMExpr oa || isListMapMExpr ob then
        throwError m!
          "rvcgen_step: found a `List.mapM` relational goal but no traversal rule applied.\n\
          Use `rvcgen_step using Rin` when the two input lists are related by a non-equality relation.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        throwError m!
          "rvcgen_step: found a `List.foldlM` relational goal but no fold rule applied.\n\
          Use `rvcgen_step using Rin` when the two input lists are related by a non-equality relation.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isReplicateExpr oa || isReplicateExpr ob then
        throwError m!
          "rvcgen_step: found a `replicate` relational goal but no iteration rule applied.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isBindExpr oa && isBindExpr ob then
        throwError m!
          "rvcgen_step: found a bind-on-both-sides relational goal but could not choose an intermediate relation.\n\
          Try `rvcgen_step using R` when equality is not the right cut relation.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      throwError m!
        "rvcgen_step: found a `RelTriple` goal, but no relational VCGen rule matched.\n\
        Left side:{indentExpr oa}\n\
        Right side:{indentExpr ob}\n\
        Postcondition:{indentExpr post}\n\
        Consider `rel_conseq`, `rel_inline`, or `rel_dist` for a non-structural step."

def throwRVCGenStepUsingError (hint : TSyntax `term) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  throwError m!
    "rvcgen_step using {hint}: the explicit hint did not match the current relational goal shape.\n\
    `using` is interpreted by goal shape as one of:\n\
    - bind cut relation\n\
    - random/query bijection\n\
    - `List.mapM` / `List.foldlM` input relation\n\
    - `simulateQ` state relation\n\
    Goal:{indentExpr target}"

/-- Try to close a relational goal by applying postcondition monotonicity and
closing both the inner triple and the implication from local hypotheses. -/
def tryCloseRelGoalConseq : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_post_mono <;> assumption))

def runRVCGenCloseConseqPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← tryCloseRelGoalConseq then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress

def runRVCGenFinish : TacticM Unit := do
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [game_rule]))
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals first
        | assumption
        | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
        | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
        | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
        | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)))
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "rvcgen finish" runRVCGenCloseConseqPass

end Relational
end TacticInternals
end OracleComp.ProgramLogic
