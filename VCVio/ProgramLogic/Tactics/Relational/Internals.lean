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

attribute [vcspec]
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
attribute [vcspec]
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_query_map_eq

private def mkRVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }

private def renderPlannedStepPreview (step : PlannedStep) (preview : PreviewResult) : String :=
  s!"{step.replayText} -> {preview.goalCount} goal(s)"

private def attachPlannerChoiceNotes
    (step : PlannedStep) (preview : PreviewResult) (alternatives : Array String) : PlannedStep :=
  withStepNotes step <|
    [s!"planner preview leaves {preview.goalCount} goal(s)"] ++
      if alternatives.isEmpty then
        []
      else
        [s!"alternatives: {String.intercalate "; " alternatives.toList}"]

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

private def relationalGoalParts? (target : Expr) : Option (Expr × Expr × Expr) :=
  match relTripleGoalParts? target with
  | some parts => some parts
  | none =>
      match relWPGoalParts? target with
      | some parts => some parts
      | none =>
          match eRelTripleGoalParts? target with
          | some (_, oa, ob, post) => some (oa, ob, post)
          | none => none

private def isERelTripleGoal (target : Expr) : Bool :=
  (eRelTripleGoalParts? target).isSome

def tryLowerRelGoal : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if relationalGoalParts? target |>.isSome then
    return false
  if isGameEquivGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.GameEquiv.of_relTriple))
  else if isEvalDistEqGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel))
  else
    return false

def runERelPureRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.eRelTriple_pure _ _ _))

def runERelBindRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.eRelTriple_bind ?_ ?_))

def runERelBindRuleUsing (cut : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.eRelTriple_bind (cut := $cut) ?_ ?_))

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
  if let some (pre, oa, ob, _) := eRelTripleGoalParts? target then
    let _ := pre
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if ← runERelPureRule then
      return true
    if isBindExpr oa && isBindExpr ob then
      if ← runERelBindRule then
        return true
    return false
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
  if let some (_, oa, ob, _) := eRelTripleGoalParts? target then
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if isBindExpr oa && isBindExpr ob then
      return (← runERelBindRuleUsing hint)
    return false
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

/-- Find the local hypotheses that work as relational `using` hints. -/
def findRelHintCandidates : TacticM (Array Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless relationalGoalParts? target |>.isSome do return #[]
  let mut found : Array Name := #[]
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
                found := found.push name
  return found

/-- Find the unique local hypothesis that works as a relational `using` hint.
Returns `none` if there are 0 or ≥ 2 viable hints (keeping ambiguity explicit). -/
def findUniqueRelHint? : TacticM (Option Name) := do
  let found ← findRelHintCandidates
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none

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

private def closeRelTheoremStepGoals : TacticM Unit := do
  discard <| tryEvalTacticSyntax (← `(tactic| all_goals try simp only [game_rule]))
  discard <| tryEvalTacticSyntax (← `(tactic|
    all_goals first
      | assumption
      | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
      | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
      | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
      | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)))

private def runRVCGenStepWithTheoremDirect
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

private def runRVCGenStepWithTheoremConseq
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let wrapper? ←
    if (relTripleGoalParts? target).isSome then
      pure <| some (← `(tactic| refine OracleComp.ProgramLogic.Relational.relTriple_post_mono ?_ ?_))
    else if (eRelTripleGoalParts? target).isSome then
      pure <| some (← `(tactic| refine OracleComp.ProgramLogic.Relational.eRelTriple_conseq le_rfl ?_ ?_))
    else
      pure none
  let some wrapper := wrapper? | return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic wrapper
      unless ← focusFirstGoalSatisfying fun target =>
          (relTripleGoalParts? target).isSome || (eRelTripleGoalParts? target).isSome do
        throwError "rvcstep with theorem: failed to focus theorem subgoal after consequence rule"
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

private def theoremHasConcreteRelationalPost (kind : VCSpecKind) (thm : Name) : MetaM Bool := do
  let declTy := (← getConstInfo thm).type
  let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  let post? :=
    match kind with
    | .relTriple =>
        match relTripleGoalParts? targetTy with
        | some (_, _, post) => some post
        | none => none
    | .eRelTriple =>
        match eRelTripleGoalParts? targetTy with
        | some (_, _, _, post) => some post
        | none => none
    | .relWP =>
        match relWPGoalParts? targetTy with
        | some (_, _, post) => some post
        | none => none
    | _ => none
  match post? with
  | none => return false
  | some post =>
      let post := post.consumeMData
      return !(post.isMVar || post.isFVar || post.isBVar)

/-- Apply an explicit relational theorem/assumption step and try to close any easy side goals. -/
def runRVCGenStepWithTheorem (thm : TSyntax `term) (requireClosed : Bool := false) :
    TacticM Bool := do
  if ← runRVCGenStepWithTheoremDirect thm requireClosed then
    return true
  runRVCGenStepWithTheoremConseq thm requireClosed

private def relationalGoalKind? (target : Expr) : Option VCSpecKind :=
  if (relTripleGoalParts? target).isSome then
    some .relTriple
  else if (relWPGoalParts? target).isSome then
    some .relWP
  else if (eRelTripleGoalParts? target).isSome then
    some .eRelTriple
  else
    none

/-- Find the registered relational theorems whose bounded application makes progress. -/
def findRegisteredRVCGenTheoremCandidates : TacticM (Array Name) := do
  let target ← instantiateMVars (← getMainTarget)
  let some kind := relationalGoalKind? target | return #[]
  let some (oa, ob, _) := relationalGoalParts? target | return #[]
  let direct :=
    ((← getRegisteredRelationalVCSpecEntries oa ob).filter (·.kind == kind)).map (·.decl)
  let fallback :=
    (← getVCSpecTheoremsOfKind kind).filter (fun name => !(direct.contains name))
  let mut found : Array Name := #[]
  for thm in direct.toList.take 8 do
    let saved ← saveState
    let ok ←
      if ← runRVCGenStepWithTheoremDirect (mkIdent thm) then
        pure true
      else if ← theoremHasConcreteRelationalPost kind thm then
        runRVCGenStepWithTheoremConseq (mkIdent thm)
      else
        pure false
    saved.restore
    if ok then
      found := found.push thm
  unless found.isEmpty do
    return found
  for thm in fallback.toList.take 8 do
    let saved ← saveState
    let ok ←
      if ← runRVCGenStepWithTheoremDirect (mkIdent thm) then
        pure true
      else if ← theoremHasConcreteRelationalPost kind thm then
        runRVCGenStepWithTheoremConseq (mkIdent thm)
      else
        pure false
    saved.restore
    if ok then
      found := found.push thm
  return found

private def buildRelHintStep (hintName : Name) : TacticM PlannedStep := do
  let target ← instantiateMVars (← getMainTarget)
  if let some (oa, ob, _) := relationalGoalParts? target then
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if isBindExpr oa && isBindExpr ob then
      let names ← getRelBindNames
      let namedHintStep :=
        mkRVCGenPlannedStep
          "rvcgen explicit hint with names"
          s!"rvcstep using {hintName}{renderAsClause names}"
          (runRVCGenStepUsingWithNames (mkIdent hintName) names)
      if ← previewPlannedStep namedHintStep then
        return namedHintStep
  return mkRVCGenPlannedStep
    "rvcgen explicit hint"
    s!"rvcstep using {hintName}"
    (runRVCGenExplicitHintStep (mkIdent hintName))

private def chooseBestRelHintStep? : TacticM (Option (PlannedStep × PreviewResult)) := do
  let hintNames ← findRelHintCandidates
  let mut best? : Option (PlannedStep × PreviewResult) := none
  let mut accepted : Array String := #[]
  for hintName in hintNames do
    let step ← buildRelHintStep hintName
    let preview ← previewPlannedStepWithGoals step
    if preview.ok then
      accepted := accepted.push (renderPlannedStepPreview step preview)
      match best? with
      | none => best? := some (step, preview)
      | some (_, bestPreview) =>
          if preview.goalCount < bestPreview.goalCount then
            best? := some (step, preview)
  match best? with
  | none => return none
  | some (step, preview) =>
      let alternatives := accepted.filter (· != renderPlannedStepPreview step preview)
      return some (attachPlannerChoiceNotes step preview alternatives, preview)

private def chooseBestRegisteredRVCGenTheoremStep? :
    TacticM (Option (PlannedStep × PreviewResult)) := do
  let theoremNames ← findRegisteredRVCGenTheoremCandidates
  let mut best? : Option (PlannedStep × PreviewResult) := none
  let mut accepted : Array String := #[]
  for theoremName in theoremNames do
    let step :=
      mkRVCGenPlannedStep
        "rvcgen registered theorem"
        s!"rvcstep with {theoremName}"
        (runRVCGenStepWithTheorem (mkIdent theoremName))
    let preview ← previewPlannedStepWithGoals step
    if preview.ok then
      accepted := accepted.push (renderPlannedStepPreview step preview)
      match best? with
      | none => best? := some (step, preview)
      | some (_, bestPreview) =>
          if preview.goalCount < bestPreview.goalCount then
            best? := some (step, preview)
  match best? with
  | none => return none
  | some (step, preview) =>
      let alternatives := accepted.filter (· != renderPlannedStepPreview step preview)
      return some (attachPlannerChoiceNotes step preview alternatives, preview)

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
        s!"rvcstep{renderAsClause names}"
        (introMainGoalNames names)
    if ← previewPlannedStep introStep then
      return some introStep
  let structuralStep :=
    mkRVCGenPlannedStep
      "rvcgen structural step"
      "rvcstep"
      runRVCGenStructuralCore
  let structuralPreview ← previewPlannedStepWithGoals structuralStep
  let hintCandidate? ← do
    if structuralPreview.ok && structuralPreview.goalCount = 0 then
      pure none
    else
      chooseBestRelHintStep?
  let theoremCandidate? ← chooseBestRegisteredRVCGenTheoremStep?
  if structuralPreview.ok then
    if let some (hintStep, hintPreview) := hintCandidate? then
      if hintPreview.goalCount < structuralPreview.goalCount then
        return some hintStep
    if let some (theoremStep, theoremPreview) := theoremCandidate? then
      if theoremPreview.goalCount < structuralPreview.goalCount then
        return some theoremStep
    return some structuralStep
  if let some (hintStep, _) := hintCandidate? then
    return some hintStep
  if let some (theoremStep, _) := theoremCandidate? then
    return some theoremStep
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
  if let some theoremName := (← findRegisteredRVCGenTheoremCandidates).toList.head? then
    if ← runRVCGenStepWithTheorem (mkIdent theoremName) then
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
    throwError "rvcstep: failed to lower the `GameEquiv` goal into relational proof mode."
  if isEvalDistEqGoal target then
    throwError "rvcstep: failed to lower the `evalDist` equality into a `RelTriple` goal."
  match relationalGoalParts? target with
  | none =>
      throwError m!
        "rvcstep: expected a `GameEquiv`, `evalDist` equality, `RelTriple`, `RelWP`, or `eRelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      let hintCandidates ← findRelHintCandidates
      let theoremCandidates ← findRegisteredRVCGenTheoremCandidates
      let goalLabel :=
        if isERelTripleGoal target then
          "`eRelTriple`"
        else if (relWPGoalParts? target).isSome then
          "`RelWP`"
        else
          "`RelTriple`"
      let hintMsg :=
        if hintCandidates.isEmpty then
          ""
        else
          s!"\nViable local `using` hints: {formatCandidateNames hintCandidates}"
      let theoremMsg :=
        if theoremCandidates.isEmpty then
          ""
        else
          s!"\nRegistered `@[vcspec]` candidates: {formatCandidateNames theoremCandidates}\n\
          Try `rvcstep?` or `rvcstep with <theorem>` for an explicit replay."
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        throwError m!
          "rvcstep: found a `simulateQ` relational goal but no simulation rule applied.\n\
          If the proof needs a state invariant, try `rvcstep using R_state`.\n\
          If the goal is an output-only `run'` equality coupling, `rvcstep` also tries the \
          exact-distribution specialization automatically.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListMapMExpr oa || isListMapMExpr ob then
        throwError m!
          "rvcstep: found a `List.mapM` relational goal but no traversal rule applied.\n\
          Use `rvcstep using Rin` when the two input lists are related by a non-equality relation.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        throwError m!
          "rvcstep: found a `List.foldlM` relational goal but no fold rule applied.\n\
          Use `rvcstep using Rin` when the two input lists are related by a non-equality relation.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isReplicateExpr oa || isReplicateExpr ob then
        throwError m!
          "rvcstep: found a `replicate` relational goal but no iteration rule applied.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isBindExpr oa && isBindExpr ob then
        throwError m!
          "rvcstep: found a bind-on-both-sides relational goal but could not choose an intermediate cut.\n\
          Try `rvcstep using R` when the default cut is not the right one.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      throwError m!
        "rvcstep: found a {goalLabel} goal, but no relational VCGen rule matched.\n\
        {hintMsg}{theoremMsg}\n\
        Left side:{indentExpr oa}\n\
        Right side:{indentExpr ob}\n\
        Postcondition:{indentExpr post}\n\
        Consider `rel_conseq`, `rel_inline`, or `rel_dist` for a non-structural step."

def throwRVCGenStepUsingError (hint : TSyntax `term) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let hintCandidates ← findRelHintCandidates
  let hintMsg :=
    if hintCandidates.isEmpty then
      ""
    else
      s!"\nViable local `using` hints here: {formatCandidateNames hintCandidates}"
  throwError m!
    "rvcstep using {hint}: the explicit hint did not match the current relational goal shape.\n\
    `using` is interpreted by goal shape as one of:\n\
    - bind cut relation\n\
    - random/query bijection\n\
    - `List.mapM` / `List.foldlM` input relation\n\
    - `simulateQ` state relation\n\
    {hintMsg}\n\
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
