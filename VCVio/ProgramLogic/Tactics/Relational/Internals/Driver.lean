/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.ProgramLogic.Relational.Loom.Quantitative
public import VCVio.ProgramLogic.Relational.SimulateQ
public meta import VCVio.ProgramLogic.Tactics.Common
public meta import VCVio.ProgramLogic.Tactics.Relational.Internals.Steps
import all VCVio.ProgramLogic.Tactics.Relational.Internals.Steps

/-!
# Relational VCGen goal dispatch and planning
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Relational

private inductive RelGoalKind where
  | relTripleVacuous
  | relTriplePure
  | relTripleRefl
  | relTripleBind
  | relTripleSpec
  | relWP
  | stdDoRelTriple
  | rawRWP
  | couplingPost
  | oneSidedCandidate
  | unknown
  deriving BEq

private def RelGoalKind.canTryImmediateClose : RelGoalKind → Bool
  | .relTripleVacuous | .relTriplePure | .relTripleRefl => true
  | _ => false

private def classifyRelGoalKind (target : Expr) : TacticM RelGoalKind := do
  if isRawStdDoRelWPGoal target then
    return .rawRWP
  if (relWPGoalParts? target).isSome then
    return .relWP
  if (findAppWithHead? ``OracleComp.ProgramLogic.Relational.CouplingPost target).isSome then
    return .couplingPost
  let some shape := relGoalShape? target | return .unknown
  let post? :=
    match relTripleGoalParts? target with
    | some (_, _, post) => some post
    | none =>
        match stdDoRelTripleGoalParts? target with
        | some (_, _, _, post) => some post
        | none => none
  if let some post := post? then
    if ← relPostIsVacuous post then
      return .relTripleVacuous
  let oa ← whnfReducible (← instantiateMVars shape.oa)
  let ob ← whnfReducible (← instantiateMVars shape.ob)
  if isPureExpr oa && isPureExpr ob then
    return .relTriplePure
  if isBindExpr oa && isBindExpr ob then
    return .relTripleBind
  if isBindExpr oa != isBindExpr ob then
    return .oneSidedCandidate
  if ← relCompsDefEq oa ob then
    return .relTripleRefl
  if shape.isStdDo then
    return .stdDoRelTriple
  return .relTripleSpec

private def tryCloseRelGoalAtCoreGateway : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let goalKind ← classifyRelGoalKind target
  match goalKind with
  | .relTripleVacuous =>
      tryEvalTacticSyntax (← `(tactic|
        first
          | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
          | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
              (fun _ _ => by trivial)))
  | _ =>
      if goalKind.canTryImmediateClose then
        tryCloseRelGoalImmediate
      else
        -- Fallback for vacuous posts whose elaborated form is easier for Lean's
        -- theorem application than for syntactic postcondition inspection.
        tryEvalTacticSyntax (← `(tactic|
          first
            | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
            | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
                (fun _ _ => by trivial)))

/-- Controlled one-sided relational bind step on the left. -/
def runRVCGenRawBindLeftStep : TacticM Bool := withMainContext do
  runRawRelWPBindLeftRule <||> runStdDoRelTripleBindLeftRule

/-- Controlled one-sided relational bind step on the right. -/
def runRVCGenRawBindRightStep : TacticM Bool := withMainContext do
  runRawRelWPBindRightRule <||> runStdDoRelTripleBindRightRule

/-- Normalize and classify the main relational goal, then try its structural rules. -/
def runRVCGenCore : TacticM Bool := withVCGenStructuralTiming <| withMainContext do
  tryNormalizeRelBindStructure
  if (← getGoals).isEmpty then
    return true
  if ← runRawRelWPReflRule then
    return true
  if ← runRawRelWPPureRule then
    return true
  if ← runRawRelWPBindRule then
    return true
  if ← runRawRelWPVCSpecBackward then
    return true
  let target ← instantiateMVars (← getMainTarget)
  if ← tryCloseRelGoalAtCoreGateway then
    return true
  if let some (_pre, oa, ob, _) := stdDoRelTripleGoalParts? target then
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if ← runERelPureRule then
      return true
    if ← runERelRndRule then
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

/-- Apply a relational structural step with an explicit intermediate relation or theorem hint. -/
def runRVCGenCoreUsing (hint : TSyntax `term) : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if let some (_, oa, ob, _) := stdDoRelTripleGoalParts? target then
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
      -- Generic bijection-coupling-bind fallback. Handles `<$>`-shaped goals (and
      -- more generally any goal that normalizes to `bind` on both sides) by
      -- treating the hint as a bijection `f : α → α`, cutting with
      -- `R := fun a b => b = f a`, and discharging the sample subgoal via
      -- `relTriple_uniformSample_bij` / `relTriple_query_bij`.
      if ← runRelBindBijRuleUsing hint then
        return true
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        runRelSimRuleUsing hint
      else
        return false

private def potentialRelHintNames : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
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
                found := found.push name
    return found

private def localNameOfExpr? (expr : Expr) : TacticM (Option Name) := do
  match expr.consumeMData with
  | .fvar fvarId =>
      match (← getLCtx).find? fvarId with
      | some decl =>
          if isUsableBinderName decl.userName then
            return some decl.userName
          return none
      | none => return none
  | _ => return none

private def pushNameIfNew (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def relTripleTopParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app := target.consumeMData
  guard <| app.getAppFn.isConstOf ``OracleComp.ProgramLogic.Relational.RelTriple
  let args ← trailingArgs? app 3
  let #[oa, ob, post] := args | none
  some (oa, ob, post)

private def provenRelPostHintNames : TacticM (Array Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless relationalGoalParts? target |>.isSome do
    return #[]
  let mut found : Array Name := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if ← isProp type then
        if let some (_, _, post) := relTripleTopParts? type then
          if let some name ← localNameOfExpr? post then
            found := pushNameIfNew found name
  return found

private def provenBijectiveHintNames : TacticM (Array Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless relationalGoalParts? target |>.isSome do
    return #[]
  let mut found : Array Name := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if ← isProp type then
        if let some app := findAppWithHead? ``Function.Bijective type then
          if let some args := trailingArgs? app 1 then
            if let some name ← localNameOfExpr? args[0]! then
              found := pushNameIfNew found name
  return found

private def priorityRelHintNames : TacticM (Array Name) := do
  let mut found := #[]
  for name in ← provenRelPostHintNames do
    found := pushNameIfNew found name
  for name in ← provenBijectiveHintNames do
    found := pushNameIfNew found name
  return found

private def findUniquePriorityRelHint? : TacticM (Option Name) := do
  let found ← priorityRelHintNames
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none

/-- Find the local hypotheses that work as relational `using` hints. -/
def findRelHintCandidates : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let proven ← priorityRelHintNames
    unless proven.isEmpty do
      return proven
    let mut found : Array Name := #[]
    for name in ← potentialRelHintNames do
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

/-- Lower a relational goal, apply the explicit hint, and name introduced binders. -/
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

private def closeRelTheoremStepGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  let (owned, rest) := ownedSubgoalsAfterMainStep before after
  let remainingOwned ← closeOwnedRelSubgoals owned
  setGoals (remainingOwned ++ rest)

/-- Try to close a relational goal by applying postcondition monotonicity and
closing both the inner triple and the implication from local hypotheses. -/
def tryCloseRelGoalConseq : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_post_mono <;> assumption))

/-- Weaken a relational postcondition through the supplied intermediate relation. -/
def runRelUptoRule (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_post_mono (R := $R) ?_ ?_))

private def runRVCGenStepWithTheoremDirect
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      let before ← getGoals
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals before
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

private def runRVCGenStepWithTheoremConseq
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if isRawStdDoRelWPGoal target then
    return (← runRawRelWPTheoremConseq thm requireClosed)
  let wrapper? ←
    if (relTripleGoalParts? target).isSome then
      pure <| some (← `(tactic|
        refine OracleComp.ProgramLogic.Relational.relTriple_post_mono ?_ ?_))
    else if (relWPGoalParts? target).isSome then
      pure <| some (← `(tactic|
        refine le_trans ?_
          (MAlgRelOrdered.relWP_mono
            (m₁ := OracleComp _) (m₂ := OracleComp _) (l := Prop) _ _ ?_)))
    else if (stdDoRelTripleGoalParts? target).isSome then
      pure <| some (← `(tactic|
        refine OracleComp.ProgramLogic.Relational.Loom.relTriple_conseq le_rfl ?_ ?_))
    else
      pure none
  let some wrapper := wrapper? | return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic wrapper
      unless ← focusFirstGoalSatisfying fun target =>
          (relTripleGoalParts? target).isSome ||
          (relWPGoalParts? target).isSome ||
          (stdDoRelTripleGoalParts? target).isSome ||
          isRawStdDoRelWPGoal target do
        throwError "rvcstep with theorem: failed to focus theorem subgoal after consequence rule"
      let before ← getGoals
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals before
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Apply a `@[vcspec]` relational rule to the current goal.
Default `rvcstep` fires cached rules directly. Raw `Std.Do'.rwp` goals also get
a narrow theorem-consequence fallback because their carrier inference can fail
before the cached path sees the concrete target carrier. -/
private def runRelationalVCSpecRule
    (entry : VCSpecEntry) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if isRawStdDoRelWPGoal target && entry.kind == .relWP then
    let saved ← saveState
    let ok ←
      match ← observing? do
        let before ← getGoals
        unless ← runVCSpecEntryRawRelConsequence entry do
          throwError "raw relational consequence rule did not apply"
        closeRelTheoremStepGoals before
      with
      | some _ => pure true
      | none => pure false
    if ok && (!requireClosed || (← getGoals).isEmpty) then
      return true
    saved.restore
  let saved ← saveState
  let ok ←
    match ← observing? do
      let before ← getGoals
      unless ← runVCSpecEntryCachedBackward entry do
        throwError "rvcstep: registered `@[vcspec]` rule did not apply"
      closeRelTheoremStepGoals before
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Try deterministic relational structural rules via cached `@[vcspec]`
before the bespoke structural dispatcher. -/
private def runDeterministicRelVCSpecRule : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some (oa, ob, _) := relationalGoalParts? target | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    for entry in entries do
      if (relVCSpecTier entry).canRunInDefaultStructural then
        if ← runRelationalVCSpecRule entry then
          return true
    return false

/-- Try direct discrimination-tree hits for the current pair of computations.
This is a default-safe registered-rule tier because it does not scan unrelated
fallback theorems or choose among broad search candidates. -/
private def runDirectRelVCSpecRule : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some kind :=
      if (relTripleGoalParts? target).isSome then
        some .relTriple
      else if (relWPGoalParts? target).isSome || isRawStdDoRelWPGoal target then
        some .relWP
      else
        none
      | return false
    let some (oa, ob, _) := relationalGoalParts? target <|> rawRelWPGoalParts? target
      | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    for entry in entries do
      if entry.kind == kind && (relVCSpecTier entry).canRunInDefaultDirect then
        if ← runRelationalVCSpecRule entry then
          return true
    return false

/-- Apply an explicit relational theorem/assumption step and try to close any easy side goals. -/
def runRVCGenStepWithTheorem (thm : TSyntax `term) (requireClosed : Bool := false) :
    TacticM Bool := do
  if ← runRVCGenStepWithTheoremDirect thm requireClosed then
    return true
  runRVCGenStepWithTheoremConseq thm requireClosed

private def relationalGoalKind? (target : Expr) : Option VCSpecKind :=
  if (relTripleGoalParts? target).isSome then
    some .relTriple
  else if (relWPGoalParts? target).isSome || isRawStdDoRelWPGoal target then
    some .relWP
  else
    none

private def takeCandidatePrefix (entries : Array VCSpecEntry) : Array VCSpecEntry :=
  (entries.toList.take 8).toArray

private def registeredRVCGenRuleCandidateTiers
    (includeFallbackSearch : Bool := false) : TacticM (Array (Array VCSpecEntry)) := do
  let target ← instantiateMVars (← getMainTarget)
  let some kind := relationalGoalKind? target | return #[]
  let some (oa, ob, _) := relationalGoalParts? target <|> rawRelWPGoalParts? target | return #[]
  let goalPattern := classifyRelationalCompPattern oa ob
  let direct :=
    (← getRegisteredRelationalVCSpecEntries oa ob).filter fun entry =>
      entry.kind == kind && (relVCSpecTier entry).canRunInDefaultDirect
  let fallbackAll :=
    (← getVCSpecEntriesOfKind kind).filter fun entry =>
      includeFallbackSearch &&
        (relVCSpecTier entry).canRunInFallbackSearch &&
        !(direct.any fun directEntry => directEntry.theoremName! == entry.theoremName!)
  let fallbackPreferred := fallbackAll.filter (·.spec.compPattern == goalPattern)
  let fallbackFallback := fallbackAll.filter (·.spec.compPattern != goalPattern)
  let mut tiers : Array (Array VCSpecEntry) := #[]
  let rawTiers :=
    if includeFallbackSearch then
      #[direct, fallbackPreferred, fallbackFallback]
    else
      #[direct]
  for tier in rawTiers do
    let tier := takeCandidatePrefix tier
    unless tier.isEmpty do
      tiers := tiers.push tier
  return tiers

private def runRelationalVCSpecFallbackSearchStep : TacticM Bool := do
  withVCGenRegisteredTiming do
    for tier in ← registeredRVCGenRuleCandidateTiers (includeFallbackSearch := true) do
      for entry in tier do
        if (relVCSpecTier entry).canRunInFallbackSearch then
          if ← runRelationalVCSpecRule entry then
            return true
    return false

/-- Find default-safe registered relational `@[vcspec]` entries whose bounded
application makes progress on the current goal. This uses direct
discrimination-tree hits only; broad fallback/search tiers are reserved for
`rvcfinish` / `rvcgen!`. -/
def findRegisteredRVCGenRuleCandidates : TacticM (Array VCSpecEntry) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredRVCGenRuleCandidateTiers do
      let mut found : Array VCSpecEntry := #[]
      for entry in tier do
        let saved ← saveState
        let ok ← runRelationalVCSpecRule entry
        saved.restore
        if ok then
          found := found.push entry
      unless found.isEmpty do
        return found
    return #[]

private def relHintCandidateSteps (hintName : Name) : TacticM (Array PlannedStep) := do
  let genericStep :=
    mkRVCGenPlannedStep
      "rvcgen explicit hint"
      s!"rvcstep using {hintName}"
      (runRVCGenExplicitHintStep (mkIdent hintName))
  let target ← instantiateMVars (← getMainTarget)
  let some (oa, ob, _) := relationalGoalParts? target | return #[genericStep]
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && isBindExpr ob do
    return #[genericStep]
  let names ← getRelBindNames
  let namedHintStep :=
    mkRVCGenPlannedStep
      "rvcgen explicit hint with names"
      s!"rvcstep using {hintName}{renderAsClause names}"
      (runRVCGenStepUsingWithNames (mkIdent hintName) names)
  return #[namedHintStep, genericStep]

private def chooseBestRelHintStep? : TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenLocalHintTiming do
    let hintNames ← findRelHintCandidates
    let traceSteps := vcvio.vcgen.traceSteps.get (← getOptions)
    let mut best? : Option (PlannedStep × PreviewResult) := none
    let mut accepted : Array String := #[]
    for hintName in hintNames do
      for step in ← relHintCandidateSteps hintName do
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
          break
    match best? with
    | none => return none
    | some (step, preview) =>
        if traceSteps then
          let alternatives := accepted.filter (· != renderPlannedStepPreview step preview)
          return some (attachPlannerChoiceNotes step preview alternatives, preview)
        return some (step, preview)

private def chooseBestRegisteredRVCGenTheoremStep? :
    TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredRVCGenRuleCandidateTiers do
      let steps := tier.map fun entry =>
        mkRVCGenPlannedStep
          "rvcgen @[vcspec] theorem rule"
          s!"rvcstep with {entry.theoremName!}"
          (runRelationalVCSpecRule entry)
      if let some chosen ← chooseBestPlannedStepCandidate? steps then
        return some chosen
    return none

/-- Structural/default relational VCGen step, excluding explicit `using`-hint fallbacks. -/
def runRVCGenStructuralCore : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  if ← runDeterministicRelVCSpecRule then
    return true
  if ← runRVCGenCore then
    return true
  if (← getGoals).isEmpty then
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
  if structuralPreview.ok && structuralPreview.goalCount == 0 then
    return some structuralStep
  let closeStep :=
    mkRVCGenPlannedStep
      "rvcgen consequence close"
      "rvcfinish"
      (withVCGenCloseTiming tryCloseRelGoalConseq)
  let closePreview ← previewPlannedStepWithGoals closeStep
  if closePreview.ok && closePreview.goalCount == 0 then
    return some closeStep
  let hintCandidate? ← chooseBestRelHintStep?
  let theoremCandidate? ← chooseBestRegisteredRVCGenTheoremStep?
  if structuralPreview.ok then
    if closePreview.ok && closePreview.goalCount < structuralPreview.goalCount then
      return some closeStep
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
  if ← tryCloseRelGoalImmediate then
    return true
  if let some hintName ← findUniquePriorityRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if ← runDeterministicRelVCSpecRule then
    return true
  if ← runRVCGenCore then
    return true
  if ← runDirectRelVCSpecRule then
    return true
  if let some hintName ← findUniqueRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if (← getGoals).isEmpty then
    return true
  return progress

/-- Execute a relational step guided by an explicit hint. -/
def runRVCGenStepUsing (hint : TSyntax `term) : TacticM Bool := do
  runRVCGenExplicitHintStep hint

/-- Try the explicit relational rule, restoring tactic state if it fails. -/
def runRVCGenStrictStepUsing (hint : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  discard <| tryLowerRelGoal
  if ← runRVCGenCoreUsing hint then
    return true
  saved.restore
  return false

/-- Run one relational pass over all goals and collect replayable successful steps. -/
def runRVCGenPassPlanned : TacticM (Array PlannedStep) := do
  let goals ← getGoals
  if goals.isEmpty then
    return #[]
  let mut newGoals : Array MVarId := #[]
  let mut steps := #[]
  for goal in goals do
    setGoals [goal]
    if let some step ← runRVCGenPlannedStep? then
      steps := steps.push step
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return steps

/-- Run one relational pass over all goals, reporting whether any goal progressed. -/
def runRVCGenPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : Array MVarId := #[]
  for goal in goals do
    setGoals [goal]
    if ← runRVCGenStep then
      progress := true
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return progress

/-- Explain a failed relational step using the current goal shape and available rules. -/
def throwRVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rvcstep: failed to lower the `GameEquiv` goal into relational proof mode."
  if isEvalDistEqGoal target then
    throwError "rvcstep: failed to lower the `evalSPMF` equality into a `RelTriple` goal."
  match relationalGoalParts? target with
  | none =>
      throwError m!
        "rvcstep: expected a `GameEquiv`, `evalSPMF` equality, `RelTriple`, `RelWP`,\n\
        or quantitative `Std.Do'.RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      let hintCandidates ← potentialRelHintNames
      let theoremCandidateTiers ← registeredRVCGenRuleCandidateTiers
      let theoremCandidates := theoremCandidateTiers.foldl (init := #[]) fun acc tier =>
        acc ++ tier.map (·.theoremName!)
      let goalLabel :=
        if isStdDoRelTripleGoal target then
          "quantitative `Std.Do'.RelTriple`"
        else if (relWPGoalParts? target).isSome then
          "`RelWP`"
        else
          "`RelTriple`"
      let hintMsg :=
        if hintCandidates.isEmpty then
          ""
        else
          s!"\nPotential local `using` hints: {formatCandidateNames hintCandidates}"
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
          Use `rvcstep using Rin` when the two input lists are related by a\n\
          non-equality relation.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        throwError m!
          "rvcstep: found a `List.foldlM` relational goal but no fold rule applied.\n\
          Use `rvcstep using Rin` when the two input lists are related by a\n\
          non-equality relation.\n\
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
          "rvcstep: found a bind-on-both-sides relational goal but could not choose\n\
          an intermediate cut.\n\
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

/-- Explain why an explicit relational hint failed and list applicable local candidates. -/
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
    - bind cut relation (`α → β → Prop`)\n\
    - bind bijection coupling (`α → α`, on synchronized uniform/query binds)\n\
    - random/query bijection (`α → α`)\n\
    - `List.mapM` / `List.foldlM` input relation\n\
    - `simulateQ` state relation\n\
    {hintMsg}\n\
    Goal:{indentExpr target}"

/-- Try to close residual relational goals using consequence rules. -/
def runRVCGenCloseConseqPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← withVCGenCloseTiming tryCloseRelGoalConseq then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress

/-- Try registered relational specification rules across the remaining goals. -/
def runRVCGenFallbackVCSpecPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : Array MVarId := #[]
  for goal in goals do
    setGoals [goal]
    if ← runRelationalVCSpecFallbackSearchStep then
      progress := true
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return progress

/-- Close immediate relational leaf goals and retain the unresolved goals. -/
def runRVCGenLeafFinish : TacticM Unit := do
  let remaining ← closeOwnedRelSubgoals (← getGoals)
  setGoals remaining

/-- Search residual goals using game rewrites, consequence, and registered specification
rules. -/
def runRVCGenSearchFinish : TacticM Unit := do
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [game_rule]))
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals first
        | assumption
        | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
        | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
            (fun _ _ => by trivial)
        | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
        | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
        | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
        | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)
        | exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _
        | (try subst_vars
           first
             | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
             | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
             | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
             | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
             | exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _
             | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)
             | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
                (fun _ _ => by trivial))))
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "rvcgen fallback search" runRVCGenFallbackVCSpecPass
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "rvcgen finish" runRVCGenCloseConseqPass

/-- Perform the immediate relational leaf closure pass. -/
def runRVCGenFinish : TacticM Unit :=
  runRVCGenLeafFinish

end Relational
end TacticInternals
end OracleComp.ProgramLogic
