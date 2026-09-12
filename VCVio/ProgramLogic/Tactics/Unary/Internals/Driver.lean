/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Common
public import VCVio.ProgramLogic.Relational.Basic
public meta import VCVio.ProgramLogic.Tactics.Relational.Internals
public import Loom.Triple.SpecLemmas
public meta import VCVio.ProgramLogic.Tactics.Unary.Internals.Rules
import all VCVio.ProgramLogic.Tactics.Unary.Internals.Rules
public meta import VCVio.ProgramLogic.Tactics.Unary.Internals.Steps
import all VCVio.ProgramLogic.Tactics.Unary.Internals.Steps

/-!
# Unary VCGen goal dispatch and planning
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

universe u v

/-! ### Goal classification and per-kind dispatch

Mirrors `Loom.Tactic.VCGen.GoalKind` and `classifyGoalKind`: the structural
core picks one strategy per goal kind instead of falling through a procedural
cascade. New monad transformers / combinators become a new
`UnaryGoalKind` constructor plus a registered `@[vcspec]` rule, not another
`tryEvalTacticSyntax` block.

Probability lowering is run opportunistically *before* classification, since
`Pr[…]` may appear inside `wp …` goals that should ultimately dispatch via
raw `wp` or `Triple` rules; only goals where lowering actually fires bypass
the rest of the pipeline. -/

/-- High-level classification of a unary VCGen target.

Kept intentionally coarse: structural details (the bind continuation,
ite condition, matcher app, …) live in the `comp` payload, not in the
constructor, so per-kind handlers can share `tryEvalTacticSyntax`-style logic
with the existing helpers. -/
inductive UnaryGoalKind where
  /-- A relational `RelTriple` / `RelWP` goal; defer to the relational planner. -/
  | relational
  /-- A unary `Triple` whose computation is a `>>=` application. -/
  | tripleBind (comp : Expr)
  /-- A unary `Triple` whose computation is `ite c a b` (non-dependent). -/
  | tripleIte
  /-- A unary `Triple` whose computation is `dite c a b` (dependent). -/
  | tripleDite
  /-- A unary `Triple` whose computation is a compiled `match` matcher. -/
  | tripleMatch (comp : Expr)
  /-- A unary `Triple` whose computation is a `replicate` / `List.mapM` /
  `List.foldlM` head. -/
  | tripleLoop (comp : Expr)
  /-- A unary `Triple` whose computation does not match the cases above; the
  dispatcher unfolds to raw `wp` and lets `@[wpStep]` rewrite. -/
  | tripleOther
  /-- A raw `wp` / `≤ wp` goal. -/
  | rawWp
  /-- Unrecognized goal shape. -/
  | unknown
  deriving Inhabited

/-- Classify the current goal target as a `UnaryGoalKind`.

Probability lowering is intentionally not a kind here: it runs opportunistically
in `runVCGenStructuralCore` before classification, so a `wp … = ∑' u, Pr[…] * …`
goal still classifies as `rawWp` / `tripleOther` rather than getting stuck in a
non-lowerable prob branch. -/
def classifyUnaryGoalKind (target : Expr) : MetaM UnaryGoalKind := do
  if (relTripleGoalParts? target).isSome then return .relational
  match tripleGoalComp? target with
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      if isBindExpr comp then return .tripleBind comp
      if isIfExpr comp then
        return if comp.consumeMData.getAppFn.isConstOf ``dite then
          .tripleDite else .tripleIte
      if (← Lean.Meta.matchMatcherApp? comp).isSome then return .tripleMatch comp
      if isReplicateHead comp || isListFoldlMHead comp || isListMapMHead comp then
        return .tripleLoop comp
      return .tripleOther
  | none =>
      if (wpGoalComp? target).isSome then return .rawWp
      else return .unknown

/-- Lower the current probability goal and, when the residual goal is a raw
`wp`, follow up with one structural raw-`wp` step. Returns `true` whenever
lowering actually fired (matching the original cascade's behaviour). -/
private def runProbStep : TacticM Bool := do
  unless ← tryLowerProbGoal do return false
  if (← getGoals).isEmpty then
    return true
  let target ← instantiateMVars (← getMainTarget)
  if (tripleGoalComp? target).isNone && (relTripleGoalParts? target).isNone
      && (wpGoalComp? target).isSome then
    discard <| tryRawWpStructuralStep
  return true

/-- Bind dispatch family: try `triple_bind` immediately, then a support-based
cut, then the explicit `triple_bind_wp` / `stdDoTriple_bind_wp` closers. -/
private def runTripleBindStep (comp : Expr) : TacticM Bool := do
  if ← tryBindImmediate comp then return true
  if ← trySupportCutBind comp then return true
  if ← tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.triple_bind_wp)) then
    closeTheoremStepGoals
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.TacticInternals.Unary.stdDoTriple_bind_wp)) then
    closeTheoremStepGoals
    return true
  return false

/-- Last-ditch triple step: unfold to a raw `wp` goal and dispatch via
`@[wpStep]`. Used when the specialized triple dispatchers do not match. -/
private def runTripleFallback : TacticM Bool := do
  match ← observing? do
      evalTactic (← `(tactic| unfold OracleComp.ProgramLogic.Triple))
      evalTactic (← `(tactic| change _ ≤ OracleComp.ProgramLogic.wp _ _))
      unless ← runWpStepRules do
        throwError "vcstep: no matching wp rule after unfolding `Triple`"
    with
  | some _ => return true
  | none => return false

/-- Structural/default unary VCGen step, excluding explicit cut/invariant/theorem-driven
fallbacks and the final close/search phase.

Implemented as a single goal-kind dispatch (mirroring
`Loom.Tactic.VCGen.solve`): each kind picks one cluster of strategies, with
the `triple*` kinds optionally chaining into `runTripleFallback` so that
specialized dispatchers can defer cleanly. Probability lowering is run
opportunistically before classification so that goals where lowering does not
fire still flow through the structural dispatcher. -/
def runVCGenStructuralCore : TacticM Bool := withVCGenStructuralTiming do
  if (← getGoals).isEmpty then return false
  discard <| normalizeStdDoTripleGoal
  if hasProbGoal (← instantiateMVars (← getMainTarget)) then
    if ← runProbStep then return true
  -- For triple-shaped goals, normalize transformer `wp` layers and try an
  -- immediate close before structural dispatch.
  if (tripleGoalComp? (← instantiateMVars (← getMainTarget))).isSome then
    peelKnownTransformerWPInGoal
    if ← tryCloseNormalizedTransformerWP then return true
  let target ← instantiateMVars (← getMainTarget)
  match ← classifyUnaryGoalKind target with
  | .relational => TacticInternals.Relational.runRVCGenStep
  | .tripleBind comp =>
      if ← runTripleBindStep comp then return true
      runTripleFallback
  | .tripleIte =>
      if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_ite <;> intro)) then
        return true
      runTripleFallback
  | .tripleDite =>
      if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_dite <;> intro)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_ite <;> intro)) then
        return true
      runTripleFallback
  | .tripleMatch comp =>
      if ← tryMatchDecomp comp then return true
      runTripleFallback
  | .tripleLoop comp =>
      if ← tryLoopInvariantRuleAuto comp then return true
      if ← tryLoopFallback comp then return true
      runTripleFallback
  | .tripleOther => runTripleFallback
  | .rawWp => tryRawWpStructuralStep
  | .unknown => return false

private def mkStructuralStepForTarget (target : Expr) : PlannedStep :=
  let step := mkVCGenPlannedStep
    "vcgen structural step"
    "vcstep"
    runVCGenStructuralCore
  if !(hasProbGoal target) && (tripleGoalComp? target |>.isNone) &&
      (relTripleGoalParts? target |>.isNone) &&
      (wpGoalComp? target).isSome then
    withStepNotes step ["continuing in raw `wp` mode"]
  else
    step

private def runVCGenStructuralCoreWithNames (names : Array Name) : TacticM Bool := do
  if ← runVCGenStructuralCore then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

private def chooseBestCutStep? : TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenLocalHintTiming do
    let steps := (← potentialLocalHintNames).map fun cutName =>
      mkVCGenPlannedStep
        "vcgen explicit cut"
        s!"vcstep using {cutName}"
        (runHoareStepRuleUsing (mkIdent cutName))
    chooseBestPlannedStepCandidate? steps

private def chooseBestInvariantStep? : TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenLocalHintTiming do
    let steps := (← potentialLocalHintNames).map fun invName =>
      mkVCGenPlannedStep
        "vcgen explicit invariant"
        s!"vcstep inv {invName}"
        (runLoopInvExplicit (mkIdent invName))
    chooseBestPlannedStepCandidate? steps

private def chooseBestTheoremStep? : TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredVCGenRuleCandidateTiers do
      let steps := tier.map fun entry =>
        mkVCGenPlannedStep
          "vcgen @[vcspec] theorem rule"
          s!"vcstep with {entry.theoremName!}"
          (runUnaryVCSpecRule entry)
      if let some chosen ← chooseBestPlannedStepCandidate? steps then
        return some chosen
    return none

private def planExplicitProbEqStep? (plainPreview : PreviewResult) :
    TacticM (Option PlannedStep) := do
  let target ← instantiateMVars (← getMainTarget)
  unless isProbEqGoal target do
    return none
  let mut steps : Array PlannedStep := #[]
  for plan in ← probEqPlannerActionPlansForGoal do
    let replayText ← renderProbEqPlan plan
    steps := steps.push <| mkVCGenPlannedStep
      "vcgen probability plan"
      replayText
      (tryProbEqActions plan)
  match ← chooseBestPlannedStepCandidate? steps with
  | none => return none
  | some (step, preview) =>
      if !(plainPreview.ok) || preview.goalCount ≤ plainPreview.goalCount then
        return some step
      return none

/-- Choose one unary VCGen step and remember how to replay it explicitly. -/
def planVCGenStep? : TacticM (Option PlannedStep) := do
  if (← getGoals).isEmpty then
    return none
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    let introStep :=
      mkVCGenPlannedStep
        "vcgen intro"
        s!"vcstep{renderAsClause names}"
        (introMainGoalNames names)
    if ← previewPlannedStep introStep then
      return some introStep
  let structuralStep := mkStructuralStepForTarget target
  if let some comp := tripleGoalComp? target then
    let comp ← whnfReducible (← instantiateMVars comp)
    if isBindExpr comp then
      let immediateBindStep :=
        mkVCGenPlannedStep
          "vcgen bind step"
          "vcstep"
          (tryBindImmediate comp)
      if ← previewPlannedStep immediateBindStep then
        let names ← getSuggestedIntroNames 1
        let namedStructuralStep :=
          mkVCGenPlannedStep
            "vcgen named bind step"
            s!"vcstep{renderAsClause names}"
            (runVCGenStructuralCoreWithNames names)
        if ← previewPlannedStep namedStructuralStep then
          return some namedStructuralStep
        return some structuralStep
      if let some (cutStep, _) ← chooseBestCutStep? then
        return some cutStep
    if isReplicateHead comp || isListFoldlMHead comp || isListMapMHead comp then
      let autoInvariantStep :=
        mkVCGenPlannedStep
          "vcgen automatic loop invariant"
          "vcstep"
          (tryLoopInvariantRuleAuto comp)
      if ← previewPlannedStep autoInvariantStep then
        return some structuralStep
      if let some (invStep, _) ← chooseBestInvariantStep? then
        return some invStep
  let structuralPreview ← previewPlannedStepWithGoals structuralStep
  if structuralPreview.ok && structuralPreview.goalCount == 0 then
    return some structuralStep
  if let some explicitProbEqStep ← planExplicitProbEqStep? structuralPreview then
    return some explicitProbEqStep
  let theoremCandidate? ← chooseBestTheoremStep?
  if structuralPreview.ok then
    if let some (theoremStep, theoremPreview) := theoremCandidate? then
      if theoremPreview.goalCount < structuralPreview.goalCount then
        return some theoremStep
    return some structuralStep
  if let some (theoremStep, _) := theoremCandidate? then
    return some theoremStep
  let closeStep :=
    mkVCGenPlannedStep
      "vcgen close/search"
      "vcstep"
      tryCloseSpecGoal
  if ← previewPlannedStep closeStep then
    return some closeStep
  return none

/-- Execute one planned unary VCGen step, returning the chosen step for replay/trace. -/
def runVCGenPlannedStep? : TacticM (Option PlannedStep) := do
  let some step ← planVCGenStep?
    | return none
  if ← executePlannedStep step then
    return some step
  return none

/-- One step of VCGen on a `Triple` goal. Returns `true` if any progress was made. -/
def runVCGenStep : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    if ← introMainGoalNames names then
      return true
  let cheapCloseState ← saveState
  if ← tryEvalTacticSyntax (← `(tactic|
      (refine Std.Do'.Triple.iff.mpr ?_
       repeat intro _
       simp [Lean.Order.PartialOrder.rel, MonadLift.monadLift,
         OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp,
         OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp_epost,
         MAlgOrdered.wp_bind, MAlgOrdered.wp_pure, MAlgOrdered.wp_map,
         one_mul, mul_one]))) then
    if (← getGoals).isEmpty then
      return true
  cheapCloseState.restore
  if ← tryCloseNormalizedTransformerWP then
    return true
  if ← runVCGenStructuralCore then
    return true
  if ← tryCloseSpecGoal then
    return true
  if let some entry ← findRegisteredVCGenRule? then
    if ← runUnaryVCSpecRule entry then
      return true
  tryCloseSpecGoal

/-- Run one VCGen pass across all current goals and record the chosen steps. -/
def runVCGenPassPlanned : TacticM (Array PlannedStep) := do
  let goals ← getGoals
  if goals.isEmpty then
    return #[]
  let mut newGoals : Array MVarId := #[]
  let mut steps := #[]
  for goal in goals do
    setGoals [goal]
    if let some step ← runVCGenPlannedStep? then
      steps := steps.push step
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return steps

/-- Run one VCGen pass across all current goals. -/
def runVCGenPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : Array MVarId := #[]
  for goal in goals do
    setGoals [goal]
    if ← runVCGenStep then
      progress := true
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return progress

end Unary
end TacticInternals
end OracleComp.ProgramLogic
