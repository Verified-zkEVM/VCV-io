/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Match.MatcherApp
public meta import Lean.Meta.Sym.Pattern
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.ProgramLogic.NotationCore

/-!
# VCGen Planner Core

Shared planning infrastructure for the unary and relational VCGen tactics.
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-- Maximum number of exhaustive planner passes before requiring manual stepping. -/
register_option vcvio.vcgen.maxPasses : Nat := {
  defValue := 64
  descr := "Maximum number of exhaustive vcgen/rvcgen passes before requiring manual stepping."
}

/-- Emit the selected steps, goal counts, and planner choice notes. -/
register_option vcvio.vcgen.traceSteps : Bool := {
  defValue := false
  descr := "Emit opt-in trace messages for chosen vcgen/rvcgen planned steps."
}

/-- Collect and report elapsed time for VCGen planner phases. -/
register_option vcvio.vcgen.time : Bool := {
  defValue := false
  descr := "Emit cumulative timing for internal vcgen/rvcgen planner phases."
}

/-- Trace hits and misses in the registered backward-rule cache. -/
register_option vcvio.vcgen.traceCachedRules : Bool := {
  defValue := false
  descr := "Emit opt-in trace messages for cached `@[vcspec]` backward-rule hits and misses."
}

/-- Accumulated nanosecond timings and backward-rule cache counters for a VCGen run. -/
structure VCGenTimingData where
  /-- Elapsed nanoseconds spent in speculative previews. -/
  previewNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in structural rule selection. -/
  structuralNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in weakest-precondition steps. -/
  wpStepNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in probability-equality planning. -/
  probPlannerNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in local hypothesis search. -/
  localHintNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in registered rule search. -/
  registeredNs : UInt64 := 0
  /-- Elapsed nanoseconds spent constructing cached backward rules. -/
  cachedRuleBuildNs : UInt64 := 0
  /-- Number of successful backward-rule cache lookups. -/
  cachedRuleHits : Nat := 0
  /-- Number of failed backward-rule cache lookups. -/
  cachedRuleMisses : Nat := 0
  /-- Elapsed nanoseconds spent in goal closure. -/
  closeNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in complete planner passes. -/
  passNs : UInt64 := 0
  /-- Elapsed nanoseconds spent in final closure. -/
  finishNs : UInt64 := 0
  deriving Inhabited

/-- Mutable timing counters shared by the unary and relational planners. -/
initialize vcGenTimingRef : IO.Ref VCGenTimingData ← IO.mkRef {}

/-- Run an action and return its result with the elapsed monotonic time in nanoseconds. -/
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

/-- Add elapsed nanoseconds to the backward-rule cache construction counter. -/
def addCachedRuleBuildTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with cachedRuleBuildNs := d.cachedRuleBuildNs + ns }

/-- Record a successful lookup in the backward-rule cache. -/
def addCachedRuleHit : BaseIO Unit :=
  addVCGenTiming fun d => { d with cachedRuleHits := d.cachedRuleHits + 1 }

/-- Record a failed lookup in the backward-rule cache. -/
def addCachedRuleMiss : BaseIO Unit :=
  addVCGenTiming fun d => { d with cachedRuleMisses := d.cachedRuleMisses + 1 }

private def addCloseTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with closeNs := d.closeNs + ns }

private def addPassTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with passNs := d.passNs + ns }

private def addFinishTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with finishNs := d.finishNs + ns }

/-- Time an action and accumulate its duration when VCGen timing is enabled. -/
def withVCGenTiming {α : Type} (add : UInt64 → BaseIO Unit) (k : TacticM α) : TacticM α := do
  if vcvio.vcgen.time.get (← getOptions) then
    let (a, ns) ← timeNs k
    add ns
    return a
  else
    k

/-- Accumulate time spent in speculative previews when VCGen timing is enabled. -/
def withVCGenPreviewTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addPreviewTime k

/-- Accumulate time spent in structural rule selection when VCGen timing is enabled. -/
def withVCGenStructuralTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addStructuralTime k

/-- Accumulate time spent in weakest-precondition steps when VCGen timing is enabled. -/
def withVCGenWpStepTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addWpStepTime k

/-- Accumulate time spent in probability-equality planning when VCGen timing is enabled. -/
def withVCGenProbPlannerTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addProbPlannerTime k

/-- Accumulate time spent in local hypothesis search when VCGen timing is enabled. -/
def withVCGenLocalHintTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addLocalHintTime k

/-- Accumulate time spent in registered rule search when VCGen timing is enabled. -/
def withVCGenRegisteredTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addRegisteredTime k

/-- Accumulate time spent in goal closure when VCGen timing is enabled. -/
def withVCGenCloseTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addCloseTime k

/-- Accumulate time spent in complete planner passes when VCGen timing is enabled. -/
def withVCGenPassTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addPassTime k

/-- Accumulate time spent in final closure when VCGen timing is enabled. -/
def withVCGenFinishTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addFinishTime k

/-- Clear the accumulated counters at the start of a timed VCGen run. -/
def resetVCGenTimingIfEnabled : TacticM Unit := do
  if vcvio.vcgen.time.get (← getOptions) then
    vcGenTimingRef.set {}

private def formatNsMs (ns : UInt64) : String :=
  s!"{ns / 1000000}ms"

/-- Report accumulated phase times and cache counters when timing is enabled. -/
def logVCGenTimingIfEnabled (label : String) : TacticM Unit := do
  if vcvio.vcgen.time.get (← getOptions) then
    let d ← vcGenTimingRef.get
    logInfo m!"[{label} timing] preview={formatNsMs d.previewNs}, \
      structural={formatNsMs d.structuralNs}, wpStep={formatNsMs d.wpStepNs}, \
      probPlanner={formatNsMs d.probPlannerNs}, localHints={formatNsMs d.localHintNs}, \
      registered={formatNsMs d.registeredNs}, \
      cachedRules={formatNsMs d.cachedRuleBuildNs} \
      (hits={d.cachedRuleHits}, misses={d.cachedRuleMisses}), close={formatNsMs d.closeNs}, \
      passes={formatNsMs d.passNs}, finish={formatNsMs d.finishNs}"

/-- Reset timing counters, execute a planner run, and report its phase times. -/
def withVCGenRunTiming {α : Type} (label : String) (k : TacticM α) : TacticM α := do
  resetVCGenTimingIfEnabled
  let a ← k
  logVCGenTimingIfEnabled label
  return a

/-- An executable proof step together with a label, replay syntax, and diagnostic notes. -/
structure PlannedStep where
  /-- Short label identifying the rule or strategy selected by the planner. -/
  label : String
  /-- Tactic text that reproduces the selected step. -/
  replayText : String
  /-- Execute the step, reporting whether it made progress. -/
  run : TacticM Bool
  /-- Additional explanations included in the optional step trace. -/
  notes : List String := []

/-- Progress flag and residual goal count observed during a speculative proof step. -/
structure PreviewResult where
  /-- Whether the speculative action reported progress. -/
  ok : Bool
  /-- Number of goals left by the speculative action. -/
  goalCount : Nat

/-- Append explanatory notes to an existing planned step. -/
def withStepNotes (step : PlannedStep) (notes : List String) : PlannedStep :=
  { step with notes := step.notes ++ notes }

/-- Format declaration names as a comma-separated list of code references. -/
def formatCandidateNames (names : Array Name) : String :=
  String.intercalate ", " <| names.toList.map fun name => s!"`{name}`"

/-- Run an action speculatively and restore the saved tactic state afterward. -/
def previewAction (action : TacticM Bool) : TacticM Bool := do
  let saved ← saveState
  let ok ← withVCGenPreviewTiming action
  saved.restore
  return ok

/-- Preview an action's progress and residual goal count, then restore tactic state. -/
def previewActionWithGoals (action : TacticM Bool) : TacticM PreviewResult := do
  let saved ← saveState
  let ok ← withVCGenPreviewTiming action
  let goalCount := (← getGoals).length
  saved.restore
  return { ok, goalCount }

/-- Preview whether a planned step succeeds without committing its proof-state changes. -/
def previewPlannedStep (step : PlannedStep) : TacticM Bool :=
  previewAction step.run

/-- Preview a planned step's success and residual goals without committing it. -/
def previewPlannedStepWithGoals (step : PlannedStep) : TacticM PreviewResult :=
  previewActionWithGoals step.run

/-- Describe a candidate by its replay text and residual goal count. -/
def renderPlannedStepPreview (step : PlannedStep) (preview : PreviewResult) : String :=
  s!"{step.replayText} -> {preview.goalCount} goal(s)"

/-- Annotate the chosen step with its residual goal count and accepted alternatives. -/
def attachPlannerChoiceNotes
    (step : PlannedStep) (preview : PreviewResult) (alternatives : Array String) : PlannedStep :=
  withStepNotes step <|
    [s!"planner preview leaves {preview.goalCount} goal(s)"] ++
      if alternatives.isEmpty then
        []
      else
        [s!"alternatives: {String.intercalate "; " alternatives.toList}"]

/-- Choose the successful candidate leaving the fewest goals, preferring earlier ties. -/
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

/-- Trace a successful step's replay text, goal-count change, and diagnostic notes. -/
def logPlannedStep (step : PlannedStep) (beforeGoals afterGoals : Nat) : TacticM Unit := do
  if vcvio.vcgen.traceSteps.get (← getOptions) then
    logInfo m!"[{step.label}] {step.replayText} (goals {beforeGoals} -> {afterGoals})"
    for note in step.notes do
      logInfo m!"  {note}"

/-- Execute a planned step and trace its result when step tracing is enabled. -/
def executePlannedStep (step : PlannedStep) : TacticM Bool := do
  let beforeGoals := (← getGoals).length
  let ok ← step.run
  if ok then
    let afterGoals := (← getGoals).length
    logPlannedStep step beforeGoals afterGoals
  return ok

/-- Render a pass as an `all_goals first` tactic, or return none for an empty pass. -/
def renderPassReplayLine (steps : Array PlannedStep) : Option String :=
  if steps.isEmpty then
    none
  else
    let body := String.intercalate " | " <| steps.toList.map (·.replayText)
    some s!"all_goals first | {body} | skip"

/-- Compute weak-head normal form while unfolding only reducible definitions. -/
def whnfReducible (e : Expr) : MetaM Expr :=
  withReducible <| whnf e

/-- Normalize the reducible oracle wrappers in a goal-side computation so its
key agrees with the patterns produced by `Sym.mkPatternFromDeclWithKey`.
`Sym.DiscrTree.getMatch` is purely structural, and those stored patterns unfold
`OracleComp`, `OracleQuery`, and `OracleSpec.toPFunctor` to the underlying
structure constructor.

Do not use the more general `Sym.preprocessType` here. Besides being intended
for declaration types rather than terms, in Lean 4.33 it also unfolds reducible
user programs. A program containing a matcher can then make later
definitional equality reduce a matcher with loose de Bruijn variables and
panic in `whnfEasyCases`. The wrappers below are the only newly
reducible declarations whose shapes registry lookup needs to expose. -/
def symMatchKey (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (pre := fun e => do
    let some declName := e.getAppFn.constName? | return .continue
    unless declName == ``OracleComp || declName == ``OracleQuery ||
        declName == ``OracleSpec.toPFunctor do
      return .continue
    let some value ← unfoldDefinition? e | return .continue
    return .visit value)

/-- Return an application's head constant, ignoring expression metadata. -/
def headConstName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

/-- Extract the last requested number of application arguments, if enough are present. -/
def trailingArgs? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.consumeMData.getAppArgs
  if _h : n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none

/-- Find an application of the named constant inside an expression, ignoring metadata. -/
def findAppWithHead? (head : Name) (e : Expr) : Option Expr :=
  (e.find? fun e' => e'.consumeMData.getAppFn.isConstOf head).map Expr.consumeMData

/-- Extract both computations and the postcondition from a VCVio or Loom relational triple. -/
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

/-- Extract both computations and the postcondition from a relational weakest precondition. -/
def relWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelWP target
  let args ← trailingArgs? app 3
  let #[oa, ob, post] := args | none
  some (oa, ob, post)

/-- Extract a Loom relational triple's precondition, computations, and postcondition. -/
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

/-- Extract the computation from a VCVio or Loom weakest-precondition expression. -/
def wpGoalComp? (target : Expr) : Option Expr := do
  let (app, k) ← findWpApp? target
  let args ← trailingArgs? app k
  some args[0]!

/-- Extract the computation and postcondition from a unary weakest precondition. -/
def wpGoalParts? (target : Expr) : Option (Expr × Expr) := do
  let (app, k) ← findWpApp? target
  let args ← trailingArgs? app k
  some (args[0]!, args[1]!)

/-- Recognize a lower bound on a unary weakest precondition and extract its three parts. -/
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

/-- Extract the computation from a VCVio or Loom unary triple. -/
def tripleGoalComp? (target : Expr) : Option Expr := do
  let (app, k) ← findTripleApp? target
  let args ← trailingArgs? app k
  some args[1]!

/-- Extract a unary triple's precondition, computation, and postcondition. -/
def tripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let (app, k) ← findTripleApp? target
  let args ← trailingArgs? app k
  some (args[0]!, args[1]!, args[2]!)

/-- Check whether an expression contains an oracle simulation. -/
def isSimulateQAction (e : Expr) : Bool :=
  (findAppWithHead? ``simulateQ e).isSome

/-- Check whether an expression contains `StateT.run`. -/
def hasStateTRunExpr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run e).isSome

/-- Check whether an expression contains `StateT.run'`. -/
def hasStateTRun'Expr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run' e).isSome

/-- Check for either stateful execution projection in an expression. -/
def hasStateTRunLike (e : Expr) : Bool :=
  hasStateTRunExpr e || hasStateTRun'Expr e

/-- Check for both an oracle simulation and a stateful execution projection. -/
def hasSimulateQRunLike (e : Expr) : Bool :=
  isSimulateQAction e && hasStateTRunLike e

/-- Check whether a postcondition contains the equality-relation wrapper. -/
def isEqRelPost (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.ProgramLogic.Relational.EqRel e).isSome

/-- Recognize a monadic or explicit state-transformer bind at the expression head. -/
def isBindExpr (e : Expr) : Bool :=
  let fn := e.consumeMData.getAppFn
  fn.isConstOf ``Bind.bind || fn.isConstOf ``StateT.bind

/-- Recognize monadic `pure` at the expression head. -/
def isPureExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Pure.pure

/-- Recognize an ordinary or dependent conditional at the expression head. -/
def isIfExpr (e : Expr) : Bool :=
  let fn := e.consumeMData.getAppFn
  fn.isConstOf ``ite || fn.isConstOf ``dite

/-- Recognize functorial map at the expression head. -/
def isMapExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Functor.map

/-- Check whether an expression contains oracle-computation replication. -/
def isReplicateExpr (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.replicate e).isSome

/-- Check whether an expression contains a monadic list traversal. -/
def isListMapMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.mapM e).isSome

/-- Check whether an expression contains a monadic left fold over a list. -/
def isListFoldlMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.foldlM e).isSome

/-- Recognize oracle-computation replication at the expression head. -/
def isReplicateHead (e : Expr) : Bool :=
  (headConstName? e) == some ``OracleComp.replicate

/-- Recognize monadic list traversal at the expression head. -/
def isListMapMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.mapM

/-- Recognize monadic list folding at the expression head. -/
def isListFoldlMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.foldlM

/-- Recognize a game-equivalence goal without unfolding the equivalence predicate. -/
def isGameEquivGoal (target : Expr) : Bool :=
  target.consumeMData.getAppFn.isConstOf ``OracleComp.ProgramLogic.GameEquiv

/-- Recognize equality with compatibility distribution evaluations on both sides. -/
def isEvalDistEqGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getArg! 1
    let rhs := target.getArg! 2
    (findAppWithHead? ``evalSPMF lhs).isSome && (findAppWithHead? ``evalSPMF rhs).isSome
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

/-- Try a tactic syntax node, returning false if tactic evaluation fails. -/
def tryEvalTacticSyntax (stx : Syntax) : TacticM Bool :=
  (evalTactic stx *> pure true) <|> pure false

/-- Move the first matching goal to the front while preserving the order of the others. -/
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

/-- Run progress-making passes up to the configured limit, failing if further progress
remains. -/
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

/-- Collect each nonempty pass's results, failing if the configured limit stops further
progress. -/
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
