/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common
import VCVio.ProgramLogic.Relational.Basic
import VCVio.ProgramLogic.Tactics.Relational.Internals

/-!
# Unary VCGen Internals

Implementation details for the unary VCGen planner and close passes.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

attribute [vcspec] OracleComp.ProgramLogic.triple_pure

private def mkVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }

private def hasProbGoal (target : Expr) : Bool :=
  (findAppWithHead? ``probEvent target).isSome || (findAppWithHead? ``probOutput target).isSome

def throwWpStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match wpGoalComp? target with
  | none =>
      throwError "vcstep: expected a goal containing `wp`; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      throwError
        "vcstep: found a `wp` goal, but none of the current single-step rules apply to:\n\
        {indentExpr comp}\n\
        Current rules handle bind, pure, `replicate`, `List.mapM`, `List.foldlM`, query, `if`, \
        uniform sampling, `map`, `simulateQ`, `simulateQ ... run'`, and `liftComp`."

def runHoareStepRuleUsing (cut : TSyntax `term) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      if isBindExpr comp then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_bind (cut := $cut)))
      else
        return false
  | none => return false

/-- Check whether an expression (possibly under `∀` quantifiers and `mdata`) contains
 a unary triple application as its head. -/
private def hasTripleHead (e : Expr) : Bool :=
  let rec go : Expr → Bool
    | .forallE _ _ body _ => go body
    | .mdata _ e => go e
    | e => (tripleGoalComp? e).isSome
  go e

/-- Extract the head function of the computation argument from a unary triple
application, after stripping `∀` quantifiers and `mdata`. -/
private def tripleCompFn? (e : Expr) : Option Expr :=
  let rec go : Expr → Option Expr
    | .forallE _ _ body _ => go body
    | .mdata _ e => go e
    | e => do
        let comp ← tripleGoalComp? e
        some comp.consumeMData.getAppFn
  go e

/-- Try to close a `Triple` goal by targeted application of local hypotheses
whose type (possibly under `∀` quantifiers) has `Triple` as head and whose
computation argument structurally matches the goal's computation.
Much faster than `assumption` + `solve_by_elim` when the goal has unresolved metavariables,
because it skips expensive `isDefEq` checks against non-matching hypotheses. -/
private def tryApplyTripleHyp : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some goalCompFn := tripleCompFn? target | return false
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hypType ← instantiateMVars ldecl.type
    unless hasTripleHead hypType do continue
    let some hypCompFn := tripleCompFn? hypType | continue
    unless goalCompFn == hypCompFn do continue
    if ← tryEvalTacticSyntax (← `(tactic| exact $(mkIdent ldecl.userName))) then
      return true
    if hypType.isForall then
      let saved ← saveState
      if ← tryEvalTacticSyntax (← `(tactic| apply $(mkIdent ldecl.userName) <;> assumption)) then
        return true
      saved.restore
  return false

/-- Try to close the current goal using only immediate local information.
This is intentionally cheap: it is used while speculating on `triple_bind`, so it must not
launch expensive proof search on goals with unresolved cut metavariables. -/
def tryCloseSpecGoalImmediate : TacticM Bool := do
  tryApplyTripleHyp <||>
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic| solve_by_elim (maxDepth := 2))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_pure _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_zero _ _)) <||>
  tryEvalTacticSyntax (← `(tactic| exact le_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_ofLE le_rfl))

/-- Try bounded local proof search on a closed goal.
We only invoke `solve_by_elim` once the target has no unresolved expression metavariables; this
avoids pathological search on speculative intermediate cuts introduced by `triple_bind`. -/
def tryCloseSpecGoalSearch : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasExprMVar then
    return false
  tryEvalTacticSyntax (← `(tactic| (
    repeat intro
    simp only [OracleComp.ProgramLogic.triple_iff_le_wp] at *
    solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans]
  )))

private def closeTheoremStepGoals : TacticM Unit := do
  let goals ← getGoals
  let mut remaining : List MVarId := []
  for goal in goals do
    if ← goal.isAssigned then continue
    setGoals [goal]
    unless ← tryApplyTripleHyp do
      remaining := remaining ++ [goal]
  setGoals remaining
  unless remaining.isEmpty do
    discard <| tryEvalTacticSyntax (← `(tactic|
      all_goals first
        | assumption
        | simp
        | (repeat intro; split_ifs <;> simp_all)
        | (
            repeat intro
            simp only [OracleComp.ProgramLogic.triple_iff_le_wp] at *
            solve_by_elim (maxDepth := 4) [OracleComp.ProgramLogic.wp_mono, le_trans]
          )))

private def runVCGenStepWithTheoremDirect
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic| apply $thm))
      closeTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

private def runVCGenStepWithTheoremConseq
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  unless (tripleGoalComp? target).isSome do
    return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic| refine OracleComp.ProgramLogic.triple_conseq le_rfl ?_ $thm))
      closeTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Apply a `@[vcspec]` unary rule to the current goal.
Default `vcstep` first tries the cached rule directly. For folded unary
`Triple` goals, a global declaration can also be applied under `triple_conseq`,
which lets a registered concrete postcondition theorem feed a weaker goal
postcondition. -/
private def runUnaryVCSpecRule
    (entry : VCSpecEntry) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      unless ← runVCSpecEntryCachedBackward entry do
        throwError "vcstep: registered `@[vcspec]` rule did not apply"
      closeTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Apply an explicit unary theorem/assumption step and try to close any easy side goals.
When `requireClosed` is true, the step only succeeds if no goals remain afterwards. -/
def runVCGenStepWithTheorem (thm : TSyntax `term) (requireClosed : Bool := false) :
    TacticM Bool := do
  if ← runVCGenStepWithTheoremDirect thm requireClosed then
    return true
  runVCGenStepWithTheoremConseq thm requireClosed

/-- Try to close the current goal (typically a `Triple` subgoal) using direct hypotheses,
canonical leaf rules, or bounded local consequence search. -/
def tryCloseSpecGoal : TacticM Bool := do
  tryCloseSpecGoalImmediate <||> tryCloseSpecGoalSearch

/-- Normalize Loom's unary triple head to VCVio's quantitative `Triple` abbrev.

The two goals are definitionally equal for `OracleComp` with the no-exception
postcondition, but proof terms produced directly against the `Std.Do'.Triple`
head can trip Lean's kernel on anonymous proofs. Normalizing before structural
steps keeps the Loom notation surface while making the unary tactic operate on
its historical canonical head. -/
private def normalizeStdDoTripleGoal : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  unless (findAppWithHead? ``Std.Do'.Triple target).isSome do
    return false
  tryEvalTacticSyntax (← `(tactic| change OracleComp.ProgramLogic.Triple _ _ _))

/-- Finish-only closure step: includes the support-sensitive leaf rules that are too expensive
for the default `vcstep` hot path. -/
def tryCloseSpecGoalFinal : TacticM Bool := do
  tryApplyTripleHyp <||>
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_pure _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_zero _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    classical
    exact OracleComp.ProgramLogic.triple_support _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_propInd_of_support _ _ (by assumption))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_probEvent_eq_one _ _ (by assumption))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_probOutput_eq_one _ _ (by assumption))) <||>
  tryEvalTacticSyntax (← `(tactic| exact le_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_ofLE le_rfl)) <||>
  tryCloseSpecGoalSearch

/-- Run one bounded finish/closure pass across all current goals. -/
def runVCGenClosePass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← withVCGenCloseTiming tryCloseSpecGoalFinal then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress

/-- Try to decompose a `match` expression in the computation by case-splitting
on its discriminant(s). Only fires when the computation is a compiled matcher
(detected via `matchMatcherApp?`). Delegates to `split` which handles the actual
case analysis. -/
def tryMatchDecomp (comp : Expr) : TacticM Bool := do
  let some _ ← Lean.Meta.matchMatcherApp? comp | return false
  tryEvalTacticSyntax (← `(tactic| split))

/-- Check if an expression is a lambda whose body does not use the bound variable
(i.e. a constant function `fun _ => c`). -/
def isConstantLambda (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ body _ => !body.hasLooseBVar 0
  | _ => false

/-- Try the strongest automatic bind step: `triple_bind` plus immediate closure of the
spec side-goal. -/
def tryBindImmediate (comp : Expr) : TacticM Bool := do
  if !isBindExpr comp then
    return false
  match ← observing? do
    evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_bind))
    unless ← tryCloseSpecGoalImmediate do throwError "" with
  | some _ => return true
  | none => return false

/-- Try only the automatic loop-invariant rules, without the structural fallback rules. -/
def tryLoopInvariantRuleAuto (comp : Expr) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, _comp, post) := tripleGoalParts? target | return false
  if isReplicateHead comp then
    if isConstantLambda post then
      match ← observing? do
        evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_replicate_inv))
        unless ← tryCloseSpecGoalImmediate do throwError "" with
      | some _ => return true
      | none => pure ()
  if isListFoldlMHead comp then
    match ← observing? do
      evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_list_foldlM_inv))
      unless ← tryCloseSpecGoalImmediate do throwError "" with
    | some _ => return true
    | none => pure ()
  if isListMapMHead comp then
    if isConstantLambda post then
      match ← observing? do
        evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_list_mapM_inv))
        unless ← tryCloseSpecGoalImmediate do throwError "" with
      | some _ => return true
      | none => pure ()
  return false

/-- Try only the structural loop fallback rules (`succ` / `cons`) after invariant search. -/
def tryLoopFallback (comp : Expr) : TacticM Bool := do
  if isReplicateHead comp then
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_replicate_succ)) then
      return true
  if isListFoldlMHead comp then
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_list_foldlM_cons)) then
      return true
  if isListMapMHead comp then
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_list_mapM_cons)) then
      return true
  return false

/-- Apply a loop invariant rule with an explicitly provided invariant. -/
def runLoopInvExplicit (inv : TSyntax `term) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | none => return false
  | some comp =>
    let comp ← whnfReducible (← instantiateMVars comp)
    if isReplicateHead comp then
      tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.triple_replicate (I := $inv) ?_ ?_ ?_))
    else if isListFoldlMHead comp then
      tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.triple_list_foldlM (I := $inv) ?_ ?_ ?_))
    else if isListMapMHead comp then
      tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.triple_list_mapM (I := $inv) ?_ ?_ ?_))
    else
      return false

/-- Find the local hypotheses that work as explicit bind cuts. -/
def findHoareCutHintCandidates : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some comp := tripleGoalComp? target | return #[]
    let comp ← whnfReducible (← instantiateMVars comp)
    unless isBindExpr comp do return #[]
    let mut found : Array Name := #[]
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        let name := localDecl.userName
        if isUsableBinderName name then
          let type ← instantiateMVars localDecl.type
          unless type.isSort do
            let saved ← saveState
            let ok ← runHoareStepRuleUsing (mkIdent name)
            saved.restore
            if ok then
              found := found.push name
    return found

/-- Find the unique local hypothesis that works as an explicit bind cut.
Returns `none` if there are 0 or ≥ 2 viable candidates. -/
def findUniqueHoareCutHint? : TacticM (Option Name) := do
  let found ← findHoareCutHintCandidates
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none

/-- Find the local hypotheses that work as explicit loop invariants. -/
def findLoopInvHintCandidates : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some comp := tripleGoalComp? target | return #[]
    let comp ← whnfReducible (← instantiateMVars comp)
    unless isReplicateHead comp || isListFoldlMHead comp || isListMapMHead comp do
      return #[]
    let mut found : Array Name := #[]
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        let name := localDecl.userName
        if isUsableBinderName name then
          let type ← instantiateMVars localDecl.type
          unless type.isSort do
            let saved ← saveState
            let ok ← runLoopInvExplicit (mkIdent name)
            saved.restore
            if ok then
              found := found.push name
    return found

/-- Find the unique local hypothesis that works as an explicit loop invariant.
Returns `none` if there are 0 or ≥ 2 viable candidates. -/
def findUniqueLoopInvHint? : TacticM (Option Name) := do
  let found ← findLoopInvHintCandidates
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none

private def potentialLocalHintNames : TacticM (Array Name) := withMainContext do
  let mut names : Array Name := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let name := localDecl.userName
      if isUsableBinderName name then
        let type ← instantiateMVars localDecl.type
        unless type.isSort do
          names := names.push name
  return names

private def unaryGoalKindAndComp? (target : Expr) : Option (VCSpecKind × Expr) :=
  match tripleGoalComp? target with
  | some comp => some (.unaryTriple, comp)
  | none =>
      match wpGoalComp? target with
      | some comp => some (.unaryWP, comp)
      | none => none

private def takeCandidatePrefix (entries : Array VCSpecEntry) : Array VCSpecEntry :=
  (entries.toList.take 8).toArray

private def registeredVCGenRuleCandidateTiers : TacticM (Array (Array VCSpecEntry)) := do
  let target ← instantiateMVars (← getMainTarget)
  let some (kind, comp) := unaryGoalKindAndComp? target | return #[]
  let goalPattern := classifyUnaryCompPattern comp
  let direct :=
    (← getRegisteredUnaryVCSpecEntries comp).filter (·.kind == kind)
  let fallbackAll :=
    (← getVCSpecEntriesOfKind kind).filter fun entry =>
      !(direct.any fun directEntry => directEntry.theoremName! == entry.theoremName!)
  let fallbackPreferred := fallbackAll.filter (·.spec.compPattern == goalPattern)
  let fallbackFallback := fallbackAll.filter (·.spec.compPattern != goalPattern)
  let mut tiers : Array (Array VCSpecEntry) := #[]
  for tier in #[direct, fallbackPreferred, fallbackFallback] do
    let tier := takeCandidatePrefix tier
    unless tier.isEmpty do
      tiers := tiers.push tier
  return tiers

/-- Find the registered unary `@[vcspec]` entries whose bounded application
makes progress on the current goal. Prefers direct discrimination-tree hits on
the goal's `comp`, falling back to kind-matched entries filtered by structural
compatibility. -/
def findRegisteredVCGenRuleCandidates : TacticM (Array VCSpecEntry) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredVCGenRuleCandidateTiers do
      let mut found : Array VCSpecEntry := #[]
      for entry in tier do
        let saved ← saveState
        let ok ← runUnaryVCSpecRule entry
        saved.restore
        if ok then
          found := found.push entry
      unless found.isEmpty do
        return found
    return #[]

/-- Find the first registered unary `@[vcspec]` entry whose bounded
application makes progress. -/
def findRegisteredVCGenRule? : TacticM (Option VCSpecEntry) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredVCGenRuleCandidateTiers do
      for entry in tier do
        let saved ← saveState
        let ok ← runUnaryVCSpecRule entry
        saved.restore
        if ok then
          return some entry
    return none

/-- Try registered `@[vcspec]` rules against a raw `wp` goal.

This is intentionally direct-hit only: raw `wp` stepping is on the hot path, so
we use the discrimination tree and avoid same-kind fallback scans. -/
private def runRawWpVCSpecBackward : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some comp := wpGoalComp? target | return false
    let comp ← whnfReducible (← instantiateMVars comp)
    let entries :=
      takeCandidatePrefix <| (← getRegisteredUnaryVCSpecEntries comp).filter fun entry =>
        entry.kind == .unaryWP || entry.kind == .unaryTriple
    for entry in entries do
      if ← runUnaryVCSpecRule entry then
        return true
    return false

def throwVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | none =>
      if hasProbGoal target then
        if isProbEqGoal target then
          throwError
            "vcstep: found a `Pr[ ...] = Pr[ ...]` goal but no swap or congruence rule applied.\n\
            Goal:{indentExpr target}\n\
            Try `vcstep rw`, `vcstep rw under 1`, `vcstep rw congr`, \
            `vcstep rw congr'`, `vcstep?`, or manual rewriting with \
            `probEvent_bind_bind_swap`."
        else
          throwError
            "vcstep: found a probability goal but could not lower it to a supported\n\
            `Triple` or raw `wp` shape.\n\
            Goal:{indentExpr target}\n\
            Supported direct lowerings include `Pr[ ...] = 1`, `Pr[ ...] = Pr[ ...]`,\n\
            and lower bounds such as `r ≤ Pr[ ...]` / `Pr[ ...] ≥ r`.\n\
            Try `rw [probEvent_eq_wp_propInd]`, `vcstep?`, or manual rewriting."
      else if let some comp := wpGoalComp? target then
        let comp ← whnfReducible (← instantiateMVars comp)
        let theoremMsg ← do
          let tiers ← registeredVCGenRuleCandidateTiers
          let thms := tiers.foldl (init := #[]) fun acc tier =>
            acc ++ tier.map (·.theoremName!)
          pure <| if thms.isEmpty then "" else
            s!"\nRegistered `@[vcspec]` candidates: {formatCandidateNames thms}"
        throwError
          "vcstep: currently in raw `wp` continuation mode, but no matching rule applied to:\n\
          {indentExpr comp}\n\
          Try `vcstep?`, `vcstep`, or manual rewriting.{theoremMsg}"
      else
        throwError
          "vcstep: expected a `Triple`, raw `wp`, or probability goal; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      let cutMsg ←
        if isBindExpr comp then
          let cuts ← potentialLocalHintNames
          pure <| if cuts.isEmpty then "" else
            s!"\nPotential local cut candidates: {formatCandidateNames cuts}"
        else
          pure ""
      let invMsg ←
        if isReplicateHead comp || isListFoldlMHead comp || isListMapMHead comp then
          let invs ← potentialLocalHintNames
          pure <| if invs.isEmpty then "" else
            s!"\nPotential local invariant candidates: {formatCandidateNames invs}"
        else
          pure ""
      let theoremMsg ← do
        let tiers ← registeredVCGenRuleCandidateTiers
        let thms := tiers.foldl (init := #[]) fun acc tier =>
          acc ++ tier.map (·.theoremName!)
        pure <| if thms.isEmpty then "" else
          s!"\nRegistered `@[vcspec]` candidates: {formatCandidateNames thms}"
      throwError
        "vcstep: found a `Triple` goal, but no matching rule applied to:{indentExpr comp}\n\
        Try `vcstep`, or manually unfolding the remaining arithmetic side conditions.\
        {cutMsg}{invMsg}{theoremMsg}"

/-- Try to close or rewrite a `Pr[ ...] = Pr[ ...]` goal by swapping adjacent independent binds.
Handles 0–2 layers of tsum peeling. -/
inductive ProbEqAction where
  | swap
  | congr
  | congrNoSupport
  | rewrite
  | rewriteUnder (depth : Nat)

private def normalizeProbEqGoal : TacticM Unit := do
  discard <| tryEvalTacticSyntax (← `(tactic|
    simp only [map_eq_bind_pure_comp, bind_assoc]))

def runProbEqSwap : TacticM Bool := do
  normalizeProbEqGoal
  tryEvalTacticSyntax (← `(tactic| (
    try simp only [bind_assoc]
    first
      | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
         exact probEvent_bind_bind_swap _ _ _ _)
      | (rw [show Pr[ _ | _ >>= fun a => _ >>= fun b => _] =
              Pr[ _ | _ >>= fun b => _ >>= fun a => _] from
            probEvent_bind_bind_swap _ _ _ _])
      | (conv in (Pr[ _ | _]) =>
          rw [show Pr[ _ | _ >>= fun a => _ >>= fun b => _] =
                Pr[ _ | _ >>= fun b => _ >>= fun a => _] from
              probEvent_bind_bind_swap _ _ _ _])
      | (rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         try simp only [bind_assoc]
         first
           | exact probEvent_bind_bind_swap _ _ _ _
           | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
              exact probEvent_bind_bind_swap _ _ _ _))
      | (rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         try simp only [bind_assoc]
         first
           | exact probEvent_bind_bind_swap _ _ _ _
           | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
              exact probEvent_bind_bind_swap _ _ _ _)))))

def runProbEqCongrNoSupportWithNames (names : Array Name) : TacticM Bool := do
  normalizeProbEqGoal
  if ← tryEvalTacticSyntax (← `(tactic| apply probOutput_bind_congr')) then
    discard <| introMainGoalNames names
    return true
  if ← tryEvalTacticSyntax (← `(tactic| apply probEvent_bind_congr')) then
    discard <| introMainGoalNames names
    return true
  return false

def runProbEqCongrNoSupport : TacticM Bool := do
  let names ← getProbCongrNames false
  runProbEqCongrNoSupportWithNames names

/-- Try to decompose a `Pr[ ... | mx >>= f₁] = Pr[ ... | mx >>= f₂]` goal by congruence,
then auto-intro the bound variable and support hypothesis. -/
def runProbEqCongrWithNames (names : Array Name) : TacticM Bool := do
  normalizeProbEqGoal
  if ← tryEvalTacticSyntax (← `(tactic| apply probOutput_bind_congr)) then
    discard <| introMainGoalNames names
    return true
  if ← tryEvalTacticSyntax (← `(tactic| apply probEvent_bind_congr)) then
    discard <| introMainGoalNames names
    return true
  return false

def runProbEqCongr : TacticM Bool := do
  let names ← getProbCongrNames true
  if ← runProbEqCongrWithNames names then
    return true
  runProbEqCongrNoSupport

private def chunkNameArray
    (names : Array Name) (width : Nat) : Option (Array (Array Name)) := Id.run do
  if width = 0 || names.isEmpty then
    return none
  if names.size % width != 0 then
    return none
  let mut chunks : Array (Array Name) := #[]
  let mut i := 0
  while i < names.size do
    chunks := chunks.push (names.extract i (i + width))
    i := i + width
  return some chunks

def runProbEqCongrChainWithNames
    (supportSensitive : Bool) (names : Array Name) : TacticM Bool := do
  let width := if supportSensitive then 2 else 1
  let some chunks := chunkNameArray names width | return false
  let saved ← saveState
  for chunk in chunks do
    let ok ←
      if supportSensitive then
        runProbEqCongrWithNames chunk
      else
        runProbEqCongrNoSupportWithNames chunk
    if !ok then
      saved.restore
      return false
  return true

/-- Build a theorem that swaps adjacent binds under `depth` shared prefixes. -/
partial def mkProbSwapUnderProof (depth : Nat) : TacticM (TSyntax `term) := do
  match depth with
  | 0 => `(term| probEvent_bind_bind_swap _ _ _ _)
  | depth + 1 =>
      let inner ← mkProbSwapUnderProof depth
      `(term| probEvent_bind_congr fun _ _ => $inner)

/-- Try to rewrite one top-level bind-swap without closing the goal. -/
def runProbEqRewrite : TacticM Bool := do
  normalizeProbEqGoal
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         rw [probEvent_bind_bind_swap]
         try simp only [probEvent_eq_eq_probOutput])
      | rw [probEvent_bind_bind_swap])))

/-- Try to rewrite one bind-swap under `depth` shared prefixes on either side. -/
def runProbEqRewriteUnder (depth : Nat) : TacticM Bool := do
  normalizeProbEqGoal
  let proof ← mkProbSwapUnderProof depth
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         first
           | (conv_lhs => rw [show _ from $proof])
           | (conv_rhs => rw [show _ from $proof])
         try simp only [probEvent_eq_eq_probOutput])
      | first
          | (conv_lhs => rw [show _ from $proof])
          | (conv_rhs => rw [show _ from $proof]))))

def runProbEqAction : ProbEqAction → TacticM Bool
  | .swap => runProbEqSwap
  | .congr => runProbEqCongr
  | .congrNoSupport => runProbEqCongrNoSupport
  | .rewrite => runProbEqRewrite
  | .rewriteUnder depth =>
      if depth = 0 then
        runProbEqRewrite
      else
        runProbEqRewriteUnder depth

private def renderProbEqAction : ProbEqAction → TacticM String
  | .swap => pure "vcstep"
  | .congr => do
      let names ← getProbCongrNames true
      pure s!"vcstep rw congr{renderAsClause names}"
  | .congrNoSupport => do
      let names ← getProbCongrNames false
      pure s!"vcstep rw congr'{renderAsClause names}"
  | .rewrite => pure "vcstep rw"
  | .rewriteUnder depth => pure s!"vcstep rw under {depth}"

private def renderProbEqPlan (actions : List ProbEqAction) : TacticM String := do
  let parts ← actions.mapM renderProbEqAction
  match parts with
  | [] => pure "vcstep"
  | [part] => pure part
  | _ => pure s!"({String.intercalate "; " parts})"

/-- Try a small backtracking-free sequence of probability-equality steps. -/
def tryProbEqActions (steps : List ProbEqAction) : TacticM Bool := do
  let saved ← saveState
  for step in steps do
    if (← getGoals).isEmpty then
      return true
    if !(← runProbEqAction step) then
      saved.restore
      return false
  return true

private def chooseBestProbEqPlan? (plans : List (List ProbEqAction)) :
    TacticM (Option (List ProbEqAction × PreviewResult)) := do
  withVCGenProbPlannerTiming do
    let mut best? : Option (List ProbEqAction × PreviewResult) := none
    for plan in plans do
      let preview ← previewActionWithGoals (tryProbEqActions plan)
      if preview.ok then
        if preview.goalCount = 0 then
          return some (plan, preview)
        match best? with
        | none => best? := some (plan, preview)
        | some (_, bestPreview) =>
            if preview.goalCount < bestPreview.goalCount then
              best? := some (plan, preview)
    return best?

private def mkRewriteChain (depth : Nat) : List ProbEqAction :=
  ((List.range depth).reverse.map fun idx => ProbEqAction.rewriteUnder (idx + 1)) ++
    [ProbEqAction.rewrite]

private def probEqCongrPlans (maxDepth : Nat) : List (List ProbEqAction) :=
  let layers := (List.range maxDepth).map fun idx =>
    let depth := idx + 1
    [List.replicate depth ProbEqAction.congr,
      List.replicate depth ProbEqAction.congrNoSupport]
  layers.foldr List.append []

private def probEqRewritePlans (maxDepth : Nat) : List (List ProbEqAction) :=
  let layers := ((List.range (maxDepth + 1)).reverse.map fun depth =>
    let chain := mkRewriteChain depth
    [chain ++ [ProbEqAction.congr], chain ++ [ProbEqAction.congrNoSupport], chain])
  layers.foldr List.append []

def probEqActionPlans : List (List ProbEqAction) :=
  [ [.swap]
  , [.congr]
  , [.congrNoSupport]
  , [.rewrite, .congr]
  , [.rewrite, .congrNoSupport]
  , [.congr, .swap]
  , [.congrNoSupport, .swap]
  , [.rewriteUnder 1, .rewrite, .congr]
  , [.rewriteUnder 1, .rewrite, .congrNoSupport]
  , [.rewriteUnder 1, .rewrite]
  , [.rewriteUnder 2, .rewriteUnder 1, .rewrite, .congr]
  , [.rewriteUnder 2, .rewriteUnder 1, .rewrite, .congrNoSupport]
  , [.rewriteUnder 2, .rewriteUnder 1, .rewrite]
  ]

private def probEqPlannerActionPlans : List (List ProbEqAction) :=
  probEqRewritePlans 4 ++ probEqCongrPlans 3 ++
    [ [.congr]
    , [.congrNoSupport]
    , [.congr, .swap]
    , [.congrNoSupport, .swap]
    , [.swap]
    ]

private def probExprComp? (expr : Expr) : Option Expr := do
  let app ←
    match findAppWithHead? ``probOutput expr with
    | some app => some app
    | none => findAppWithHead? ``probEvent expr
  let args ← trailingArgs? app 2
  let #[comp, _] := args | none
  some comp

private partial def topBindDepth (expr : Expr) : Nat :=
  let expr := expr.consumeMData
  if isBindExpr expr then
    let args := expr.getAppArgs
    if h : 0 < args.size then
      let k := args[args.size - 1]
      match k.consumeMData with
      | .lam _ _ body _ => topBindDepth body + 1
      | _ => 1
    else
      1
  else
    0

private def probEqBindDepth? (target : Expr) : Option Nat := do
  let target := target.consumeMData
  guard <| target.isAppOfArity ``Eq 3
  let lhsComp ← probExprComp? (target.getArg! 1)
  let rhsComp ← probExprComp? (target.getArg! 2)
  some (Nat.min (topBindDepth lhsComp) (topBindDepth rhsComp))

private def probEqPlannerActionPlansForDepth (bindDepth : Nat) : List (List ProbEqAction) :=
  let maxRewriteDepth := Nat.min 4 (bindDepth - 2)
  let maxCongrDepth := Nat.min 3 bindDepth
  probEqRewritePlans maxRewriteDepth ++ probEqCongrPlans maxCongrDepth ++
    [ [.congr]
    , [.congrNoSupport]
    , [.congr, .swap]
    , [.congrNoSupport, .swap]
    , [.swap]
    ]

private def probEqPlannerActionPlansForGoal : TacticM (List (List ProbEqAction)) := do
  let target ← instantiateMVars (← getMainTarget)
  match probEqBindDepth? target with
  | some depth => return probEqPlannerActionPlansForDepth depth
  | none => return probEqPlannerActionPlans

def tryProbEqPlans (plans : List (List ProbEqAction)) : TacticM Bool := do
  match ← chooseBestProbEqPlan? plans with
  | none => return false
  | some (plan, _) => tryProbEqActions plan

/-- Try to handle a `Pr[ ...] = Pr[ ...]` equality goal by swap, congr, or swap+congr.
Also tries a fallback bridge from exact `probOutput` equalities into relational VCGen. -/
def runProbOutputEqRelBridge : TacticM Bool := do
  let saved ← saveState
  let tryBridge (symmFirst : Bool) : TacticM Bool := do
    match ← observing? do
      if symmFirst then
        evalTactic (← `(tactic| symm))
      evalTactic (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.probOutput_eq_of_relTriple_eqRel))
    with
    | some _ => return true
    | none => return false
  if ← tryBridge false then
    return true
  saved.restore
  if ← tryBridge true then
    return true
  saved.restore
  return false

/-- Try to handle a `Pr[ ...] = Pr[ ...]` equality goal by swap, congr, or swap+congr. -/
def tryProbEqGoal : TacticM Bool := do
  if ← tryProbEqPlans probEqActionPlans then
    return true
  runProbOutputEqRelBridge

def throwVCGenStepRwError (depth : Nat) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if depth = 0 then
    throwError
      "vcstep rw: expected a `Pr[ ...] = Pr[ ...]` goal where one top-level\n\
      bind-swap rewrite applies.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "vcstep rw under {depth}: expected a `Pr[ ...] = Pr[ ...]` goal where one\n\
      bind-swap rewrite applies under {depth} shared bind prefix(es).\n\
      Goal:{indentExpr target}"

def throwVCGenStepRwCongrError (supportSensitive : Bool) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if supportSensitive then
    throwError
      "vcstep rw congr: expected a `Pr[ ...] = Pr[ ...]` goal with a shared outer\n\
      bind, leaving the bound variable and a support hypothesis.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "vcstep rw congr': expected a `Pr[ ...] = Pr[ ...]` goal with a shared outer\n\
      bind, leaving only the bound variable.\n\
      Goal:{indentExpr target}"

/-- Try to lower a probability goal into a `Triple`, `wp`, or probability-equality goal. -/
def tryLowerProbGoal : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let isProbEventGoal := (findAppWithHead? ``probEvent target).isSome
  let isProbOutputGoal := (findAppWithHead? ``probOutput target).isSome
  unless isProbEventGoal || isProbOutputGoal do return false
  if isProbEqGoal target then
    if ← tryProbEqGoal then return true
  if isProbEventGoal then
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [← OracleComp.ProgramLogic.triple_propInd_iff_probEvent_eq_one];
        simp only [OracleComp.ProgramLogic.propInd_true])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [eq_comm (a := 1),
            ← OracleComp.ProgramLogic.triple_propInd_iff_probEvent_eq_one];
        simp only [OracleComp.ProgramLogic.propInd_true])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [← OracleComp.ProgramLogic.triple_propInd_iff_le_probEvent])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [ge_iff_le, ← OracleComp.ProgramLogic.triple_propInd_iff_le_probEvent])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.probEvent_eq_wp_propInd])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        simp only [OracleComp.ProgramLogic.probEvent_eq_wp_propInd])) then
      return true
  if isProbOutputGoal then
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.probOutput_eq_one_iff_triple])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [eq_comm, OracleComp.ProgramLogic.probOutput_eq_one_iff_triple])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.le_probOutput_iff_triple_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [ge_iff_le, OracleComp.ProgramLogic.le_probOutput_iff_triple_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        simp only [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])) then
      return true
  return false

/-- Continue structural stepping on a raw `wp` goal after probability lowering or explicit
`wp`-level work. This stays deliberately smaller than the `Triple` path. -/
def tryRawWpStructuralStep : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some comp := wpGoalComp? target | return false
  let comp ← whnfReducible (← instantiateMVars comp)
  if ← runRawWpVCSpecBackward then
    return true
  if ← runWpStepRules then
    return true
  if ← tryMatchDecomp comp then
    return true
  return false

/-- Try to synthesize a support-based intermediate postcondition for a bind step.
When the computation is `oa >>= f` and no explicit spec is available, tries applying
`triple_bind` with an inferred cut and closing the spec subgoal via `triple_support`,
which unifies the cut to `fun x => 𝟙⟦x ∈ support oa⟧`. -/
def trySupportCutBind (comp : Expr) : TacticM Bool := do
  if !isBindExpr comp then return false
  match ← observing? do
    evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_bind))
    unless ← tryEvalTacticSyntax (← `(tactic|
      classical exact OracleComp.ProgramLogic.triple_support _)) do
      throwError "" with
  | some _ => return true
  | none => return false

/-- Structural/default unary VCGen step, excluding explicit cut/invariant/theorem-driven
fallbacks and the final close/search phase. -/
def runVCGenStructuralCore : TacticM Bool := withVCGenStructuralTiming do
  if (← getGoals).isEmpty then return false
  discard <| normalizeStdDoTripleGoal
  let target ← instantiateMVars (← getMainTarget)
  if ← tryLowerProbGoal then
    if (← getGoals).isEmpty then
      return true
    let target ← instantiateMVars (← getMainTarget)
    if (tripleGoalComp? target |>.isNone) && (relTripleGoalParts? target |>.isNone) &&
        (wpGoalComp? target).isSome then
      if ← tryRawWpStructuralStep then
        return true
    return true
  if relTripleGoalParts? target |>.isSome then
    return (← TacticInternals.Relational.runRVCGenStep)
  match tripleGoalComp? target with
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      if isBindExpr comp then
        if ← tryBindImmediate comp then
          return true
        if ← trySupportCutBind comp then
          return true
        if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_bind_wp)) then
          return true
      if isIfExpr comp then
        if comp.consumeMData.getAppFn.isConstOf ``dite then
          if ← tryEvalTacticSyntax (← `(tactic|
            apply OracleComp.ProgramLogic.triple_dite <;> intro)) then
            return true
        if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_ite <;> intro)) then
          return true
      if ← tryMatchDecomp comp then
        return true
      if ← tryLoopInvariantRuleAuto comp then
        return true
      if ← tryLoopFallback comp then
        return true
      match ← (observing? do
        evalTactic (← `(tactic| unfold OracleComp.ProgramLogic.Triple))
        evalTactic (← `(tactic| change _ ≤ OracleComp.ProgramLogic.wp _ _))
        unless ← runWpStepRules do
          throwError "vcstep: no matching wp rule after unfolding `Triple`") with
      | some _ => return true
      | none => return false
  | none => return (← tryRawWpStructuralStep)

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
  if ← runVCGenStructuralCore then
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
