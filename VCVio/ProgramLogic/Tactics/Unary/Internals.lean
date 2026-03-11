/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common
import VCVio.ProgramLogic.Tactics.Relational

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

def throwWpStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match wpGoalComp? target with
  | none =>
      throwError "wp_step: expected a goal containing `wp`; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      throwError
        "wp_step: found a `wp` goal, but none of the current single-step rules apply to:{indentExpr comp}\n\
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

def throwQVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | none =>
      let hasProbGoal := (findAppWithHead? ``probEvent target).isSome ||
                         (findAppWithHead? ``probOutput target).isSome
      if hasProbGoal then
        if isProbEqGoal target then
          throwError
            "qvcgen_step: found a `Pr[...] = Pr[...]` goal but no swap or congruence rule applied.\n\
            Goal:{indentExpr target}\n\
            Try `qvcgen_step rw`, `qvcgen_step rw under 1`, `qvcgen_step rw congr`, \
            `qvcgen_step rw congr'`, or manual rewriting with `probEvent_bind_bind_swap`."
        else
          throwError
            "qvcgen_step: found a probability goal but could not lower it to a `Triple` or `wp` goal.\n\
            Goal:{indentExpr target}\n\
            Try `rw [probEvent_eq_wp_propInd]`, or manual rewriting."
      else
        throwError "qvcgen_step: expected a `Triple` or probability goal; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      throwError
        "qvcgen_step: found a `Triple` goal, but no matching rule applied to:{indentExpr comp}\n\
        Try `wp_step`, or manually unfolding the remaining arithmetic side conditions."

/-- Try to close the current goal using only immediate local information.
This is intentionally cheap: it is used while speculating on `triple_bind`, so it must not
launch expensive proof search on goals with unresolved cut metavariables. -/
def tryCloseSpecGoalImmediate : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic| solve_by_elim (maxDepth := 2))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_pure _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_zero _ _)) <||>
  tryEvalTacticSyntax (← `(tactic| exact le_refl _))

/-- Try bounded local proof search on a closed goal.
We only invoke `solve_by_elim` once the target has no unresolved expression metavariables; this
avoids pathological search on speculative intermediate cuts introduced by `triple_bind`. -/
def tryCloseSpecGoalSearch : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasExprMVar then
    return false
  tryEvalTacticSyntax (← `(tactic| (
    repeat intro
    simp only [OracleComp.ProgramLogic.Triple] at *
    solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans]
  )))

/-- Try opt-in registry lookup for a unary `Triple` goal.
The lookup is deliberately narrow: we only index by the computation head symbol and only try a
small bounded set of `@[vcgen]` lemmas. -/
def tryCloseSpecGoalRegistered : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some comp := tripleGoalComp? target | return false
  let candidates := (← getRegisteredVCGenTheorems comp).toList.take 8
  let rec go : List Name → TacticM Bool
    | [] => return false
    | thm :: rest => do
        let saved ← saveState
        let ok ←
          tryEvalTacticSyntax (← `(tactic| (
            apply $(mkIdent thm):ident
            all_goals first
              | assumption
              | (
                  repeat intro
                  simp only [OracleComp.ProgramLogic.Triple] at *
                  solve_by_elim (maxDepth := 4) [OracleComp.ProgramLogic.wp_mono, le_trans]
                )
          )))
        if ok && (← getGoals).isEmpty then
          return true
        saved.restore
        go rest
  go candidates

/-- Try to close the current goal (typically a `Triple` subgoal) using direct hypotheses,
canonical leaf rules, or bounded local consequence search. -/
def tryCloseSpecGoal : TacticM Bool := do
  tryCloseSpecGoalImmediate <||> tryCloseSpecGoalRegistered <||> tryCloseSpecGoalSearch

/-- Finish-only closure step: includes the support-sensitive leaf rules that are too expensive
for the default `qvcgen_step` hot path. -/
def tryCloseSpecGoalFinal : TacticM Bool := do
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
  tryCloseSpecGoalRegistered <||> tryCloseSpecGoalSearch

/-- Run one bounded finish/closure pass across all current goals. -/
def runVCGenClosePass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← tryCloseSpecGoalFinal then
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
  | .lam _ _ body _ => !body.hasLooseBVars
  | _ => false

/-- Try to apply a loop invariant or stepping rule for loops. -/
def tryLoopInvariantAuto (comp : Expr) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some app := findAppWithHead? ``OracleComp.ProgramLogic.Triple target | return false
  let some args := trailingArgs? app 3 | return false
  let post := args[2]!
  if isReplicateHead comp then
    if isConstantLambda post then
      match ← observing? do
        evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_replicate_inv))
        unless ← tryCloseSpecGoalImmediate do throwError "" with
      | some _ => return true
      | none => pure ()
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_replicate_succ)) then
      return true
  if isListFoldlMHead comp then
    match ← observing? do
      evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_list_foldlM_inv))
      unless ← tryCloseSpecGoalImmediate do throwError "" with
    | some _ => return true
    | none =>
      if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_list_foldlM_cons)) then
        return true
  if isListMapMHead comp then
    if isConstantLambda post then
      match ← observing? do
        evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_list_mapM_inv))
        unless ← tryCloseSpecGoalImmediate do throwError "" with
      | some _ => return true
      | none => pure ()
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

/-- Try to close or rewrite a `Pr[...] = Pr[...]` goal by swapping adjacent independent binds.
Handles 0–2 layers of tsum peeling. -/
inductive ProbEqAction where
  | swap
  | congr
  | congrNoSupport
  | congrAny
  | rewrite
  | rewriteUnder (depth : Nat)

def runProbEqSwap : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| (
    try simp only [bind_assoc]
    first
      | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
         exact probEvent_bind_bind_swap _ _ _ _)
      | (rw [show Pr[_ | _ >>= fun a => _ >>= fun b => _] =
              Pr[_ | _ >>= fun b => _ >>= fun a => _] from
            probEvent_bind_bind_swap _ _ _ _])
      | (conv in (Pr[_ | _]) =>
          rw [show Pr[_ | _ >>= fun a => _ >>= fun b => _] =
                Pr[_ | _ >>= fun b => _ >>= fun a => _] from
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

/-- Try to decompose a `Pr[... | mx >>= f₁] = Pr[... | mx >>= f₂]` goal by congruence,
then auto-intro the bound variable and support hypothesis. -/
def runProbEqCongrWithNames (names : Array Name) : TacticM Bool := do
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

/-- Build a theorem that swaps adjacent binds under `depth` shared prefixes. -/
partial def mkProbSwapUnderProof (depth : Nat) : TacticM (TSyntax `term) := do
  match depth with
  | 0 => `(term| probEvent_bind_bind_swap _ _ _ _)
  | depth + 1 =>
      let inner ← mkProbSwapUnderProof depth
      `(term| probEvent_bind_congr fun _ _ => $inner)

/-- Try to rewrite one top-level bind-swap without closing the goal. -/
def runProbEqRewrite : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         rw [probEvent_bind_bind_swap]
         try simp only [probEvent_eq_eq_probOutput])
      | rw [probEvent_bind_bind_swap])))

/-- Try to rewrite one bind-swap under `depth` shared prefixes on either side. -/
def runProbEqRewriteUnder (depth : Nat) : TacticM Bool := do
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
  | .congrAny => runProbEqCongr
  | .rewrite => runProbEqRewrite
  | .rewriteUnder depth =>
      if depth = 0 then
        runProbEqRewrite
      else
        runProbEqRewriteUnder depth

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

/-- Try to handle a `Pr[...] = Pr[...]` equality goal by swap, congr, or swap+congr.
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

/-- Try to handle a `Pr[...] = Pr[...]` equality goal by swap, congr, or swap+congr. -/
def tryProbEqGoal : TacticM Bool := do
  if ← tryProbEqActions [.swap] then return true
  if ← tryProbEqActions [.congrAny] then return true
  if ← tryProbEqActions [.rewrite, .congrAny] then return true
  if ← tryProbEqActions [.congrAny, .swap] then return true
  if ← tryProbEqActions [.rewriteUnder 1, .rewrite, .congrAny] then
    return true
  runProbOutputEqRelBridge

def throwQVCGenStepRwError (depth : Nat) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if depth = 0 then
    throwError
      "qvcgen_step rw: expected a `Pr[...] = Pr[...]` goal where one top-level bind-swap rewrite applies.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "qvcgen_step rw under {depth}: expected a `Pr[...] = Pr[...]` goal where one bind-swap rewrite applies under {depth} shared bind prefix(es).\n\
      Goal:{indentExpr target}"

def throwQVCGenStepRwCongrError (supportSensitive : Bool) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if supportSensitive then
    throwError
      "qvcgen_step rw congr: expected a `Pr[...] = Pr[...]` goal with a shared outer bind, leaving the bound variable and a support hypothesis.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "qvcgen_step rw congr': expected a `Pr[...] = Pr[...]` goal with a shared outer bind, leaving only the bound variable.\n\
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
        rw [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        simp only [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])) then
      return true
  return false

/-- One step of VCGen on a `Triple` goal. Returns `true` if any progress was made. -/
def runVCGenStep : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let target ← instantiateMVars (← getMainTarget)
  if ← tryLowerProbGoal then
    return true
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    if ← introMainGoalNames names then
      return true
  if relTripleGoalParts? target |>.isSome then
    return (← tryEvalTacticSyntax (← `(tactic| rvcgen_step)))
  match tripleGoalComp? target with
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      if isBindExpr comp then
        match ← observing? do
          evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_bind))
          unless ← tryCloseSpecGoalImmediate do throwError "" with
        | some _ => return true
        | none =>
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
      if ← tryLoopInvariantAuto comp then
        return true
      match ← (observing? do
        evalTactic (← `(tactic| unfold OracleComp.ProgramLogic.Triple))
        evalTactic (← `(tactic| change _ ≤ OracleComp.ProgramLogic.wp _ _))
        unless ← runWpStepRules do
          throwError "qvcgen_step: no matching wp rule after unfolding `Triple`") with
      | some _ => return true
      | none => tryCloseSpecGoal
  | none => tryCloseSpecGoal

/-- Run one VCGen pass across all current goals. -/
def runVCGenPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← runVCGenStep then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress

end Unary
end TacticInternals
end OracleComp.ProgramLogic
