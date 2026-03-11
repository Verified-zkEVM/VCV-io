/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common
import VCVio.ProgramLogic.Tactics.Relational

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

private def throwWpStepError : TacticM Unit := withMainContext do
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

private def runHoareStepRuleUsing (cut : TSyntax `term) : TacticM Bool := do
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

private def throwQVCGenStepError : TacticM Unit := withMainContext do
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

/-! ## Unary WP tactics -/

/-- `wp_step` applies exactly one WP decomposition rule and stops.
This gives step-by-step control for raw `wp` goals (`_ ≤ wp _ _`). -/
elab "wp_step" : tactic => do
  if ← runWpStepRules then
    return
  throwWpStepError

/-! ## Quantitative VCGen: spec-aware stepping for `Triple` goals -/

/-- Try to close the current goal using only immediate local information.
This is intentionally cheap: it is used while speculating on `triple_bind`, so it must not
launch expensive proof search on goals with unresolved cut metavariables. -/
private def tryCloseSpecGoalImmediate : TacticM Bool := do
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
private def tryCloseSpecGoalSearch : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasExprMVar then
    return false
  tryEvalTacticSyntax (← `(tactic| (
    repeat intro
    simp only [OracleComp.ProgramLogic.Triple] at *
    solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans]
  )))

/-- Try to close the current goal (typically a `Triple` subgoal) using direct hypotheses,
canonical leaf rules, or bounded local consequence search. -/
private def tryCloseSpecGoal : TacticM Bool := do
  tryCloseSpecGoalImmediate <||> tryCloseSpecGoalSearch

/-- Try to decompose a `match` expression in the computation by case-splitting
on its discriminant(s). Only fires when the computation is a compiled matcher
(detected via `matchMatcherApp?`). Delegates to `split` which handles the actual
case analysis. -/
private def tryMatchDecomp (comp : Expr) : TacticM Bool := do
  let some _ ← Lean.Meta.matchMatcherApp? comp | return false
  tryEvalTacticSyntax (← `(tactic| split))

/-- Check if an expression is a lambda whose body does not use the bound variable
(i.e. a constant function `fun _ => c`). -/
private def isConstantLambda (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ body _ => !body.hasLooseBVars
  | _ => false

/-- Try to apply a loop invariant or stepping rule for loops.

For **invariant** mode (exact shape match): applies `triple_replicate_inv` etc.
directly if the postcondition is constant and a step-preservation hypothesis
is available.

For **stepping** mode (fallback): applies `triple_replicate_succ` etc. which
rewrites `Triple pre (replicate (n+1) oa) post` into
`Triple pre oa (fun x => wp (replicate n oa) (fun xs => post (x :: xs)))`,
bypassing the expensive WP fallback path. -/
private def tryLoopInvariantAuto (comp : Expr) : TacticM Bool := do
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

/-- Apply a loop invariant rule with an explicitly provided invariant.
Uses the pre-composed `triple_replicate` / `triple_list_foldlM` / `triple_list_mapM`
which include consequence bridging, leaving pre/post/step subgoals. -/
private def runLoopInvExplicit (inv : TSyntax `term) : TacticM Bool := do
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
private inductive ProbEqAction where
  | swap
  | congr
  | congrNoSupport
  | congrAny
  | rewrite
  | rewriteUnder (depth : Nat)

private def runProbEqSwap : TacticM Bool := do
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

private def runProbEqCongrNoSupport : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      apply probOutput_bind_congr'; intro _)) then
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      apply probEvent_bind_congr'; intro _)) then
    return true
  return false

/-- Try to decompose a `Pr[... | mx >>= f₁] = Pr[... | mx >>= f₂]` goal by congruence,
then auto-intro the bound variable and support hypothesis. -/
private def runProbEqCongr : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      apply probOutput_bind_congr; intro _ _)) then
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      apply probEvent_bind_congr; intro _ _)) then
    return true
  runProbEqCongrNoSupport

/-- Build a theorem that swaps adjacent binds under `depth` shared prefixes. -/
private partial def mkProbSwapUnderProof (depth : Nat) : TacticM (TSyntax `term) := do
  match depth with
  | 0 => `(term| probEvent_bind_bind_swap _ _ _ _)
  | depth + 1 =>
      let inner ← mkProbSwapUnderProof depth
      `(term| probEvent_bind_congr fun _ _ => $inner)

/-- Try to rewrite one top-level bind-swap without closing the goal. -/
private def runProbEqRewrite : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         rw [probEvent_bind_bind_swap]
         try simp only [probEvent_eq_eq_probOutput])
      | rw [probEvent_bind_bind_swap])))

/-- Try to rewrite one bind-swap under `depth` shared prefixes on either side. -/
private def runProbEqRewriteUnder (depth : Nat) : TacticM Bool := do
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

private def runProbEqAction : ProbEqAction → TacticM Bool
  | .swap => runProbEqSwap
  | .congr => do
      if ← tryEvalTacticSyntax (← `(tactic|
          apply probOutput_bind_congr; intro _ _)) then
        return true
      tryEvalTacticSyntax (← `(tactic|
        apply probEvent_bind_congr; intro _ _))
  | .congrNoSupport => runProbEqCongrNoSupport
  | .congrAny => runProbEqCongr
  | .rewrite => runProbEqRewrite
  | .rewriteUnder depth =>
      if depth = 0 then
        runProbEqRewrite
      else
        runProbEqRewriteUnder depth

/-- Try a small backtracking-free sequence of probability-equality steps. -/
private def tryProbEqActions (steps : List ProbEqAction) : TacticM Bool := do
  let saved ← saveState
  for step in steps do
    if (← getGoals).isEmpty then
      return true
    if !(← runProbEqAction step) then
      saved.restore
      return false
  return true

/-- Try to handle a `Pr[...] = Pr[...]` equality goal by swap, congr, or swap+congr.
Also tries small bounded rewrite sequences such as congr-then-swap and
one-sided under-prefix rewrites. -/
private def runProbOutputEqRelBridge : TacticM Bool := do
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

/-- Try to handle a `Pr[...] = Pr[...]` equality goal by swap, congr, or swap+congr.
Also tries a fallback bridge from exact `probOutput` equalities into relational VCGen. -/
private def tryProbEqGoal : TacticM Bool := do
  if ← tryProbEqActions [.swap] then return true
  if ← tryProbEqActions [.congrAny] then return true
  if ← tryProbEqActions [.rewrite, .congrAny] then return true
  if ← tryProbEqActions [.congrAny, .swap] then return true
  if ← tryProbEqActions [.rewriteUnder 1, .rewrite, .congrAny] then
    return true
  runProbOutputEqRelBridge

private def throwQVCGenStepRwError (depth : Nat) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if depth = 0 then
    throwError
      "qvcgen_step rw: expected a `Pr[...] = Pr[...]` goal where one top-level bind-swap rewrite applies.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "qvcgen_step rw under {depth}: expected a `Pr[...] = Pr[...]` goal where one bind-swap rewrite applies under {depth} shared bind prefix(es).\n\
      Goal:{indentExpr target}"

private def throwQVCGenStepRwCongrError (supportSensitive : Bool) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if supportSensitive then
    throwError
      "qvcgen_step rw congr: expected a `Pr[...] = Pr[...]` goal with a shared outer bind, leaving the bound variable and a support hypothesis.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "qvcgen_step rw congr': expected a `Pr[...] = Pr[...]` goal with a shared outer bind, leaving only the bound variable.\n\
      Goal:{indentExpr target}"

/-- Try to lower a probability goal into a `Triple`, `wp`, or probability-equality goal.

Recognized shapes:
- `Pr[p | oa] = 1` or `1 = Pr[p | oa]` → rewrite to `Triple 1 oa (indicator)`
- `Pr[= x | oa] = 1` or `1 = Pr[= x | oa]` → rewrite to `Triple 1 oa (indicator)`
- `Pr[... | oa] = Pr[... | ob]` → try swap (bind reorder), congr (shared prefix), swap+congr,
  or an exact-`probOutput` bridge into `RelTriple`
- `Pr[p | oa] = ...` or `... = Pr[p | oa]` (general) → rewrite `Pr` to `wp`
- `_ ≤ Pr[p | oa]` or `Pr[p | oa] ≤ _` → rewrite `Pr` to `wp`

Returns `true` if any rewrite fired. -/
private def tryLowerProbGoal : TacticM Bool := do
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

/-- One step of VCGen on a `Triple` goal with the following strategy:

1. **Probability lowering**: rewrite `Pr[...]` goals into `Triple` or `wp` form
2. `∀`-binder: `intro` and continue
3. **Bind** (spec-based): `triple_bind` + close spec subgoal from local context
4. **Bind** (backward WP): `triple_bind_wp` to get `Triple pre oa (fun x => wp (ob x) post)`
5. **Conditional** (`ite`/`dite`): split into branch goals with discriminant hypotheses
6. **Match**: case-split on the discriminant variable
7. **Loop** (auto invariant or step): apply `triple_*_inv` from context or `triple_*_succ`/`_cons`
8. **Leaf**: unfold `Triple` and apply WP rules, or try to close directly

Returns `true` if any progress was made. -/
private def runVCGenStep : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let target ← instantiateMVars (← getMainTarget)
  if ← tryLowerProbGoal then
    return true
  if target.isForall then
    if ← tryEvalTacticSyntax (← `(tactic| intro _)) then
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

/-- Run one VCGen pass across all current goals.

This is stricter than repeatedly stepping only the main goal: after a split, one branch may be
ready only for arithmetic cleanup while another still has program structure to decompose. -/
private def runVCGenPass : TacticM Bool := do
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

/-- `qvcgen_step` applies one quantitative VCGen step to a `Triple` or probability goal.

For `Triple` goals: decomposes a bind via `triple_bind` and automatically tries to close
the spec subgoal using hypotheses in the local context, with backward WP fallback.
Also handles `ite`/`dite` splitting, `match` case analysis, loop invariant auto-detection
from context, and WP-rule unfolding, including `simulateQ ... run'`.

For `Pr[...] = 1` goals: automatically lowers the goal into a `Triple` form.

For `Pr[...] = Pr[...]` goals: tries bind-swap (`probEvent_bind_bind_swap`), bind
congruence (`probOutput_bind_congr` / `probEvent_bind_congr`), swap-then-congr,
or an exact-`probOutput` bridge into relational VCGen.
Handles up to 2 layers of tsum peeling for nested swaps.

Variants:
- `qvcgen_step using cut` for an explicit intermediate postcondition.
- `qvcgen_step inv I` to apply a loop invariant `I` to a `replicate`/`foldlM`/`mapM` goal.
- `qvcgen_step rw` to perform one explicit top-level probability-equality rewrite step.
- `qvcgen_step rw under n` to rewrite one bind-swap under `n` shared bind prefixes.
- `qvcgen_step rw congr` to expose one shared bind plus its support hypothesis.
- `qvcgen_step rw congr'` to expose one shared bind without a support hypothesis. -/
syntax "qvcgen_step" ("using" term)? : tactic

elab_rules : tactic
  | `(tactic| qvcgen_step) => do
      if ← runVCGenStep then return
      throwQVCGenStepError
  | `(tactic| qvcgen_step using $cut) => do
      if ← runHoareStepRuleUsing cut then return
      throwQVCGenStepError

syntax "qvcgen_step" &"rw" : tactic
syntax "qvcgen_step" &"rw" " under " num : tactic
syntax "qvcgen_step" &"rw" &"congr" : tactic
syntax "qvcgen_step" &"rw" &"congr'" : tactic

elab_rules : tactic
  | `(tactic| qvcgen_step rw) => do
      if ← runProbEqAction .rewrite then return
      throwQVCGenStepRwError 0
  | `(tactic| qvcgen_step rw under $n:num) => do
      let depth := n.getNat
      if ← runProbEqAction (.rewriteUnder depth) then return
      throwQVCGenStepRwError depth
  | `(tactic| qvcgen_step rw congr) => do
      if ← runProbEqAction .congr then return
      throwQVCGenStepRwCongrError true
  | `(tactic| qvcgen_step rw congr') => do
      if ← runProbEqAction .congrNoSupport then return
      throwQVCGenStepRwCongrError false

syntax "qvcgen_step" &"inv" term : tactic

elab_rules : tactic
  | `(tactic| qvcgen_step inv $inv) => do
      if ← runLoopInvExplicit inv then return
      throwError
        "qvcgen_step inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
        or `List.mapM`."

/-- `qvcgen` exhaustively decomposes a `Triple` or probability goal with spec-aware stepping.

Accepts `Triple` goals, `Pr[...] = 1` goals, and `Pr[...] = Pr[...]` equality goals.
Probability goals are automatically lowered or dispatched (swap/congr) before structural
decomposition continues.

Enhancements over simple structural decomposition:
- Lowers `Pr[...]` goals into `Triple` or `wp` form before decomposition
- Bridges exact `Pr[= x | oa] = Pr[= x | ob]` goals into relational VCGen when helpful
- After bind decomposition, tries to close spec subgoals from local context
- Falls back to backward WP (`triple_bind_wp`) when no spec is available
- Splits `ite`/`dite` conditionals into branch goals with hypotheses
- Case-splits `match` expressions on their discriminants
- Auto-detects loop invariants from context for `replicate`/`foldlM`/`mapM`
- Keeps decomposing across all open goals after branch splits
- Understands `simulateQ` and `simulateQ ... run'` through the unary WP rules
- Normalizes remaining `wp` terms and indicator arithmetic via simp
- Finishes with bounded local consequence search on closed goals

Typical usage: bring specs into context with `have` or as function parameters, then
call `qvcgen` to automatically decompose and apply them. -/
elab "qvcgen" : tactic => do
  while (← runVCGenPass) do pure ()
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [
        OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_bind,
        OracleComp.ProgramLogic.wp_query, OracleComp.ProgramLogic.wp_ite,
        OracleComp.ProgramLogic.wp_dite, OracleComp.ProgramLogic.wp_map,
        OracleComp.ProgramLogic.wp_uniformSample,
        OracleComp.ProgramLogic.wp_const,
        OracleComp.ProgramLogic.propInd_true, OracleComp.ProgramLogic.propInd_false,
        OracleComp.ProgramLogic.propInd_eq_ite,
        ite_true, ite_false, if_true, if_false, dite_true, dite_false,
        one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero,
        game_rule]))
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals first
        | assumption
        | exact OracleComp.ProgramLogic.triple_pure _ _
        | exact OracleComp.ProgramLogic.triple_zero _ _
        | (classical
           exact OracleComp.ProgramLogic.triple_support _)
        | (exact OracleComp.ProgramLogic.triple_propInd_of_support _ _ (by assumption))
        | (exact OracleComp.ProgramLogic.triple_probEvent_eq_one _ _ (by assumption))
        | (exact OracleComp.ProgramLogic.triple_probOutput_eq_one _ _ (by assumption))
        | exact le_refl _
        | (
            repeat intro
            simp only [OracleComp.ProgramLogic.Triple] at *
            solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans]
          )))

/-- `exp_norm` normalizes expectation / indicator arithmetic in the current goal.

Rewrites using linearity of expectation (`wp_add`, `wp_mul_const`), indicator algebra
(`propInd_true`, `propInd_false`, `propInd_and`), and standard WP step rules. -/
macro "exp_norm" : tactic =>
  `(tactic| simp only [
    OracleComp.ProgramLogic.propInd_true, OracleComp.ProgramLogic.propInd_false,
    OracleComp.ProgramLogic.propInd_and, OracleComp.ProgramLogic.propInd_eq_ite,
    OracleComp.ProgramLogic.propInd_not, OracleComp.ProgramLogic.propInd_le_one,
    OracleComp.ProgramLogic.propInd,
    OracleComp.ProgramLogic.wp_add, OracleComp.ProgramLogic.wp_mul_const,
    OracleComp.ProgramLogic.wp_const, OracleComp.ProgramLogic.wp_eq_tsum,
    OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_bind,
    OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_ite,
    OracleComp.ProgramLogic.wp_dite,
    ite_true, ite_false, if_true, if_false, dite_true, dite_false,
    one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero,
    game_rule])

/-- `by_hoare` transforms a probability goal into a quantitative WP goal. -/
macro "by_hoare" : tactic =>
  `(tactic|
    first
      | rw [OracleComp.ProgramLogic.probEvent_eq_wp_indicator]
      | rw [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])

end OracleComp.ProgramLogic
