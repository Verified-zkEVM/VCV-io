/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

private def tryCloseRelGoalImmediate : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure
    assumption))

private def tryCloseLeadingRelGoalImmediate : TacticM Unit := do
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

private def reorderRelBindGoals : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | first :: second :: rest =>
      setGoals ([second, first] ++ rest)
  | _ => pure ()

private def tryLowerRelGoal : TacticM Bool := withMainContext do
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

private def runRelBindRule : TacticM Bool := do
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

private def runRelBindRuleUsing (R : TSyntax `term) : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_)) then
    reorderRelBindGoals
    tryCloseLeadingRelGoalImmediate
    return true
  return false

private def runRelMapRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_map))

private def runRelReplicateRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate))

private def runRelMapMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))

private def runRelMapMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := $R) ?_ ?_))

private def runRelFoldlMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same))

private def runRelFoldlMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
      (Rin := $R) ?_ ?_ ?_))

private def runRelRndRuleUsing (f : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f) <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f) <;> [skip; skip]))

private def runRelRndRuleWithContextBijection : TacticM Bool := withMainContext do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if let some app := findAppWithHead? ``Function.Bijective type then
        if let some args := trailingArgs? app 1 then
          let fStx ← PrettyPrinter.delab args[0]!
          if ← runRelRndRuleUsing fStx then
            return true
  return false

private def runRelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_query _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  runRelRndRuleWithContextBijection <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij <;> [skip; skip]))

private def runRelCondRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_if <;> [intro _; intro _])) <||>
  tryEvalTacticSyntax (← `(tactic|
    (simp only [game_rule]
     apply OracleComp.ProgramLogic.Relational.relTriple_if <;> [intro _; intro _])))

private def runByUptoRule (bad : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
      (bad := $bad)))

private def runRelSimRule : TacticM Bool := withMainContext do
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

private def runRelSimRuleUsing (R : TSyntax `term) : TacticM Bool := withMainContext do
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

private def runRelSimDistRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, post) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) || !isEqRelPost post then
        return false
      tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_impl_evalDist_eq))
  | none => return false

private def runRVCGenCore : TacticM Bool := withMainContext do
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

private def runRVCGenCoreUsing (hint : TSyntax `term) : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | none => return false
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob && !(hasStateTRun'Expr oa && hasStateTRun'Expr ob && isEqRelPost post) then
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

/-- One step of relational VCGen.

Strategy:
1. Lower `GameEquiv` / `evalDist = evalDist` goals into `RelTriple`
2. `∀`-binder: `intro` and continue
3. Close trivial `RelTriple` leaves (`refl`, `pure`, assumptions)
4. Synchronized control flow (`if`)
5. Oracle simulation (`simulateQ`) with exact-distribution specialization when obvious
6. Structural traversals (`map`, `replicate`, `List.mapM`, `List.foldlM`)
7. Monadic bind decomposition with auto-intro of continuation binders
8. Random/query coupling as the fallback structural rule -/
private def runRVCGenStep : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    if ← tryEvalTacticSyntax (← `(tactic| intro _)) then
      progress := true
  if ← runRVCGenCore then
    return true
  return progress

private def runRVCGenStepUsing (hint : TSyntax `term) : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    if ← tryEvalTacticSyntax (← `(tactic| intro _)) then
      progress := true
  if ← runRVCGenCoreUsing hint then
    return true
  return progress

private def runRVCGenPass : TacticM Bool := do
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

private def throwRVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rvcgen_step: failed to lower the `GameEquiv` goal into relational proof mode."
  if isEvalDistEqGoal target then
    throwError "rvcgen_step: failed to lower the `evalDist` equality into a `RelTriple` goal."
  match relTripleGoalParts? target with
  | none =>
      throwError
        "rvcgen_step: expected a `GameEquiv`, `evalDist` equality, or `RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        throwError
          "rvcgen_step: found a `simulateQ` relational goal but no simulation rule applied.\n\
          If the proof needs a state invariant, try `rvcgen_step using R_state`.\n\
          If the goal is an output-only `run'` equality coupling, `rvcgen_step` also tries the \
          exact-distribution specialization automatically.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListMapMExpr oa || isListMapMExpr ob then
        throwError
          "rvcgen_step: found a `List.mapM` relational goal but no traversal rule applied.\n\
          Use `rvcgen_step using Rin` when the two input lists are related by a non-equality relation.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        throwError
          "rvcgen_step: found a `List.foldlM` relational goal but no fold rule applied.\n\
          Use `rvcgen_step using Rin` when the two input lists are related by a non-equality relation.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isReplicateExpr oa || isReplicateExpr ob then
        throwError
          "rvcgen_step: found a `replicate` relational goal but no iteration rule applied.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isBindExpr oa && isBindExpr ob then
        throwError
          "rvcgen_step: found a bind-on-both-sides relational goal but could not choose an intermediate relation.\n\
          Try `rvcgen_step using R` when equality is not the right cut relation.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      throwError
        "rvcgen_step: found a `RelTriple` goal, but no relational VCGen rule matched.\n\
        Left side:{indentExpr oa}\n\
        Right side:{indentExpr ob}\n\
        Postcondition:{indentExpr post}\n\
        Consider `rel_conseq`, `rel_inline`, or `rel_dist` for a non-structural step."

private def throwRVCGenStepUsingError (hint : TSyntax `term) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  throwError
    "rvcgen_step using {hint}: the explicit hint did not match the current relational goal shape.\n\
    `using` is interpreted by goal shape as one of:\n\
    - bind cut relation\n\
    - random/query bijection\n\
    - `List.mapM` / `List.foldlM` input relation\n\
    - `simulateQ` state relation\n\
    Goal:{indentExpr target}"

/-- `rvcgen_step` applies one relational VCGen step.

It first lowers `GameEquiv` / `evalDist` equality goals into relational mode, then
tries the obvious structural relational rule: synchronized conditionals, `simulateQ`,
`Functor.map`, bounded traversals, bind decomposition, or random/query coupling.

`rvcgen_step using t` supplies the explicit witness needed for the current shape:
- bind cut relation
- random/query bijection
- traversal input relation (`List.mapM` / `List.foldlM`)
- `simulateQ` state relation -/
syntax "rvcgen_step" ("using" term)? : tactic

elab_rules : tactic
  | `(tactic| rvcgen_step) => do
      if ← runRVCGenStep then
        return
      throwRVCGenStepError
  | `(tactic| rvcgen_step using $hint) => do
      if ← runRVCGenStepUsing hint then
        return
      throwRVCGenStepUsingError hint

/-- `rvcgen` repeatedly applies relational VCGen steps across all current goals until stuck.

`rvcgen using t` uses the explicit hint `t` for the first step on the main goal, then
continues with ordinary hint-free relational VCGen on all remaining goals. -/
syntax "rvcgen" ("using" term)? : tactic

private def runRVCGenFinish : TacticM Unit := do
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

elab_rules : tactic
  | `(tactic| rvcgen) => do
      while (← runRVCGenPass) do pure ()
      runRVCGenFinish
  | `(tactic| rvcgen using $hint) => do
      if ← runRVCGenStepUsing hint then
        while (← runRVCGenPass) do pure ()
        runRVCGenFinish
      else
        throwRVCGenStepUsingError hint

/-- `rel_conseq` weakens or strengthens the postcondition of a `RelTriple` goal.

Given a goal `RelTriple oa ob R'`, applies `relTriple_post_mono` to produce:
1. `RelTriple oa ob ?R` — the triple with a (possibly easier) postcondition
2. `∀ x y, ?R x y → R' x y` — the implication between postconditions

Use `rel_conseq with R` to specify the intermediate postcondition explicitly. -/
syntax "rel_conseq" ("with" term)? : tactic

macro_rules
  | `(tactic| rel_conseq) =>
    `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_post_mono)
  | `(tactic| rel_conseq with $R) =>
    `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_post_mono (R := $R) ?_ ?_)

/-- `rel_inline` unfolds definitions and then tries to close or simplify the relational goal.
Use `rel_inline foo bar` to unfold specific definitions, or just `rel_inline` to simplify. -/
macro "rel_inline" ids:ident* : tactic =>
  if ids.size > 0 then
    `(tactic|
      (unfold $ids*
       try simp only [game_rule]
       try first
         | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
         | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
         | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
         | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)))
  else
    `(tactic|
      (simp only [game_rule]
       try first
         | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
         | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
         | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
         | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)))

/-! ## Proof mode entry tactics -/

/-- `by_equiv` transforms a `GameEquiv g₁ g₂` goal into `RelTriple g₁ g₂ (EqRel α)`.
Also works for `evalDist g₁ = evalDist g₂` goals.
Always targets `RelTriple` (coupling-based), never `RelTriple'` (eRHL-based),
so that `rvcgen_step` / `rvcgen` work on the resulting goal. -/
macro "by_equiv" : tactic =>
  `(tactic|
    first
      | apply OracleComp.ProgramLogic.GameEquiv.of_relTriple
      | (change OracleComp.ProgramLogic.Relational.RelTriple _ _ _)
      | (apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel))

/-- `rel_dist` reduces a `RelTriple oa ob (EqRel α)` goal to `evalDist oa = evalDist ob`.

This is the reverse direction of `by_equiv`: while `by_equiv` enters relational mode from a
distributional equality, `rel_dist` exits relational mode back to distributional reasoning.

Useful when both sides are equal in distribution but not syntactically identical, and the
equality is easier to prove at the `evalDist` level than via stepwise coupling. -/
macro "rel_dist" : tactic =>
  `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq)

/-- `game_trans` introduces an intermediate game for transitivity of `GameEquiv`.

Given a goal `g₁ ≡ₚ g₃`, `game_trans g₂` produces two subgoals:
1. `g₁ ≡ₚ g₂`
2. `g₂ ≡ₚ g₃`

This is the fundamental tactic for multi-step game-hopping chains. -/
syntax "game_trans" term : tactic

macro_rules
  | `(tactic| game_trans $g) =>
    `(tactic|
      refine OracleComp.ProgramLogic.GameEquiv.trans (g₂ := $g) ?_ ?_)

/-- `by_dist` transforms a TV distance or advantage bound goal into a subgoal
suitable for relational or coupling reasoning. -/
syntax "by_dist" (term)? : tactic

macro_rules
  | `(tactic| by_dist) =>
    `(tactic|
      apply OracleComp.ProgramLogic.AdvBound.of_tvDist)
  | `(tactic| by_dist $eps) =>
    `(tactic|
      (apply OracleComp.ProgramLogic.AdvBound.of_tvDist (ε₂ := $eps)))

/-- `by_upto bad` applies the "identical until bad" TV-distance theorem for `simulateQ`.
It leaves the standard four subgoals: initial non-bad state, agreement off bad,
and bad-state monotonicity for each implementation. -/
syntax "by_upto" term : tactic

elab_rules : tactic
  | `(tactic| by_upto $bad) => do
      if ← runByUptoRule bad then
        return
      let target ← instantiateMVars (← getMainTarget)
      throwError
        "by_upto: expected a TV-distance goal for two `simulateQ ... run'` computations bounded by\n\
        the probability of a bad event on the left simulation; got:{indentExpr target}"

end OracleComp.ProgramLogic
