/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Unary.Internals

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-! ## Unary WP tactics -/

/-- `wp_step` applies exactly one WP decomposition rule and stops.
This gives step-by-step control for raw `wp` goals (`_ ≤ wp _ _`). -/
elab "wp_step" : tactic => do
  if ← runWpStepRules then
    return
  TacticInternals.Unary.throwWpStepError

/-! ## Quantitative VCGen: spec-aware stepping for `Triple` goals -/

private def binderIdentsToNames (ids : Syntax.TSepArray `Lean.binderIdent ",") : Array Name :=
  ids.getElems.map fun
    | `(binderIdent| $name:ident) => name.getId
    | _ => Name.anonymous

private def runQVCGenFinish : TacticM Unit := do
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
    discard <| runBoundedPasses "qvcgen finish" TacticInternals.Unary.runVCGenClosePass

private def runQVCGenStepWithNames (names : Array Name) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    return (← introMainGoalNames names)
  if isProbEqGoal target then
    if names.size ≥ 2 then
      if ← TacticInternals.Unary.runProbEqCongrWithNames names then
        return true
    if names.size = 1 then
      if ← TacticInternals.Unary.runProbEqCongrNoSupportWithNames names then
        return true
  if ← TacticInternals.Unary.runVCGenStep then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

private def runQVCGenStepWithTheoremNames
    (thm : TSyntax `term) (names : Array Name) : TacticM Bool := do
  if ← TacticInternals.Unary.runVCGenStepWithTheorem thm then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

/-- `qvcgen_step` applies one quantitative VCGen step to a `Triple` or probability goal.

For `Triple` goals: decomposes a bind via `triple_bind` and automatically tries to close
the spec subgoal using hypotheses in the local context, with backward WP fallback.
Also handles `ite`/`dite` splitting, `match` case analysis, loop invariant auto-detection
from context, and WP-rule unfolding, including `simulateQ ... run'`.
After the built-in leaf rules, it may also use user-authored `@[vcgen]` lemmas whose
registered head symbol matches the current computation.

For `Pr[...] = 1` goals: automatically lowers the goal into a `Triple` form.

For `Pr[...] = Pr[...]` goals: tries bind-swap (`probEvent_bind_bind_swap`), bind
congruence (`probOutput_bind_congr` / `probEvent_bind_congr`), swap-then-congr,
or an exact-`probOutput` bridge into relational VCGen.
Handles up to 2 layers of tsum peeling for nested swaps.

Variants:
- `qvcgen_step using cut` for an explicit intermediate postcondition.
- `qvcgen_step with thm` to force a specific unary theorem/assumption step.
- `qvcgen_step inv I` to apply a loop invariant `I` to a `replicate`/`foldlM`/`mapM` goal.
- `qvcgen_step rw` to perform one explicit top-level probability-equality rewrite step.
- `qvcgen_step rw under n` to rewrite one bind-swap under `n` shared bind prefixes.
- `qvcgen_step rw congr` to expose one shared bind plus its support hypothesis.
- `qvcgen_step rw congr'` to expose one shared bind without a support hypothesis.

Use `@[vcgen]` on unary `Triple` theorems to opt them into the bounded head-symbol lookup. -/
syntax "qvcgen_step" ("using" term)? : tactic
syntax "qvcgen_step" "with" term : tactic
syntax "qvcgen_step" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "qvcgen_step" "using" term "as" "⟨" binderIdent,* "⟩" : tactic
syntax "qvcgen_step" "with" term "as" "⟨" binderIdent,* "⟩" : tactic
syntax "qvcgen_step?" : tactic

elab_rules : tactic
  | `(tactic| qvcgen_step as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runQVCGenStepWithNames names then return
      TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen_step using $cut as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen_step with $thm as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runQVCGenStepWithTheoremNames thm names then return
      TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen_step) => do
      if ← TacticInternals.Unary.runVCGenStep then return
      TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen_step using $cut) => do
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then return
      TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen_step with $thm) => do
      if ← TacticInternals.Unary.runVCGenStepWithTheorem thm then return
      TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen_step?) => do
      let some step ← TacticInternals.Unary.runVCGenPlannedStep?
        | TacticInternals.Unary.throwQVCGenStepError
      addTryThisTextSuggestion (← getRef) step.replayText

syntax "qvcgen_step" &"rw" : tactic
syntax "qvcgen_step" &"rw" " under " num : tactic
syntax "qvcgen_step" &"rw" &"congr" : tactic
syntax "qvcgen_step" &"rw" &"congr'" : tactic
syntax "qvcgen_step" &"rw" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "qvcgen_step" &"rw" " under " num "as" "⟨" binderIdent,* "⟩" : tactic
syntax "qvcgen_step" &"rw" &"congr" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "qvcgen_step" &"rw" &"congr'" "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| qvcgen_step rw as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction .rewrite then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwQVCGenStepRwError 0
  | `(tactic| qvcgen_step rw under $n:num as ⟨ $ids,* ⟩) => do
      let depth := n.getNat
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwQVCGenStepRwError depth
  | `(tactic| qvcgen_step rw congr as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrWithNames names then return
      TacticInternals.Unary.throwQVCGenStepRwCongrError true
  | `(tactic| qvcgen_step rw congr' as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrNoSupportWithNames names then return
      TacticInternals.Unary.throwQVCGenStepRwCongrError false
  | `(tactic| qvcgen_step rw) => do
      if ← TacticInternals.Unary.runProbEqAction .rewrite then return
      TacticInternals.Unary.throwQVCGenStepRwError 0
  | `(tactic| qvcgen_step rw under $n:num) => do
      let depth := n.getNat
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then return
      TacticInternals.Unary.throwQVCGenStepRwError depth
  | `(tactic| qvcgen_step rw congr) => do
      if ← TacticInternals.Unary.runProbEqAction .congr then return
      TacticInternals.Unary.throwQVCGenStepRwCongrError true
  | `(tactic| qvcgen_step rw congr') => do
      if ← TacticInternals.Unary.runProbEqAction .congrNoSupport then return
      TacticInternals.Unary.throwQVCGenStepRwCongrError false

syntax "qvcgen_step" &"inv" term : tactic
syntax "qvcgen_step" &"inv" term "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| qvcgen_step inv $inv as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runLoopInvExplicit inv then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      throwError
        "qvcgen_step inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
        or `List.mapM`."
  | `(tactic| qvcgen_step inv $inv) => do
      if ← TacticInternals.Unary.runLoopInvExplicit inv then return
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
call `qvcgen` to automatically decompose and apply them.

Variants:
- `qvcgen using cut` performs one explicit bind step with intermediate postcondition `cut`,
  then continues with exhaustive decomposition on all resulting goals.
- `qvcgen inv I` applies an explicit loop invariant `I` to the first `replicate`/`foldlM`/`mapM`
  goal, then continues with exhaustive decomposition. -/
syntax "qvcgen" ("using" term)? : tactic
syntax "qvcgen" &"inv" term : tactic
syntax "qvcgen?" : tactic

elab_rules : tactic
  | `(tactic| qvcgen) => do
      discard <| runBoundedPasses "qvcgen" TacticInternals.Unary.runVCGenPass
      runQVCGenFinish
  | `(tactic| qvcgen using $cut) => do
      discard <| TacticInternals.Unary.tryLowerProbGoal
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then
        discard <| runBoundedPasses "qvcgen" TacticInternals.Unary.runVCGenPass
        runQVCGenFinish
      else
        TacticInternals.Unary.throwQVCGenStepError
  | `(tactic| qvcgen inv $inv) => do
      discard <| TacticInternals.Unary.tryLowerProbGoal
      if ← TacticInternals.Unary.runLoopInvExplicit inv then
        discard <| runBoundedPasses "qvcgen" TacticInternals.Unary.runVCGenPass
        runQVCGenFinish
      else
        throwError
          "qvcgen inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
          or `List.mapM`."
  | `(tactic| qvcgen?) => do
      let batches ← runBoundedPassesCollect "qvcgen?" TacticInternals.Unary.runVCGenPassPlanned
      let needsFinish := !(← getGoals).isEmpty
      runQVCGenFinish
      let mut lines : List String :=
        batches.toList.filterMap renderPassReplayLine
      if needsFinish then
        lines := lines ++ [
          "all_goals try simp only [OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_bind, OracleComp.ProgramLogic.wp_query, OracleComp.ProgramLogic.wp_ite, OracleComp.ProgramLogic.wp_dite, OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_uniformSample, OracleComp.ProgramLogic.wp_const, OracleComp.ProgramLogic.propInd_true, OracleComp.ProgramLogic.propInd_false, OracleComp.ProgramLogic.propInd_eq_ite, ite_true, ite_false, if_true, if_false, dite_true, dite_false, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, game_rule]",
          "all_goals first | assumption | exact OracleComp.ProgramLogic.triple_pure _ _ | exact OracleComp.ProgramLogic.triple_zero _ _ | (classical exact OracleComp.ProgramLogic.triple_support _) | (exact OracleComp.ProgramLogic.triple_propInd_of_support _ _ (by assumption)) | (exact OracleComp.ProgramLogic.triple_probEvent_eq_one _ _ (by assumption)) | (exact OracleComp.ProgramLogic.triple_probOutput_eq_one _ _ (by assumption)) | exact le_refl _ | (repeat intro; simp only [OracleComp.ProgramLogic.Triple] at *; solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans])"
        ]
      if lines.isEmpty then
        lines := ["qvcgen"]
      addTryThisTextSuggestion (← getRef) <| String.intercalate "\n" lines

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
