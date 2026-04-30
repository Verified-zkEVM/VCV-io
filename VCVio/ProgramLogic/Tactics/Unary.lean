/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Unary.Internals

/-!
# Unary VC Tactics

User-facing unary VCGen tactics and finish passes.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-! ## Unary VC tactics -/

private def binderIdentsToNames (ids : Syntax.TSepArray `Lean.binderIdent ",") : Array Name :=
  ids.getElems.map fun
    | `(binderIdent| $name:ident) => name.getId
    | _ => Name.anonymous

private def runVCGenFinish : TacticM Unit := do
  unless (← getGoals).isEmpty do
    -- Only `wp_*`, `propInd_*`, and `game_rule` are kept here; generic ring/if normalization
    -- (`one_mul`, `zero_add`, `ite_true`, `if_false`, `dite_true`, …) is already in Mathlib's
    -- default simp-set and was rarely firing on the Triple/wp-shaped goals that reach this
    -- finish pass — building those extra simp entries on every `vcgen` invocation was a
    -- constant tax without an observed win.
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [
        OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_bind,
        OracleComp.ProgramLogic.wp_query, OracleComp.ProgramLogic.wp_ite,
        OracleComp.ProgramLogic.wp_dite, OracleComp.ProgramLogic.wp_map,
        OracleComp.ProgramLogic.wp_uniformSample,
        OracleComp.ProgramLogic.wp_const,
        OracleComp.ProgramLogic.propInd_true, OracleComp.ProgramLogic.propInd_false,
        OracleComp.ProgramLogic.propInd_eq_ite,
        game_rule]))
  unless (← getGoals).isEmpty do
    discard <| tryEvalTacticSyntax
      (← `(tactic| all_goals try
        (refine Std.Do'.Triple.iff.mpr ?_
         repeat intro _
         simp [Lean.Order.PartialOrder.rel,
           MonadStateOf.get, MonadStateOf.set, MonadReaderOf.read, MonadWriter.tell,
           StateT.get, StateT.set, StateT.lift, ReaderT.read,
           StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set,
           StateT.run_lift, StateT.run_map,
           ReaderT.run_bind, ReaderT.run_pure, ReaderT.run_monadLift, ReaderT.run_read,
           ReaderT.run_map,
           Std.Do'.WriterT.apply_wp,
           OracleComp.ProgramLogic.Loom.WriterT.wp_bind,
           OracleComp.ProgramLogic.Loom.WriterT.wp_pure,
           OracleComp.ProgramLogic.Loom.WriterT.wp_tell,
           OracleComp.ProgramLogic.Loom.WriterT.wp_monadLift,
           OracleComp.ProgramLogic.Loom.WriterT.wp_map,
           WriterT.run_bind, WriterT.run_pure, WriterT.run_tell, WriterT.run_map,
           MAlgOrdered.wp_bind, MAlgOrdered.wp_pure, MAlgOrdered.wp_map,
           OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp,
           OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp_epost,
           MonadLift.monadLift, pure_bind, bind_assoc, map_pure, Functor.map_map,
           one_mul, mul_one, mul_assoc]
         try exact le_rfl)))
  unless (← getGoals).isEmpty do
    discard <| tryEvalTacticSyntax
      (← `(tactic| all_goals try
        (simp_rw [← mul_assoc]
         dsimp [StateT.set, ReaderT.run, WriterT.run]
         simp [
           StateT.set, StateT.run_set, StateT.run_pure, StateT.run_monadLift,
           TacticInternals.Unary.wp_StateT_run_set_layer,
           TacticInternals.Unary.wp_StateT_run_set_layer',
           ReaderT.run, ReaderT.run_read, ReaderT.run_pure, ReaderT.run_monadLift,
           TacticInternals.Unary.wp_ReaderT_run_read_layer,
           TacticInternals.Unary.wp_ReaderT_run_read_layer',
           Std.Do'.WriterT.apply_wp,
           OracleComp.ProgramLogic.Loom.WriterT.wp_tell,
           OracleComp.ProgramLogic.Loom.WriterT.wp_monadLift,
           WriterT.run_tell, WriterT.run_pure, WriterT.run_monadLift, WriterT.run_map,
           OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp,
           OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp_epost,
           MAlgOrdered.wp_bind, MAlgOrdered.wp_pure, MAlgOrdered.wp_map,
           MonadLift.monadLift, pure_bind, bind_assoc, map_pure, Functor.map_map,
           one_mul, mul_one, mul_assoc]
         try exact le_rfl)))
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "vcgen finish" TacticInternals.Unary.runVCGenClosePass
  unless (← getGoals).isEmpty do
    discard <| tryEvalTacticSyntax
      (← `(tactic| all_goals try
        (simp_rw [← mul_assoc]
         dsimp [StateT.set, ReaderT.run, WriterT.run]
         simp [
           StateT.set, StateT.run_set, StateT.run_pure, StateT.run_monadLift,
           TacticInternals.Unary.wp_StateT_run_set_layer,
           TacticInternals.Unary.wp_StateT_run_set_layer',
           ReaderT.run, ReaderT.run_read, ReaderT.run_pure, ReaderT.run_monadLift,
           TacticInternals.Unary.wp_ReaderT_run_read_layer,
           TacticInternals.Unary.wp_ReaderT_run_read_layer',
           Std.Do'.WriterT.apply_wp,
           OracleComp.ProgramLogic.Loom.WriterT.wp_tell,
           OracleComp.ProgramLogic.Loom.WriterT.wp_monadLift,
           WriterT.run_tell, WriterT.run_pure, WriterT.run_monadLift, WriterT.run_map,
           OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp,
           OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp_epost,
           MAlgOrdered.wp_bind, MAlgOrdered.wp_pure, MAlgOrdered.wp_map,
           MonadLift.monadLift, pure_bind, bind_assoc, map_pure, Functor.map_map,
           one_mul, mul_one, mul_assoc]
         try exact le_rfl)))

private def runVCGenStepWithNames (names : Array Name) : TacticM Bool := do
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

private def runVCGenStepWithTheoremNames
    (thm : TSyntax `term) (names : Array Name) : TacticM Bool := do
  if ← TacticInternals.Unary.runVCGenStepWithTheorem thm then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

private def logPlannerNotes (steps : Array PlannedStep) : TacticM Unit := do
  let mut emitted : Array String := #[]
  for step in steps do
    for note in step.notes do
      unless note = "continuing in raw `wp` mode" do
        continue
      unless emitted.contains note do
        emitted := emitted.push note
        logInfo m!"Planner note: {note}"

/-- `vcstep` applies one quantitative VCGen step to a `Triple`, raw `wp`, or probability goal.

For `Triple` goals: decomposes a bind via `triple_bind` and automatically tries to close
the spec subgoal using hypotheses in the local context, with backward WP fallback.
Also handles `ite`/`dite` splitting, `match` case analysis, loop invariant auto-detection
from context, and WP-rule unfolding, including `simulateQ ... run'`.
After the built-in leaf rules, it may also use user-authored `@[vcspec]` lemmas whose
registered head symbol matches the current computation.

For `Pr[ ...] = 1` and lower-bound goals such as `r ≤ Pr[ p | oa]`: automatically lowers the
goal into a `Triple` form.

For `Pr[ ...] = Pr[ ...]` goals: tries bind-swap (`probEvent_bind_bind_swap`), bind
congruence (`probOutput_bind_congr` / `probEvent_bind_congr`), swap-then-congr,
or an exact-`probOutput` bridge into relational VCGen.
Handles up to 2 layers of tsum peeling for nested swaps.

For other general `Pr[ ...]` goals: rewrites to raw `wp` form and keeps stepping structurally
when a `wp` rule applies, rather than immediately exiting the VCGen pipeline.

Variants:
- `vcstep using cut` for an explicit intermediate postcondition.
- `vcstep with thm` to force a specific unary theorem/assumption step.
- `vcstep inv I` to apply a loop invariant `I` to a `replicate`/`foldlM`/`mapM` goal.
- `vcstep rw` to perform one explicit top-level probability-equality rewrite step.
- `vcstep rw under n` to rewrite one bind-swap under `n` shared bind prefixes.
- `vcstep rw normalize` to run the bounded probability-equality planner explicitly.
- `vcstep rw congr` to expose one shared bind plus its support hypothesis.
- `vcstep rw congr'` to expose one shared bind without a support hypothesis.

Use `@[vcspec]` on unary `Triple` or raw `wp` theorems to opt them into bounded lookup. -/
syntax "vcstep" ("using" term)? : tactic
syntax "vcstep" "with" term : tactic
syntax "vcstep" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "vcstep" "using" term "as" "⟨" binderIdent,* "⟩" : tactic
syntax "vcstep" "with" term "as" "⟨" binderIdent,* "⟩" : tactic
syntax "vcstep?" : tactic

elab_rules : tactic
  | `(tactic| vcstep as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runVCGenStepWithNames names then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcstep using $cut as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcstep with $thm as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runVCGenStepWithTheoremNames thm names then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcstep) => do
      if ← TacticInternals.Unary.runVCGenStep then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcstep using $cut) => do
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcstep with $thm) => do
      if ← TacticInternals.Unary.runVCGenStepWithTheorem thm then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcstep?) => do
      let some step ← TacticInternals.Unary.runVCGenPlannedStep?
        | TacticInternals.Unary.throwVCGenStepError
      addTryThisTextSuggestion (← getRef) step.replayText
      logPlannerNotes #[step]

syntax "vcstep" &"rw" : tactic
syntax "vcstep" &"rw" " under " num : tactic
syntax "vcstep" &"rw" &"normalize" : tactic
syntax "vcstep" &"rw" &"congr" : tactic
syntax "vcstep" &"rw" &"congr'" : tactic
syntax "vcstep" &"rw" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "vcstep" &"rw" " under " num "as" "⟨" binderIdent,* "⟩" : tactic
syntax "vcstep" &"rw" &"congr" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "vcstep" &"rw" &"congr'" "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| vcstep rw as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction .rewrite then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwVCGenStepRwError 0
  | `(tactic| vcstep rw under $n:num as ⟨ $ids,* ⟩) => do
      let depth := n.getNat
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwVCGenStepRwError depth
  | `(tactic| vcstep rw congr as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrChainWithNames true names then return
      TacticInternals.Unary.throwVCGenStepRwCongrError true
  | `(tactic| vcstep rw congr' as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrChainWithNames false names then return
      TacticInternals.Unary.throwVCGenStepRwCongrError false
  | `(tactic| vcstep rw) => do
      if ← TacticInternals.Unary.runProbEqAction .rewrite then return
      TacticInternals.Unary.throwVCGenStepRwError 0
  | `(tactic| vcstep rw under $n:num) => do
      let depth := n.getNat
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then return
      TacticInternals.Unary.throwVCGenStepRwError depth
  | `(tactic| vcstep rw normalize) => do
      if ← TacticInternals.Unary.runProbEqNormalize then return
      TacticInternals.Unary.throwVCGenStepRwNormalizeError
  | `(tactic| vcstep rw congr) => do
      if ← TacticInternals.Unary.runProbEqAction .congr then return
      TacticInternals.Unary.throwVCGenStepRwCongrError true
  | `(tactic| vcstep rw congr') => do
      if ← TacticInternals.Unary.runProbEqAction .congrNoSupport then return
      TacticInternals.Unary.throwVCGenStepRwCongrError false

syntax "vcstep" &"inv" term : tactic
syntax "vcstep" &"inv" term "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| vcstep inv $inv as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runLoopInvExplicit inv then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      throwError
        "vcstep inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
        or `List.mapM`."
  | `(tactic| vcstep inv $inv) => do
      if ← TacticInternals.Unary.runLoopInvExplicit inv then return
      throwError
        "vcstep inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
        or `List.mapM`."

/-- `vcgen` exhaustively decomposes a `Triple`, raw `wp`, or probability goal
with spec-aware stepping.

Accepts `Triple` goals, raw `wp` goals, lower-bound / exact probability goals, and
`Pr[ ...] = Pr[ ...]` equality goals. Probability goals are automatically lowered or
dispatched (swap/congr) before structural decomposition continues.

Enhancements over simple structural decomposition:
- Lowers `Pr[ ...]` goals into `Triple` or raw `wp` form before decomposition
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
call `vcgen` to automatically decompose and apply them.

Variants:
- `vcgen using cut` performs one explicit bind step with intermediate postcondition `cut`,
  then continues with exhaustive decomposition on all resulting goals.
- `vcgen inv I` applies an explicit loop invariant `I` to the first `replicate`/`foldlM`/`mapM`
  goal, then continues with exhaustive decomposition. -/
syntax "vcgen" ("using" term)? : tactic
syntax "vcgen" &"inv" term : tactic
syntax "vcgen?" : tactic

elab_rules : tactic
  | `(tactic| vcgen) => withVCGenRunTiming "vcgen" do
      discard <| runBoundedPasses "vcgen" TacticInternals.Unary.runVCGenPass
      withVCGenFinishTiming runVCGenFinish
  | `(tactic| vcgen using $cut) => withVCGenRunTiming "vcgen" do
      discard <| TacticInternals.Unary.tryLowerProbGoal
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then
        discard <| runBoundedPasses "vcgen" TacticInternals.Unary.runVCGenPass
        withVCGenFinishTiming runVCGenFinish
      else
        TacticInternals.Unary.throwVCGenStepError
  | `(tactic| vcgen inv $inv) => withVCGenRunTiming "vcgen" do
      discard <| TacticInternals.Unary.tryLowerProbGoal
      if ← TacticInternals.Unary.runLoopInvExplicit inv then
        discard <| runBoundedPasses "vcgen" TacticInternals.Unary.runVCGenPass
        withVCGenFinishTiming runVCGenFinish
      else
        throwError
          "vcgen inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
          or `List.mapM`."
  | `(tactic| vcgen?) => withVCGenRunTiming "vcgen?" do
      let batches ← runBoundedPassesCollect "vcgen?" TacticInternals.Unary.runVCGenPassPlanned
      let needsFinish := !(← getGoals).isEmpty
      withVCGenFinishTiming runVCGenFinish
      for batch in batches do
        logPlannerNotes batch
      let mut lines : List String :=
        batches.toList.filterMap renderPassReplayLine
      if needsFinish then
        lines := lines ++ [
          String.intercalate "" [
            "all_goals try simp only [OracleComp.ProgramLogic.wp_pure, ",
            "OracleComp.ProgramLogic.wp_bind, OracleComp.ProgramLogic.wp_query, ",
            "OracleComp.ProgramLogic.wp_ite, OracleComp.ProgramLogic.wp_dite, ",
            "OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_uniformSample, ",
            "OracleComp.ProgramLogic.wp_const, OracleComp.ProgramLogic.propInd_true, ",
            "OracleComp.ProgramLogic.propInd_false, OracleComp.ProgramLogic.propInd_eq_ite, ",
            "ite_true, ite_false, if_true, if_false, dite_true, dite_false, ",
            "one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, game_rule]",
          ],
          String.intercalate "" [
            "all_goals first | assumption | exact OracleComp.ProgramLogic.triple_pure _ _ | ",
            "exact OracleComp.ProgramLogic.triple_zero _ _ | ",
            "(classical exact OracleComp.ProgramLogic.triple_support _) | ",
            "(exact OracleComp.ProgramLogic.triple_propInd_of_support _ _ (by assumption)) | ",
            "(exact OracleComp.ProgramLogic.triple_probEvent_eq_one _ _ (by assumption)) | ",
            "(exact OracleComp.ProgramLogic.triple_probOutput_eq_one _ _ (by assumption)) | ",
            "exact le_refl _ | (repeat intro; simp only [OracleComp.ProgramLogic.Triple] at *; ",
            "solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans])",
          ]
        ]
      if lines.isEmpty then
        lines := ["vcgen"]
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
