/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Relational.Internals

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

private def binderIdentsToNames (ids : Syntax.TSepArray `Lean.binderIdent ",") : Array Name :=
  ids.getElems.map fun
    | `(binderIdent| $name:ident) => name.getId
    | _ => Name.anonymous

private def runRVCGenStepWithNames (names : Array Name) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    return (← introMainGoalNames names)
  if ← TacticInternals.Relational.runRVCGenStep then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

private def runRVCGenStepUsingWithNames (hint : TSyntax `term) (names : Array Name) : TacticM Bool := do
  TacticInternals.Relational.runRVCGenStepUsingWithNames hint names

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
syntax "rvcgen_step" "as" "⟨" binderIdent,* "⟩" : tactic
syntax "rvcgen_step" "using" term "as" "⟨" binderIdent,* "⟩" : tactic
syntax "rvcgen_step?" : tactic

elab_rules : tactic
  | `(tactic| rvcgen_step as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runRVCGenStepWithNames names then
        return
      TacticInternals.Relational.throwRVCGenStepError
  | `(tactic| rvcgen_step using $hint as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runRVCGenStepUsingWithNames hint names then
        return
      TacticInternals.Relational.throwRVCGenStepUsingError hint
  | `(tactic| rvcgen_step) => do
      if ← TacticInternals.Relational.runRVCGenStep then
        return
      TacticInternals.Relational.throwRVCGenStepError
  | `(tactic| rvcgen_step using $hint) => do
      if ← TacticInternals.Relational.runRVCGenStepUsing hint then
        return
      TacticInternals.Relational.throwRVCGenStepUsingError hint
  | `(tactic| rvcgen_step?) => do
      let some step ← TacticInternals.Relational.runRVCGenPlannedStep?
        | TacticInternals.Relational.throwRVCGenStepError
      addTryThisTextSuggestion (← getRef) step.replayText

/-- `rvcgen` repeatedly applies relational VCGen steps across all current goals until stuck.

`rvcgen using t` uses the explicit hint `t` for the first step on the main goal, then
continues with ordinary hint-free relational VCGen on all remaining goals. -/
syntax "rvcgen" ("using" term)? : tactic
syntax "rvcgen?" : tactic

elab_rules : tactic
  | `(tactic| rvcgen) => do
      discard <| runBoundedPasses "rvcgen" TacticInternals.Relational.runRVCGenPass
      TacticInternals.Relational.runRVCGenFinish
  | `(tactic| rvcgen using $hint) => do
      if ← TacticInternals.Relational.runRVCGenStepUsing hint then
        discard <| runBoundedPasses "rvcgen" TacticInternals.Relational.runRVCGenPass
        TacticInternals.Relational.runRVCGenFinish
      else
        TacticInternals.Relational.throwRVCGenStepUsingError hint
  | `(tactic| rvcgen?) => do
      let batches ← runBoundedPassesCollect "rvcgen?" TacticInternals.Relational.runRVCGenPassPlanned
      let needsFinish := !(← getGoals).isEmpty
      TacticInternals.Relational.runRVCGenFinish
      let mut lines : List String :=
        batches.toList.filterMap renderPassReplayLine
      if needsFinish then
        lines := lines ++ [
          "all_goals try simp only [game_rule]",
          "all_goals first | assumption | exact OracleComp.ProgramLogic.Relational.relTriple_refl _ | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)"
        ]
      if lines.isEmpty then
        lines := ["rvcgen"]
      addTryThisTextSuggestion (← getRef) <| String.intercalate "\n" lines

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
      if ← TacticInternals.Relational.runByUptoRule bad then
        return
      let target ← instantiateMVars (← getMainTarget)
      throwError
        "by_upto: expected a TV-distance goal for two `simulateQ ... run'` computations bounded by\n\
        the probability of a bad event on the left simulation; got:{indentExpr target}"

end OracleComp.ProgramLogic
