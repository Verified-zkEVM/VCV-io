/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Quantitative
import VCVio.ProgramLogic.Relational.Loom.Quantitative
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Tactics.Common

/-!
# Relational VCGen Internals

Implementation details for the relational VCGen planner and step selection.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Relational

/-! ### Registered VC-spec rules

Centralized `@[vcspec]` registrations for the relational planner. Lemmas added here become
candidates for the registered-rule branch of `rvcstep`/`rvcgen` (and surface in the
"Registered `@[vcspec]` candidates" hint when the planner gets stuck), in addition to any
structural rule that `runRVCGenCore` already tries by goal shape. -/

attribute [vcspec]
  -- Core relational rules from `Relational/Basic.lean`
  OracleComp.ProgramLogic.Relational.relTriple_pure_pure
  OracleComp.ProgramLogic.Relational.relTriple_bind
  OracleComp.ProgramLogic.Relational.relTriple_map
  OracleComp.ProgramLogic.Relational.relTriple_if
  OracleComp.ProgramLogic.Relational.relTriple_replicate
  OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel
  OracleComp.ProgramLogic.Relational.relTriple_list_mapM
  OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel
  OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
  OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same
  OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij
  OracleComp.ProgramLogic.Relational.relTriple_uniformSample_refl
  -- Quantitative rules from the default `Std.Do'.RelTriple` carrier.
  OracleComp.ProgramLogic.Relational.Loom.relTriple_pure
  OracleComp.ProgramLogic.Relational.Loom.relTriple_bind
  OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_bij
  -- Raw relational WP rule from the Std.Do bridge
  Std.Do'.RelWP.rwp_pure
  -- `simulateQ`-aware rules from `Relational/SimulateQ.lean`
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_query_map_eq

private def mkRVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }

/-- Attempt to close the current relational/eRHL leaf goal with the canonical fast paths.

Tries, in order:
* `assumption` (catches a hypothesis matching the relational triple verbatim);
* `relTriple_true _ _` (vacuous postcondition `fun _ _ => True`, via the product coupling);
* `relTriple_post_const` together with `intros; trivial` (postcondition reduces to a
  trivially provable proposition such as `() = ()`);
* `relTriple_refl` (identical computations, equality coupling);
* `relTriple_eqRel_of_eq rfl` (syntactically identical computations);
* `relTriple_pure_pure rfl` (`pure x ⨯ pure x` with reflexive postcondition);
* `relTriple_pure_pure` together with `assumption` (`pure a ⨯ pure b` with `R a b` in scope);
* quantitative `Std.Do'.RelTriple` pure-pure leaves;
* the same closers after `subst_vars` (resolves goals where the pure values are
  syntactically distinct but unified via local equality hypotheses);
* `relTriple_pure_pure ∘ symm` (`pure a ⨯ pure b` with `R b a` in scope). -/
def tryCloseRelGoalImmediate : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_true _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
    intros; trivial)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    (try subst_vars
     first
       | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
       | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
       | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
       | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
       | exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _
       | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)
       | (refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
          intros; trivial)))) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> (symm; assumption)))

private def relationalGoalParts? (target : Expr) : Option (Expr × Expr × Expr) :=
  match relTripleGoalParts? target with
  | some parts => some parts
  | none =>
      match relWPGoalParts? target with
      | some parts => some parts
      | none =>
          match stdDoRelTripleGoalParts? target with
          | some (_, oa, ob, post) => some (oa, ob, post)
          | none => none

private def isStdDoRelTripleGoal (target : Expr) : Bool :=
  (stdDoRelTripleGoalParts? target).isSome

def tryLowerRelGoal : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if relationalGoalParts? target |>.isSome then
    return false
  if isGameEquivGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.GameEquiv.of_relTriple))
  else if isEvalDistEqGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel))
  else
    return false

/-- Normalize the monad structure of both sides of a relational/eRHL goal.

Applies the standard set of monad simplification lemmas (right-association, pure-bind
elimination, `bind_pure_comp`, `Functor.map_map`, `map_pure`) to flatten nested binds
and strip pure-bind layers so that downstream rule selection (especially
`relTriple_bind`) sees aligned structures on both sides. The pass is best-effort:
`try simp only` always succeeds and leaves the goal unchanged when no lemma applies. -/
def tryNormalizeRelBindStructure : TacticM Unit := do
  let _ ← tryEvalTacticSyntax (← `(tactic|
    try simp only [bind_assoc, pure_bind, bind_pure_comp, Functor.map_map, map_pure]))

def runERelPureRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _))

def runERelBindRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.Loom.relTriple_bind ?_ ?_))

def runERelBindRuleUsing (cut : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.Loom.relTriple_bind (cut := $cut) ?_ ?_))

private def runStdDoRelTripleBindLeftRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post) := stdDoRelTripleGoalParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && !isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_left_le _ _ _ _ _ _)))

private def runStdDoRelTripleBindRightRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post) := stdDoRelTripleGoalParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless !isBindExpr oa && isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_right_le _ _ _ _ _ _)))

/-- Monad-law normalization used as a fallback when a direct `relTriple_bind`
attempt fails. Flattens nested binds (`bind_assoc`) and reduces `pure_bind` so
that `commit`-style intermediate computations (e.g. `do x ← oa; pure (x, x)`)
align with the corresponding flat form on the other side. -/
def tryFlattenRelBindGoal : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
      OracleComp.bind_pure_comp]))

/-- After `relTriple_bind ?_ ?_` produces `[sample, continuation, …pre-existing]`,
this helper tries to auto-close the sample subgoal (typically `RelTriple oa oa
(EqRel _)` closes via `relTriple_refl`) and the continuation subgoal in isolation,
then puts any unclosed continuation first for the user's natural `intro`-style flow.

Pre-existing goals (those already in the goal list before `relTriple_bind` produced
the two new subgoals at the head) are preserved unchanged at the tail; the helper
never touches or reorders them. This guards against the multi-goal scenario where
`rvcstep` is invoked on a goal sitting alongside other open goals (for example,
after `constructor`): a naive close-then-swap would, when the sample closes,
swap the continuation with an unrelated trailing goal, and a follow-up close pass
could fire on it. -/
def closeSampleAndReorderBindGoals : TacticM Unit := do
  let goalsBefore ← getGoals
  match goalsBefore with
  | sample :: continuation :: rest =>
      setGoals [sample]
      let _ ← tryCloseRelGoalImmediate
      let postSample ← getGoals
      setGoals [continuation]
      let _ ← tryCloseRelGoalImmediate
      let postCont ← getGoals
      setGoals (postCont ++ postSample ++ rest)
  | _ => pure ()

def runRelBindRule : TacticM Bool := do
  tryNormalizeRelBindStructure
  if ← tryCloseRelGoalImmediate then
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_)) then
    closeSampleAndReorderBindGoals
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_)) then
    closeSampleAndReorderBindGoals
    return true
  -- Fallback: flatten nested binds via monad laws and retry the EqRel-bind cut.
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind
         (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))) then
    closeSampleAndReorderBindGoals
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_))) then
    closeSampleAndReorderBindGoals
    return true
  return false

/-- Bijection-coupling interpretation of an `rvcstep using f` hint when both sides
of a bind start with a uniform sample / query.

Given a goal `RelTriple ((⋯ : OracleComp _ α) >>= fa) ((⋯ : OracleComp _ α) >>= fb) S`,
applies `relTriple_bind` with the cut `R := fun a b => b = f a`, closes the sample
subgoal via `relTriple_uniformSample_bij` (or `relTriple_query_bij`), and on the
continuation introduces the coupled values together with the equality witness and
substitutes it.

Resulting goal order:
1. The continuation `RelTriple (fa a) (fb (f a)) S` for an arbitrary fresh `a`.
2. The bijectivity side condition `Function.Bijective f`.
3. Any prior trailing goals.

Returns `true` iff every step of the recipe fired; otherwise restores state and
returns `false` so a caller can try a different interpretation of the hint. -/
def runRelBindBijRuleUsing (f : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  -- Best-effort normalization so `<$>` / `bind_pure_comp` shapes are also
  -- recognized as bind-on-both-sides for the purposes of the recipe.
  let _ ← tryEvalTacticSyntax (← `(tactic|
    try simp only [bind_assoc, pure_bind, bind_pure_comp, Functor.map_map, map_pure,
      map_bind, OracleComp.bind_pure_comp]))
  unless ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (R := fun a b => b = $f a) ?_ ?_)) do
    saved.restore
    return false
  let bindGoals ← getGoals
  match bindGoals with
  | sample :: cont :: rest =>
      setGoals [sample]
      let sampleClosed ← tryEvalTacticSyntax (← `(tactic|
        first
          | refine OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij
              (f := $f) ?_ _ (fun _ => rfl)
          | refine OracleComp.ProgramLogic.Relational.relTriple_query_bij
              _ (f := $f) ?_ _ (fun _ => rfl)))
      unless sampleClosed do
        saved.restore
        return false
      let bijGoals ← getGoals
      setGoals [cont]
      let _ ← tryEvalTacticSyntax (← `(tactic| intro _ _ heq; subst heq))
      let contGoals ← getGoals
      setGoals (contGoals ++ bijGoals ++ rest)
      return true
  | _ =>
      saved.restore
      return false

def runRelBindRuleUsing (R : TSyntax `term) : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_)) then
    closeSampleAndReorderBindGoals
    return true
  -- Fallback 1: flatten nested binds and retry with the explicit cut.
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_))) then
    closeSampleAndReorderBindGoals
    return true
  -- Fallback 2: hint may be a bijection `f : α → α` (not a relation).
  -- Try the bijection-coupling recipe used when both sides bind a uniform sample.
  if ← runRelBindBijRuleUsing R then
    return true
  return false

def runRelMapRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_map))

def runRelReplicateRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate))

def runRelMapMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))

def runRelMapMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := $R) ?_ ?_))

def runRelFoldlMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same))

def runRelFoldlMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
      (Rin := $R) ?_ ?_ ?_))

def runRelRndRuleUsing (f : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f) <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f) <;> skip))

def runRelRndRuleWithContextBijection : TacticM Bool := withMainContext do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if let some app := findAppWithHead? ``Function.Bijective type then
        if let some args := trailingArgs? app 1 then
          let fStx ← PrettyPrinter.delab args[0]!
          if ← runRelRndRuleUsing fStx then
            return true
  return false

def runRelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_query _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  runRelRndRuleWithContextBijection <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij <;> skip))

def runRelCondRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    (simp only [game_rule]
     apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _)))

def runByUptoRule (bad : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
      (bad := $bad)))

def runRelSimRule : TacticM Bool := withMainContext do
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

def runRelSimRuleUsing (R : TSyntax `term) : TacticM Bool := withMainContext do
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

def runRelSimDistRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, post) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) || !isEqRelPost post then
        return false
      tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_impl_evalDist_eq))
  | none => return false

private def rawRelWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  if let some parts := relWPGoalParts? target then
    return parts
  let target := target.consumeMData
  let rhs ←
    if target.isAppOfArity ``LE.le 4 ||
        target.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
      some (target.getArg! 3)
    else
      none
  let app ← findAppWithHead? ``Std.Do'.rwp rhs
  let args ← trailingArgs? app 5
  let #[oa, ob, post, _epost₁, _epost₂] := args | none
  some (oa, ob, post)

private def isRawStdDoRelWPGoal (target : Expr) : Bool :=
  (rawRelWPGoalParts? target).isSome ||
    (findAppWithHead? ``Std.Do'.rwp target).isSome

private def rawRelWPGoalFullParts? (target : Expr) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr) := do
  let target := target.consumeMData
  let pre ←
    if target.isAppOfArity ``LE.le 4 ||
        target.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
      some (target.getArg! 2)
    else
      none
  let rhs := target.getArg! 3
  let app ← findAppWithHead? ``Std.Do'.rwp rhs
  let args ← trailingArgs? app 5
  let #[oa, ob, post, epost₁, epost₂] := args | none
  some (pre, oa, ob, post, epost₁, epost₂)

private def pureValue? (e : Expr) : Option Expr := do
  let e := e.consumeMData
  guard <| e.getAppFn.isConstOf ``Pure.pure
  e.getAppArgs.back?

private def monadFnFromCompType? (type : Expr) : Option Expr := do
  let type := type.consumeMData
  let args := type.getAppArgs
  guard <| 0 < args.size
  some <| mkAppN type.getAppFn (args.extract 0 (args.size - 1))

private def rawOrderBounds? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``LE.le 4 ||
      type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
    return some (type.getArg! 2, type.getArg! 3)
  return none

private def runRawRelWPReflRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (lhs, rhs) ← rawOrderBounds? target | return false
  unless (← isDefEq lhs rhs) do
    return false
  tryEvalTacticSyntax (← `(tactic| exact Lean.Order.PartialOrder.rel_refl))

/-- Direct leaf rule for raw `Std.Do'.rwp` pure-pure goals.
This handles the raw counterpart of the folded quantitative `RelTriple` pure
case without first manufacturing a registered-rule consequence wrapper. -/
private def runRawRelWPPureRule : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      let target ← instantiateMVars (← goal.getType)
      let some (_pre, oa, ob, post, epost₁, epost₂) := rawRelWPGoalFullParts? target
        | return false
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      let some a := pureValue? oa | return false
      let some b := pureValue? ob | return false
      try
        let some m₁ := monadFnFromCompType? (← inferType oa) | return false
        let some m₂ := monadFnFromCompType? (← inferType ob) | return false
        let pred ← inferType (mkApp2 post a b)
        let epred₁ ← inferType epost₁
        let epred₂ ← inferType epost₂
        let prf ← mkAppOptM ``Std.Do'.RelWP.rwp_pure
          #[some m₁, some m₂, some pred, some epred₁, some epred₂,
            none, none, none, none, none, none, none, none,
            none, none, some a, some b, some post, some epost₁, some epost₂]
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
        let prf ← instantiateMVars prf
        if prf.hasExprMVar then
          throwError "raw rwp pure proof still has metavariables:{indentExpr prf}"
        let prfTy ← instantiateMVars (← inferType prf)
        unless ← isDefEq target prfTy do
          return false
        goal.assign prf
        setGoals rest
        return true
      catch _ =>
        return false

/-- Direct bind rule for raw `Std.Do'.rwp` goals with binds on both sides. -/
private def runRawRelWPBindRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post, _epost₁, _epost₂) := rawRelWPGoalFullParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_le _ _ _ _ _ _ _)))

/-- Explicit left-bind rule for raw `Std.Do'.rwp` goals. -/
private def runRawRelWPBindLeftRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post, _epost₁, _epost₂) := rawRelWPGoalFullParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && !isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_left_le _ _ _ _ _ _)))

/-- Explicit right-bind rule for raw `Std.Do'.rwp` goals. -/
private def runRawRelWPBindRightRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post, _epost₁, _epost₂) := rawRelWPGoalFullParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless !isBindExpr oa && isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_right_le _ _ _ _ _ _)))

/-- Try direct-hit registered `@[vcspec]` rules against a raw relational WP goal. -/
private def runRawRelWPTheoremConseq (thm : TSyntax `term)
    (requireClosed : Bool := false) : TacticM Bool := do
  unless isRawStdDoRelWPGoal (← instantiateMVars (← getMainTarget)) do
    return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic|
        refine Std.Do'.RelWP.rwp_consequence_rel _ _ _ _ _ _
          (by
            intro a b
            by_cases h : a = b <;> simp [h, Lean.Order.PartialOrder.rel])
          $thm))
      discard <| tryEvalTacticSyntax (← `(tactic|
        all_goals first
          | assumption
          | trivial
          | simp [Lean.Order.PartialOrder.rel]
          | (repeat intro; split_ifs <;> simp [Lean.Order.PartialOrder.rel])))
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

private def runRawRelWPVCSpecBackward : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some (oa, ob, _) := rawRelWPGoalParts? target | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    let entries :=
      entries.filter (·.kind == .relWP) ++ entries.filter (·.kind == .relTriple)
    for entry in entries.toList.take 8 do
      let saved ← saveState
      if ← liftMetaM <| entry.hasProofPremise then
        let ok ←
          match ← observing? do
            unless ← runVCSpecEntryRawRelConsequence entry do
              throwError "raw relational consequence rule did not apply"
            discard <| tryEvalTacticSyntax (← `(tactic|
              all_goals first
                | assumption
                | trivial
                | simp [Lean.Order.PartialOrder.rel]
                | (repeat intro; split_ifs <;> simp [Lean.Order.PartialOrder.rel])))
          with
          | some _ => pure true
          | none => pure false
        if ok then
          return true
        saved.restore
      let ok ←
        match ← observing? do
          runVCSpecEntryCachedBackward entry
        with
        | some ok => pure ok
        | none => pure false
      if ok then
        return true
      saved.restore
    return false

/-- Controlled one-sided relational bind step on the left. -/
def runRVCGenRawBindLeftStep : TacticM Bool := withMainContext do
  runRawRelWPBindLeftRule <||> runStdDoRelTripleBindLeftRule

/-- Controlled one-sided relational bind step on the right. -/
def runRVCGenRawBindRightStep : TacticM Bool := withMainContext do
  runRawRelWPBindRightRule <||> runStdDoRelTripleBindRightRule

def runRVCGenCore : TacticM Bool := withVCGenStructuralTiming <| withMainContext do
  tryNormalizeRelBindStructure
  if ← runRawRelWPReflRule then
    return true
  if ← runRawRelWPPureRule then
    return true
  if ← runRawRelWPBindRule then
    return true
  if ← runRawRelWPVCSpecBackward then
    return true
  let target ← instantiateMVars (← getMainTarget)
  if let some (pre, oa, ob, _) := stdDoRelTripleGoalParts? target then
    let _ := pre
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if ← tryCloseRelGoalImmediate then
      return true
    if ← runERelPureRule then
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

private def closeRelTheoremStepGoals : TacticM Unit := do
  discard <| tryEvalTacticSyntax (← `(tactic|
    all_goals try (repeat intro; split_ifs <;> simp [Lean.Order.PartialOrder.rel])))
  discard <| tryEvalTacticSyntax (← `(tactic|
    all_goals first
      | assumption
      | trivial
      | simp [Lean.Order.PartialOrder.rel]
      | (repeat intro; split_ifs <;> simp [Lean.Order.PartialOrder.rel])
      | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
      | (refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
         intros; trivial)
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
           | (repeat intro; split_ifs <;> simp [Lean.Order.PartialOrder.rel])
           | (refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
              intros; trivial))))

/-- Try to close a relational goal by applying postcondition monotonicity and
closing both the inner triple and the implication from local hypotheses. -/
def tryCloseRelGoalConseq : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_post_mono <;> assumption))

private def runRVCGenStepWithTheoremDirect
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals
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
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals
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
  if isRawStdDoRelWPGoal target && (← liftMetaM <| entry.hasProofPremise) then
    let saved ← saveState
    let ok ←
      match ← observing? do
        unless ← runVCSpecEntryRawRelConsequence entry do
          throwError "raw relational consequence rule did not apply"
        closeRelTheoremStepGoals
      with
      | some _ => pure true
      | none => pure false
    if ok && (!requireClosed || (← getGoals).isEmpty) then
      return true
    saved.restore
  let saved ← saveState
  let ok ←
    match ← observing? do
      unless ← runVCSpecEntryCachedBackward entry do
        throwError "rvcstep: registered `@[vcspec]` rule did not apply"
      closeRelTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  if isRawStdDoRelWPGoal target then
    if let some declName := entry.declName? then
      if ← runRVCGenStepWithTheoremConseq (mkIdent declName) requireClosed then
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

private def registeredRVCGenRuleCandidateTiers : TacticM (Array (Array VCSpecEntry)) := do
  let target ← instantiateMVars (← getMainTarget)
  let some kind := relationalGoalKind? target | return #[]
  let some (oa, ob, _) := relationalGoalParts? target <|> rawRelWPGoalParts? target | return #[]
  let goalPattern := classifyRelationalCompPattern oa ob
  let direct :=
    (← getRegisteredRelationalVCSpecEntries oa ob).filter (·.kind == kind)
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

/-- Find the registered relational `@[vcspec]` entries whose bounded
application makes progress on the current goal. Prefers direct
discrimination-tree hits on `(oa, ob)`, falling back to kind-matched entries
filtered by structural compatibility. -/
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
  if ← runRVCGenCore then
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
      "rvcstep"
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
  if let some hintName ← findUniquePriorityRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if ← runRVCGenCore then
    return true
  if let some hintName ← findUniqueRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if ← withVCGenCloseTiming tryCloseRelGoalConseq then
    return true
  if let some entry := (← findRegisteredRVCGenRuleCandidates).toList.head? then
    if ← runRelationalVCSpecRule entry then
      return true
  return progress

def runRVCGenStepUsing (hint : TSyntax `term) : TacticM Bool := do
  runRVCGenExplicitHintStep hint

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

def throwRVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rvcstep: failed to lower the `GameEquiv` goal into relational proof mode."
  if isEvalDistEqGoal target then
    throwError "rvcstep: failed to lower the `evalDist` equality into a `RelTriple` goal."
  match relationalGoalParts? target with
  | none =>
      throwError m!
        "rvcstep: expected a `GameEquiv`, `evalDist` equality, `RelTriple`, `RelWP`,\n\
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

def runRVCGenFinish : TacticM Unit := do
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [game_rule]))
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals first
        | assumption
        | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
        | (refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
           intros; trivial)
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
             | (refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
                intros; trivial))))
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "rvcgen finish" runRVCGenCloseConseqPass

end Relational
end TacticInternals
end OracleComp.ProgramLogic
