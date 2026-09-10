/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.ProgramLogic.Relational.Loom.Quantitative
public import VCVio.ProgramLogic.Relational.SimulateQ
public meta import VCVio.ProgramLogic.Tactics.Common

/-!
# Relational VCGen rules and step implementations
-/

public meta section

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
  OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_refl
  OracleComp.ProgramLogic.Relational.Loom.relTriple_query_bij
  OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl
  -- Raw relational WP rule from the Std.Do bridge
  Std.Do'.RelWP.rwp_pure
  -- `simulateQ`-aware rules from `Relational/SimulateQ.lean`
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_query_map_eq

private def mkRVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }

private structure RelGoalShape where
  oa : Expr
  ob : Expr
  isStdDo : Bool

private def relGoalShape? (target : Expr) : Option RelGoalShape := do
  if let some (_pre, oa, ob, _post) := stdDoRelTripleGoalParts? target then
    some { oa, ob, isStdDo := true }
  else if let some (oa, ob, _post) := relTripleGoalParts? target then
    some { oa, ob, isStdDo := false }
  else
    none

private def currentRelGoalShape? : TacticM (Option RelGoalShape) := do
  let target ← instantiateMVars (← getMainTarget)
  match relGoalShape? target with
  | none => return none
  | some shape =>
      let oa ← whnfReducible (← instantiateMVars shape.oa)
      let ob ← whnfReducible (← instantiateMVars shape.ob)
      return some { shape with oa, ob }

private def relCompsDefEq (oa ob : Expr) : TacticM Bool := do
  let saved ← saveState
  let ok ← isDefEq oa ob
  saved.restore
  return ok

private def propClosesByTrivial (prop : Expr) : TacticM Bool := do
  let saved ← saveState
  let goal ← mkFreshExprMVar prop
  let goalId := goal.mvarId!
  setGoals [goalId]
  let ok ← tryEvalTacticSyntax (← `(tactic| trivial))
  let closed := ok && (← getGoals).isEmpty
  saved.restore
  return closed

private def relPostIsVacuous (post : Expr) : TacticM Bool := do
  let post ← instantiateMVars post
  let postTy ← whnf (← inferType post)
  let .forallE _ α body _ := postTy.consumeMData
    | return false
  let body ← whnf body
  let .forallE _ β _ _ := body.consumeMData
    | return false
  withLocalDeclD `a α fun a => do
    withLocalDeclD `b β fun b => do
      let prop ← whnfReducible (← instantiateMVars (mkApp2 post a b))
      if prop.isConstOf ``True then
        return true
      propClosesByTrivial prop

/-- Attempt to close the current relational/eRHL leaf goal with the canonical fast paths.

Tries, in order:
* `assumption` (catches a hypothesis matching the relational triple verbatim);
* quantitative `Std.Do'.RelTriple` pure-pure leaves;
* `relTriple_refl` (identical computations, equality coupling);
* `relTriple_eqRel_of_eq rfl` (syntactically identical computations);
* `relTriple_pure_pure rfl` (`pure x ⨯ pure x` with reflexive postcondition);
* `relTriple_pure_pure` together with `assumption` (`pure a ⨯ pure b` with `R a b` in scope);
* a small proof-search variant of `relTriple_pure_pure` using `rfl`, `assumption`, or
  a symmetric assumption for the value-level relation;
* the same closers after `subst_vars` (resolves goals where the pure values are
  syntactically distinct but unified via local equality hypotheses);
* `relTriple_true _ _` / `relTriple_post_const` only when the postcondition has first
  been classified as vacuous.

The vacuous-postcondition rules are intentionally last and guarded. Applying them blindly to
non-vacuous pure leaves can create expensive failed elaboration attempts and obscure the
predictable pure/reflexive close path. -/
def tryCloseRelGoalImmediate : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic| assumption)) then
    return true
  let target ← instantiateMVars (← getMainTarget)
  let relTriplePost? := relTripleGoalParts? target |>.map (fun (_, _, post) => post)
  let some shape ← currentRelGoalShape? | return false
  if shape.isStdDo then
    if isPureExpr shape.oa && isPureExpr shape.ob then
      return (← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _)))
    return false
  if ← relCompsDefEq shape.oa shape.ob then
    if ← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) then
      return true
  if isPureExpr shape.oa && isPureExpr shape.ob then
    if ← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ?_ <;>
          first | rfl | assumption | symm; assumption)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        (try subst_vars
         first
           | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
           | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
           | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
           | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)))) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> (symm; assumption))) then
      return true
  if let some post := relTriplePost? then
    if ← relPostIsVacuous post then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_post_const
            (fun _ _ => by trivial))) then
        return true
  let saved ← saveState
  if ← tryEvalTacticSyntax (← `(tactic| subst_vars)) then
    let some shape ← currentRelGoalShape? | saved.restore; return false
    if !shape.isStdDo && (← relCompsDefEq shape.oa shape.ob) then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) then
        return true
    if !shape.isStdDo && isPureExpr shape.oa && isPureExpr shape.ob then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ?_ <;>
            first | rfl | assumption | symm; assumption)) then
        return true
    if shape.isStdDo && isPureExpr shape.oa && isPureExpr shape.ob then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _)) then
        return true
    saved.restore
  return false

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

private def sameMVarId (x y : MVarId) : Bool :=
  x.name == y.name

private def stripSuffix? (xs suffix : List MVarId) : Option (List MVarId) :=
  if xs.length < suffix.length then
    none
  else
    let splitAt := xs.length - suffix.length
    let pref := xs.take splitAt
    let tail := xs.drop splitAt
    if (tail.zip suffix).all fun (x, y) => sameMVarId x y then
      some pref
    else
      none

private def ownedSubgoalsAfterMainStep (before after : List MVarId) : List MVarId × List MVarId :=
  match before with
  | [] => (after, [])
  | _ :: rest =>
      match stripSuffix? after rest with
      | some owned => (owned, rest)
      | none => (after, [])

/-- Lower game equivalence or distribution equality to a relational proof goal. -/
def tryLowerRelGoal : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if relationalGoalParts? target |>.isSome then
    return false
  if isGameEquivGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.GameEquiv.of_relTriple))
  else if isEvalDistEqGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.evalSPMF_eq_of_relTriple_eqRel))
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

/-- Apply the quantitative relational rule for two pure computations. -/
def runERelPureRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _))

/-- Try reflexive quantitative coupling rules for oracle queries and uniform samples. -/
def runERelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_refl))

/-- Apply quantitative relational bind composition. -/
def runERelBindRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.Loom.relTriple_bind ?_ ?_))

/-- Apply quantitative relational bind composition with an explicit intermediate assertion. -/
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

private def tryCloseRelOwnedGoal : TacticM Bool := do
  let ok ← tryCloseRelGoalImmediate
  if ok then
    return (← getGoals).isEmpty
  let ok ← tryEvalTacticSyntax (← `(tactic|
      first
        | assumption
        | trivial
        | (intro _; assumption)
        | (simp only [OracleComp.ProgramLogic.Relational.EqRel]; symm; assumption)))
  if ok then
    return (← getGoals).isEmpty
  let target ← instantiateMVars (← getMainTarget)
  if (relationalGoalParts? target).isSome || (findAppWithHead? ``Std.Do'.rwp target).isSome then
    return false
  let ok ← tryEvalTacticSyntax (← `(tactic|
      first
        | simp only [Lean.Order.PartialOrder.rel]
        | (repeat intro; split_ifs <;> simp only [Lean.Order.PartialOrder.rel])))
  return ok && (← getGoals).isEmpty

private def closeOwnedRelSubgoals (owned : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in owned do
    if ← goal.isAssigned then
      continue
    setGoals [goal]
    unless ← tryCloseRelOwnedGoal do
      remaining := remaining ++ (← getGoals)
  return remaining

/-- Cheap owned-goal closer used after explicit user-guided decomposition.

This avoids the heavier relational leaf closer and its fallback simplification. In particular,
`rvcstep using R` should close the sample side of a bind and close only trivial continuations
such as `intros; assumption`, otherwise leaving the continuation for the user's proof script. -/
private def tryCloseRelOwnedGoalCheap : TacticM Bool := do
  let ok ← tryEvalTacticSyntax (← `(tactic|
      first
        | assumption
        | trivial
        | (intros; assumption)
        | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
        | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;>
            first | rfl | assumption | symm; assumption)
        | (intros
           subst_vars
           first
             | assumption
             | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
             | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;>
                first | rfl | assumption | symm; assumption))
        | (simp only [OracleComp.ProgramLogic.Relational.EqRel]; symm; assumption)))
  return ok && (← getGoals).isEmpty

/-- Run `tryCloseRelOwnedGoalCheap` on exactly the listed owned goals, preserving failures. -/
private def closeOwnedRelSubgoalsCheap (owned : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in owned do
    if ← goal.isAssigned then
      continue
    setGoals [goal]
    unless ← tryCloseRelOwnedGoalCheap do
      remaining := remaining ++ (← getGoals)
  return remaining

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
      let postSample ← closeOwnedRelSubgoals [sample]
      let postCont ← closeOwnedRelSubgoals [continuation]
      setGoals (postCont ++ postSample ++ rest)
  | _ => pure ()

/-- Close the bind sample subgoal normally and the continuation only by cheap closers.

This is the explicit-cut variant of `closeSampleAndReorderBindGoals`, used by
`rvcstep using R`. Supplying `R` is already the strategic choice, so the tactic should not
run the full continuation closer and accidentally search through the user-owned continuation. -/
private def closeSampleAndCheapContinuation : TacticM Unit := do
  let goalsBefore ← getGoals
  match goalsBefore with
  | sample :: continuation :: rest =>
      let postSample ← closeOwnedRelSubgoals [sample]
      let postCont ← closeOwnedRelSubgoalsCheap [continuation]
      setGoals (postCont ++ postSample ++ rest)
  | _ => pure ()

/-- Try immediate or support-sensitive relational bind decomposition. -/
def runRelBindRule : TacticM Bool := do
  tryNormalizeRelBindStructure
  if (← getGoals).isEmpty then
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
applies a specialized bind-bijection rule when possible. The continuation then
mentions only the left sample, with the right sample already rewritten to `f a`.

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
    try simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Functor.map_map,
      map_pure, map_bind]))
  if ← tryEvalTacticSyntax (← `(tactic|
      first
        | refine OracleComp.ProgramLogic.Relational.relTriple_bind_uniformSample_bij
            (f := $f) ?_ ?_
        | refine OracleComp.ProgramLogic.Relational.relTriple_bind_query_bij
            _ (f := $f) ?_ ?_)) then
    match ← getGoals with
    | cont :: bijGoals =>
        setGoals [cont]
        let _ ← tryEvalTacticSyntax (← `(tactic| intro x))
        discard <| tryCloseRelOwnedGoalCheap
        let contGoals ← getGoals
        setGoals (contGoals ++ bijGoals)
        return true
    | _ =>
        saved.restore
        return false
  saved.restore
  let saved ← saveState
  let _ ← tryEvalTacticSyntax (← `(tactic|
    try simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Functor.map_map,
      map_pure, map_bind]))
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
      discard <| tryCloseRelOwnedGoalCheap
      let contGoals ← getGoals
      setGoals (contGoals ++ bijGoals ++ rest)
      return true
  | _ =>
      saved.restore
      return false

/-- Decompose relational binds using the supplied intermediate relation. -/
def runRelBindRuleUsing (R : TSyntax `term) : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_)) then
    closeSampleAndCheapContinuation
    return true
  -- Fallback 1: flatten nested binds and retry with the explicit cut.
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_))) then
    closeSampleAndCheapContinuation
    return true
  -- Fallback 2: hint may be a bijection `f : α → α` (not a relation).
  -- Try the bijection-coupling recipe used when both sides bind a uniform sample.
  if ← runRelBindBijRuleUsing R then
    return true
  return false

/-- Apply the relational rule for mapping both computations. -/
def runRelMapRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_map))

/-- Apply the relational rule for repeated computations. -/
def runRelReplicateRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate))

/-- Apply a relational list-traversal rule, preferring the same-input specialization. -/
def runRelMapMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))

private def closeRelAssumptionSideGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  let (owned, rest) := ownedSubgoalsAfterMainStep before after
  let remainingOwned ← closeOwnedRelSubgoals owned
  setGoals (remainingOwned ++ rest)

/-- Apply relational list traversal with an explicit input-element relation. -/
def runRelMapMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let before ← getGoals
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
        (Rin := $R) ?_ ?_)) then
    closeRelAssumptionSideGoals before
    return true
  return false

/-- Apply the relational left-fold rule for a shared input list. -/
def runRelFoldlMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same))

/-- Apply relational left folding with an explicit input-element relation. -/
def runRelFoldlMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let before ← getGoals
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
        (Rin := $R) ?_ ?_ ?_)) then
    closeRelAssumptionSideGoals before
    return true
  return false

/-- Couple oracle queries or uniform samples using the supplied bijection. -/
def runRelRndRuleUsing (f : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f) <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f) <;> skip))

/-- Search the local context for a bijection usable by a sampling rule. -/
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

/-- Try direct, reflexive, or locally bijective sampling couplings. -/
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

/-- Split synchronized conditional computations and introduce the branch assumptions. -/
def runRelCondRule : TacticM Bool := do
  let before ← getGoals
  if ← tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _)) <||>
      tryEvalTacticSyntax (← `(tactic|
        (simp only [game_rule]
         apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _))) then
    let after ← getGoals
    let (owned, rest) := ownedSubgoalsAfterMainStep before after
    let remainingOwned ← closeOwnedRelSubgoals owned
    setGoals (remainingOwned ++ rest)
    return true
  return false

/-- Bound simulation distance by the probability of the supplied bad predicate. -/
def runByUptoRule (bad : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
      (bad := $bad)))

/-- Swap the two computations in a relational triple. -/
def runRelSymmRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_symm))

/-- Factor a relational triple through the supplied intermediate computation. -/
def runRelTransRule (mid : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
      (mid := $mid) ?_ ?_)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right
      (mid := $mid) ?_ ?_))

/-- Swap adjacent independent binds in the left computation using relational transitivity. -/
def runRelSwapLeftRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
      (hleft := OracleComp.ProgramLogic.Relational.relTriple_bind_bind_swap_eqRel) ?_))

/-- Swap adjacent independent binds in the right computation using relational transitivity. -/
def runRelSwapRightRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right
      (hright := OracleComp.ProgramLogic.Relational.relTriple_bind_bind_swap_eqRel) ?_))

/-- Swap left-hand binds and apply bind composition with the supplied relation. -/
def runRelSwapLeftRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  if ← runRelSwapLeftRule then
    if ← runRelBindRuleUsing R then
      return true
  saved.restore
  return false

/-- Swap right-hand binds and apply bind composition with the supplied relation. -/
def runRelSwapRightRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  if ← runRelSwapRightRule then
    if ← runRelBindRuleUsing R then
      return true
  saved.restore
  return false

/-- Apply stateful simulation coupling when both computations run oracle simulations. -/
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

/-- Apply stateful simulation coupling with an explicit state relation. -/
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

/-- Apply the output-distribution specialization of stateful simulation coupling. -/
def runRelSimDistRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, post) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) || !isEqRelPost post then
        return false
      tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_impl_evalSPMF_eq))
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
      let before ← getGoals
      evalTactic (← `(tactic|
        refine Std.Do'.RelWP.rwp_consequence_rel _ _ _ _ _ _
          (by
            intro a b
            by_cases h : a = b <;> simp [h, Lean.Order.PartialOrder.rel])
          $thm))
      let after ← getGoals
      let (owned, rest) := ownedSubgoalsAfterMainStep before after
      let remainingOwned ← closeOwnedRelSubgoals owned
      setGoals (remainingOwned ++ rest)
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Registered relational rules that are safe as deterministic structural steps.
They may decompose the current goal, but they do not choose cuts, bijections, or
one-sided bind frontiers. -/
private def structuralRelVCSpecDecls : List Name := [
  ``OracleComp.ProgramLogic.Relational.relTriple_map,
  ``OracleComp.ProgramLogic.Relational.relTriple_replicate,
  ``OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same
]

/-- Registered relational rules that close deterministic leaves. -/
private def leafRelVCSpecDecls : List Name := [
  ``OracleComp.ProgramLogic.Relational.relTriple_pure_pure,
  ``OracleComp.ProgramLogic.Relational.relTriple_uniformSample_refl,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_pure,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_refl,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl,
  ``Std.Do'.RelWP.rwp_pure
]

/-- Registered relational rules that require an explicit user choice. -/
private def explicitRelVCSpecDecls : List Name := [
  ``OracleComp.ProgramLogic.Relational.relTriple_bind,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_mapM,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_foldlM,
  ``OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij,
  ``OracleComp.ProgramLogic.Relational.relTriple_query_bij,
  ``OracleComp.ProgramLogic.Relational.relTriple_bind_uniformSample_bij,
  ``OracleComp.ProgramLogic.Relational.relTriple_bind_query_bij,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_bind,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_bij,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_query_bij
]

private inductive RelVCSpecTier where
  | structural
  | leaf
  | explicit
  | fallback
  deriving BEq

private def relVCSpecEntryDeclIn (entry : VCSpecEntry) (decls : List Name) : Bool :=
  match entry.declName? with
  | some declName => decls.contains declName
  | none => false

private def relVCSpecTier (entry : VCSpecEntry) : RelVCSpecTier :=
  if relVCSpecEntryDeclIn entry structuralRelVCSpecDecls then
    .structural
  else if relVCSpecEntryDeclIn entry leafRelVCSpecDecls then
    .leaf
  else if relVCSpecEntryDeclIn entry explicitRelVCSpecDecls then
    .explicit
  else
    .fallback

private def RelVCSpecTier.canRunInDefaultDirect : RelVCSpecTier → Bool
  | .explicit => false
  | _ => true

private def RelVCSpecTier.canRunInDefaultStructural : RelVCSpecTier → Bool
  | .structural | .leaf => true
  | _ => false

private def RelVCSpecTier.canRunInFallbackSearch : RelVCSpecTier → Bool
  | .fallback => true
  | _ => false

private def runRawRelWPVCSpecBackward : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some (oa, ob, _) := rawRelWPGoalParts? target | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    let entries :=
      (entries.filter fun entry =>
        entry.kind == .relWP && (relVCSpecTier entry).canRunInDefaultDirect) ++
      (entries.filter fun entry =>
        entry.kind == .relTriple && (relVCSpecTier entry).canRunInDefaultDirect)
    for entry in entries.toList.take 8 do
      let saved ← saveState
      if entry.kind == .relWP then
        let ok ←
          match ← observing? do
            let before ← getGoals
            unless ← runVCSpecEntryRawRelConsequence entry do
              throwError "raw relational consequence rule did not apply"
            let after ← getGoals
            let (owned, rest) := ownedSubgoalsAfterMainStep before after
            let remainingOwned ← closeOwnedRelSubgoals owned
            setGoals (remainingOwned ++ rest)
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

end Relational
end TacticInternals
end OracleComp.ProgramLogic
