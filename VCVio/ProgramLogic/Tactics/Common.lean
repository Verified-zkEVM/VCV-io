/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic
import Lean.Meta.Match.MatcherApp
import VCVio.OracleComp.Constructions.Replicate
import VCVio.ProgramLogic.Notation

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

def whnfReducible (e : Expr) : MetaM Expr :=
  withReducible <| whnf e

def headConstName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

def trailingArgs? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.consumeMData.getAppArgs
  if _h : n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none

partial def findAppWithHead? (head : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.getAppFn.isConstOf head then
    some e
  else
    match e with
    | .app f a => findAppWithHead? head f <|> findAppWithHead? head a
    | .lam _ t b _ => findAppWithHead? head t <|> findAppWithHead? head b
    | .forallE _ t b _ => findAppWithHead? head t <|> findAppWithHead? head b
    | .letE _ t v b _ => findAppWithHead? head t <|> findAppWithHead? head v <|> findAppWithHead? head b
    | .mdata _ b => findAppWithHead? head b
    | .proj _ _ b => findAppWithHead? head b
    | _ => none

def relTripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelTriple target
  let args ← trailingArgs? app 3
  some (args[0]!, args[1]!, args[2]!)

def wpGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.wp target
  let args ← trailingArgs? app 2
  some args[0]!

def tripleGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Triple target
  let args ← trailingArgs? app 3
  some args[1]!

def isSimulateQAction (e : Expr) : Bool :=
  (findAppWithHead? ``simulateQ e).isSome

def hasStateTRunExpr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run e).isSome

def hasStateTRun'Expr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run' e).isSome

def hasStateTRunLike (e : Expr) : Bool :=
  hasStateTRunExpr e || hasStateTRun'Expr e

def hasSimulateQRunLike (e : Expr) : Bool :=
  isSimulateQAction e && hasStateTRunLike e

def isEqRelPost (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.ProgramLogic.Relational.EqRel e).isSome

def isBindExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Bind.bind

def isPureExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Pure.pure

def isIfExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``ite || e.consumeMData.getAppFn.isConstOf ``dite

def isMapExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Functor.map

def isReplicateExpr (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.replicate e).isSome

def isListMapMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.mapM e).isSome

def isListFoldlMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.foldlM e).isSome

def isReplicateHead (e : Expr) : Bool :=
  (headConstName? e) == some ``OracleComp.replicate

def isListMapMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.mapM

def isListFoldlMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.foldlM

def isGameEquivGoal (target : Expr) : Bool :=
  target.consumeMData.getAppFn.isConstOf ``OracleComp.ProgramLogic.GameEquiv

def isEvalDistEqGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getArg! 1
    let rhs := target.getArg! 2
    (findAppWithHead? ``evalDist lhs).isSome && (findAppWithHead? ``evalDist rhs).isSome
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

def tryEvalTacticSyntax (stx : Syntax) : TacticM Bool := do
  let some _ ← observing? (evalTactic stx) | return false
  return true

def runWpStepRules : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_bind])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_pure])) <||>
    tryEvalTacticSyntax (← `(tactic| simp only [OracleComp.ProgramLogic.wp_pure])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_replicate_zero])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_replicate_succ])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_mapM_nil])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_mapM_cons])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_foldlM_nil])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_list_foldlM_cons])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_query])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_ite])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_dite])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_uniformSample])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_map])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_simulateQ_eq])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_liftComp]))

end OracleComp.ProgramLogic
