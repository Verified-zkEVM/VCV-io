/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common.Registry

/-!
# Backward application for VCSpec entries

Shared native application helpers for `@[vcspec]` entries.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/--
If `(prf, type)` proves a `Std.Do'.Triple`, return the corresponding
`pre ⊑ wp ...` proof via `Std.Do'.Triple.iff`.
Otherwise return the proof unchanged.
-/
private def bridgeTriple? (prf type : Expr) : MetaM (Expr × Expr) := do
  let type ← whnfR type
  if type.isAppOfArity ``Std.Do'.Triple 12 then
    let .const _ lvls := type.getAppFn
      | return (prf, type)
    let args := type.getAppArgs
    let tripleIff := mkAppN (mkConst ``Std.Do'.Triple.iff lvls)
      #[ args[0]!,  -- m
         args[1]!,  -- Pred
         args[2]!,  -- EPred
         args[4]!,  -- Monad
         args[5]!,  -- Assertion Pred
         args[6]!,  -- Assertion EPred
         args[7]!,  -- WP
         args[3]!,  -- α
         args[9]!,  -- x
         args[8]!,  -- pre
         args[10]!, -- post
         args[11]!  -- epost
       ]
    let prf' ← mkAppM ``Iff.mp #[tripleIff, prf]
    let type' ← instantiateMVars (← inferType prf')
    return (prf', type')
  return (prf, type)

/-- If a raw `≤` goal fixes the predicate carrier, push that information into
a universe-polymorphic `⊑` proof before `Meta.apply`. -/
private def fixPredFromGoal? (prfTy goalTy : Expr) : MetaM Unit := do
  let prfTy ← whnfR prfTy
  let goalTy ← whnfR goalTy
  unless prfTy.isAppOfArity ``Lean.Order.PartialOrder.rel 4 do return
  unless goalTy.isAppOfArity ``LE.le 4 do return
  let prfPred := prfTy.getArg! 0
  let goalPred := goalTy.getArg! 0
  _ ← isDefEq prfPred goalPred

/-- A goal whose target is already in `≤`/`⊑` weakest-precondition form. -/
private def isRawBackwardGoal (target : Expr) : MetaM Bool := do
  let target ← whnfR target
  return target.isAppOfArity ``LE.le 4 ||
    target.isAppOfArity ``Lean.Order.PartialOrder.rel 4

/-- Try to apply a registered `@[vcspec]` entry directly to a goal metavariable.

This instantiates the stored `SpecProof`, bridges `Triple` proofs when the goal
is already in raw weakest-precondition form, applies with fresh metavariables,
and returns the generated subgoals. Goal-specific close passes remain in the
unary and relational planners because they know which leaf rules are cheap and
valid for their logic. -/
def VCSpecEntry.tryApplyBackward (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let (_xs, _bis, prf, type) ← entry.proof.instantiate
  let goalTy ← instantiateMVars (← mvarId.getType)
  let (prf, type) ←
    if ← isRawBackwardGoal goalTy then
      bridgeTriple? prf type
    else
      pure (prf, type)
  fixPredFromGoal? type goalTy
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a `@[vcspec]` entry to the current main goal, preserving the tail goals.

This helper performs only the theorem application. Callers should run their
existing cheap close pass afterwards. -/
def runVCSpecEntryBackward (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyBackward goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

end OracleComp.ProgramLogic
