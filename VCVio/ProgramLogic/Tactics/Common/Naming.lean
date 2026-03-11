/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common.Core

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

def isUsableBinderName (name : Name) : Bool :=
  !name.isAnonymous && !name.hasMacroScopes

def mkSupportHypName (name : Name) : Name :=
  Name.mkSimple s!"h{toString name}"

private partial def freshUserNameAux (used : Name → Bool) (base : String) (idx : Nat) : Name :=
  let candidate :=
    if idx = 0 then
      Name.mkSimple base
    else
      Name.mkSimple s!"{base}{idx + 1}"
  if used candidate then
    freshUserNameAux used base (idx + 1)
  else
    candidate

def freshUserNameLike (base : Name) : TacticM Name := do
  let baseStr :=
    if base.isAnonymous then
      "x"
    else
      toString base
  let lctx ← getLCtx
  return freshUserNameAux (fun name => (lctx.findFromUserName? name).isSome) baseStr 0

def freshenSuggestedNames (names : Array Name) : TacticM (Array Name) := do
  let lctx ← getLCtx
  let mut used : List Name := []
  let mut result := #[]
  for name in names do
    let base :=
      if name.isAnonymous then
        Name.mkSimple "x"
      else
        name
    let mut idx := 0
    let mut fresh := base
    let mut searching := true
    while searching do
      fresh :=
        if idx = 0 then
          base
        else
          Name.mkSimple s!"{toString base}{idx + 1}"
      if (lctx.findFromUserName? fresh).isSome || fresh ∈ used then
        idx := idx + 1
      else
        searching := false
    used := fresh :: used
    result := result.push fresh
  return result

def binderNameFromExpr? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .lam name _ _ _ => if isUsableBinderName name then some name else none
  | .forallE name _ _ _ => if isUsableBinderName name then some name else none
  | _ => none

def getBindLambdaName? (comp : Expr) : Option Name := do
  guard (isBindExpr comp)
  let args := comp.consumeMData.getAppArgs
  let lam := args[args.size - 1]!
  binderNameFromExpr? lam

def probGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``probEvent target <|> findAppWithHead? ``probOutput target
  let args ← trailingArgs? app 2
  some args[0]!

partial def getLeadingBinderNames (target : Expr) : Array Name :=
  let rec go (e : Expr) (acc : Array Name) :=
    match e.consumeMData with
    | .forallE name _ body _ =>
        let acc :=
          if isUsableBinderName name then
            acc.push name
          else
            acc
        go body acc
    | _ => acc
  go target #[]

def getGoalBindVarName? : TacticM (Option Name) := do
  let target ← instantiateMVars (← getMainTarget)
  if let some comp := tripleGoalComp? target then
    return getBindLambdaName? comp
  if let some comp := probGoalComp? target then
    return getBindLambdaName? comp
  return none

def getSuggestedIntroNames (count : Nat) : TacticM (Array Name) := do
  let target ← instantiateMVars (← getMainTarget)
  let explicit := getLeadingBinderNames target
  let bindName? ← getGoalBindVarName?
  let baseNames :=
    if explicit.isEmpty then
      match bindName? with
      | some name =>
          if count = 1 then
            #[name]
          else
            #[name, mkSupportHypName name]
      | none =>
          if count = 1 then
            #[Name.mkSimple "x"]
          else
            #[Name.mkSimple "x", Name.mkSimple "hx"]
    else
      explicit
  let names :=
    if count ≤ baseNames.size then
      baseNames.extract 0 count
    else if baseNames.size = 1 && count = 2 then
      #[baseNames[0]!, mkSupportHypName baseNames[0]!]
    else
      let defaults :=
        #[Name.mkSimple "x", Name.mkSimple "hx", Name.mkSimple "y", Name.mkSimple "hy"]
      (baseNames ++ defaults).extract 0 count
  freshenSuggestedNames names

def getProbCongrNames (supportSensitive : Bool) : TacticM (Array Name) := do
  let count := if supportSensitive then 2 else 1
  let target ← instantiateMVars (← getMainTarget)
  let bindName? := do
    let comp ← probGoalComp? target
    getBindLambdaName? comp
  let names :=
    match bindName? with
    | some name =>
        if supportSensitive then
          #[name, mkSupportHypName name]
        else
          #[name]
    | none =>
        if supportSensitive then
          #[Name.mkSimple "x", Name.mkSimple "hx"]
        else
          #[Name.mkSimple "x"]
  let names :=
    if names.size < count then
      names.push (Name.mkSimple "hx")
    else
      names
  freshenSuggestedNames names

def introMainGoalNames (names : Array Name) : TacticM Bool := do
  let mut progress := false
  for name in names do
    if ← tryEvalTacticSyntax (← `(tactic| intro $(mkIdent name):ident)) then
      progress := true
  return progress

def introAllGoalsNames (names : Array Name) : TacticM Unit := do
  for name in names do
    discard <| tryEvalTacticSyntax (← `(tactic| all_goals first | intro $(mkIdent name):ident | skip))

def renameInaccessibleNames (names : Array Name) : TacticM Unit := do
  for name in names do
    discard <| tryEvalTacticSyntax (← `(tactic| all_goals first | rename_i $(mkIdent name):ident | skip))

def renderAsClause (names : Array Name) : String :=
  if names.isEmpty then
    ""
  else
    let body := String.intercalate ", " <| names.toList.map toString
    s!" as ⟨{body}⟩"

end OracleComp.ProgramLogic
