/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.Core

/-! # VC Spec Intermediate Representation

This module defines the intermediate representation used to classify and index program-logic
specification rules for tactic lookup and compilation.
-/

open Lean Elab Meta

namespace OracleComp.ProgramLogic

inductive VCSpecKind where
  | unaryTriple
  | unaryWP
  | relTriple
  | relWP
  | eRelTriple
  deriving Inhabited, BEq, Repr

inductive VCSpecLookupKey where
  | unary (head : Name)
  | relational (leftHead rightHead : Name)
  deriving Inhabited, BEq, Repr

inductive VCSpecArgShape where
  | schematic
  | concrete
  deriving Inhabited, BEq, Repr

inductive VCSpecCompForm where
  | bind
  | pure
  | ite
  | map
  | replicate
  | listMapM
  | listFoldlM
  | query
  | simulateQ
  | other
  deriving Inhabited, BEq, Repr

inductive VCSpecCompPattern where
  | unary (form : VCSpecCompForm)
  | relational (leftForm rightForm : VCSpecCompForm)
  deriving Inhabited, BEq, Repr

structure NormalizedVCSpec where
  kind : VCSpecKind
  lookupKey : VCSpecLookupKey
  compPattern : VCSpecCompPattern
  theoremBinderCount : Nat
  preShape : Option VCSpecArgShape
  postShape : VCSpecArgShape
  deriving Inhabited, BEq, Repr

def VCSpecLookupKey.toLegacyKey : VCSpecLookupKey → Sum Name (Name × Name)
  | .unary head => .inl head
  | .relational leftHead rightHead => .inr (leftHead, rightHead)

private def classifyArgShape (e : Expr) : VCSpecArgShape :=
  let e := e.consumeMData
  if e.isFVar || e.isMVar then
    .schematic
  else
    .concrete

private def headConstNameOrError (attrName : Name) (kindMsg : String) (comp : Expr) :
    MetaM Name := do
  let comp ← whnfReducible (← instantiateMVars comp)
  let some head := headConstName? comp
    | throwError
        m!"@[{attrName}] only supports {kindMsg} with a constant head symbol, got:{indentExpr comp}"
  return head

private def relationalLookupKeyOrError (oa ob : Expr) : MetaM VCSpecLookupKey := do
  let leftHead ← headConstNameOrError `vcspec "relational left computations" oa
  let rightHead ← headConstNameOrError `vcspec "relational right computations" ob
  return .relational leftHead rightHead

def classifyVCSpecCompForm (comp : Expr) : VCSpecCompForm :=
  let comp := comp.consumeMData
  if isBindExpr comp then
    .bind
  else if isPureExpr comp then
    .pure
  else if isIfExpr comp then
    .ite
  else if isMapExpr comp then
    .map
  else if isReplicateExpr comp then
    .replicate
  else if isListMapMExpr comp then
    .listMapM
  else if isListFoldlMExpr comp then
    .listFoldlM
  else if isSimulateQAction comp then
    .simulateQ
  else if (findAppWithHead? ``query comp).isSome then
    .query
  else
    .other

def classifyUnaryCompPattern (comp : Expr) : VCSpecCompPattern :=
  .unary (classifyVCSpecCompForm comp)

def classifyRelationalCompPattern (oa ob : Expr) : VCSpecCompPattern :=
  .relational (classifyVCSpecCompForm oa) (classifyVCSpecCompForm ob)

def normalizeVCSpecTarget (attrName : Name) (declTy : Expr) : MetaM NormalizedVCSpec := do
  let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  let binderCount := xs.size
  if let some (pre, comp, post) := tripleGoalParts? targetTy then
    return {
      kind := .unaryTriple
      lookupKey := .unary (← headConstNameOrError attrName "unary computations" comp)
      compPattern := classifyUnaryCompPattern comp
      theoremBinderCount := binderCount
      preShape := some (classifyArgShape pre)
      postShape := classifyArgShape post
    }
  if let some (pre, comp, post) := rawWPGoalParts? targetTy then
    return {
      kind := .unaryWP
      lookupKey := .unary (← headConstNameOrError attrName "unary computations" comp)
      compPattern := classifyUnaryCompPattern comp
      theoremBinderCount := binderCount
      preShape := some (classifyArgShape pre)
      postShape := classifyArgShape post
    }
  if let some (comp, post) := wpGoalParts? targetTy then
    return {
      kind := .unaryWP
      lookupKey := .unary (← headConstNameOrError attrName "unary computations" comp)
      compPattern := classifyUnaryCompPattern comp
      theoremBinderCount := binderCount
      preShape := none
      postShape := classifyArgShape post
    }
  if let some (oa, ob, post) := relTripleGoalParts? targetTy then
    return {
      kind := .relTriple
      lookupKey := ← relationalLookupKeyOrError oa ob
      compPattern := classifyRelationalCompPattern oa ob
      theoremBinderCount := binderCount
      preShape := none
      postShape := classifyArgShape post
    }
  if let some (oa, ob, post) := relWPGoalParts? targetTy then
    return {
      kind := .relWP
      lookupKey := ← relationalLookupKeyOrError oa ob
      compPattern := classifyRelationalCompPattern oa ob
      theoremBinderCount := binderCount
      preShape := none
      postShape := classifyArgShape post
    }
  if let some (pre, oa, ob, post) := eRelTripleGoalParts? targetTy then
    return {
      kind := .eRelTriple
      lookupKey := ← relationalLookupKeyOrError oa ob
      compPattern := classifyRelationalCompPattern oa ob
      theoremBinderCount := binderCount
      preShape := some (classifyArgShape pre)
      postShape := classifyArgShape post
    }
  throwError
    m!"@[{attrName}] expects a theorem whose target is one of:\n\
    - a unary `Triple`\n\
    - a unary raw `wp` goal\n\
    - a relational `RelTriple`\n\
    - a relational raw `RelWP`\n\
    - an `eRelTriple`\n\
    got:{indentExpr declTy}"

end OracleComp.ProgramLogic
