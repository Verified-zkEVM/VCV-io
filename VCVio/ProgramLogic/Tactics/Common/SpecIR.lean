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

/-- Indexed sub-expressions extracted from a `@[vcspec]` theorem, used to compute
discrimination-tree keys for structural lookup.

For unary kinds (`Triple` / `wp`), `comp?` holds the computation argument.
For relational kinds (`RelTriple` / `RelWP` / `eRelTriple`), `pair?` holds
`(oa, ob)`. These expressions live in the same `MetaM` state as the
`forallMetaTelescopeReducing` call that introduced their metavariables, and so
must be consumed (e.g. fed to `DiscrTree.mkPath`) before that state is dropped. -/
structure VCSpecIndexExprs where
  comp? : Option Expr := none
  pair? : Option (Expr × Expr) := none
  deriving Inhabited

namespace VCSpecIndexExprs

/-- Index expressions for a unary spec keyed on `comp`. -/
def unary (comp : Expr) : VCSpecIndexExprs := { comp? := some comp }

/-- Index expressions for a relational spec keyed on `(oa, ob)`. -/
def relational (oa ob : Expr) : VCSpecIndexExprs := { pair? := some (oa, ob) }

end VCSpecIndexExprs

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

/-- Normalize a `@[vcspec]` theorem target into a `NormalizedVCSpec` paired with
the indexed sub-expressions needed to build discrimination-tree keys.

The returned `VCSpecIndexExprs` reference metavariables introduced by the
internal `forallMetaTelescopeReducing` call and must be consumed inside the
same `MetaM` invocation. -/
def normalizeAndExtractVCSpecTarget (attrName : Name) (declTy : Expr) :
    MetaM (NormalizedVCSpec × VCSpecIndexExprs) := do
  let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  let binderCount := xs.size
  if let some (pre, comp, post) := tripleGoalParts? targetTy then
    let spec : NormalizedVCSpec := {
      kind := .unaryTriple
      lookupKey := .unary (← headConstNameOrError attrName "unary computations" comp)
      compPattern := classifyUnaryCompPattern comp
      theoremBinderCount := binderCount
      preShape := some (classifyArgShape pre)
      postShape := classifyArgShape post
    }
    return (spec, .unary comp)
  if let some (pre, comp, post) := rawWPGoalParts? targetTy then
    let spec : NormalizedVCSpec := {
      kind := .unaryWP
      lookupKey := .unary (← headConstNameOrError attrName "unary computations" comp)
      compPattern := classifyUnaryCompPattern comp
      theoremBinderCount := binderCount
      preShape := some (classifyArgShape pre)
      postShape := classifyArgShape post
    }
    return (spec, .unary comp)
  if let some (comp, post) := wpGoalParts? targetTy then
    let spec : NormalizedVCSpec := {
      kind := .unaryWP
      lookupKey := .unary (← headConstNameOrError attrName "unary computations" comp)
      compPattern := classifyUnaryCompPattern comp
      theoremBinderCount := binderCount
      preShape := none
      postShape := classifyArgShape post
    }
    return (spec, .unary comp)
  if let some (oa, ob, post) := relTripleGoalParts? targetTy then
    let spec : NormalizedVCSpec := {
      kind := .relTriple
      lookupKey := ← relationalLookupKeyOrError oa ob
      compPattern := classifyRelationalCompPattern oa ob
      theoremBinderCount := binderCount
      preShape := none
      postShape := classifyArgShape post
    }
    return (spec, .relational oa ob)
  if let some (oa, ob, post) := relWPGoalParts? targetTy then
    let spec : NormalizedVCSpec := {
      kind := .relWP
      lookupKey := ← relationalLookupKeyOrError oa ob
      compPattern := classifyRelationalCompPattern oa ob
      theoremBinderCount := binderCount
      preShape := none
      postShape := classifyArgShape post
    }
    return (spec, .relational oa ob)
  if let some (pre, oa, ob, post) := eRelTripleGoalParts? targetTy then
    let spec : NormalizedVCSpec := {
      kind := .eRelTriple
      lookupKey := ← relationalLookupKeyOrError oa ob
      compPattern := classifyRelationalCompPattern oa ob
      theoremBinderCount := binderCount
      preShape := some (classifyArgShape pre)
      postShape := classifyArgShape post
    }
    return (spec, .relational oa ob)
  throwError
    m!"@[{attrName}] expects a theorem whose target is one of:\n\
    - a unary `Triple`\n\
    - a unary raw `wp` goal\n\
    - a relational `RelTriple`\n\
    - a relational raw `RelWP`\n\
    - an `eRelTriple`\n\
    got:{indentExpr declTy}"

/-- Normalize a `@[vcspec]` theorem target, dropping the extracted index
expressions. Use `normalizeAndExtractVCSpecTarget` when the indexed
sub-expressions are needed (e.g. by the registry to build `DiscrTree` keys). -/
def normalizeVCSpecTarget (attrName : Name) (declTy : Expr) : MetaM NormalizedVCSpec := do
  return (← normalizeAndExtractVCSpecTarget attrName declTy).1

end OracleComp.ProgramLogic
