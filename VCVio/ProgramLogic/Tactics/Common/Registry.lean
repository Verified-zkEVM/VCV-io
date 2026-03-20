/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.Core

open Lean Elab Meta

namespace OracleComp.ProgramLogic

inductive VCSpecKind where
  | unaryTriple
  | unaryWP
  | relTriple
  | relWP
  | eRelTriple
  deriving Inhabited, BEq, Repr

structure VCSpecEntry where
  decl : Name
  kind : VCSpecKind
  deriving Inhabited, BEq, Repr

structure VCSpecRegistry where
  all : List VCSpecEntry := []
  unary : NameMap (Array VCSpecEntry) := {}
  relational : NameMap (NameMap (Array VCSpecEntry)) := {}
  deriving Inhabited

private def VCSpecRegistry.addUnary
    (registry : VCSpecRegistry) (head : Name) (entry : VCSpecEntry) : VCSpecRegistry :=
  let prev := match registry.unary.find? head with
    | some prev => prev
    | none => #[]
  { registry with unary := registry.unary.insert head (prev.push entry) }

private def VCSpecRegistry.addRelational
    (registry : VCSpecRegistry) (leftHead rightHead : Name) (entry : VCSpecEntry) :
    VCSpecRegistry :=
  let inner := match registry.relational.find? leftHead with
    | some inner => inner
    | none => {}
  let prev := match inner.find? rightHead with
    | some prev => prev
    | none => #[]
  { registry with
      relational := registry.relational.insert leftHead (inner.insert rightHead (prev.push entry)) }

private def headConstNameOrError (attrName : Name) (kindMsg : String) (comp : Expr) :
    MetaM Name := do
  let comp ← whnfReducible (← instantiateMVars comp)
  let some head := headConstName? comp
    | throwError
        m!"@[{attrName}] only supports {kindMsg} with a constant head symbol, got:{indentExpr comp}"
  return head

private def relationalHeadsOrError (oa ob : Expr) : MetaM (Name × Name) := do
  let leftHead ← headConstNameOrError `vcspec "relational left computations" oa
  let rightHead ← headConstNameOrError `vcspec "relational right computations" ob
  return (leftHead, rightHead)

private def detectVCSpecShape (declTy : Expr) : MetaM (VCSpecKind × Sum Name (Name × Name)) := do
  let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  if let some comp := tripleGoalComp? targetTy then
    return (.unaryTriple, .inl (← headConstNameOrError `vcspec "unary computations" comp))
  if let some comp := wpGoalComp? targetTy then
    return (.unaryWP, .inl (← headConstNameOrError `vcspec "unary computations" comp))
  if let some (oa, ob, _) := relTripleGoalParts? targetTy then
    return (.relTriple, .inr (← relationalHeadsOrError oa ob))
  if let some (oa, ob, _) := relWPGoalParts? targetTy then
    return (.relWP, .inr (← relationalHeadsOrError oa ob))
  if let some (_, oa, ob, _) := eRelTripleGoalParts? targetTy then
    return (.eRelTriple, .inr (← relationalHeadsOrError oa ob))
  throwError
    m!"@[vcspec] expects a theorem whose target is one of:\n\
    - a unary `Triple`\n\
    - a unary raw `wp` goal\n\
    - a relational `RelTriple`\n\
    - a relational raw `RelWP`\n\
    - an `eRelTriple`\n\
    got:{indentExpr declTy}"

initialize vcSpecRegistry :
    SimpleScopedEnvExtension
      (VCSpecEntry × Sum Name (Name × Name))
      VCSpecRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry (entry, key) =>
      let registry := { registry with all := entry :: registry.all }
      match key with
      | .inl head => registry.addUnary head entry
      | .inr (leftHead, rightHead) => registry.addRelational leftHead rightHead entry
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `vcspec
  descr := "Register a unary or relational program-logic theorem for vcgen/rvcgen lookup."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (specKind, key) ← detectVCSpecShape declTy
    vcSpecRegistry.add ({ decl, kind := specKind }, key) kind
}

private def getUnaryEntriesForHead (head : Name) : CoreM (Array VCSpecEntry) := do
  pure <| match (vcSpecRegistry.getState (← getEnv)).unary.find? head with
    | some entries => entries
    | none => #[]

private def getRelationalEntriesForHeads (leftHead rightHead : Name) :
    CoreM (Array VCSpecEntry) := do
  pure <| match (vcSpecRegistry.getState (← getEnv)).relational.find? leftHead with
    | none => #[]
    | some inner =>
        match inner.find? rightHead with
        | some entries => entries
        | none => #[]

def getRegisteredUnaryVCSpecEntries (comp : Expr) : MetaM (Array VCSpecEntry) := do
  let comp ← whnfReducible (← instantiateMVars comp)
  let some head := headConstName? comp
    | return #[]
  getUnaryEntriesForHead head

def getRegisteredRelationalVCSpecEntries (oa ob : Expr) : MetaM (Array VCSpecEntry) := do
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  let some leftHead := headConstName? oa
    | return #[]
  let some rightHead := headConstName? ob
    | return #[]
  getRelationalEntriesForHeads leftHead rightHead

def getRegisteredUnaryVCSpecTheorems (comp : Expr) : MetaM (Array Name) := do
  return (← getRegisteredUnaryVCSpecEntries comp).map (·.decl)

def getRegisteredRelationalVCSpecTheorems (oa ob : Expr) : MetaM (Array Name) := do
  return (← getRegisteredRelationalVCSpecEntries oa ob).map (·.decl)

def getVCSpecEntriesOfKind (kind : VCSpecKind) : CoreM (Array VCSpecEntry) := do
  let registry := vcSpecRegistry.getState (← getEnv)
  return (registry.all.filter (·.kind == kind)).toArray

def getVCSpecTheoremsOfKind (kind : VCSpecKind) : CoreM (Array Name) := do
  return (← getVCSpecEntriesOfKind kind).map (·.decl)

end OracleComp.ProgramLogic
