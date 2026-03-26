/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.SpecIR

/-!
# VCSpec Registry

Shared registry structures for looking up VC specification lemmas by head symbol.
-/

open Lean Elab Meta

namespace OracleComp.ProgramLogic

structure VCSpecEntry where
  decl : Name
  spec : NormalizedVCSpec
  deriving Inhabited, BEq, Repr

def VCSpecEntry.kind (entry : VCSpecEntry) : VCSpecKind :=
  entry.spec.kind

def VCSpecEntry.lookupKey (entry : VCSpecEntry) : VCSpecLookupKey :=
  entry.spec.lookupKey

structure VCSpecRegistry where
  all : Array VCSpecEntry := #[]
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

initialize vcSpecRegistry :
    SimpleScopedEnvExtension
      VCSpecEntry
      VCSpecRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      let registry := { registry with all := registry.all.push entry }
      match entry.lookupKey with
      | .unary head => registry.addUnary head entry
      | .relational leftHead rightHead => registry.addRelational leftHead rightHead entry
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `vcspec
  descr := "Register a unary or relational program-logic theorem for vcgen/rvcgen lookup."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let spec ← normalizeVCSpecTarget `vcspec declTy
    vcSpecRegistry.add { decl, spec } kind
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
  return registry.all.filter (·.kind == kind)

def getVCSpecTheoremsOfKind (kind : VCSpecKind) : CoreM (Array Name) := do
  return (← getVCSpecEntriesOfKind kind).map (·.decl)

def getNormalizedUnaryVCSpecs (comp : Expr) : MetaM (Array NormalizedVCSpec) := do
  return (← getRegisteredUnaryVCSpecEntries comp).map (·.spec)

def getNormalizedRelationalVCSpecs (oa ob : Expr) : MetaM (Array NormalizedVCSpec) := do
  return (← getRegisteredRelationalVCSpecEntries oa ob).map (·.spec)

end OracleComp.ProgramLogic
