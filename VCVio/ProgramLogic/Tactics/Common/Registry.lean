/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.Core

open Lean Elab Meta

namespace OracleComp.ProgramLogic

initialize vcgenRegistry :
    SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (head, decl) =>
      let prev := match m.find? head with
        | some prev => prev
        | none => #[]
      m.insert head (prev.push decl)
    initial := {}
  }

initialize rvcgenRegistry :
    SimpleScopedEnvExtension ((Name × Name) × Name) (NameMap (NameMap (Array Name))) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m ((leftHead, rightHead), decl) =>
      let inner := match m.find? leftHead with
        | some inner => inner
        | none => {}
      let prev := match inner.find? rightHead with
        | some prev => prev
        | none => #[]
      m.insert leftHead (inner.insert rightHead (prev.push decl))
    initial := {}
  }

private def getVCGenHeadFromType (declTy : Expr) : MetaM Name := do
  let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  let some comp := tripleGoalComp? targetTy
    | throwError
        m!"@[vcgen] expects a theorem whose target is a unary `Triple` goal, got:{indentExpr declTy}"
  let comp ← whnfReducible (← instantiateMVars comp)
  let some head := headConstName? comp
    | throwError
        m!"@[vcgen] only supports computations with a constant head symbol, got:{indentExpr comp}"
  return head

private def getRVCGenHeadsFromType (declTy : Expr) : MetaM (Name × Name) := do
  let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  let some (oa, ob, _) := relTripleGoalParts? targetTy
    | throwError
        m!"@[rvcgen] expects a theorem whose target is a relational `RelTriple` goal, got:{indentExpr declTy}"
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  let some leftHead := headConstName? oa
    | throwError
        m!"@[rvcgen] only supports computations whose left side has a constant head symbol, got:{indentExpr oa}"
  let some rightHead := headConstName? ob
    | throwError
        m!"@[rvcgen] only supports computations whose right side has a constant head symbol, got:{indentExpr ob}"
  return (leftHead, rightHead)

initialize registerBuiltinAttribute {
  name := `vcgen
  descr := "Register a unary `Triple` theorem for qvcgen's opt-in head-symbol lookup."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let head ← getVCGenHeadFromType declTy
    vcgenRegistry.add (head, decl) kind
}

initialize registerBuiltinAttribute {
  name := `rvcgen
  descr := "Register a relational `RelTriple` theorem for rvcgen's opt-in head-symbol lookup."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let heads ← getRVCGenHeadsFromType declTy
    rvcgenRegistry.add (heads, decl) kind
}

def getRegisteredVCGenTheorems (comp : Expr) : MetaM (Array Name) := do
  let comp ← whnfReducible (← instantiateMVars comp)
  let some head := headConstName? comp
    | return #[]
  return match (vcgenRegistry.getState (← getEnv)).find? head with
    | some thms => thms
    | none => #[]

def getRegisteredRVCGenTheorems (oa ob : Expr) : MetaM (Array Name) := do
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  let some leftHead := headConstName? oa
    | return #[]
  let some rightHead := headConstName? ob
    | return #[]
  return match (rvcgenRegistry.getState (← getEnv)).find? leftHead with
    | none => #[]
    | some inner =>
        match inner.find? rightHead with
        | some thms => thms
        | none => #[]

end OracleComp.ProgramLogic
