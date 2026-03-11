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

initialize registerBuiltinAttribute {
  name := `vcgen
  descr := "Register a unary `Triple` theorem for qvcgen's opt-in head-symbol lookup."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let head ← getVCGenHeadFromType declTy
    vcgenRegistry.add (head, decl) kind
}

def getRegisteredVCGenTheorems (comp : Expr) : MetaM (Array Name) := do
  let comp ← whnfReducible (← instantiateMVars comp)
  let some head := headConstName? comp
    | return #[]
  return match (vcgenRegistry.getState (← getEnv)).find? head with
    | some thms => thms
    | none => #[]

end OracleComp.ProgramLogic
