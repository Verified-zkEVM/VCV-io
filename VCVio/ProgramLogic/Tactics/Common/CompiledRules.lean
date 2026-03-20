/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common.Registry

open Lean Elab Meta

namespace OracleComp.ProgramLogic

inductive UnaryRuleApplicationMode where
  | direct
  | tripleConseq
  deriving Inhabited, BEq, Repr

inductive RelationalRuleApplicationMode where
  | direct
  | postConseq
  deriving Inhabited, BEq, Repr

structure CompiledUnaryVCSpecRule where
  entry : VCSpecEntry
  modes : Array UnaryRuleApplicationMode
  deriving Inhabited, Repr

structure CompiledRelationalVCSpecRule where
  entry : VCSpecEntry
  modes : Array RelationalRuleApplicationMode
  deriving Inhabited, Repr

def CompiledUnaryVCSpecRule.theoremName (rule : CompiledUnaryVCSpecRule) : Name :=
  rule.entry.decl

def CompiledUnaryVCSpecRule.kind (rule : CompiledUnaryVCSpecRule) : VCSpecKind :=
  rule.entry.kind

def CompiledUnaryVCSpecRule.replayText (rule : CompiledUnaryVCSpecRule) : String :=
  s!"vcstep with {rule.theoremName}"

def CompiledUnaryVCSpecRule.canUseConsequence (rule : CompiledUnaryVCSpecRule) : Bool :=
  rule.modes.contains .tripleConseq

def CompiledRelationalVCSpecRule.theoremName (rule : CompiledRelationalVCSpecRule) : Name :=
  rule.entry.decl

def CompiledRelationalVCSpecRule.kind (rule : CompiledRelationalVCSpecRule) : VCSpecKind :=
  rule.entry.kind

def CompiledRelationalVCSpecRule.replayText (rule : CompiledRelationalVCSpecRule) : String :=
  s!"rvcstep with {rule.theoremName}"

def CompiledRelationalVCSpecRule.canUseConsequence (rule : CompiledRelationalVCSpecRule) : Bool :=
  rule.modes.contains .postConseq

def compileUnaryVCSpecRule? (entry : VCSpecEntry) : Option CompiledUnaryVCSpecRule :=
  match entry.kind with
  | .unaryTriple =>
      let modes :=
        if entry.spec.postShape == .concrete then
          #[.direct, .tripleConseq]
        else
          #[.direct]
      some { entry, modes }
  | .unaryWP =>
      some { entry, modes := #[.direct] }
  | _ => none

def compileUnaryVCSpecRules (entries : Array VCSpecEntry) : Array CompiledUnaryVCSpecRule :=
  entries.filterMap compileUnaryVCSpecRule?

def compileRelationalVCSpecRule? (entry : VCSpecEntry) : Option CompiledRelationalVCSpecRule :=
  match entry.kind with
  | .relTriple | .eRelTriple =>
      let modes :=
        if entry.spec.postShape == .concrete then
          #[.direct, .postConseq]
        else
          #[.direct]
      some { entry, modes }
  | .relWP =>
      some { entry, modes := #[.direct] }
  | _ => none

def compileRelationalVCSpecRules
    (entries : Array VCSpecEntry) : Array CompiledRelationalVCSpecRule :=
  entries.filterMap compileRelationalVCSpecRule?

def getCompiledUnaryVCSpecRules (comp : Expr) : MetaM (Array CompiledUnaryVCSpecRule) := do
  return compileUnaryVCSpecRules (← getRegisteredUnaryVCSpecEntries comp)

def getCompiledUnaryVCSpecRulesOfKind (kind : VCSpecKind) :
    CoreM (Array CompiledUnaryVCSpecRule) := do
  return compileUnaryVCSpecRules (← getVCSpecEntriesOfKind kind)

def getCompiledRelationalVCSpecRules (oa ob : Expr) :
    MetaM (Array CompiledRelationalVCSpecRule) := do
  return compileRelationalVCSpecRules (← getRegisteredRelationalVCSpecEntries oa ob)

def getCompiledRelationalVCSpecRulesOfKind (kind : VCSpecKind) :
    CoreM (Array CompiledRelationalVCSpecRule) := do
  return compileRelationalVCSpecRules (← getVCSpecEntriesOfKind kind)

end OracleComp.ProgramLogic
