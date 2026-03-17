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

structure CompiledUnaryVCSpecRule where
  entry : VCSpecEntry
  modes : Array UnaryRuleApplicationMode
  deriving Inhabited, Repr

def CompiledUnaryVCSpecRule.theoremName (rule : CompiledUnaryVCSpecRule) : Name :=
  rule.entry.decl

def CompiledUnaryVCSpecRule.kind (rule : CompiledUnaryVCSpecRule) : VCSpecKind :=
  rule.entry.kind

def CompiledUnaryVCSpecRule.replayText (rule : CompiledUnaryVCSpecRule) : String :=
  s!"vcstep with {rule.theoremName}"

def CompiledUnaryVCSpecRule.canUseConsequence (rule : CompiledUnaryVCSpecRule) : Bool :=
  rule.modes.contains .tripleConseq

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

def getCompiledUnaryVCSpecRules (comp : Expr) : MetaM (Array CompiledUnaryVCSpecRule) := do
  return compileUnaryVCSpecRules (← getRegisteredUnaryVCSpecEntries comp)

def getCompiledUnaryVCSpecRulesOfKind (kind : VCSpecKind) : CoreM (Array CompiledUnaryVCSpecRule) := do
  return compileUnaryVCSpecRules (← getVCSpecEntriesOfKind kind)

end OracleComp.ProgramLogic
