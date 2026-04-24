/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common.Registry

/-! # Compiled Program-Logic Rules

This module packages registered unary and relational VC-spec rules into compact compiled forms
used by the `vcstep` and `rvcstep` tactic infrastructure.
-/

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
  deriving Inhabited

structure CompiledRelationalVCSpecRule where
  entry : VCSpecEntry
  modes : Array RelationalRuleApplicationMode
  deriving Inhabited

def CompiledUnaryVCSpecRule.theoremName (rule : CompiledUnaryVCSpecRule) : Name :=
  rule.entry.theoremName!

def CompiledUnaryVCSpecRule.kind (rule : CompiledUnaryVCSpecRule) : VCSpecKind :=
  rule.entry.kind

def CompiledUnaryVCSpecRule.replayText (rule : CompiledUnaryVCSpecRule) : String :=
  s!"vcstep with {rule.theoremName}"

def CompiledUnaryVCSpecRule.canUseConsequence (rule : CompiledUnaryVCSpecRule) : Bool :=
  rule.modes.contains .tripleConseq

def CompiledRelationalVCSpecRule.theoremName (rule : CompiledRelationalVCSpecRule) : Name :=
  rule.entry.theoremName!

def CompiledRelationalVCSpecRule.kind (rule : CompiledRelationalVCSpecRule) : VCSpecKind :=
  rule.entry.kind

def CompiledRelationalVCSpecRule.replayText (rule : CompiledRelationalVCSpecRule) : String :=
  s!"rvcstep with {rule.theoremName}"

def CompiledRelationalVCSpecRule.canUseConsequence (rule : CompiledRelationalVCSpecRule) : Bool :=
  rule.modes.contains .postConseq

-- Consequence modes (`.tripleConseq` / `.postConseq`) remain in the enums and their executors
-- remain in `Unary/Internals.lean` and `Relational/Internals.lean` so a future attribute can
-- opt rules in explicitly. The default compilation emits only `.direct`: every `@[vcspec]`
-- rule currently in the codebase is closed by direct application alone, and trying the
-- consequence fallback on every failed direct application was a per-`vcstep` cost with no
-- observed benefit.
def compileUnaryVCSpecRule? (entry : VCSpecEntry) : Option CompiledUnaryVCSpecRule :=
  match entry.kind with
  | .unaryTriple | .unaryWP => some { entry, modes := #[.direct] }
  | _ => none

def compileUnaryVCSpecRules (entries : Array VCSpecEntry) : Array CompiledUnaryVCSpecRule :=
  entries.filterMap compileUnaryVCSpecRule?

def compileRelationalVCSpecRule? (entry : VCSpecEntry) : Option CompiledRelationalVCSpecRule :=
  match entry.kind with
  | .relTriple | .eRelTriple | .relWP =>
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
