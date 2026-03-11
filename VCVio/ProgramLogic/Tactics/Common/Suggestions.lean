/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Tactic.TryThis

open Lean Meta

namespace OracleComp.ProgramLogic

def addTryThisTextSuggestion (ref : Syntax) (text : String) : MetaM Unit := do
  Meta.Tactic.TryThis.addSuggestion ref
    { suggestion := .string text }
    (origSpan? := some ref)
    (header := "Try this:\n")

end OracleComp.ProgramLogic
