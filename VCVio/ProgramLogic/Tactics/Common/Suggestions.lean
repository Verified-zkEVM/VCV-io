/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import Lean.Meta.Tactic.TryThis

/-!
# VCGen Suggestions

Helpers for attaching `Try this` suggestions to tactic diagnostics.
-/

open Lean Meta

namespace OracleComp.ProgramLogic

def addTryThisTextSuggestion (ref : Syntax) (text : String) : MetaM Unit := do
  Meta.Tactic.TryThis.addSuggestion ref
    { suggestion := .string text }
    (origSpan? := some ref)
    (header := "Try this:\n")

end OracleComp.ProgramLogic
