/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic
import VCVio.ProgramLogic.Tactics.Common.WpStepRegistry
import VCVio.ProgramLogic.Unary.SimulateQ

/-!
# `runWpStepRules` Dispatch

Dispatch tactic for raw `wp`-shaped goals plus the canonical `@[wpStep]`
registrations for every `wp_*` lemma shipped in
`VCVio/ProgramLogic/Unary/HoareTriple.lean` and
`VCVio/ProgramLogic/Unary/SimulateQ.lean`.

The registrations live here (rather than in the rule files themselves) because
`Unary/HoareTriple.lean` and `Unary/SimulateQ.lean` sit below the tactic
infrastructure in the import DAG, mirroring the centralized `attribute [vcspec]`
block in `VCVio/ProgramLogic/Tactics/Relational/Internals.lean`.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-! ## Canonical registrations -/

attribute [wpStep]
  -- Pure / bind / branching from `Unary/HoareTriple.lean`
  OracleComp.ProgramLogic.wp_pure
  OracleComp.ProgramLogic.wp_bind
  OracleComp.ProgramLogic.wp_ite
  OracleComp.ProgramLogic.wp_dite
  OracleComp.ProgramLogic.wp_map
  -- Replicate / list iterators
  OracleComp.ProgramLogic.wp_replicate_zero
  OracleComp.ProgramLogic.wp_replicate_succ
  OracleComp.ProgramLogic.wp_list_mapM_nil
  OracleComp.ProgramLogic.wp_list_mapM_cons
  OracleComp.ProgramLogic.wp_list_foldlM_nil
  OracleComp.ProgramLogic.wp_list_foldlM_cons
  -- Sampling / queries
  OracleComp.ProgramLogic.wp_query
  OracleComp.ProgramLogic.wp_uniformSample
  -- `simulateQ` / coercion-bridging from `Unary/SimulateQ.lean`
  OracleComp.ProgramLogic.wp_simulateQ_eq
  OracleComp.ProgramLogic.wp_simulateQ_run'_eq
  OracleComp.ProgramLogic.wp_liftComp

/-! ## Dispatch -/

/-- Advance a `wp`-shaped goal by one rewrite, dispatching via the `@[wpStep]`
discrimination-tree registry.

Locates the `wp oa post` sub-expression of the main target, asks the registry for
entries whose LHS pattern matches `oa`, and tries each in turn (`rw`, then
`simp only` as a fallback to cover bound-variable LHSs that block `rw`). Returns
`false` when no candidate succeeds, or when the goal contains no `wp`
application at all. -/
def runWpStepRules : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some wpApp := findAppWithHead? ``OracleComp.ProgramLogic.wp target | return false
  let some args := trailingArgs? wpApp 2 | return false
  let oa ← instantiateMVars args[0]!
  let entries ← getRegisteredWpStepEntries oa
  for entry in entries do
    let rwStx ← `(tactic| rw [$(mkIdent entry.decl):ident])
    if ← tryEvalTacticSyntax rwStx then return true
    let simpStx ← `(tactic| simp only [$(mkIdent entry.decl):ident])
    if ← tryEvalTacticSyntax simpStx then return true
  return false

end OracleComp.ProgramLogic
