/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.Core

/-!
# `@[wpStep]` Registry

Discrimination-tree backed registry for the equational `wp _ _ = …` rewrites used by
the inner driver of `vcstep` / `vcgen` for raw `wp`-shaped goals.

A `@[wpStep]` lemma has shape `wp comp post = …`; the registry indexes it by the
discrimination-tree path of its `comp` argument. The dispatch tactic
`runWpStepRules`, together with the canonical registrations for every shipped
`wp_*` lemma, lives in `VCVio.ProgramLogic.Tactics.Common.WpStepDispatch`.
-/

open Lean Elab Meta Lean.Meta

namespace OracleComp.ProgramLogic

/-- Pre-computed discrimination-tree keys for the `comp` sub-expression of a
`@[wpStep]` theorem (the LHS computation in `wp comp post = …`). -/
abbrev WpStepPatternKeys := Array DiscrTree.Key

/-- A registered `@[wpStep]` lemma: its declaration name plus the discrimination-tree
keys for fast structural lookup against the `oa` of a `wp oa post` goal. -/
structure WpStepEntry where
  decl : Name
  patternKeys : WpStepPatternKeys
  deriving Inhabited, BEq, Repr

/-- Persistent state for the `@[wpStep]` registry.

* `all` retains insertion order, exposed for diagnostics / tooling.
* `tree` is the discrimination tree used by `getRegisteredWpStepEntries`. -/
structure WpStepRegistry where
  all : Array WpStepEntry := #[]
  tree : DiscrTree WpStepEntry := .empty
  deriving Inhabited

private def WpStepRegistry.addToTree (tree : DiscrTree WpStepEntry) (entry : WpStepEntry) :
    DiscrTree WpStepEntry :=
  if entry.patternKeys.isEmpty then tree
  else tree.insertKeyValue entry.patternKeys entry

initialize wpStepRegistry :
    SimpleScopedEnvExtension WpStepEntry WpStepRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      { registry with
          all := registry.all.push entry
          tree := WpStepRegistry.addToTree registry.tree entry }
    initial := {}
  }

/-- Extract the LHS computation `comp` from a `@[wpStep]` theorem whose target,
after instantiating universally quantified variables, has shape `wp comp post = …`.
Returns `none` if the target is not an `Eq` whose LHS is a `wp` application. -/
private def extractWpStepLhsComp (declTy : Expr) : MetaM (Option Expr) := do
  let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
  let target := targetTy.consumeMData
  unless target.isAppOfArity ``Eq 3 do return none
  let lhs := target.getArg! 1
  match wpGoalParts? lhs with
  | some (oa, _) => return some oa
  | none => return none

private def buildWpStepEntry (decl : Name) (declTy : Expr) : MetaM WpStepEntry := do
  let some lhsComp ← extractWpStepLhsComp declTy
    | throwError m!
        "@[wpStep] expects a theorem of shape `wp comp post = …`; got:{indentExpr declTy}"
  let keys ← DiscrTree.mkPath lhsComp
  return { decl, patternKeys := keys }

initialize registerBuiltinAttribute {
  name := `wpStep
  descr := "Register an equational `wp comp post = …` rule for the runWpStepRules planner."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let entry ← buildWpStepEntry decl declTy
    wpStepRegistry.add entry kind
}

/-- Retrieve the `@[wpStep]` entries whose LHS pattern matches `oa` structurally. -/
def getRegisteredWpStepEntries (oa : Expr) : MetaM (Array WpStepEntry) := do
  let oa ← instantiateMVars oa
  let registry := wpStepRegistry.getState (← getEnv)
  registry.tree.getMatch oa

end OracleComp.ProgramLogic
